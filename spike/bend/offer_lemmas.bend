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
import ./resolution.bend as Res
import ./ops.bend as Ops
import ./standin.bend as Stand
import ./fetch.bend as Fetch
import ./bookmark_lemmas.bend as BmL
import ./spelling_lemmas.bend as Spell
import ./arrange_lemmas.bend as ArrangeL
import ./revision.bend as Rev
import ./sort_lemmas.bend as SortL

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

def or_l(a: Bool, -b: Bool, e: {a == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, e) : {Bool.or(_, b) == True{} : Bool}
  {==}

def some_inj(+a: String, -b: String, e: {Some{a} == Some{b} : Maybe<&2, String>}) -> {a == b : String}:
  Equal.cong(Maybe<&2, String>, String, m => Maybe.default(&2, String, m, a), Some{a}, Some{b}, e)

def m_none(m: Maybe<&2, String>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      Empty

def none_some(-x: String, e: {None{} == Some{x} : Maybe<&2, String>}) -> Empty:
  %e : {m_none(_) : Type}
  Unit{}

# The store's listing as `offer` was handed it: its payloads, documents
# and revisions, the rule files and bookmark files read from disk, each by
# its label and digest, and the files of `claims/`.
type Listing is Data:
  Listing{payloads: List<&2, T.Split>, documents: List<&2, T.Split>, revisions: List<&2, T.Split>, rules: List<&2, T.Split>, claims: List<&2, T.Split>, names: List<&2, T.Split>}

def body.splits(bs: List<&2, Prune.Body>) -> List<&2, T.Split>:
  match bs:
    case Nil{}:
      Nil{}
    case Prune.Body{+p, +d, ok, f} <> rest:
      T.Split{p, d} <> body.splits(rest)

def listing.of(s: Prune.Stored, +claims: List<&2, T.Split>, +rids: List<&2, T.Split>, +nids: List<&2, T.Split>) -> Listing:
  match s:
    case Prune.Stored{docs, revs, od, bs, ps, names, rules}:
      Listing{ps, body.splits(bs), revs, rids, claims, nids}

# The part of the listing a line of each kind is drawn from.
def group(g: Listing, +k: String) -> List<&2, T.Split>:
  match g:
    case Listing{ps, ds, vs, rs, cs, ns}:
      Bool.pick(List<&2, T.Split>, String.eq(k, "payload"), ps,
      Bool.pick(List<&2, T.Split>, String.eq(k, "operation"), ds,
      Bool.pick(List<&2, T.Split>, String.eq(k, "revision"), vs,
      Bool.pick(List<&2, T.Split>, String.eq(k, "rule"), rs,
      Bool.pick(List<&2, T.Split>, String.eq(k, "reserved"), cs,
      Bool.pick(List<&2, T.Split>, String.eq(k, "name"), ns, Nil{}))))))

# Whether `ss` lists label `l` with digest `d`.
def has(ss: List<&2, T.Split>, +l: String, +d: String) -> Bool:
  match ss:
    case Nil{}:
      False{}
    case T.Split{+k, +v} <> rest:
      Bool.or(Bool.and(String.eq(k, l), String.eq(v, d)), has(rest, l, d))

def at(ss: List<&2, T.Split>, m: Maybe<&2, String>, +d: String) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{+l}:
      has(ss, l, d)

# A line names a file of the listing: where `fetch` files the path it
# gives, the listing of its kind holds that label with that digest.
def names_file(g: Listing, o: Offer.Offered) -> Bool:
  match o:
    case Offer.Offered{+k, +d, f, +p}:
      at(group(g, k), Fetch.filed_under(p), d)

# Whether a list of lines holds one of kind `k` for digest `d`.
def offers(os: List<&2, Offer.Offered>, +k: String, +d: String) -> Bool:
  match os:
    case Nil{}:
      False{}
    case Offer.Offered{+k2, +d2, f, p} <> rest:
      Bool.or(Bool.and(String.eq(k2, k), String.eq(d2, d)), offers(rest, k, d))

# Every file of `ss` has a line of kind `k` at the path a fetcher asks for
# it at, naming its digest.
def covers(ss: List<&2, T.Split>, +os: List<&2, Offer.Offered>, +k: String, +prefix: String) -> Bool:
  match ss:
    case Nil{}:
      True{}
    case T.Split{+l, +d} <> rest:
      Bool.and(offers(SortL.keyed(~Offer.Offered, ~(o => Offer.offered.path(o)), Offer.addressed(prefix, l), os), k, d), covers(rest, os, k, prefix))

# Every file the store lists has its line
# ---------------------------------------

def offers_more(os: List<&2, Offer.Offered>, +x: Offer.Offered, +k: String, +d: String, h: {offers(os, k, d) == True{} : Bool}) -> {offers(x <> os, k, d) == True{} : Bool}:
  match x:
    case Offer.Offered{+k2, +d2, f, p}:
      or_r(Bool.and(String.eq(k2, k), String.eq(d2, d)), offers(os, k, d), h)

def offers_pick(c: Bool, +x: Offer.Offered, +os: List<&2, Offer.Offered>, +k: String, +d: String, h: {offers(os, k, d) == True{} : Bool}) -> {offers(Bool.pick(List<&2, Offer.Offered>, c, x <> os, os), k, d) == True{} : Bool}:
  match c:
    case True{}:
      offers_more(os, x, k, d, h)
    case False{}:
      h

def offers_app_l.at(a: Bool, -r: Bool, -s: Bool, h: {Bool.or(a, r) == True{} : Bool}, ih: {r == True{} : Bool} -> {s == True{} : Bool}) -> {Bool.or(a, s) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      ih(h)

def offers_app_l(xs: List<&2, Offer.Offered>, +ys: List<&2, Offer.Offered>, +k: String, +d: String, h: {offers(xs, k, d) == True{} : Bool}) -> {offers(List.append(&2, Offer.Offered, xs, ys), k, d) == True{} : Bool}:
  match xs:
    case Nil{}:
      Empty.absurd({offers(ys, k, d) == True{} : Bool}, S.false_true(h))
    case Offer.Offered{+k2, +d2, f, p} <> +rest:
      offers_app_l.at(Bool.and(String.eq(k2, k), String.eq(d2, d)), offers(rest, k, d), offers(List.append(&2, Offer.Offered, rest, ys), k, d), h, x => offers_app_l(rest, ys, k, d, x))

def offers_app_r(xs: List<&2, Offer.Offered>, +ys: List<&2, Offer.Offered>, +k: String, +d: String, +h: {offers(ys, k, d) == True{} : Bool}) -> {offers(List.append(&2, Offer.Offered, xs, ys), k, d) == True{} : Bool}:
  match xs:
    case Nil{}:
      h
    case +x <> +rest:
      offers_more(List.append(&2, Offer.Offered, rest, ys), x, k, d, offers_app_r(rest, ys, k, d, h))

def covers_app_l(ss: List<&2, T.Split>, +xs: List<&2, Offer.Offered>, +ys: List<&2, Offer.Offered>, +k: String, +prefix: String, +h: {covers(ss, xs, k, prefix) == True{} : Bool}) -> {covers(ss, List.append(&2, Offer.Offered, xs, ys), k, prefix) == True{} : Bool}:
  match ss:
    case Nil{}:
      {==}
    case T.Split{+l, +d} <> +rest:
      +q : String = Offer.addressed(prefix, l)
      +hd = PruneL.and_l(offers(SortL.keyed(~Offer.Offered, ~(o => Offer.offered.path(o)), q, xs), k, d), covers(rest, xs, k, prefix), h)
      +tl = PruneL.and_r(offers(SortL.keyed(~Offer.Offered, ~(o => Offer.offered.path(o)), q, xs), k, d), covers(rest, xs, k, prefix), h)
      %Equal.sym(List<&2, Offer.Offered>, SortL.keyed(~Offer.Offered, ~(o => Offer.offered.path(o)), q, List.append(&2, Offer.Offered, xs, ys)), List.append(&2, Offer.Offered, SortL.keyed(~Offer.Offered, ~(o => Offer.offered.path(o)), q, xs), SortL.keyed(~Offer.Offered, ~(o => Offer.offered.path(o)), q, ys)), SortL.keyed_app(~Offer.Offered, ~(o => Offer.offered.path(o)), q, xs, ys)) : {Bool.and(offers(_, k, d), covers(rest, List.append(&2, Offer.Offered, xs, ys), k, prefix)) == True{} : Bool}
      and_tt(offers(List.append(&2, Offer.Offered, SortL.keyed(~Offer.Offered, ~(o => Offer.offered.path(o)), q, xs), SortL.keyed(~Offer.Offered, ~(o => Offer.offered.path(o)), q, ys)), k, d), covers(rest, List.append(&2, Offer.Offered, xs, ys), k, prefix),
        offers_app_l(SortL.keyed(~Offer.Offered, ~(o => Offer.offered.path(o)), q, xs), SortL.keyed(~Offer.Offered, ~(o => Offer.offered.path(o)), q, ys), k, d, hd),
        covers_app_l(rest, xs, ys, k, prefix, tl))

def covers_app_r(ss: List<&2, T.Split>, +xs: List<&2, Offer.Offered>, +ys: List<&2, Offer.Offered>, +k: String, +prefix: String, +h: {covers(ss, ys, k, prefix) == True{} : Bool}) -> {covers(ss, List.append(&2, Offer.Offered, xs, ys), k, prefix) == True{} : Bool}:
  match ss:
    case Nil{}:
      {==}
    case T.Split{+l, +d} <> +rest:
      +q : String = Offer.addressed(prefix, l)
      +hd = PruneL.and_l(offers(SortL.keyed(~Offer.Offered, ~(o => Offer.offered.path(o)), q, ys), k, d), covers(rest, ys, k, prefix), h)
      +tl = PruneL.and_r(offers(SortL.keyed(~Offer.Offered, ~(o => Offer.offered.path(o)), q, ys), k, d), covers(rest, ys, k, prefix), h)
      %Equal.sym(List<&2, Offer.Offered>, SortL.keyed(~Offer.Offered, ~(o => Offer.offered.path(o)), q, List.append(&2, Offer.Offered, xs, ys)), List.append(&2, Offer.Offered, SortL.keyed(~Offer.Offered, ~(o => Offer.offered.path(o)), q, xs), SortL.keyed(~Offer.Offered, ~(o => Offer.offered.path(o)), q, ys)), SortL.keyed_app(~Offer.Offered, ~(o => Offer.offered.path(o)), q, xs, ys)) : {Bool.and(offers(_, k, d), covers(rest, List.append(&2, Offer.Offered, xs, ys), k, prefix)) == True{} : Bool}
      and_tt(offers(List.append(&2, Offer.Offered, SortL.keyed(~Offer.Offered, ~(o => Offer.offered.path(o)), q, xs), SortL.keyed(~Offer.Offered, ~(o => Offer.offered.path(o)), q, ys)), k, d), covers(rest, List.append(&2, Offer.Offered, xs, ys), k, prefix),
        offers_app_r(SortL.keyed(~Offer.Offered, ~(o => Offer.offered.path(o)), q, xs), SortL.keyed(~Offer.Offered, ~(o => Offer.offered.path(o)), q, ys), k, d, hd),
        covers_app_r(rest, xs, ys, k, prefix, tl))

def covers_sort(ss: List<&2, T.Split>, +xs: List<&2, Offer.Offered>, +k: String, +prefix: String, +h: {covers(ss, xs, k, prefix) == True{} : Bool}) -> {covers(ss, Offer.by_path(xs), k, prefix) == True{} : Bool}:
  match ss:
    case Nil{}:
      {==}
    case T.Split{+l, +d} <> +rest:
      +q : String = Offer.addressed(prefix, l)
      %Equal.sym(List<&2, Offer.Offered>, SortL.keyed(~Offer.Offered, ~(o => Offer.offered.path(o)), q, Offer.by_path(xs)), SortL.keyed(~Offer.Offered, ~(o => Offer.offered.path(o)), q, xs), SortL.sort_keyed(~Offer.Offered, ~(o => Offer.offered.path(o)), xs, q)) : {Bool.and(offers(_, k, d), covers(rest, Offer.by_path(xs), k, prefix)) == True{} : Bool}
      and_tt(offers(SortL.keyed(~Offer.Offered, ~(o => Offer.offered.path(o)), q, xs), k, d), covers(rest, Offer.by_path(xs), k, prefix),
        PruneL.and_l(offers(SortL.keyed(~Offer.Offered, ~(o => Offer.offered.path(o)), q, xs), k, d), covers(rest, xs, k, prefix), h),
        covers_sort(rest, xs, k, prefix, PruneL.and_r(offers(SortL.keyed(~Offer.Offered, ~(o => Offer.offered.path(o)), q, xs), k, d), covers(rest, xs, k, prefix), h)))

def covers_more(ss: List<&2, T.Split>, +x: Offer.Offered, +xs: List<&2, Offer.Offered>, +k: String, +prefix: String, +h: {covers(ss, xs, k, prefix) == True{} : Bool}) -> {covers(ss, x <> xs, k, prefix) == True{} : Bool}:
  match ss:
    case Nil{}:
      {==}
    case T.Split{+l, +d} <> +rest:
      +q : String = Offer.addressed(prefix, l)
      and_tt(offers(SortL.keyed(~Offer.Offered, ~(o => Offer.offered.path(o)), q, x <> xs), k, d), covers(rest, x <> xs, k, prefix),
        offers_pick(String.eq(Offer.offered.path(x), q), x, SortL.keyed(~Offer.Offered, ~(o => Offer.offered.path(o)), q, xs), k, d, PruneL.and_l(offers(SortL.keyed(~Offer.Offered, ~(o => Offer.offered.path(o)), q, xs), k, d), covers(rest, xs, k, prefix), h)),
        covers_more(rest, x, xs, k, prefix, PruneL.and_r(offers(SortL.keyed(~Offer.Offered, ~(o => Offer.offered.path(o)), q, xs), k, d), covers(rest, xs, k, prefix), h)))

# A file's own line, at the path a fetcher asks for it at.
def own_line(+k: String, +d: String, +f: Maybe<&2, String>, +q: String, +rest: List<&2, Offer.Offered>) -> {offers(SortL.keyed(~Offer.Offered, ~(o => Offer.offered.path(o)), q, Offer.Offered{k, d, f, q} <> rest), k, d) == True{} : Bool}:
  %Equal.sym(Bool, String.eq(q, q), True{}, S.eq_refl(q)) : {offers(Bool.pick(List<&2, Offer.Offered>, _, Offer.Offered{k, d, f, q} <> SortL.keyed(~Offer.Offered, ~(o => Offer.offered.path(o)), q, rest), SortL.keyed(~Offer.Offered, ~(o => Offer.offered.path(o)), q, rest)), k, d) == True{} : Bool}
  %Equal.sym(Bool, String.eq(k, k), True{}, S.eq_refl(k)) : {Bool.or(Bool.and(_, String.eq(d, d)), offers(SortL.keyed(~Offer.Offered, ~(o => Offer.offered.path(o)), q, rest), k, d)) == True{} : Bool}
  %Equal.sym(Bool, String.eq(d, d), True{}, S.eq_refl(d)) : {Bool.or(Bool.and(True{}, _), offers(SortL.keyed(~Offer.Offered, ~(o => Offer.offered.path(o)), q, rest), k, d)) == True{} : Bool}
  {==}

def covers_splits(ss: List<&2, T.Split>, +k: String, +prefix: String) -> {covers(ss, Offer.splits.offered(ss, k, prefix), k, prefix) == True{} : Bool}:
  match ss:
    case Nil{}:
      {==}
    case T.Split{+l, +d} <> +rest:
      and_tt(offers(SortL.keyed(~Offer.Offered, ~(o => Offer.offered.path(o)), Offer.addressed(prefix, l), Offer.Offered{k, d, None{}, Offer.addressed(prefix, l)} <> Offer.splits.offered(rest, k, prefix)), k, d), covers(rest, Offer.Offered{k, d, None{}, Offer.addressed(prefix, l)} <> Offer.splits.offered(rest, k, prefix), k, prefix),
        own_line(k, d, None{}, Offer.addressed(prefix, l), Offer.splits.offered(rest, k, prefix)),
        covers_more(rest, Offer.Offered{k, d, None{}, Offer.addressed(prefix, l)}, Offer.splits.offered(rest, k, prefix), k, prefix, covers_splits(rest, k, prefix)))

def covers_bodies(bs: List<&2, Prune.Body>, +prefix: String) -> {covers(body.splits(bs), Offer.bodies.offered(bs, prefix), "operation", prefix) == True{} : Bool}:
  match bs:
    case Nil{}:
      {==}
    case Prune.Body{+l, +d, ok, +f} <> +rest:
      and_tt(offers(SortL.keyed(~Offer.Offered, ~(o => Offer.offered.path(o)), Offer.addressed(prefix, l), Offer.Offered{"operation", d, f, Offer.addressed(prefix, l)} <> Offer.bodies.offered(rest, prefix)), "operation", d), covers(body.splits(rest), Offer.Offered{"operation", d, f, Offer.addressed(prefix, l)} <> Offer.bodies.offered(rest, prefix), "operation", prefix),
        own_line("operation", d, f, Offer.addressed(prefix, l), Offer.bodies.offered(rest, prefix)),
        covers_more(body.splits(rest), Offer.Offered{"operation", d, f, Offer.addressed(prefix, l)}, Offer.bodies.offered(rest, prefix), "operation", prefix, covers_bodies(rest, prefix)))

# The digest the listing gives label `l`: the first it lists it with.
def given(ss: List<&2, T.Split>, +l: String) -> Maybe<&2, String>:
  match ss:
    case Nil{}:
      None{}
    case T.Split{+k, +v} <> rest:
      Bool.pick(Maybe<&2, String>, String.eq(k, l), Some{v}, given(rest, l))

# A file that is not private and that the listing gives a digest, kept by
# its label and that digest.
def kept(priv: Bool, m: Maybe<&2, String>, +label: String, rest: List<&2, T.Split>) -> List<&2, T.Split>:
  match priv:
    case True{}:
      rest
    case False{}:
      match m:
        case None{}:
          rest
        case Some{d}:
          T.Split{label, d} <> rest

# The rules a fetcher is owed: each rule whose line does not begin
# `private` and whose file, `skipped/` and its name, the listing holds,
# by that label and the digest the listing gives it.
def public_rules(rs: List<&2, Receive.Ruled>, +ids: List<&2, T.Split>) -> List<&2, T.Split>:
  match rs:
    case Nil{}:
      Nil{}
    case Receive.Ruled{+file, +line, l} <> rest:
      kept(String.starts_with(line, "private"), given(ids, "skipped/" ++ file), "skipped/" ++ file, public_rules(rest, ids))

# The bookmarks a fetcher is owed: each that is not private and whose
# file, `names/` and its name and `.txt`, the listing holds, by that label
# and the digest the listing gives it.
def public_names(bs: List<&2, Bm.Bookmark>, +ids: List<&2, T.Split>) -> List<&2, T.Split>:
  match bs:
    case Nil{}:
      Nil{}
    case Bm.Bookmark{+n, t, +p} <> rest:
      kept(p, given(ids, "names/" ++ n ++ ".txt"), "names/" ++ n ++ ".txt", public_names(rest, ids))

def given_lookup(ss: List<&2, T.Split>, +l: String) -> {given(ss, l) == Arrange.lookup(ss, l) : Maybe<&2, String>}:
  match ss:
    case Nil{}:
      {==}
    case T.Split{+k, +v} <> rest:
      %given_lookup(rest, l) : {Bool.pick(Maybe<&2, String>, String.eq(k, l), Some{v}, given(rest, l)) == Bool.pick(Maybe<&2, String>, String.eq(k, l), Some{v}, _) : Maybe<&2, String>}
      {==}

def found_kept(c: Bool, m: Maybe<&2, String>, +label: String, +k: String, +prefix: String, +ss: List<&2, T.Split>, +os: List<&2, Offer.Offered>, ih: {Offer.splits.offered(ss, k, prefix) == os : List<&2, Offer.Offered>}) -> {Offer.splits.offered(kept(c, m, label, ss), k, prefix) == Offer.offered.found(Bool.not(c), m, label, k, prefix, os) : List<&2, Offer.Offered>}:
  match c:
    case True{}:
      match m:
        case None{}:
          ih
        case Some{d}:
          ih
    case False{}:
      match m:
        case None{}:
          ih
        case Some{+d}:
          %ih : {Offer.Offered{k, d, None{}, Offer.addressed(prefix, label)} <> Offer.splits.offered(ss, k, prefix) == Offer.Offered{k, d, None{}, Offer.addressed(prefix, label)} <> _ : List<&2, Offer.Offered>}
          {==}

def rules_are(rs: List<&2, Receive.Ruled>, +ids: List<&2, T.Split>, +prefix: String) -> {Offer.splits.offered(public_rules(rs, ids), "rule", prefix) == Offer.rules.offered(rs, ids, prefix) : List<&2, Offer.Offered>}:
  match rs:
    case Nil{}:
      {==}
    case Receive.Ruled{+file, +line, l} <> +rest:
      %given_lookup(ids, "skipped/" ++ file) : {Offer.splits.offered(kept(String.starts_with(line, "private"), given(ids, "skipped/" ++ file), "skipped/" ++ file, public_rules(rest, ids)), "rule", prefix) == Offer.offered.found(Bool.not(String.starts_with(line, "private")), _, "skipped/" ++ file, "rule", prefix, Offer.rules.offered(rest, ids, prefix)) : List<&2, Offer.Offered>}
      found_kept(String.starts_with(line, "private"), given(ids, "skipped/" ++ file), "skipped/" ++ file, "rule", prefix, public_rules(rest, ids), Offer.rules.offered(rest, ids, prefix), rules_are(rest, ids, prefix))

def names_are(bs: List<&2, Bm.Bookmark>, +ids: List<&2, T.Split>, +prefix: String) -> {Offer.splits.offered(public_names(bs, ids), "name", prefix) == Offer.names.offered(bs, ids, prefix) : List<&2, Offer.Offered>}:
  match bs:
    case Nil{}:
      {==}
    case Bm.Bookmark{+n, t, +p} <> +rest:
      %given_lookup(ids, "names/" ++ n ++ ".txt") : {Offer.splits.offered(kept(p, given(ids, "names/" ++ n ++ ".txt"), "names/" ++ n ++ ".txt", public_names(rest, ids)), "name", prefix) == Offer.offered.found(Bool.not(p), _, "names/" ++ n ++ ".txt", "name", prefix, Offer.names.offered(rest, ids, prefix)) : List<&2, Offer.Offered>}
      found_kept(p, given(ids, "names/" ++ n ++ ".txt"), "names/" ++ n ++ ".txt", "name", prefix, public_names(rest, ids), Offer.names.offered(rest, ids, prefix), names_are(rest, ids, prefix))

def covers_rules(+rs: List<&2, Receive.Ruled>, +ids: List<&2, T.Split>, +prefix: String) -> {covers(public_rules(rs, ids), Offer.rules.offered(rs, ids, prefix), "rule", prefix) == True{} : Bool}:
  %rules_are(rs, ids, prefix) : {covers(public_rules(rs, ids), _, "rule", prefix) == True{} : Bool}
  covers_splits(public_rules(rs, ids), "rule", prefix)

def covers_names(+bs: List<&2, Bm.Bookmark>, +ids: List<&2, T.Split>, +prefix: String) -> {covers(public_names(bs, ids), Offer.names.offered(bs, ids, prefix), "name", prefix) == True{} : Bool}:
  %names_are(bs, ids, prefix) : {covers(public_names(bs, ids), _, "name", prefix) == True{} : Bool}
  covers_splits(public_names(bs, ids), "name", prefix)

# Every payload, document, revision and file of `claims/` the listing
# holds, every rule that is not private whose file it holds, and every
# bookmark that is not private whose file it holds, has a line of its
# kind, at the path a fetcher asks for it at, naming its digest.
def lists_all(g: Listing, +rules: List<&2, Receive.Ruled>, +marks: List<&2, Bm.Bookmark>, +prefix: String, +os: List<&2, Offer.Offered>) -> Bool:
  match g:
    case Listing{ps, ds, vs, rs, cs, ns}:
      Bool.and(covers(ps, os, "payload", prefix), Bool.and(covers(ds, os, "operation", prefix), Bool.and(covers(vs, os, "revision", prefix), Bool.and(covers(cs, os, "reserved", prefix), Bool.and(covers(public_rules(rules, rs), os, "rule", prefix), covers(public_names(marks, ns), os, "name", prefix))))))

def complete(+prefix: String, s: Prune.Stored, +marks: List<&2, Bm.Bookmark>, +claims: List<&2, T.Split>, +rids: List<&2, T.Split>, +nids: List<&2, T.Split>) -> {lists_all(listing.of(s, claims, rids, nids), Receive.ruled(Offer.rules.of(s)), marks, prefix, Offer.entries(prefix, s, marks, claims, rids, nids)) == True{} : Bool}:
  match s:
    case Prune.Stored{docs, +revs, od, +bs, +ps, names, +rules}:
      +bp : List<&2, Offer.Offered> = Offer.by_path(Offer.splits.offered(ps, "payload", prefix))
      +bb : List<&2, Offer.Offered> = Offer.by_path(Offer.bodies.offered(bs, prefix))
      +bv : List<&2, Offer.Offered> = Offer.by_path(Offer.splits.offered(revs, "revision", prefix))
      +br : List<&2, Offer.Offered> = Offer.by_path(Offer.rules.offered(Receive.ruled(rules), rids, prefix))
      +bc : List<&2, Offer.Offered> = Offer.by_path(Offer.splits.offered(claims, "reserved", prefix))
      +bn : List<&2, Offer.Offered> = Offer.by_path(Offer.names.offered(marks, nids, prefix))
      +front : List<&2, Offer.Offered> = List.append(&2, Offer.Offered, bp, List.append(&2, Offer.Offered, bb, List.append(&2, Offer.Offered, bv, Nil{})))
      +back : List<&2, Offer.Offered> = List.append(&2, Offer.Offered, br, List.append(&2, Offer.Offered, bc, List.append(&2, Offer.Offered, bn, Nil{})))
      and_tt(covers(ps, List.append(&2, Offer.Offered, front, back), "payload", prefix), Bool.and(covers(body.splits(bs), List.append(&2, Offer.Offered, front, back), "operation", prefix), Bool.and(covers(revs, List.append(&2, Offer.Offered, front, back), "revision", prefix), Bool.and(covers(claims, List.append(&2, Offer.Offered, front, back), "reserved", prefix), Bool.and(covers(public_rules(Receive.ruled(rules), rids), List.append(&2, Offer.Offered, front, back), "rule", prefix), covers(public_names(marks, nids), List.append(&2, Offer.Offered, front, back), "name", prefix))))),
        covers_app_l(ps, front, back, "payload", prefix,
          covers_app_l(ps, bp, List.append(&2, Offer.Offered, bb, List.append(&2, Offer.Offered, bv, Nil{})), "payload", prefix,
            covers_sort(ps, Offer.splits.offered(ps, "payload", prefix), "payload", prefix, covers_splits(ps, "payload", prefix)))),
        and_tt(covers(body.splits(bs), List.append(&2, Offer.Offered, front, back), "operation", prefix), Bool.and(covers(revs, List.append(&2, Offer.Offered, front, back), "revision", prefix), Bool.and(covers(claims, List.append(&2, Offer.Offered, front, back), "reserved", prefix), Bool.and(covers(public_rules(Receive.ruled(rules), rids), List.append(&2, Offer.Offered, front, back), "rule", prefix), covers(public_names(marks, nids), List.append(&2, Offer.Offered, front, back), "name", prefix)))),
          covers_app_l(body.splits(bs), front, back, "operation", prefix,
            covers_app_r(body.splits(bs), bp, List.append(&2, Offer.Offered, bb, List.append(&2, Offer.Offered, bv, Nil{})), "operation", prefix,
              covers_app_l(body.splits(bs), bb, List.append(&2, Offer.Offered, bv, Nil{}), "operation", prefix,
                covers_sort(body.splits(bs), Offer.bodies.offered(bs, prefix), "operation", prefix, covers_bodies(bs, prefix))))),
          and_tt(covers(revs, List.append(&2, Offer.Offered, front, back), "revision", prefix), Bool.and(covers(claims, List.append(&2, Offer.Offered, front, back), "reserved", prefix), Bool.and(covers(public_rules(Receive.ruled(rules), rids), List.append(&2, Offer.Offered, front, back), "rule", prefix), covers(public_names(marks, nids), List.append(&2, Offer.Offered, front, back), "name", prefix))),
            covers_app_l(revs, front, back, "revision", prefix,
              covers_app_r(revs, bp, List.append(&2, Offer.Offered, bb, List.append(&2, Offer.Offered, bv, Nil{})), "revision", prefix,
                covers_app_r(revs, bb, List.append(&2, Offer.Offered, bv, Nil{}), "revision", prefix,
                  covers_app_l(revs, bv, Nil{}, "revision", prefix,
                    covers_sort(revs, Offer.splits.offered(revs, "revision", prefix), "revision", prefix, covers_splits(revs, "revision", prefix)))))),
            and_tt(covers(claims, List.append(&2, Offer.Offered, front, back), "reserved", prefix), Bool.and(covers(public_rules(Receive.ruled(rules), rids), List.append(&2, Offer.Offered, front, back), "rule", prefix), covers(public_names(marks, nids), List.append(&2, Offer.Offered, front, back), "name", prefix)),
              covers_app_r(claims, front, back, "reserved", prefix,
                covers_app_r(claims, br, List.append(&2, Offer.Offered, bc, List.append(&2, Offer.Offered, bn, Nil{})), "reserved", prefix,
                covers_app_l(claims, bc, List.append(&2, Offer.Offered, bn, Nil{}), "reserved", prefix,
                  covers_sort(claims, Offer.splits.offered(claims, "reserved", prefix), "reserved", prefix, covers_splits(claims, "reserved", prefix))))),
              and_tt(covers(public_rules(Receive.ruled(rules), rids), List.append(&2, Offer.Offered, front, back), "rule", prefix), covers(public_names(marks, nids), List.append(&2, Offer.Offered, front, back), "name", prefix),
                covers_app_r(public_rules(Receive.ruled(rules), rids), front, back, "rule", prefix,
                  covers_app_l(public_rules(Receive.ruled(rules), rids), br, List.append(&2, Offer.Offered, bc, List.append(&2, Offer.Offered, bn, Nil{})), "rule", prefix,
                    covers_sort(public_rules(Receive.ruled(rules), rids), Offer.rules.offered(Receive.ruled(rules), rids, prefix), "rule", prefix, covers_rules(Receive.ruled(rules), rids, prefix)))),
                covers_app_r(public_names(marks, nids), front, back, "name", prefix,
                  covers_app_r(public_names(marks, nids), br, List.append(&2, Offer.Offered, bc, List.append(&2, Offer.Offered, bn, Nil{})), "name", prefix,
                    covers_app_r(public_names(marks, nids), bc, List.append(&2, Offer.Offered, bn, Nil{}), "name", prefix,
                      covers_app_l(public_names(marks, nids), bn, Nil{}, "name", prefix,
                        covers_sort(public_names(marks, nids), Offer.names.offered(marks, nids, prefix), "name", prefix, covers_names(marks, nids, prefix)))))))))))

# Where `fetch` files what a manifest names
# -----------------------------------------

def sw_nil(z: String) -> {String.starts_with(z, SNil{}) == True{} : Bool}:
  match z:
    case SNil{}:
      {==}
    case SCon{h, t}:
      {==}

def drop_zero(t: String) -> {String.drop(t, 0n) == t : String}:
  match t:
    case SNil{}:
      {==}
    case SCon{h, r}:
      {==}

def char_refl(c: Char) -> {Char.is_eq(c, c) == True{} : Bool}:
  match c:
    case Chr{U32{w}}:
      (%Equal.sym(Cmp, Word.cmp(32n, w, w), EQ{}, S.word_refl(32n, w)) : {Cmp.is_eq(_) == True{} : Bool}
        {==})

def ne_sym.at(+x: Char, +y: Char, b: Bool, eb: {Char.is_eq(y, x) == b : Bool}, e: {Char.is_eq(x, y) == False{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, S.true_false(Equal.trans(Bool, True{}, Char.is_eq(x, x), False{}, Equal.sym(Bool, Char.is_eq(x, x), True{}, char_refl(x)),
        (%BmL.chr_eq(y, x, eb) : {Char.is_eq(x, _) == False{} : Bool}
          e))))

# Two characters that are not one are not one either way round.
def ne_sym(+x: Char, +y: Char, e: {Char.is_eq(x, y) == False{} : Bool}) -> {Char.is_eq(y, x) == False{} : Bool}:
  ne_sym.at(x, y, Char.is_eq(y, x), {==}, e)

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

def sw_if_false(+x: String, +y: String, b: Bool, e: {b == False{} : Bool}) -> {String.starts_with.if(x, y, b) == False{} : Bool}:
  %Equal.sym(Bool, b, False{}, e) : {String.starts_with.if(x, y, _) == False{} : Bool}
  {==}

def sw_slash.at(b: Bool, +a: Char, +p: String, +r: String, +c: Char, +u: String, eb: {Char.is_eq(a, c) == b : Bool}, ih: {String.starts_with(p ++ "/" ++ r, u ++ "/") == String.starts_with(p ++ "/", u ++ "/") : Bool}) -> {String.starts_with.if(p ++ "/" ++ r, u ++ "/", b) == String.starts_with.if(p ++ "/", u ++ "/", b) : Bool}:
  match b:
    case True{}:
      ih
    case False{}:
      {==}

# A name with no `/` in it, a `/` and anything, starts with another such
# name and a `/` exactly where the name and its `/` alone do.
def sw_slash(p: String, u: String, +r: String, +hp: {T.has_char(p, '/') == False{} : Bool}, +hu: {T.has_char(u, '/') == False{} : Bool}) -> {String.starts_with(p ++ "/" ++ r, u ++ "/") == String.starts_with(p ++ "/", u ++ "/") : Bool}:
  match p u:
    case SNil{} SNil{}:
      %Equal.sym(Bool, String.starts_with(r, SNil{}), True{}, sw_nil(r)) : {_ == True{} : Bool}
      {==}
    case SNil{} SCon{+c, +ut}:
      +nc = ne_sym(c, '/', or_false_l(Char.is_eq(c, '/'), T.has_char(ut, '/'), hu))
      Equal.trans(Bool, String.starts_with.if(r, ut ++ "/", Char.is_eq('/', c)), False{}, String.starts_with.if(SNil{}, ut ++ "/", Char.is_eq('/', c)),
        sw_if_false(r, ut ++ "/", Char.is_eq('/', c), nc), Equal.sym(Bool, String.starts_with.if(SNil{}, ut ++ "/", Char.is_eq('/', c)), False{}, sw_if_false(SNil{}, ut ++ "/", Char.is_eq('/', c), nc)))
    case SCon{+a, +pt} SNil{}:
      +na = or_false_l(Char.is_eq(a, '/'), T.has_char(pt, '/'), hp)
      Equal.trans(Bool, String.starts_with.if(pt ++ "/" ++ r, SNil{}, Char.is_eq(a, '/')), False{}, String.starts_with.if(pt ++ "/", SNil{}, Char.is_eq(a, '/')),
        sw_if_false(pt ++ "/" ++ r, SNil{}, Char.is_eq(a, '/'), na), Equal.sym(Bool, String.starts_with.if(pt ++ "/", SNil{}, Char.is_eq(a, '/')), False{}, sw_if_false(pt ++ "/", SNil{}, Char.is_eq(a, '/'), na)))
    case SCon{+a, +pt} SCon{+c, +ut}:
      sw_slash.at(Char.is_eq(a, c), a, pt, r, c, ut, {==}, sw_slash(pt, ut, r, or_false_r(Char.is_eq(a, '/'), T.has_char(pt, '/'), hp), or_false_r(Char.is_eq(c, '/'), T.has_char(ut, '/'), hu)))

def ah.at(b: Bool, +c: Char, +t: String, +l: String, eb: {Char.is_eq(c, '/') == b : Bool}, hb: {b == False{} : Bool}, ih: {Fetch.after.history(t ++ "/history/" ++ l) == Some{l} : Maybe<&2, String>}) -> {Bool.pick(Maybe<&2, String>, String.starts_with.if(t ++ "/history/" ++ l, "history/", b), Some{String.drop(t ++ "/history/" ++ l, 8n)}, Fetch.after.history(t ++ "/history/" ++ l)) == Some{l} : Maybe<&2, String>}:
  %Equal.sym(Bool, b, False{}, hb) : {Bool.pick(Maybe<&2, String>, String.starts_with.if(t ++ "/history/" ++ l, "history/", _), Some{String.drop(t ++ "/history/" ++ l, 8n)}, Fetch.after.history(t ++ "/history/" ++ l)) == Some{l} : Maybe<&2, String>}
  ih

# Past a name with no `/` in it, the first `/history/` is the one after it.
def after_name(p: String, +l: String, +hp: {T.has_char(p, '/') == False{} : Bool}) -> {Fetch.after.history(p ++ "/history/" ++ l) == Some{l} : Maybe<&2, String>}:
  match p:
    case SNil{}:
      %Equal.sym(Bool, String.starts_with(l, SNil{}), True{}, sw_nil(l)) : {Bool.pick(Maybe<&2, String>, _, Some{String.drop(l, 0n)}, Fetch.after.history("history/" ++ l)) == Some{l} : Maybe<&2, String>}
      %Equal.sym(String, String.drop(l, 0n), l, drop_zero(l)) : {Some{_} == Some{l} : Maybe<&2, String>}
      {==}
    case SCon{+c, +t}:
      ah.at(Char.is_eq(c, '/'), c, t, l, {==}, or_false_l(Char.is_eq(c, '/'), T.has_char(t, '/'), hp), after_name(t, l, or_false_r(Char.is_eq(c, '/'), T.has_char(t, '/'), hp)))

# `fetch` files what `offer` names a label at under that label, for a copy
# whose directory's name has no `/` in it and is not `history`.
def filed_at(prefix: String, +l: String, +hp: {T.has_char(prefix, '/') == False{} : Bool}, hh: {String.starts_with(prefix ++ "/", "history/") == False{} : Bool}) -> {Fetch.filed_under(Offer.addressed(prefix, l)) == Some{l} : Maybe<&2, String>}:
  match prefix:
    case SNil{}:
      %Equal.sym(Bool, String.starts_with(l, SNil{}), True{}, sw_nil(l)) : {Bool.pick(Maybe<&2, String>, _, Some{String.drop(l, 0n)}, Fetch.after.history("history/" ++ l)) == Some{l} : Maybe<&2, String>}
      %Equal.sym(String, String.drop(l, 0n), l, drop_zero(l)) : {Some{_} == Some{l} : Maybe<&2, String>}
      {==}
    case SCon{+c, +t}:
      +no = Equal.trans(Bool, String.starts_with(SCon{c, t} ++ "/" ++ ("history/" ++ l), "history" ++ "/"), String.starts_with(SCon{c, t} ++ "/", "history" ++ "/"), False{}, sw_slash(SCon{c, t}, "history", "history/" ++ l, hp, {==}), hh)
      %Equal.sym(Bool, String.starts_with(SCon{c, t} ++ "/history/" ++ l, "history/"), False{}, no) : {Bool.pick(Maybe<&2, String>, _, Some{String.drop(SCon{c, t} ++ "/history/" ++ l, 8n)}, Fetch.after.history(SCon{c, t} ++ "/history/" ++ l)) == Some{l} : Maybe<&2, String>}
      after_name(SCon{c, t}, l, hp)

# Every line names a file of the listing
# --------------------------------------

def self_has(+l: String, +d: String, +rest: List<&2, T.Split>) -> {has(T.Split{l, d} <> rest, l, d) == True{} : Bool}:
  %Equal.sym(Bool, String.eq(l, l), True{}, S.eq_refl(l)) : {Bool.or(Bool.and(_, String.eq(d, d)), has(rest, l, d)) == True{} : Bool}
  %Equal.sym(Bool, String.eq(d, d), True{}, S.eq_refl(d)) : {Bool.or(Bool.and(True{}, _), has(rest, l, d)) == True{} : Bool}
  {==}

# Every file of `ss` is in `gs`.
def within(ss: List<&2, T.Split>, +gs: List<&2, T.Split>) -> Bool:
  match ss:
    case Nil{}:
      True{}
    case T.Split{+l, +d} <> rest:
      Bool.and(has(gs, l, d), within(rest, gs))

def within_more(ss: List<&2, T.Split>, +x: T.Split, +gs: List<&2, T.Split>, +h: {within(ss, gs) == True{} : Bool}) -> {within(ss, x <> gs) == True{} : Bool}:
  match ss:
    case Nil{}:
      {==}
    case T.Split{+l, +d} <> +rest:
      match x:
        case T.Split{+k, +v}:
          and_tt(has(T.Split{k, v} <> gs, l, d), within(rest, T.Split{k, v} <> gs),
            or_r(Bool.and(String.eq(k, l), String.eq(v, d)), has(gs, l, d), PruneL.and_l(has(gs, l, d), within(rest, gs), h)),
            within_more(rest, T.Split{k, v}, gs, PruneL.and_r(has(gs, l, d), within(rest, gs), h)))

def within_self(ss: List<&2, T.Split>) -> {within(ss, ss) == True{} : Bool}:
  match ss:
    case Nil{}:
      {==}
    case T.Split{+l, +d} <> +rest:
      and_tt(has(T.Split{l, d} <> rest, l, d), within(rest, T.Split{l, d} <> rest), self_has(l, d, rest), within_more(rest, T.Split{l, d}, rest, within_self(rest)))

# A file's line names it where the listing of its kind holds it.
def named_at(+g: Listing, +k: String, +gs: List<&2, T.Split>, +prefix: String, +l: String, +d: String, +f: Maybe<&2, String>, eg: {group(g, k) == gs : List<&2, T.Split>}, hp: {T.has_char(prefix, '/') == False{} : Bool}, hh: {String.starts_with(prefix ++ "/", "history/") == False{} : Bool}, hl: {has(gs, l, d) == True{} : Bool}) -> {names_file(g, Offer.Offered{k, d, f, Offer.addressed(prefix, l)}) == True{} : Bool}:
  %Equal.sym(List<&2, T.Split>, group(g, k), gs, eg) : {at(_, Fetch.filed_under(Offer.addressed(prefix, l)), d) == True{} : Bool}
  %Equal.sym(Maybe<&2, String>, Fetch.filed_under(Offer.addressed(prefix, l)), Some{l}, filed_at(prefix, l, hp, hh)) : {at(gs, _, d) == True{} : Bool}
  hl

def sound_splits(ss: List<&2, T.Split>, +k: String, +prefix: String, +g: Listing, +gs: List<&2, T.Split>, +eg: {group(g, k) == gs : List<&2, T.Split>}, +hp: {T.has_char(prefix, '/') == False{} : Bool}, +hh: {String.starts_with(prefix ++ "/", "history/") == False{} : Bool}, +hw: {within(ss, gs) == True{} : Bool}) -> {SortL.all_at(~Offer.Offered, ~Listing, ~(c => o => names_file(c, o)), g, Offer.splits.offered(ss, k, prefix)) == True{} : Bool}:
  match ss:
    case Nil{}:
      {==}
    case T.Split{+l, +d} <> +rest:
      and_tt(names_file(g, Offer.Offered{k, d, None{}, Offer.addressed(prefix, l)}), SortL.all_at(~Offer.Offered, ~Listing, ~(c => o => names_file(c, o)), g, Offer.splits.offered(rest, k, prefix)),
        named_at(g, k, gs, prefix, l, d, None{}, eg, hp, hh, PruneL.and_l(has(gs, l, d), within(rest, gs), hw)),
        sound_splits(rest, k, prefix, g, gs, eg, hp, hh, PruneL.and_r(has(gs, l, d), within(rest, gs), hw)))

def sound_bodies(bs: List<&2, Prune.Body>, +prefix: String, +g: Listing, +gs: List<&2, T.Split>, +eg: {group(g, "operation") == gs : List<&2, T.Split>}, +hp: {T.has_char(prefix, '/') == False{} : Bool}, +hh: {String.starts_with(prefix ++ "/", "history/") == False{} : Bool}, +hw: {within(body.splits(bs), gs) == True{} : Bool}) -> {SortL.all_at(~Offer.Offered, ~Listing, ~(c => o => names_file(c, o)), g, Offer.bodies.offered(bs, prefix)) == True{} : Bool}:
  match bs:
    case Nil{}:
      {==}
    case Prune.Body{+l, +d, ok, +f} <> +rest:
      and_tt(names_file(g, Offer.Offered{"operation", d, f, Offer.addressed(prefix, l)}), SortL.all_at(~Offer.Offered, ~Listing, ~(c => o => names_file(c, o)), g, Offer.bodies.offered(rest, prefix)),
        named_at(g, "operation", gs, prefix, l, d, f, eg, hp, hh, PruneL.and_l(has(gs, l, d), within(body.splits(rest), gs), hw)),
        sound_bodies(rest, prefix, g, gs, eg, hp, hh, PruneL.and_r(has(gs, l, d), within(body.splits(rest), gs), hw)))

def lookup_step(c: Bool, +k: String, +v: String, +rest: List<&2, T.Split>, +label: String, +d: String, ec: {String.eq(k, label) == c : Bool}, e: {Bool.pick(Maybe<&2, String>, c, Some{v}, Arrange.lookup(rest, label)) == Some{d} : Maybe<&2, String>}, ih: {Arrange.lookup(rest, label) == Some{d} : Maybe<&2, String>} -> {has(rest, label, d) == True{} : Bool}) -> {has(T.Split{k, v} <> rest, label, d) == True{} : Bool}:
  match c:
    case True{}:
      %S.eq_true(k, label, ec) : {has(T.Split{k, v} <> rest, _, d) == True{} : Bool}
      %some_inj(v, d, e) : {has(T.Split{k, v} <> rest, k, _) == True{} : Bool}
      self_has(k, v, rest)
    case False{}:
      or_r(Bool.and(String.eq(k, label), String.eq(v, d)), has(rest, label, d), ih(e))

# A file found by its label is listed at that label, with that digest.
def lookup_has(ids: List<&2, T.Split>, +label: String, +d: String, e: {Arrange.lookup(ids, label) == Some{d} : Maybe<&2, String>}) -> {has(ids, label, d) == True{} : Bool}:
  match ids:
    case Nil{}:
      Empty.absurd({False{} == True{} : Bool}, none_some(d, e))
    case T.Split{+k, +v} <> +rest:
      lookup_step(String.eq(k, label), k, v, rest, label, d, {==}, e, x => lookup_has(rest, label, d, x))

def sound_found(keep: Bool, found: Maybe<&2, String>, +label: String, +kind: String, +prefix: String, +rest: List<&2, Offer.Offered>, +g: Listing, +ids: List<&2, T.Split>, eg: {group(g, kind) == ids : List<&2, T.Split>}, hp: {T.has_char(prefix, '/') == False{} : Bool}, hh: {String.starts_with(prefix ++ "/", "history/") == False{} : Bool}, ef: {Arrange.lookup(ids, label) == found : Maybe<&2, String>}, ih: {SortL.all_at(~Offer.Offered, ~Listing, ~(c => o => names_file(c, o)), g, rest) == True{} : Bool}) -> {SortL.all_at(~Offer.Offered, ~Listing, ~(c => o => names_file(c, o)), g, Offer.offered.found(keep, found, label, kind, prefix, rest)) == True{} : Bool}:
  match keep:
    case True{}:
      match found:
        case Some{+d}:
          and_tt(names_file(g, Offer.Offered{kind, d, None{}, Offer.addressed(prefix, label)}), SortL.all_at(~Offer.Offered, ~Listing, ~(c => o => names_file(c, o)), g, rest), named_at(g, kind, ids, prefix, label, d, None{}, eg, hp, hh, lookup_has(ids, label, d, ef)), ih)
        case None{}:
          ih
    case False{}:
      ih

def sound_rules(rs: List<&2, Receive.Ruled>, +ids: List<&2, T.Split>, +prefix: String, +g: Listing, +eg: {group(g, "rule") == ids : List<&2, T.Split>}, +hp: {T.has_char(prefix, '/') == False{} : Bool}, +hh: {String.starts_with(prefix ++ "/", "history/") == False{} : Bool}) -> {SortL.all_at(~Offer.Offered, ~Listing, ~(c => o => names_file(c, o)), g, Offer.rules.offered(rs, ids, prefix)) == True{} : Bool}:
  match rs:
    case Nil{}:
      {==}
    case Receive.Ruled{+file, +line, l} <> +rest:
      sound_found(Bool.not(String.starts_with(line, "private")), Arrange.lookup(ids, "skipped/" ++ file), "skipped/" ++ file, "rule", prefix, Offer.rules.offered(rest, ids, prefix), g, ids, eg, hp, hh, {==}, sound_rules(rest, ids, prefix, g, eg, hp, hh))

def sound_names(bs: List<&2, Bm.Bookmark>, +ids: List<&2, T.Split>, +prefix: String, +g: Listing, +eg: {group(g, "name") == ids : List<&2, T.Split>}, +hp: {T.has_char(prefix, '/') == False{} : Bool}, +hh: {String.starts_with(prefix ++ "/", "history/") == False{} : Bool}) -> {SortL.all_at(~Offer.Offered, ~Listing, ~(c => o => names_file(c, o)), g, Offer.names.offered(bs, ids, prefix)) == True{} : Bool}:
  match bs:
    case Nil{}:
      {==}
    case Bm.Bookmark{+n, t, +p} <> +rest:
      sound_found(Bool.not(p), Arrange.lookup(ids, "names/" ++ n ++ ".txt"), "names/" ++ n ++ ".txt", "name", prefix, Offer.names.offered(rest, ids, prefix), g, ids, eg, hp, hh, {==}, sound_names(rest, ids, prefix, g, eg, hp, hh))

def sound_sorted(+g: Listing, +os: List<&2, Offer.Offered>, +h: {SortL.all_at(~Offer.Offered, ~Listing, ~(c => o => names_file(c, o)), g, os) == True{} : Bool}) -> {SortL.all_at(~Offer.Offered, ~Listing, ~(c => o => names_file(c, o)), g, Offer.by_path(os)) == True{} : Bool}:
  SortL.all_sort_at(~Offer.Offered, ~(a => b => Offer.offered_le(a, b)), ~Listing, ~(c => o => names_file(c, o)), g, os, h)

def sound_app(+g: Listing, +xs: List<&2, Offer.Offered>, +ys: List<&2, Offer.Offered>, +hx: {SortL.all_at(~Offer.Offered, ~Listing, ~(c => o => names_file(c, o)), g, xs) == True{} : Bool}, +hy: {SortL.all_at(~Offer.Offered, ~Listing, ~(c => o => names_file(c, o)), g, ys) == True{} : Bool}) -> {SortL.all_at(~Offer.Offered, ~Listing, ~(c => o => names_file(c, o)), g, List.append(&2, Offer.Offered, xs, ys)) == True{} : Bool}:
  SortL.all_app_at(~Offer.Offered, ~Listing, ~(c => o => names_file(c, o)), g, xs, ys, hx, hy)

# Three groups, each by path, one after another.
def sound_three(+g: Listing, +a: List<&2, Offer.Offered>, +b: List<&2, Offer.Offered>, +c: List<&2, Offer.Offered>, +ha: {SortL.all_at(~Offer.Offered, ~Listing, ~(c => o => names_file(c, o)), g, a) == True{} : Bool}, +hb: {SortL.all_at(~Offer.Offered, ~Listing, ~(c => o => names_file(c, o)), g, b) == True{} : Bool}, +hc: {SortL.all_at(~Offer.Offered, ~Listing, ~(c => o => names_file(c, o)), g, c) == True{} : Bool}) -> {SortL.all_at(~Offer.Offered, ~Listing, ~(c => o => names_file(c, o)), g, List.concat(&2, Offer.Offered, [Offer.by_path(a), Offer.by_path(b), Offer.by_path(c)])) == True{} : Bool}:
  sound_app(g, Offer.by_path(a), List.concat(&2, Offer.Offered, [Offer.by_path(b), Offer.by_path(c)]), sound_sorted(g, a, ha),
    sound_app(g, Offer.by_path(b), List.concat(&2, Offer.Offered, [Offer.by_path(c)]), sound_sorted(g, b, hb),
      sound_app(g, Offer.by_path(c), Nil{}, sound_sorted(g, c, hc), {==})))

# Every line of the manifest names a file of the store's listing.
def sound(+prefix: String, s: Prune.Stored, +marks: List<&2, Bm.Bookmark>, +claims: List<&2, T.Split>, +rids: List<&2, T.Split>, +nids: List<&2, T.Split>, +hp: {T.has_char(prefix, '/') == False{} : Bool}, +hh: {String.starts_with(prefix ++ "/", "history/") == False{} : Bool}) -> {SortL.all_at(~Offer.Offered, ~Listing, ~(c => o => names_file(c, o)), listing.of(s, claims, rids, nids), Offer.entries(prefix, s, marks, claims, rids, nids)) == True{} : Bool}:
  match s:
    case Prune.Stored{docs, +revs, od, +bs, +ps, names, +rules}:
      +g : Listing = Listing{ps, body.splits(bs), revs, rids, claims, nids}
      sound_app(g, List.concat(&2, Offer.Offered, [Offer.by_path(Offer.splits.offered(ps, "payload", prefix)), Offer.by_path(Offer.bodies.offered(bs, prefix)), Offer.by_path(Offer.splits.offered(revs, "revision", prefix))]),
        List.concat(&2, Offer.Offered, [Offer.by_path(Offer.rules.offered(Receive.ruled(rules), rids, prefix)), Offer.by_path(Offer.splits.offered(claims, "reserved", prefix)), Offer.by_path(Offer.names.offered(marks, nids, prefix))]),
        sound_three(g, Offer.splits.offered(ps, "payload", prefix), Offer.bodies.offered(bs, prefix), Offer.splits.offered(revs, "revision", prefix),
          sound_splits(ps, "payload", prefix, g, ps, {==}, hp, hh, within_self(ps)),
          sound_bodies(bs, prefix, g, body.splits(bs), {==}, hp, hh, within_self(body.splits(bs))),
          sound_splits(revs, "revision", prefix, g, revs, {==}, hp, hh, within_self(revs))),
        sound_three(g, Offer.rules.offered(Receive.ruled(rules), rids, prefix), Offer.splits.offered(claims, "reserved", prefix), Offer.names.offered(marks, nids, prefix),
          sound_rules(Receive.ruled(rules), rids, prefix, g, {==}, hp, hh),
          sound_splits(claims, "reserved", prefix, g, claims, {==}, hp, hh, within_self(claims)),
          sound_names(marks, nids, prefix, g, {==}, hp, hh)))

# The manifest names every file of the store's listing it lists by the
# digest the listing gives it, and lists every payload, document, revision
# and file of `claims/`.
def digests(+prefix: String, +s: Prune.Stored, +marks: List<&2, Bm.Bookmark>, +claims: List<&2, T.Split>, +rids: List<&2, T.Split>, +nids: List<&2, T.Split>, +hp: {T.has_char(prefix, '/') == False{} : Bool}, +hh: {String.starts_with(prefix ++ "/", "history/") == False{} : Bool}) -> {Bool.and(SortL.all_at(~Offer.Offered, ~Listing, ~(c => o => names_file(c, o)), listing.of(s, claims, rids, nids), Offer.entries(prefix, s, marks, claims, rids, nids)), lists_all(listing.of(s, claims, rids, nids), Receive.ruled(Offer.rules.of(s)), marks, prefix, Offer.entries(prefix, s, marks, claims, rids, nids))) == True{} : Bool}:
  and_tt(SortL.all_at(~Offer.Offered, ~Listing, ~(c => o => names_file(c, o)), listing.of(s, claims, rids, nids), Offer.entries(prefix, s, marks, claims, rids, nids)), lists_all(listing.of(s, claims, rids, nids), Receive.ruled(Offer.rules.of(s)), marks, prefix, Offer.entries(prefix, s, marks, claims, rids, nids)),
    sound(prefix, s, marks, claims, rids, nids, hp, hh), complete(prefix, s, marks, claims, rids, nids))

# What a document forgets
# -----------------------

def forgets_of(b: Prune.Body) -> Maybe<&2, String>:
  match b:
    case Prune.Body{p, i, ok, f}:
      f

def two_forgets(r: Bool, +path: String, +id: String, +text: String) -> {Bool.pick(Maybe<&2, String>, r, None{}, Prune.ops.forgets(Ops.parse(text))) == Bool.pick(Maybe<&2, String>, Bool.and(r, True{}), None{}, forgets_of(Prune.body.of.two(path, id, text, r))) : Maybe<&2, String>}:
  match r:
    case True{}:
      {==}
    case False{}:
      {==}

def pick_false(r: Bool, +x: Maybe<&2, String>) -> {x == Bool.pick(Maybe<&2, String>, Bool.and(r, False{}), None{}, x) : Maybe<&2, String>}:
  match r:
    case True{}:
      {==}
    case False{}:
      {==}

def read_forgets(fp: Bool, +path: String, +id: String, +text: String) -> {Bool.pick(Maybe<&2, String>, fp, Stand.payload.forgets(Stand.payload.parse(text)), Bool.pick(Maybe<&2, String>, Res.is_resolution(text), None{}, Prune.ops.forgets(Ops.parse(text)))) == Bool.pick(Maybe<&2, String>, Bool.and(Res.is_resolution(text), Bool.not(fp)), None{}, forgets_of(Prune.body.of(path, id, text, fp))) : Maybe<&2, String>}:
  match fp:
    case True{}:
      pick_false(Res.is_resolution(text), Stand.payload.forgets(Stand.payload.parse(text)))
    case False{}:
      two_forgets(Res.is_resolution(text), path, id, text)

# `offer`'s catalogue lists a document as forgetting what the reading
# `prune`, `receive` and `export` share reads it as forgetting, save a
# resolution that is no stand-in, which it lists as forgetting nothing.
def catalogue(+path: String, +id: String, +text: String) -> {Offer.catalogue.forgets(text) == Bool.pick(Maybe<&2, String>, Bool.and(Res.is_resolution(text), Bool.not(Prune.forgotten.payload(T.lines(text)))), None{}, forgets_of(Prune.body.of(path, id, text, Prune.forgotten.payload(T.lines(text))))) : Maybe<&2, String>}:
  read_forgets(Prune.forgotten.payload(T.lines(text)), path, id, text)

# Reading a line back
# -------------------

def hex_sp.at(+c: Char, b: Bool, eb: {Char.is_eq(c, ' ') == b : Bool}, h: {T.is_hex(c) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, S.false_true(Equal.trans(Bool, False{}, T.is_hex(c), True{}, (%Equal.sym(Char, c, ' ', BmL.chr_eq(c, ' ', eb)) : {False{} == T.is_hex(_) : Bool}
        {==}), h)))

# A string of hex characters has no space in it.
def nosp_hex(s: String, +h: {T.all_chars(~T.is_hex, s) == True{} : Bool}) -> {T.has_char(s, ' ') == False{} : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      ArrangeL.or_ff(Char.is_eq(c, ' '), T.has_char(t, ' '),
        hex_sp.at(c, Char.is_eq(c, ' '), {==}, ArrangeL.and_tl(T.is_hex(c), T.all_chars(~T.is_hex, t), h)),
        nosp_hex(t, ArrangeL.and_tr(T.is_hex(c), T.all_chars(~T.is_hex, t), h)))

# A digest has no space in it.
def nosp_digest(+d: String, h: {T.is_digest(d) == True{} : Bool}) -> {T.has_char(d, ' ') == False{} : Bool}:
  nosp_hex(d, ArrangeL.and_tr(Nat.is_eq(String.length(d), 64n), T.all_chars(~T.is_hex, d), h))

def go_step(b: Bool, +c: Char, +t: String, +r: String, +acc: String, eb: {Char.is_eq(c, ' ') == b : Bool}, +hb: {b == False{} : Bool}, ih: {T.split_once.go(t ++ (" " ++ r), SCon{c, acc}) == Some{T.Split{String.reverse.go(SCon{c, acc}, t), r}} : Maybe<&2, T.Split>}) -> {Bool.pick(Maybe<&2, T.Split>, b, Some{T.Split{String.reverse(acc), t ++ (" " ++ r)}}, T.split_once.go(t ++ (" " ++ r), SCon{c, acc})) == Some{T.Split{String.reverse.go(acc, SCon{c, t}), r}} : Maybe<&2, T.Split>}:
  match b:
    case True{}:
      Empty.absurd({Some{T.Split{String.reverse(acc), t ++ (" " ++ r)}} == Some{T.Split{String.reverse.go(acc, SCon{c, t}), r}} : Maybe<&2, T.Split>}, S.true_false(hb))
    case False{}:
      ih

# The walk that cuts at the first space, over a word with none, a space
# and the rest: the word, and the rest.
def go_word(t: String, +acc: String, +r: String, +h: {T.has_char(t, ' ') == False{} : Bool}) -> {T.split_once.go(t ++ (" " ++ r), acc) == Some{T.Split{String.reverse.go(acc, t), r}} : Maybe<&2, T.Split>}:
  match t:
    case SNil{}:
      {==}
    case SCon{+c, +u}:
      go_step(Char.is_eq(c, ' '), c, u, r, acc, {==}, ArrangeL.or_ff_l(Char.is_eq(c, ' '), T.has_char(u, ' '), h),
        go_word(u, SCon{c, acc}, r, ArrangeL.or_ff_r(Char.is_eq(c, ' '), T.has_char(u, ' '), h)))

# A word with no space, a space and the rest cut at the first space is
# the word and the rest.
def cut_word(+a: String, +r: String, +h: {T.has_char(a, ' ') == False{} : Bool}) -> {T.split_once(a ++ (" " ++ r)) == Some{T.Split{a, r}} : Maybe<&2, T.Split>}:
  Equal.trans(Maybe<&2, T.Split>, T.split_once(a ++ (" " ++ r)), T.split_once.go(a ++ (" " ++ r), SNil{}), Some{T.Split{a, r}}, Spell.split_fast(a ++ (" " ++ r), SNil{}), go_word(a, SNil{}, r, h))

# A kind a reader knows has no space in it and does not start as `head`
# does.
def not_h(k: String) -> Bool:
  match k:
    case SNil{}:
      False{}
    case SCon{c, t}:
      Bool.not(Char.is_eq(c, 'h'))

def kind_ok(+k: String) -> Bool:
  Bool.and(Bool.not(T.has_char(k, ' ')), not_h(k))

def kinds_ok(ks: List<&2, String>) -> Bool:
  match ks:
    case Nil{}:
      True{}
    case +k <> rest:
      Bool.and(kind_ok(k), kinds_ok(rest))

def member_ok.of(c: Bool, +l: String, +rest: List<&2, String>, +k: String, +ec: {String.eq(l, k) == c : Bool}, +ha: {Bool.and(kind_ok(l), kinds_ok(rest)) == True{} : Bool}, hm: {Bool.or(c, Rev.member(rest, k)) == True{} : Bool}, ih: {kinds_ok(rest) == True{} : Bool} -> {Rev.member(rest, k) == True{} : Bool} -> {kind_ok(k) == True{} : Bool}) -> {kind_ok(k) == True{} : Bool}:
  match c:
    case True{}:
      %S.eq_true(l, k, ec) : {kind_ok(_) == True{} : Bool}
      ArrangeL.and_tl(kind_ok(l), kinds_ok(rest), ha)
    case False{}:
      ih(ArrangeL.and_tr(kind_ok(l), kinds_ok(rest), ha), hm)

def member_ok(ks: List<&2, String>, +k: String, +ha: {kinds_ok(ks) == True{} : Bool}, hm: {Rev.member(ks, k) == True{} : Bool}) -> {kind_ok(k) == True{} : Bool}:
  match ks:
    case Nil{}:
      Empty.absurd({kind_ok(k) == True{} : Bool}, S.false_true(hm))
    case +l <> +rest:
      member_ok.of(String.eq(l, k), l, rest, k, {==}, ha, hm, a => b => member_ok(rest, k, a, b))

# Every kind a reader of `historica-offer-1` knows.
def known(+k: String, hm: {Rev.member(Fetch.KINDS(), k) == True{} : Bool}) -> {kind_ok(k) == True{} : Bool}:
  member_ok(Fetch.KINDS(), k, {==}, hm)

def head_pick(b: Bool, +t: String, -y: String, eb: {Bool.not(b) == True{} : Bool}) -> {Bool.pick(Maybe<&2, String>, b, T.strip_prefix(t, y), None{}) == None{} : Maybe<&2, String>}:
  match b:
    case True{}:
      Empty.absurd({T.strip_prefix(t, y) == None{} : Maybe<&2, String>}, S.false_true(eb))
    case False{}:
      {==}

# A line starting with a kind is no head's.
def head_none(k: String, +x: String, h: {not_h(k) == True{} : Bool}) -> {T.strip_prefix(k ++ x, "head ") == None{} : Maybe<&2, String>}:
  match k:
    case SNil{}:
      Empty.absurd({T.strip_prefix(SNil{} ++ x, "head ") == None{} : Maybe<&2, String>}, S.false_true(h))
    case SCon{+c, +t}:
      head_pick(Char.is_eq(c, 'h'), t ++ x, "ead ", h)

# What a line says a file forgets: a digest, or `-` for nothing.
def forgets_ok(g: Maybe<&2, String>) -> Bool:
  match g:
    case None{}:
      True{}
    case Some{x}:
      T.is_digest(x)

def dash_digest(c: Bool, +x: String, ec: {String.eq(x, "-") == c : Bool}, h: {T.is_digest(x) == True{} : Bool}) -> {Bool.pick(Maybe<&2, String>, c, None{}, Some{x}) == Some{x} : Maybe<&2, String>}:
  match c:
    case True{}:
      Empty.absurd({None{} == Some{x} : Maybe<&2, String>}, S.false_true((%S.eq_true(x, "-", ec) : {T.is_digest(_) == True{} : Bool}; h)))
    case False{}:
      {==}

def g_nosp(g: Maybe<&2, String>, h: {forgets_ok(g) == True{} : Bool}) -> {T.has_char(Maybe.default(&2, String, g, "-"), ' ') == False{} : Bool}:
  match g:
    case None{}:
      {==}
    case Some{+x}:
      nosp_digest(x, h)

def g_ok(g: Maybe<&2, String>, h: {forgets_ok(g) == True{} : Bool}) -> {Bool.or(String.eq(Maybe.default(&2, String, g, "-"), "-"), T.is_digest(Maybe.default(&2, String, g, "-"))) == True{} : Bool}:
  match g:
    case None{}:
      {==}
    case Some{+x}:
      PruneL.or_rt(String.eq(x, "-"), T.is_digest(x), h)

def g_back(g: Maybe<&2, String>, h: {forgets_ok(g) == True{} : Bool}) -> {Fetch.forgets.of(Maybe.default(&2, String, g, "-")) == g : Maybe<&2, String>}:
  match g:
    case None{}:
      {==}
    case Some{+x}:
      dash_digest(String.eq(x, "-"), x, {==}, h)

def pick3(a: Bool, b: Bool, c: Bool, -x: Fetch.LRead, -y: Fetch.LRead, -z: Fetch.LRead, -w: Fetch.LRead, ea: {a == True{} : Bool}, eb: {b == True{} : Bool}, ec: {c == True{} : Bool}) -> {Bool.pick(Fetch.LRead, a, Bool.pick(Fetch.LRead, b, Bool.pick(Fetch.LRead, c, x, y), z), w) == x : Fetch.LRead}:
  match a b c:
    case True{} True{} True{}:
      {==}
    case False{} _ _:
      Empty.absurd({Bool.pick(Fetch.LRead, False{}, Bool.pick(Fetch.LRead, b, Bool.pick(Fetch.LRead, c, x, y), z), w) == x : Fetch.LRead}, S.false_true(ea))
    case True{} False{} _:
      Empty.absurd({Bool.pick(Fetch.LRead, True{}, Bool.pick(Fetch.LRead, False{}, Bool.pick(Fetch.LRead, c, x, y), z), w) == x : Fetch.LRead}, S.false_true(eb))
    case True{} True{} False{}:
      Empty.absurd({Bool.pick(Fetch.LRead, True{}, Bool.pick(Fetch.LRead, True{}, Bool.pick(Fetch.LRead, False{}, x, y), z), w) == x : Fetch.LRead}, S.false_true(ec))

# `fetch` reads the line `offer` writes for a file back as that file:
# its kind, its digest, what it forgets and its path, whatever spaces the
# path holds.
def line_back(+k: String, +d: String, +g: Maybe<&2, String>, +p: String, +rest: List<&2, String>, +nh: Bool, +hk: {Rev.member(Fetch.KINDS(), k) == True{} : Bool}, +hd: {T.is_digest(d) == True{} : Bool}, +hg: {forgets_ok(g) == True{} : Bool}) -> {Fetch.line.at(Offer.offered.line(Offer.Offered{k, d, g, p}) <> rest, nh) == Fetch.LRead.Entry{Offer.Offered{k, d, g, p}} : Fetch.LRead}:
  +gd = Maybe.default(&2, String, g, "-")
  +ko = known(k, hk)
  +r2 = gd ++ (" " ++ p)
  +r1 = d ++ (" " ++ r2)
  %Equal.sym(Maybe<&2, String>, T.strip_prefix(k ++ (" " ++ r1), "head "), None{}, head_none(k, " " ++ r1, ArrangeL.and_tr(Bool.not(T.has_char(k, ' ')), not_h(k), ko))) : {Fetch.line.head(nh, _, k ++ (" " ++ r1)) == Fetch.LRead.Entry{Offer.Offered{k, d, g, p}} : Fetch.LRead}
  %Equal.sym(Maybe<&2, T.Split>, T.split_once(k ++ (" " ++ r1)), Some{T.Split{k, r1}}, cut_word(k, r1, ArrangeL.not_tt(T.has_char(k, ' '), ArrangeL.and_tl(Bool.not(T.has_char(k, ' ')), not_h(k), ko)))) : {Fetch.line.fields(Fetch.four.a(_)) == Fetch.LRead.Entry{Offer.Offered{k, d, g, p}} : Fetch.LRead}
  %Equal.sym(Maybe<&2, T.Split>, T.split_once(r1), Some{T.Split{d, r2}}, cut_word(d, r2, nosp_digest(d, hd))) : {Fetch.line.fields(Fetch.four.b(k, _)) == Fetch.LRead.Entry{Offer.Offered{k, d, g, p}} : Fetch.LRead}
  %Equal.sym(Maybe<&2, T.Split>, T.split_once(r2), Some{T.Split{gd, p}}, cut_word(gd, p, g_nosp(g, hg))) : {Fetch.line.fields(Fetch.four.c(k, d, _)) == Fetch.LRead.Entry{Offer.Offered{k, d, g, p}} : Fetch.LRead}
  Equal.trans(Fetch.LRead, Fetch.line.entry(Fetch.Four{k, d, gd, p}), Fetch.LRead.Entry{Offer.Offered{k, d, Fetch.forgets.of(gd), p}}, Fetch.LRead.Entry{Offer.Offered{k, d, g, p}},
    pick3(Rev.member(Fetch.KINDS(), k), T.is_digest(d), Bool.or(String.eq(gd, "-"), T.is_digest(gd)), Fetch.LRead.Entry{Offer.Offered{k, d, Fetch.forgets.of(gd), p}}, Fetch.LRead.Bad{"a forgotten digest that is not a digest"}, Fetch.LRead.Bad{"a digest that is not a digest"}, Fetch.LRead.Skip{}, hk, hd, g_ok(g, hg)),
    Equal.cong(Maybe<&2, String>, Fetch.LRead, x => Fetch.LRead.Entry{Offer.Offered{k, d, x, p}}, Fetch.forgets.of(gd), g, g_back(g, hg)))
