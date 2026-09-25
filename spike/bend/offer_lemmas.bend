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
import ./string_lemmas.bend as S

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
  Equal.cong(List<&2, Offer.Offered>, List<&2, String>, x => Offer.manifest.of(Offer.manifest.front(prefix, s), Offer.rules.offered(Receive.ruled(Offer.rules.of(s)), rids, prefix), Offer.splits.offered(claims, "reserved", prefix), x),
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
      Equal.cong(List<&2, Offer.Offered>, List<&2, String>, x => Offer.manifest.of(Offer.manifest.front(prefix, Prune.Stored{docs, revs, od, bods, ps, names, rs}), x, Offer.splits.offered(claims, "reserved", prefix), Offer.names.offered(bs, nids, prefix)),
        Offer.rules.offered(Receive.ruled(rs), rids, prefix), Offer.rules.offered(Receive.ruled(Offer.shared_files(rs)), rids, prefix), rules_shared(rs, rids, prefix))

# The words
# ---------

def m_some(m: Maybe<&2, String>) -> Type:
  match m:
    case None{}:
      Empty
    case Some{x}:
      Unit

def some_none(-w: String, e: {Some{w} == None{} : Maybe<&2, String>}) -> Empty:
  %e : {m_some(_) : Type}
  Unit{}

def dash_one(c: Bool, +w: String, ec: {String.starts_with(w, "-") == c : Bool}, ed: {Bool.pick(Maybe<&2, String>, c, Some{w}, None{}) == None{} : Maybe<&2, String>}) -> {Bool.and(String.eq(w, w), Bool.not(String.starts_with(w, "-"))) == True{} : Bool}:
  match c:
    case True{}:
      Empty.absurd({Bool.and(String.eq(w, w), Bool.not(String.starts_with(w, "-"))) == True{} : Bool}, some_none(w, ed))
    case False{}:
      %Equal.sym(Bool, String.eq(w, w), True{}, S.eq_refl(w)) : {Bool.and(_, Bool.not(String.starts_with(w, "-"))) == True{} : Bool}
      %Equal.sym(Bool, String.starts_with(w, "-"), False{}, ec) : {Bool.and(True{}, Bool.not(_)) == True{} : Bool}
      {==}

def plain_ok(ws: List<&2, String>, ed: {Offer.first_dash(ws) == None{} : Maybe<&2, String>}) -> {Offer.args.ok(ws, Offer.args.plain(ws)) == True{} : Bool}:
  match ws:
    case Nil{}:
      {==}
    case +w <> rest:
      match rest:
        case Nil{}:
          dash_one(String.starts_with(w, "-"), w, {==}, ed)
        case x <> more:
          {==}

def of_ok(+ws: List<&2, String>, dm: Maybe<&2, String>, ed: {Offer.first_dash(ws) == dm : Maybe<&2, String>}) -> {Offer.args.ok(ws, Offer.args.of(ws, dm)) == True{} : Bool}:
  match dm:
    case Some{w}:
      {==}
    case None{}:
      plain_ok(ws, ed)

# A command line `offer` accepts is one directory and nothing else.
def words(+ws: List<&2, String>) -> {Offer.args.ok(ws, Offer.args.r(ws)) == True{} : Bool}:
  of_ok(ws, Offer.first_dash(ws), {==})
