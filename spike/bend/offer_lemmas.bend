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
