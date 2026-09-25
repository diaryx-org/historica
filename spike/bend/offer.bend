# `offer <dir>`: the listing a published copy has no way to give.
#
# Decision 0048, as 0052 amends it: every other way a store travels hands
# the reader a directory it can walk, and a URL cannot be walked. So this
# writes the walk down — to standard output, whole, so that
# `historica offer store > offer.txt` is the publish. It is pointed at the
# published copy, the directory `export` wrote, and every path it prints
# begins with that directory's own name, since a fetcher resolves each
# against the directory the manifest sits in.
#
# The heads come first — every head of the graph, superseded ones too,
# since they answer relatedness and nothing else — then one line per file
# that travels, in the order a fetcher should take them: payloads, then
# documents, then revisions, then the rules and the other tool's files no
# revision names, then the bookmarks (decision 0056). A line is the kind,
# the digest, what it forgets or `-`, and the path, last, since it is the
# one field that may hold a space. A rule or a bookmark that is private is
# not named: its file's name would be the disclosure its key exists to
# prevent.

import Base
import ./text.bend as T
import ./revision.bend as Rev
import ./store.bend as Store
import ./naming.bend as Naming
import ./bookmark.bend as Bm
import ./commands.bend as Main
import ./arrange.bend as Arrange
import ./prune.bend as Prune
import ./receive.bend as Receive
import ./folder.bend as Folder
import ./tree.bend as Tree
import ./standin.bend as Stand
import ./resolution.bend as Res
import ./ops.bend as Ops

# The words
# ---------

def first_dash(ws: List<&2, String>) -> Maybe<&2, String>:
  match ws:
    case Nil{}:
      None{}
    case +w <> rest:
      Bool.pick(Maybe<&2, String>, String.starts_with(w, "-"), Some{w}, first_dash(rest))

def args.plain(ws: List<&2, String>) -> Result<&2, &2, Main.Refused, String>:
  match ws:
    case Nil{}:
      Fail{Main.Refused{2, "`offer` wants the directory of the published copy: the one `export` wrote, with the manifest going beside it"}}
    case d <> Nil{}:
      Done{d}
    case d <> extra <> more:
      Fail{Main.Refused{2, "`offer` takes one directory, and `" ++ extra ++ "` is a second"}}

def args.of(+ws: List<&2, String>, dash: Maybe<&2, String>) -> Result<&2, &2, Main.Refused, String>:
  match dash:
    case Some{w}:
      Fail{Main.Refused{2, "`" ++ w ++ "` is not an argument `offer` takes"}}
    case None{}:
      args.plain(ws)

# A word starting `-` is refused wherever it stands, and the one other word
# is the directory.
def args.r(+ws: List<&2, String>) -> Result<&2, &2, Main.Refused, String>:
  args.of(ws, first_dash(ws))

# What a command line `offer` accepts says, written back as words: the
# directory, alone.
def args.read(r: Result<&2, &2, Main.Refused, String>) -> Maybe<&2, List<&2, String>>:
  match r:
    case Fail{e}:
      None{}
    case Done{d}:
      Some{[d]}

# The manifest
# ------------

# One transferable file: what sort it is, its digest, what it forgets, and
# its path from the manifest's own directory.
type Offered is Data:
  Offered{kind: String, digest: String, forgets: Maybe<&2, String>, path: String}

def offered.line(o: Offered) -> String:
  match o:
    case Offered{k, d, f, p}:
      k ++ " " ++ d ++ " " ++ Maybe.default(&2, String, f, "-") ++ " " ++ p

def offered.path(o: Offered) -> String:
  match o:
    case Offered{k, d, f, p}:
      p

def offered.kind(o: Offered) -> String:
  match o:
    case Offered{k, d, f, p}:
      k

# A store-relative label, as a fetcher asks for it: under the manifest's
# directory's name, or from `history/` down where there is none.
def addressed(+prefix: String, +label: String) -> String:
  Bool.pick(String, String.is_empty(prefix), "history/" ++ label, prefix ++ "/history/" ++ label)

def offered_le(+a: Offered, +b: Offered) -> Bool:
  String.is_le(offered.path(a), offered.path(b))

def by_path(+os: List<&2, Offered>) -> List<&2, Offered>:
  List.sort(~Offered, ~(a => b => offered_le(a, b)), os)

def splits.offered(ss: List<&2, T.Split>, +kind: String, +prefix: String) -> List<&2, Offered>:
  match ss:
    case Nil{}:
      Nil{}
    case T.Split{+p, +d} <> rest:
      Offered{kind, d, None{}, addressed(prefix, p)} <> splits.offered(rest, kind, prefix)

def bodies.offered(bs: List<&2, Prune.Body>, +prefix: String) -> List<&2, Offered>:
  match bs:
    case Nil{}:
      Nil{}
    case Prune.Body{+p, +d, ok, f} <> rest:
      Offered{"operation", d, f, addressed(prefix, p)} <> bodies.offered(rest, prefix)

# One file that travels where `keep` says so, at the digest its file was
# read to have; a file no longer there is a line shorter.
def offered.found(keep: Bool, found: Maybe<&2, String>, +label: String, +kind: String, +prefix: String, rest: List<&2, Offered>) -> List<&2, Offered>:
  match keep found:
    case True{} Some{d}:
      Offered{kind, d, None{}, addressed(prefix, label)} <> rest
    case _ _:
      rest

# The rules that travel, each at its file: a `private` rule's file name is
# derived from its text, and naming it would publish what it keeps back.
def rules.offered(rs: List<&2, Receive.Ruled>, +ids: List<&2, T.Split>, +prefix: String) -> List<&2, Offered>:
  match rs:
    case Nil{}:
      Nil{}
    case Receive.Ruled{+file, +line, l} <> rest:
      offered.found(Bool.not(String.starts_with(line, "private")), Arrange.lookup(ids, "skipped/" ++ file), "skipped/" ++ file, "rule", prefix, rules.offered(rest, ids, prefix))

# The bookmarks that travel, each at its file: a bookmark's file name is
# its name, which is what `private` keeps out of every copy.
def names.offered(bs: List<&2, Bm.Bookmark>, +ids: List<&2, T.Split>, +prefix: String) -> List<&2, Offered>:
  match bs:
    case Nil{}:
      Nil{}
    case Bm.Bookmark{+n, t, +p} <> rest:
      offered.found(Bool.not(p), Arrange.lookup(ids, "names/" ++ n ++ ".txt"), "names/" ++ n ++ ".txt", "name", prefix, names.offered(rest, ids, prefix))

def labels.offered(ls: List<&2, T.Split>, +prefix: String) -> List<&2, Offered>:
  splits.offered(ls, "reserved", prefix)

def heads.said(hs: List<&2, String>) -> List<&2, String>:
  match hs:
    case Nil{}:
      Nil{}
    case h <> rest:
      ("head " ++ h) <> heads.said(rest)

def rules.of(s: Prune.Stored) -> List<&2, T.Split>:
  match s:
    case Prune.Stored{docs, revs, od, bs, ps, names, rules}:
      rules

# The manifest's first lines: the header, the graph's heads in digest
# order, and the files every revision could name — payloads, documents,
# revisions — each group by path.
def manifest.front(+prefix: String, s: Prune.Stored) -> List<&2, String>:
  match s:
    case Prune.Stored{+docs, +revs, od, +bs, +ps, names, rules}:
      +fs = Arrange.distinct(Prune.fulls(Arrange.revision_docs(docs)))
      "historica-offer-1" <> List.append(&2, String, heads.said(Main.sorted_distinct(Rev.heads(Main.history(fs)))),
        T.map(~Offered, ~String, ~(o => offered.line(o)), List.concat(&2, Offered, [
          by_path(splits.offered(ps, "payload", prefix)),
          by_path(bodies.offered(bs, prefix)),
          by_path(splits.offered(revs, "revision", prefix))])))

# And the files no revision names: the rules, the other tool's, the
# bookmarks — each group by path.
def manifest.of(+front: List<&2, String>, rules: List<&2, Offered>, claims: List<&2, Offered>, names: List<&2, Offered>) -> List<&2, String>:
  List.append(&2, String, front, T.map(~Offered, ~String, ~(o => offered.line(o)), List.concat(&2, Offered, [by_path(rules), by_path(claims), by_path(names)])))

# Every line of the manifest, in the order `Offer` is rendered.
def manifest(+prefix: String, +s: Prune.Stored, +marks: List<&2, Bm.Bookmark>, +claims: List<&2, T.Split>, +rule_ids: List<&2, T.Split>, +name_ids: List<&2, T.Split>) -> List<&2, String>:
  manifest.of(manifest.front(prefix, s), rules.offered(Receive.ruled(rules.of(s)), rule_ids, prefix), splits.offered(claims, "reserved", prefix), names.offered(marks, name_ids, prefix))

# What the laws say of a manifest
# -------------------------------

# A line names a file of the listing it was drawn from, by the digest that
# listing gives the file.
def listed(ss: List<&2, T.Split>, +prefix: String, +path: String, +digest: String) -> Bool:
  match ss:
    case Nil{}:
      False{}
    case T.Split{+l, +d} <> rest:
      Bool.or(Bool.and(String.eq(addressed(prefix, l), path), String.eq(d, digest)), listed(rest, prefix, path, digest))

def offered.from(os: List<&2, Offered>, +ss: List<&2, T.Split>, +prefix: String) -> Bool:
  match os:
    case Nil{}:
      True{}
    case Offered{k, +d, f, +p} <> rest:
      Bool.and(listed(ss, prefix, p, d), offered.from(rest, ss, prefix))

def body.splits(bs: List<&2, Prune.Body>) -> List<&2, T.Split>:
  match bs:
    case Nil{}:
      Nil{}
    case Prune.Body{+p, +d, ok, f} <> rest:
      T.Split{p, d} <> body.splits(rest)

# Every line of a manifest, group by group: each payload, document,
# revision, rule, file of `claims/` and bookmark is named by the digest the
# store's listing gives the file at that path.
def manifest.from(+prefix: String, s: Prune.Stored, +marks: List<&2, Bm.Bookmark>, +claims: List<&2, T.Split>, +rule_ids: List<&2, T.Split>, +name_ids: List<&2, T.Split>) -> Bool:
  match s:
    case Prune.Stored{docs, +revs, od, +bs, +ps, names, rules}:
      Bool.and(offered.from(splits.offered(ps, "payload", prefix), ps, prefix),
        Bool.and(offered.from(bodies.offered(bs, prefix), body.splits(bs), prefix),
          Bool.and(offered.from(splits.offered(revs, "revision", prefix), revs, prefix),
            Bool.and(offered.from(rules.offered(Receive.ruled(rules), rule_ids, prefix), rule_ids, prefix),
              Bool.and(offered.from(splits.offered(claims, "reserved", prefix), claims, prefix),
                offered.from(names.offered(marks, name_ids, prefix), name_ids, prefix))))))

# The bookmarks that travel.
def shared(bs: List<&2, Bm.Bookmark>) -> List<&2, Bm.Bookmark>:
  match bs:
    case Nil{}:
      Nil{}
    case Bm.Bookmark{+n, +t, +p} <> rest:
      Tree.keep(~Bm.Bookmark, Bool.not(p), Bm.Bookmark{n, t, p}, shared(rest))

def rule.private(r: Maybe<&2, Receive.Ruled>) -> Bool:
  match r:
    case None{}:
      False{}
    case Some{Receive.Ruled{f, +line, l}}:
      String.starts_with(line, "private")

# The files of `skipped/` that are not a private rule's.
def shared_files(rs: List<&2, T.Split>) -> List<&2, T.Split>:
  match rs:
    case Nil{}:
      Nil{}
    case T.Split{+path, +text} <> rest:
      Tree.keep(~T.Split, Bool.not(rule.private(Receive.ruled.of(Receive.skipped_file(path), text, Folder.rule_in(text)))), T.Split{path, text}, shared_files(rest))

# The same store, with no private rule in it.
def shared_rules(s: Prune.Stored) -> Prune.Stored:
  match s:
    case Prune.Stored{docs, revs, od, bs, ps, names, rules}:
      Prune.Stored{docs, revs, od, bs, ps, names, shared_files(rules)}

# Reading
# -------

def header.r(+copy: String, header: Result<&1, &1, U32 & String, String>) -> Result<&2, &2, Main.Refused, Unit>:
  match header:
    case Done{x}:
      Done{Unit{}}
    case Fail{e}:
      Fail{Main.Refused{1, copy ++ " holds no `history/historica.txt`, so there is nothing to offer; `offer` is pointed at the published copy — the directory `export` wrote — rather than at the store inside it"}}

def ids.of(+root: String, ds: List<&2, Store.Doc>) -> List<&2, T.Split>:
  match ds:
    case Nil{}:
      Nil{}
    case Store.Doc{+path, +id, n, t} <> rest:
      T.Split{Store.relative(root, path), id} <> ids.of(root, rest)

def name_file(b: Bm.Bookmark) -> String:
  "names/" ++ Bm.name_of(b) ++ ".txt"

def rule_path(s: T.Split) -> String:
  Prune.split.path(s)

def prefix.of(+copy: String, real: Result<&1, &1, U32 & String, String>) -> String:
  match real:
    case Done{r}:
      Naming.last(r)
    case Fail{e}:
      Naming.last(copy)

# What the Rust tool's catalogue of `operations/` says a document forgets,
# which is what its manifest lists: a payload's stand-in and an operation
# document their `forgets` line, and a resolution nothing, since the
# catalogue parses no resolution — a forgetting one included.
def catalogue.forgets(+text: String) -> Maybe<&2, String>:
  Bool.pick(Maybe<&2, String>, Prune.forgotten.payload(T.lines(text)), Stand.payload.forgets(Stand.payload.parse(text)),
    Bool.pick(Maybe<&2, String>, Res.is_resolution(text), None{}, Prune.ops.forgets(Ops.parse(text))))

def catalogued(+root: String, ds: List<&2, Store.Doc>) -> List<&2, Prune.Body>:
  match ds:
    case Nil{}:
      Nil{}
    case Store.Doc{+path, +id, n, +text} <> rest:
      Prune.Body{Store.relative(root, path), id, True{}, catalogue.forgets(text)} <> catalogued(root, rest)

# The store as the catalogue has it: each document with what the catalogue
# says it forgets.
def stored.catalogued(+root: String, s: Prune.Stored) -> Prune.Stored:
  match s:
    case Prune.Stored{docs, revs, +od, bs, ps, names, rules}:
      Prune.Stored{docs, revs, od, List.sort(~Prune.Body, ~(a => b => Prune.body_le(a, b)), catalogued(root, od)), ps, names, rules}

def offer(+args: List<&2, String>) -> IO(Unit):
  do IO<Unit>:
    dir : String <- Main.refused.io(String, args.r(args))
    here : Result<&1, &1, U32 & String, String> <- Store.really(SNil{})
    base : String <- Main.init.io(String, here)
    +copy : String = Main.path_join(base, dir)
    header : Result<&1, &1, U32 & String, String> <- Store.really(copy ++ "/history/historica.txt")
    Main.refused.io(Unit, header.r(copy, header))
    +root : String = copy ++ "/history"
    st : Prune.Stored <- Prune.read(root)
    +st2 : Prune.Stored = stored.catalogued(root, st)
    Main.refused.io(Unit, Arrange.opened.r(List.sort(~Store.Doc, ~(a => b => Arrange.doc_le(a, b)), Receive.stored.docs(st2))))
    bs : List<&2, Bm.Bookmark> <- Main.bookmarks(root)
    +bs2 : List<&2, Bm.Bookmark> = bs
    listed : List<&2, String> <- Store.claims_paths(root)
    +cl : List<&2, String> = Prune.not_platform(listed)
    stats : List<&2, String> <- Store.stats(root, cl)
    rds : List<&2, Store.Doc> <- Store.read_docs(Store.under(root, T.map(~T.Split, ~String, ~(x => rule_path(x)), rules.of(st2))))
    nds : List<&2, Store.Doc> <- Store.read_docs(Store.under(root, T.map(~Bm.Bookmark, ~String, ~(b => name_file(b)), bs2)))
    real : Result<&1, &1, U32 & String, String> <- Store.really(copy)
    Arrange.print_lines(manifest(prefix.of(copy, real), st2, bs2, Arrange.zip.stats(cl, stats), ids.of(root, rds), ids.of(root, nds)))
