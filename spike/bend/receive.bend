# `receive <dir> [--dry-run] [--join-unrelated] [--fields]`: another local
# store's immutable history, unioned into this one.
#
# Decision 0029: copying a store is already transport, and receiving is the
# narrower operation copying cannot perform safely once both stores have
# changed. Documents union by what they hold — a revision, a document or a
# payload is received where this store has nothing with its digest — and
# the mutable files are kept apart: a bookmark this store lacks arrives
# whole, one both hold at one target joins its axis (decision 0062), and one
# they point at two things is a disagreement that stops the whole receive.
# Rules union like the documents (0045), and so does the one directory
# another tool keeps that travels, `claims/`, by name and unread (0053).
# What either store forgets is received by neither, and an original this
# store still holds that an arriving forgetting document stands in for is
# destroyed (0014). Nothing moves in either working copy.
#
# Every document received is read here and hashed in `sha256.bend`, and
# filed under the digest its bytes have, whatever the source called it; a
# payload is copied by the host, which hashes it on the way past and refuses
# one that no longer has the digest the listing found.

import Base
import ./text.bend as T
import ./revision.bend as Rev
import ./store.bend as Store
import ./tree.bend as Tree
import ./naming.bend as Naming
import ./bookmark.bend as Bm
import ./folder.bend as Folder
import ./sha256.bend as Sha
import ./utf8.bend as Utf8
import ./commands.bend as Main
import ./arrange.bend as Arrange
import ./prune.bend as Prune
import ./check.bend as Check

# The words
# ---------

type ReceiveCmd is Data:
  ReceiveCmd{dry: Bool, fields: Bool, join: Bool, source: String}

type RWord is Data:
  RWord.Dry{}
  RWord.Fields{}
  RWord.Join{}
  RWord.Flag{}
  RWord.Plain{}
  RWord.End{}

def rword(+w: String) -> RWord:
  Bool.pick(RWord, Bool.or(String.eq(w, "-n"), String.eq(w, "--dry-run")), RWord.Dry{},
  Bool.pick(RWord, String.eq(w, "--fields"), RWord.Fields{},
  Bool.pick(RWord, String.eq(w, "--join-unrelated"), RWord.Join{},
  Bool.pick(RWord, String.starts_with(w, "-"), RWord.Flag{}, RWord.Plain{}))))

def rword.of(ws: List<&2, String>) -> RWord:
  match ws:
    case Nil{}:
      RWord.End{}
    case +w <> rest:
      rword(w)

def args.done(+dry: Bool, +fields: Bool, +join: Bool, source: Maybe<&2, String>) -> Result<&2, &2, Main.Refused, ReceiveCmd>:
  match source:
    case None{}:
      Fail{Main.Refused{2, "`receive` wants a source directory"}}
    case Some{s}:
      Done{ReceiveCmd{dry, fields, join, s}}

# A plan is not on disk, so `--fields` has nothing to say of one; and there
# is nothing to receive from without a directory.
def args.end.of(both: Bool, +dry: Bool, +fields: Bool, +join: Bool, source: Maybe<&2, String>) -> Result<&2, &2, Main.Refused, ReceiveCmd>:
  match both:
    case True{}:
      Fail{Main.Refused{2, "`receive --dry-run --fields` is refused: `--fields` states what is on disk, and a plan is not on disk. ask for one or the other"}}
    case False{}:
      args.done(dry, fields, join, source)

def args.end(+dry: Bool, +fields: Bool, +join: Bool, source: Maybe<&2, String>) -> Result<&2, &2, Main.Refused, ReceiveCmd>:
  args.end.of(Bool.and(dry, fields), dry, fields, join, source)

# The words in order, as the Rust tool reads them: each flag wherever it
# stands, the first word that is not one the source, and the first word
# that is neither refused where it stands. `k` is what the first word is.
def args.go(ws: List<&2, String>, k: RWord, +dry: Bool, +fields: Bool, +join: Bool, +source: Maybe<&2, String>) -> Result<&2, &2, Main.Refused, ReceiveCmd>:
  match ws:
    case Nil{}:
      args.end(dry, fields, join, source)
    case +w <> +rest:
      match k:
        case RWord.Dry{}:
          args.go(rest, rword.of(rest), True{}, fields, join, source)
        case RWord.Fields{}:
          args.go(rest, rword.of(rest), dry, True{}, join, source)
        case RWord.Join{}:
          args.go(rest, rword.of(rest), dry, fields, True{}, source)
        case RWord.Flag{}:
          Fail{Main.Refused{2, "`" ++ w ++ "` is not an argument `receive` takes"}}
        case RWord.End{}:
          args.end(dry, fields, join, source)
        case RWord.Plain{}:
          match source:
            case None{}:
              args.go(rest, rword.of(rest), dry, fields, join, Some{w})
            case Some{s}:
              Fail{Main.Refused{2, "`receive` wants one source directory, not `" ++ w ++ "`"}}

def args.r(+ws: List<&2, String>) -> Result<&2, &2, Main.Refused, ReceiveCmd>:
  args.go(ws, rword.of(ws), False{}, False{}, False{}, None{})

# What a command `receive` read says, written back as words: its three
# flags, and the source directory as the one other word.
type Said is Data:
  Said{dry: Bool, fields: Bool, join: Bool, words: List<&2, String>}

def args.read(r: Result<&2, &2, Main.Refused, ReceiveCmd>) -> Maybe<&2, Said>:
  match r:
    case Fail{e}:
      None{}
    case Done{ReceiveCmd{dry, fields, join, source}}:
      Some{Said{dry, fields, join, [source]}}

# A store as receive reads it
# ---------------------------

# One rule, as its file states it: the file, below `skipped/`, the rule's
# own line — `skip` or `private`, `skip-name` or `private-name`, and the
# value, a directory's with its `/` — and the label a store that has no
# file of that name writes the rule under.
type Ruled is Data:
  Ruled{file: String, line: String, label: String}

# The key of the one rule a file states: the first word of its first line
# that says anything.
def rule.key(ls: List<&2, String>) -> String:
  match ls:
    case Nil{}:
      SNil{}
    case +l <> rest:
      Bool.pick(String, Bool.or(String.is_empty(l), String.starts_with(l, "#")), rule.key(rest), T.word(l))

def rule.value(sc: Folder.Scope) -> String:
  match sc:
    case Folder.Scope.Path{v}:
      v
    case Folder.Scope.Under{v}:
      v ++ "/"
    case Folder.Scope.Name{p}:
      p
    case Folder.Scope.NameUnder{p}:
      p ++ "/"

def rule.named(sc: Folder.Scope) -> Bool:
  match sc:
    case Folder.Scope.Name{p}:
      True{}
    case Folder.Scope.NameUnder{p}:
      True{}
    case _:
      False{}

def rule.under(sc: Folder.Scope) -> Bool:
  match sc:
    case Folder.Scope.Under{p}:
      True{}
    case Folder.Scope.NameUnder{p}:
      True{}
    case _:
      False{}

# The line a rule is written as, whatever spacing its file had.
def rule.line(+private: Bool, +sc: Folder.Scope) -> String:
  Bool.pick(String, private, Bool.pick(String, rule.named(sc), "private-name", "private"), Bool.pick(String, rule.named(sc), "skip-name", "skip")) ++ " " ++ rule.value(sc)

# `Rule::label`: the rule's own value, as a file under `skipped/`.
def rule.natural(sc: Folder.Scope) -> String:
  match sc:
    case Folder.Scope.Path{v}:
      Naming.scrubbed(v) ++ ".txt"
    case Folder.Scope.Under{v}:
      Naming.scrubbed(v) ++ "/all.txt"
    case Folder.Scope.Name{p}:
      "name " ++ Naming.scrubbed(p) ++ ".txt"
    case Folder.Scope.NameUnder{p}:
      "name " ++ Naming.scrubbed(p) ++ "/all.txt"

def components_ok(cs: List<&2, String>) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case +c <> rest:
      Bool.and(Bool.and(Bool.not(String.is_empty(c)), Nat.is_le(List.length(&2, U32, Utf8.encode(c)), 200n)), components_ok(rest))

# Whether the natural label is one the directory can carry: not a name the
# platform writes, not the note, `all.txt` only for a rule over a
# directory, no `*`, and no component empty or too long.
def spellable(+sc: Folder.Scope, +natural: String) -> Bool:
  +last = Naming.last(natural)
  Bool.and(Bool.and(Bool.not(Naming.platform_name(last)), Bool.not(String.eq(natural, "README.txt"))),
    Bool.and(Bool.or(Bool.not(String.eq(last, "all.txt")), rule.under(sc)),
      Bool.and(Bool.not(T.has_char(natural, '*')), components_ok(String.split(natural, '/')))))

# The label a rule falls back on: its line's digest, so two replicas that
# both fall back fall back to one name.
def rule.digest_label(+line: String) -> String:
  String.take(Sha.digest(Utf8.encode(line)), Naming.DIGEST_CHARS()) ++ ".txt"

def rule.label(+sc: Folder.Scope, +line: String) -> String:
  Bool.pick(String, spellable(sc, rule.natural(sc)), rule.natural(sc), rule.digest_label(line))

def ruled.of(+file: String, +text: String, st: Folder.Stated) -> Maybe<&2, Ruled>:
  match st:
    case Folder.Stated.One{+sc}:
      +line = rule.line(String.starts_with(rule.key(Folder.lines.trimmed(String.split(text, '\n'))), "private"), sc)
      Some{Ruled{file, line, rule.label(sc, line)}}
    case _:
      None{}

def ruled.push(r: Maybe<&2, Ruled>, rest: List<&2, Ruled>) -> List<&2, Ruled>:
  match r:
    case None{}:
      rest
    case Some{x}:
      x <> rest

def skipped_file(+path: String) -> String:
  Maybe.default(&2, String, T.strip_prefix(path, "skipped/"), path)

# Every rule a store states, each with its file, in the walk's order.
def ruled(rs: List<&2, T.Split>) -> List<&2, Ruled>:
  match rs:
    case Nil{}:
      Nil{}
    case T.Split{+path, +text} <> rest:
      ruled.push(ruled.of(skipped_file(path), text, Folder.rule_in(text)), ruled(rest))

def ruled.line(r: Ruled) -> String:
  match r:
    case Ruled{f, line, l}:
      line

def ruled.label(r: Ruled) -> String:
  match r:
    case Ruled{f, l, label}:
      label

# A store as `receive` reads it, on either side: where it is, what `prune`
# reads of it, its bookmarks, and the files of `claims/` by digest.
type Side is Data:
  Side{root: String, stored: Prune.Stored, marks: List<&2, Bm.Bookmark>, claims: List<&2, T.Split>}

def stored.of(s: Side) -> Prune.Stored:
  match s:
    case Side{r, st, m, c}:
      st

def side.root(s: Side) -> String:
  match s:
    case Side{r, st, m, c}:
      r

def side.marks(s: Side) -> List<&2, Bm.Bookmark>:
  match s:
    case Side{r, st, m, c}:
      m

def side.claims(s: Side) -> List<&2, T.Split>:
  match s:
    case Side{r, st, m, c}:
      c

def stored.docs(s: Prune.Stored) -> List<&2, Store.Doc>:
  match s:
    case Prune.Stored{docs, revs, od, bs, ps, names, rules}:
      docs

def stored.odocs(s: Prune.Stored) -> List<&2, Store.Doc>:
  match s:
    case Prune.Stored{docs, revs, od, bs, ps, names, rules}:
      od

def stored.bodies(s: Prune.Stored) -> List<&2, Prune.Body>:
  match s:
    case Prune.Stored{docs, revs, od, bs, ps, names, rules}:
      bs

def stored.payloads(s: Prune.Stored) -> List<&2, T.Split>:
  match s:
    case Prune.Stored{docs, revs, od, bs, ps, names, rules}:
      ps

def stored.rules(s: Prune.Stored) -> List<&2, T.Split>:
  match s:
    case Prune.Stored{docs, revs, od, bs, ps, names, rules}:
      rules

# What each side holds
# --------------------

def doc.id_le(+a: Store.Doc, +b: Store.Doc) -> Bool:
  String.is_le(Store.id_of(a), Store.id_of(b))

def doc.keep(b: Bool, d: Store.Doc, rest: List<&2, Store.Doc>) -> List<&2, Store.Doc>:
  match b:
    case True{}:
      d <> rest
    case False{}:
      rest

def docs.dedup(ds: List<&2, Store.Doc>, +prev: String) -> List<&2, Store.Doc>:
  match ds:
    case Nil{}:
      Nil{}
    case +d <> rest:
      doc.keep(Bool.not(String.eq(Store.id_of(d), prev)), d, docs.dedup(rest, Store.id_of(d)))

# Each document once, by digest, in digest order: what a map by digest
# holds of files that may be copies of each other.
def docs.distinct(+ds: List<&2, Store.Doc>) -> List<&2, Store.Doc>:
  docs.dedup(List.sort(~Store.Doc, ~(a => b => doc.id_le(a, b)), ds), SNil{})

def docs.parsing(ds: List<&2, Store.Doc>) -> List<&2, Store.Doc>:
  match ds:
    case Nil{}:
      Nil{}
    case +d <> rest:
      doc.keep(Arrange.parses(d), d, docs.parsing(rest))

# The revision documents a side holds, each once, in digest order.
def side.revisions(+s: Side) -> List<&2, Store.Doc>:
  docs.distinct(docs.parsing(Arrange.revision_docs(stored.docs(stored.of(s)))))

def side.fulls(+s: Side) -> List<&2, Main.Full>:
  Arrange.distinct(Prune.fulls(Arrange.revision_docs(stored.docs(stored.of(s)))))

def split.le(+a: T.Split, +b: T.Split) -> Bool:
  match a b:
    case T.Split{p, +x} T.Split{q, +y}:
      String.is_le(x, y)

def split.digest(s: T.Split) -> String:
  match s:
    case T.Split{p, d}:
      d

def splits.dedup(ss: List<&2, T.Split>, +prev: String) -> List<&2, T.Split>:
  match ss:
    case Nil{}:
      Nil{}
    case +s <> rest:
      Tree.keep(~T.Split, Bool.not(String.eq(split.digest(s), prev)), s, splits.dedup(rest, split.digest(s)))

# Each payload once, by digest, in digest order, at the first path in the
# walk's order that holds it.
def splits.distinct(+ss: List<&2, T.Split>) -> List<&2, T.Split>:
  splits.dedup(List.sort(~T.Split, ~(a => b => split.le(a, b)), ss), SNil{})

def forgets.push(f: Maybe<&2, String>, rest: List<&2, String>) -> List<&2, String>:
  match f:
    case None{}:
      rest
    case Some{t}:
      t <> rest

# Every digest these documents forget.
def body.forgets(bs: List<&2, Prune.Body>) -> List<&2, String>:
  match bs:
    case Nil{}:
      Nil{}
    case Prune.Body{p, i, ok, f} <> rest:
      forgets.push(f, body.forgets(rest))

def any_in(xs: List<&2, String>, +s: Set()) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case +x <> rest:
      Bool.or(Arrange.has(s, x), any_in(rest, s))

def edges(fs: List<&2, Main.Full>) -> List<&2, String>:
  match fs:
    case Nil{}:
      Nil{}
    case +f <> rest:
      List.append(&2, String, List.append(&2, String, Main.parents_of(f), Prune.supersedes_of(f)), edges(rest))

# Decision 0029: an empty store may be seeded, and otherwise one shared
# revision, or one revision naming the other's as a parent or as what it
# supersedes, is the evidence that two stores are partial views of one
# history.
def related(+ours: List<&2, Main.Full>, +theirs: List<&2, Main.Full>) -> Bool:
  +oi = Set.from_list(Main.ids(ours))
  +ti = Set.from_list(Main.ids(theirs))
  Bool.or(Bool.or(List.is_empty(&2, Main.Full, ours), List.is_empty(&2, Main.Full, theirs)),
    Bool.or(any_in(Main.ids(theirs), oi), Bool.or(any_in(edges(theirs), oi), any_in(edges(ours), ti))))

# The plan
# --------

# A bookmark both stores hold at two targets: the one disagreement that
# stops a receive, since neither can be told which is meant.
type Conflict is Data:
  Conflict{name: String, here: Bm.Bookmark, there: Bm.Bookmark}

# What the source's bookmarks come to: those this store will write, and
# the disagreements.
type Marked is Data:
  Marked{names: List<&2, Bm.Bookmark>, conflicts: List<&2, Conflict>}

def same_target(a: Bm.Target, b: Bm.Target) -> Bool:
  String.eq(Bm.show_target(a), Bm.show_target(b))

def marked.joined(+n: String, +ht: Bm.Target, +hp: Bool, +tp: Bool) -> Marked:
  Bool.pick(Marked, Bool.and(tp, Bool.not(hp)), Marked{[Bm.Bookmark{n, ht, True{}}], Nil{}}, Marked{Nil{}, Nil{}})

# Decision 0062, for one of the source's bookmarks: one this store lacks
# arrives whole; one both hold at one target joins its axis, private where
# either says so, and is written only where that changes it; one both hold
# at two targets is a disagreement.
def marked.one(there: Bm.Bookmark, here: Maybe<&2, Bm.Bookmark>) -> Marked:
  match there here:
    case +t None{}:
      Marked{[t], Nil{}}
    case Bm.Bookmark{+n, +tt, +tp} Some{Bm.Bookmark{+hn, +ht, +hp}}:
      Bool.pick(Marked, same_target(tt, ht), marked.joined(n, ht, hp, tp), Marked{Nil{}, [Conflict{n, Bm.Bookmark{hn, ht, hp}, Bm.Bookmark{n, tt, tp}}]})

def marked.join(a: Marked, b: Marked) -> Marked:
  match a b:
    case Marked{an, ac} Marked{bn, bc}:
      Marked{List.append(&2, Bm.Bookmark, an, bn), List.append(&2, Conflict, ac, bc)}

def marked.all(ts: List<&2, Bm.Bookmark>, +here: List<&2, Bm.Bookmark>) -> Marked:
  match ts:
    case Nil{}:
      Marked{Nil{}, Nil{}}
    case +t <> rest:
      marked.join(marked.one(t, Main.found_of(here, Bm.name_of(t))), marked.all(rest, here))

def docs.lacking(ds: List<&2, Store.Doc>, +have: Set()) -> List<&2, Store.Doc>:
  match ds:
    case Nil{}:
      Nil{}
    case +d <> rest:
      doc.keep(Bool.not(Arrange.has(have, Store.id_of(d))), d, docs.lacking(rest, have))

def splits.lacking(ss: List<&2, T.Split>, +have: Set()) -> List<&2, T.Split>:
  match ss:
    case Nil{}:
      Nil{}
    case +s <> rest:
      Tree.keep(~T.Split, Bool.not(Arrange.has(have, split.digest(s))), s, splits.lacking(rest, have))

def split.label(s: T.Split) -> String:
  match s:
    case T.Split{l, d}:
      l

def labels.lacking(ss: List<&2, T.Split>, +have: Set()) -> List<&2, T.Split>:
  match ss:
    case Nil{}:
      Nil{}
    case +s <> rest:
      Tree.keep(~T.Split, Bool.not(Arrange.has(have, split.label(s))), s, labels.lacking(rest, have))

def rules.lacking(rs: List<&2, Ruled>, +have: Set()) -> List<&2, Ruled>:
  match rs:
    case Nil{}:
      Nil{}
    case +r <> rest:
      Tree.keep(~Ruled, Bool.not(Arrange.has(have, ruled.line(r))), r, rules.lacking(rest, have))

def body.ids(bs: List<&2, Prune.Body>) -> List<&2, String>:
  T.map(~Prune.Body, ~String, ~(b => Prune.body.id(b)), bs)

def payload.ids(ps: List<&2, T.Split>) -> List<&2, String>:
  T.map(~T.Split, ~String, ~(s => split.digest(s)), ps)

# What receiving will write, worked out before anything is: the source's
# revisions, documents and payloads this store has nothing under the digest
# of, less what either store forgets; its bookmarks, as decision 0062 joins
# them, and the disagreements; its rules and the files of `claims/` this
# store lacks; and the originals here a forgetting document stands in for.
type RPlan is Data:
  RPlan{revisions: List<&2, Store.Doc>, documents: List<&2, Store.Doc>, payloads: List<&2, T.Split>, names: List<&2, Bm.Bookmark>, rules: List<&2, Ruled>, reserved: List<&2, T.Split>, destroys: List<&2, String>, conflicts: List<&2, Conflict>}

def marked.names(m: Marked) -> List<&2, Bm.Bookmark>:
  match m:
    case Marked{ns, cs}:
      ns

def marked.conflicts(m: Marked) -> List<&2, Conflict>:
  match m:
    case Marked{ns, cs}:
      cs

def among(xs: List<&2, String>, +s: Set()) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case +x <> rest:
      Rev.keep(Arrange.has(s, x), x, among(rest, s))

# Every digest a forgetting document of either store stands in for.
def forgotten(+here: Side, +there: Side) -> List<&2, String>:
  List.append(&2, String, body.forgets(stored.bodies(stored.of(here))), body.forgets(stored.bodies(stored.of(there))))

# What this store has of each kind, and what neither may be given: the
# revisions it holds; the documents of `operations/` it holds and every
# digest either store forgets; its payloads and the same.
def have.revisions(+here: Side) -> Set():
  Set.from_list(Main.ids(side.fulls(here)))

def have.documents(+here: Side, +there: Side) -> Set():
  Set.from_list(List.append(&2, String, body.ids(stored.bodies(stored.of(here))), forgotten(here, there)))

def have.payloads(+here: Side, +there: Side) -> Set():
  Set.from_list(List.append(&2, String, payload.ids(stored.payloads(stored.of(here))), forgotten(here, there)))

# The originals here a forgetting document stands in for: what either
# store forgets that this one still holds, a document or a payload.
def destroys(+here: Side, +there: Side) -> List<&2, String>:
  Main.sorted_distinct(among(forgotten(here, there), Set.from_list(List.append(&2, String, body.ids(stored.bodies(stored.of(here))), payload.ids(stored.payloads(stored.of(here)))))))

# `Store::receive_plan`, once both stores are known to pass the check and
# to be related.
def plan.of(+here: Side, +there: Side) -> RPlan:
  +m = marked.all(side.marks(there), side.marks(here))
  RPlan{
    docs.lacking(side.revisions(there), have.revisions(here)),
    docs.lacking(docs.distinct(stored.odocs(stored.of(there))), have.documents(here, there)),
    splits.lacking(splits.distinct(stored.payloads(stored.of(there))), have.payloads(here, there)),
    marked.names(m),
    rules.lacking(ruled(stored.rules(stored.of(there))), Set.from_list(T.map(~Ruled, ~String, ~(r => ruled.line(r)), ruled(stored.rules(stored.of(here)))))),
    labels.lacking(side.claims(there), Set.from_list(T.map(~T.Split, ~String, ~(s => split.label(s)), side.claims(here)))),
    destroys(here, there),
    marked.conflicts(m)}

# What the laws say of a plan
# ---------------------------

def docs.fresh(ds: List<&2, Store.Doc>, +have: Set()) -> Bool:
  match ds:
    case Nil{}:
      True{}
    case +d <> rest:
      Bool.and(Bool.not(Arrange.has(have, Store.id_of(d))), docs.fresh(rest, have))

def splits.fresh(ss: List<&2, T.Split>, +have: Set()) -> Bool:
  match ss:
    case Nil{}:
      True{}
    case +s <> rest:
      Bool.and(Bool.not(Arrange.has(have, split.digest(s))), splits.fresh(rest, have))

# Whether a plan takes only what this store lacks: revisions it does not
# hold, and documents and payloads it has nothing under the digest of and
# neither store forgets.
def fresh(+here: Side, +there: Side, p: RPlan) -> Bool:
  match p:
    case RPlan{rs, ds, ps, ns, rules, res, des, cs}:
      Bool.and(docs.fresh(rs, have.revisions(here)), Bool.and(docs.fresh(ds, have.documents(here, there)), splits.fresh(ps, have.payloads(here, there))))

def keeps.of(+t: Bm.Target, found: Maybe<&2, Bm.Bookmark>) -> Bool:
  match found:
    case None{}:
      True{}
    case Some{Bm.Bookmark{hn, +ht, hp}}:
      same_target(ht, t)

# Whether writing this bookmark leaves one this store has pointing where
# it did: a name it lacks, or one it holds at the same target.
def keeps(+hm: List<&2, Bm.Bookmark>, b: Bm.Bookmark) -> Bool:
  match b:
    case Bm.Bookmark{+n, +t, p}:
      keeps.of(t, Main.found_of(hm, n))

def names_kept(bs: List<&2, Bm.Bookmark>, +hm: List<&2, Bm.Bookmark>) -> Bool:
  match bs:
    case Nil{}:
      True{}
    case +b <> rest:
      Bool.and(keeps(hm, b), names_kept(rest, hm))

def rplan.destroys(p: RPlan) -> List<&2, String>:
  match p:
    case RPlan{rs, ds, ps, ns, rules, res, des, cs}:
      des

def plan.related(ok: Bool, +here: Side, +there: Side) -> Result<&2, &2, Main.Refused, RPlan>:
  match ok:
    case True{}:
      Done{plan.of(here, there)}
    case False{}:
      Fail{Main.Refused{1, "these nonempty stores share no revision or graph edge; use `--join-unrelated` only if combining two histories is intended"}}

def plan.source(ok: Bool, +here: Side, +there: Side, +join: Bool) -> Result<&2, &2, Main.Refused, RPlan>:
  match ok:
    case True{}:
      plan.related(Bool.or(join, related(side.fulls(here), side.fulls(there))), here, there)
    case False{}:
      Fail{Main.Refused{1, "the source store does not pass `check`; receive writes nothing until its errors are repaired"}}

def plan.here(ok: Bool, +here: Side, +there: Side, +join: Bool) -> Result<&2, &2, Main.Refused, RPlan>:
  match ok:
    case True{}:
      plan.source(Prune.sound(stored.of(there)), here, there, join)
    case False{}:
      Fail{Main.Refused{1, "the receiving store does not pass `check`; receive writes nothing until its errors are repaired"}}

# Nothing is planned from a store `check` would call broken, on either
# side, or between two nonempty stores that share nothing, unless asked.
def plan.r(+here: Side, +there: Side, +join: Bool) -> Result<&2, &2, Main.Refused, RPlan>:
  plan.here(Prune.sound(stored.of(here)), here, there, join)

# What the laws say of forgetting: whether a forgetting document stands
# in for this digest, and whether one among these does.
def stands.for(f: Maybe<&2, String>, +d: String) -> Bool:
  match f:
    case None{}:
      False{}
    case Some{t}:
      String.eq(t, d)

def forgot.by(bs: List<&2, Prune.Body>, +d: String) -> Bool:
  match bs:
    case Nil{}:
      False{}
    case Prune.Body{p, i, ok, f} <> rest:
      Bool.or(stands.for(f, d), forgot.by(rest, d))

# The report
# ----------

def count.line(+prefix: String, +n: Nat, +what: String) -> String:
  prefix ++ " " ++ Nat.show(n) ++ " " ++ what

def count.if(+prefix: String, +n: Nat, +what: String) -> List<&2, String>:
  Bool.pick(List<&2, String>, Nat.is_eq(n, 0n), Nil{}, [count.line(prefix, n, what)])

def said.bookmarks(bs: List<&2, Bm.Bookmark>) -> List<&2, String>:
  match bs:
    case Nil{}:
      Nil{}
    case +b <> rest:
      ("would receive bookmark " ++ Bm.name_of(b) ++ " -> " ++ Bm.show(b)) <> said.bookmarks(rest)

def said.conflicts(cs: List<&2, Conflict>) -> List<&2, String>:
  match cs:
    case Nil{}:
      Nil{}
    case Conflict{n, h, t} <> rest:
      ("conflict: name " ++ n ++ " is " ++ Bm.show(h) ++ " here and " ++ Bm.show(t) ++ " there") <> said.conflicts(rest)

def refused.conflicts(cs: List<&2, Conflict>) -> String:
  match cs:
    case Nil{}:
      SNil{}
    case Conflict{n, h, t} <> rest:
      "  name " ++ n ++ ": here `" ++ Bm.show(h) ++ "`, there `" ++ Bm.show(t) ++ "`\n" ++ refused.conflicts(rest)

# What a dry run prints: how many of each kind would arrive, every bookmark
# as it would be written, and every disagreement.
def said.plan(p: RPlan) -> List<&2, String>:
  match p:
    case RPlan{+rs, +ds, +ps, +ns, +rules, +res, +des, +cs}:
      List.concat(&2, String, [
        [count.line("would receive", List.length(&2, Store.Doc, rs), "revisions"),
         count.line("would receive", List.length(&2, Store.Doc, ds), "content documents"),
         count.line("would receive", List.length(&2, T.Split, ps), "payloads")],
        said.bookmarks(ns),
        count.if("would receive", List.length(&2, Ruled, rules), "rules"),
        count.if("would receive", List.length(&2, T.Split, res), "files another tool wrote"),
        count.if("would destroy", List.length(&2, String, des), "forgotten originals"),
        said.conflicts(cs)])

def rplan.conflicts(p: RPlan) -> List<&2, Conflict>:
  match p:
    case RPlan{rs, ds, ps, ns, rules, res, des, cs}:
      cs

def rplan.revisions(p: RPlan) -> List<&2, Store.Doc>:
  match p:
    case RPlan{rs, ds, ps, ns, rules, res, des, cs}:
      rs

def rplan.names(p: RPlan) -> List<&2, Bm.Bookmark>:
  match p:
    case RPlan{rs, ds, ps, ns, rules, res, des, cs}:
      ns

# A plan with a disagreement in it writes nothing.
def agreed.r(+p: RPlan) -> Result<&2, &2, Main.Refused, RPlan>:
  Bool.pick(Result<&2, &2, Main.Refused, RPlan>, List.is_empty(&2, Conflict, rplan.conflicts(p)), Done{p},
    Fail{Main.Refused{1, "the stores disagree about mutable files; receive writes nothing:\n" ++ refused.conflicts(rplan.conflicts(p))}})

# What was done: how many of each kind arrived, and the originals destroyed.
type Received is Data:
  Received{revisions: Nat, documents: Nat, payloads: Nat, names: Nat, rules: Nat, reserved: Nat, destroyed: Nat}

def said.received(r: Received) -> List<&2, String>:
  match r:
    case Received{+rs, +ds, +ps, +ns, +rules, +res, +des}:
      List.concat(&2, String, [
        [count.line("received", rs, "revisions"), count.line("received", ds, "content documents"), count.line("received", ps, "payloads")],
        count.if("received", ns, "bookmarks"),
        count.if("received", rules, "rules"),
        count.if("received", res, "files another tool wrote"),
        count.if("destroyed", des, "forgotten originals")])

def said.revisions(ds: List<&2, Store.Doc>) -> List<&2, String>:
  match ds:
    case Nil{}:
      Nil{}
    case d <> rest:
      ("revision " ++ Store.id_of(d)) <> said.revisions(rest)

def said.names(bs: List<&2, Bm.Bookmark>) -> List<&2, String>:
  match bs:
    case Nil{}:
      Nil{}
    case b <> rest:
      ("name " ++ Bm.name_of(b)) <> said.names(rest)

# Decision 0074's statement: each revision received, then each bookmark,
# as the Rust tool's ordered set spells them.
def said.fields(+p: RPlan) -> List<&2, String>:
  Main.WROTE() <> List.append(&2, String, said.revisions(rplan.revisions(p)), said.names(List.sort(~Bm.Bookmark, ~(a => b => String.is_le(Bm.name_of(a), Bm.name_of(b))), rplan.names(p))))

# Writing
# -------

# The rules this store will write, each under its label: its own where no
# file here has that name yet, its digest's where one does, and a rule
# once however often the source states it.
def rules.written(rs: List<&2, Ruled>, +existing: Set(), +done: List<&2, String>, +taken: List<&2, String>) -> List<&2, T.Split>:
  match rs:
    case Nil{}:
      Nil{}
    case Ruled{f, +line, +label} <> rest:
      +dup = Rev.member(done, line)
      +chosen = Bool.pick(String, Bool.or(Arrange.has(existing, label), Rev.member(taken, label)), rule.digest_label(line), label)
      Tree.keep(~T.Split, Bool.not(dup), T.Split{chosen, line}, rules.written(rest, existing, line <> done, Bool.pick(List<&2, String>, dup, taken, chosen <> taken)))

def rplan.rules(p: RPlan) -> List<&2, Ruled>:
  match p:
    case RPlan{rs, ds, ps, ns, rules, res, des, cs}:
      rules

def io.of(r: Result<&1, &1, U32 & String, String>) -> IO(String):
  Main.name.io(r)

def copied.payloads(+from: String, +to: String, ps: List<&2, T.Split>) -> IO(Unit):
  match ps:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case T.Split{+p, +d} <> rest:
      do IO<Unit>:
        w : Result<&1, &1, U32 & String, String> <- Store.copied(from ++ "/" ++ p ++ "\n" ++ to ++ "/operations/" ++ d ++ "\n" ++ d)
        x : String <- io.of(w)
        copied.payloads(from, to, rest)

# Each document under its digest, the bytes that were read and hashed here:
# a name the source gave it is never the name it is filed under.
def filed.docs(+to: String, +dir: String, +suffix: String, ds: List<&2, Store.Doc>) -> IO(Unit):
  match ds:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case Store.Doc{p, +id, n, +text} <> rest:
      do IO<Unit>:
        w : Result<&1, &1, U32 & String, String> <- Store.filed(to ++ "/" ++ dir ++ "/" ++ id ++ suffix ++ "\n" ++ text)
        x : String <- io.of(w)
        filed.docs(to, dir, suffix, rest)

def written.names(+to: String, bs: List<&2, Bm.Bookmark>) -> IO(Unit):
  match bs:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case Bm.Bookmark{+n, t, p} <> rest:
      do IO<Unit>:
        w : Result<&1, &1, U32 & String, String> <- Store.written(to ++ "/names/" ++ n ++ ".txt\n" ++ Bm.write(Bm.Stated{t, p}))
        x : String <- io.of(w)
        written.names(to, rest)

def written.rules(+to: String, ws: List<&2, T.Split>) -> IO(Unit):
  match ws:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case T.Split{+label, +line} <> rest:
      do IO<Unit>:
        w : Result<&1, &1, U32 & String, String> <- Store.filed(to ++ "/skipped/" ++ label ++ "\n" ++ line ++ "\n")
        x : String <- io.of(w)
        written.rules(to, rest)

def copied.claims(+from: String, +to: String, cs: List<&2, T.Split>) -> IO(Unit):
  match cs:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case T.Split{+label, +d} <> rest:
      do IO<Unit>:
        w : Result<&1, &1, U32 & String, String> <- Store.copied(from ++ "/" ++ label ++ "\n" ++ to ++ "/" ++ label ++ "\n" ++ d)
        x : String <- io.of(w)
        copied.claims(from, to, rest)

def body.split.of(b: Prune.Body) -> T.Split:
  Prune.body.split(b)

def kept.in(ss: List<&2, T.Split>, +gone: Set()) -> List<&2, T.Split>:
  match ss:
    case Nil{}:
      Nil{}
    case +s <> rest:
      Tree.keep(~T.Split, Arrange.has(gone, split.digest(s)), s, kept.in(rest, gone))

# The files here a forgetting document stands in for: every operation
# document holding a forgotten digest, and the file the store finds a
# forgotten payload at — the first the walk reaches.
def destroyed(+bs: List<&2, Prune.Body>, +ps: List<&2, T.Split>, +des: List<&2, String>) -> List<&2, String>:
  +gone = Set.from_list(des)
  Main.sorted_distinct(List.append(&2, String,
    T.map(~T.Split, ~String, ~(s => Prune.split.path(s)), kept.in(T.map(~Prune.Body, ~T.Split, ~(b => body.split.of(b)), bs), gone)),
    T.map(~T.Split, ~String, ~(s => Prune.split.path(s)), kept.in(splits.distinct(ps), gone))))

def stored.labels(+s: Prune.Stored) -> Set():
  Set.from_list(T.map(~T.Split, ~String, ~(x => skipped_file(Prune.split.path(x))), stored.rules(s)))

# What a receive that wrote its plan says it did.
def done.said(+fields: Bool, +p: RPlan, +written: Nat, +gone: Nat) -> List<&2, String>:
  match fields:
    case True{}:
      said.fields(p)
    case False{}:
      match p:
        case RPlan{+rs, +ds, +ps, +ns, rules, +res, des, cs}:
          said.received(Received{List.length(&2, Store.Doc, rs), List.length(&2, Store.Doc, ds), List.length(&2, T.Split, ps), List.length(&2, Bm.Bookmark, ns), written, List.length(&2, T.Split, res), gone})

# The plan carried out, content before the revisions that name it, as the
# Rust tool orders it, so that an interruption leaves less reachable
# rather than a revision naming bytes that never arrived.
def receive.write(+fields: Bool, +here: Side, +there: Side, +p: RPlan) -> IO(Unit):
  match p:
    case RPlan{+rs, +ds, +ps, +ns, +rules, +res, +des, cs}:
      +hr = side.root(here)
      +tr = side.root(there)
      +ws = rules.written(rules, stored.labels(stored.of(here)), Nil{}, Nil{})
      +gone = destroyed(stored.bodies(stored.of(here)), stored.payloads(stored.of(here)), des)
      do IO<Unit>:
        copied.payloads(tr, hr, ps)
        filed.docs(hr, "operations", ".ops.txt", ds)
        Prune.removed(hr, gone)
        sw : Result<&1, &1, U32 & String, String> <- Store.swept(hr ++ "/operations")
        filed.docs(hr, "revisions", ".rev.txt", rs)
        written.names(hr, ns)
        written.rules(hr, ws)
        copied.claims(tr, hr, res)
        Arrange.print_lines(done.said(fields, RPlan{rs, ds, ps, ns, rules, res, des, cs}, List.length(&2, T.Split, ws), List.length(&2, String, gone)))

def planned.io(+dry: Bool, +fields: Bool, +here: Side, +there: Side, +p: RPlan) -> IO(Unit):
  match dry:
    case True{}:
      do IO<Unit>:
        Arrange.print_lines(said.plan(p))
        Bool.pick(IO(Unit), List.is_empty(&2, Conflict, rplan.conflicts(p)), IO.pure(Unit, Unit{}), Store.ended(1n))
    case False{}:
      do IO<Unit>:
        agreed : RPlan <- Main.stated.io(RPlan, fields, agreed.r(p))
        receive.write(fields, here, there, agreed)

# Reading
# -------

# One side, as it is opened: a revision that does not parse refuses it, as
# the Rust tool's store refuses to open, and so does a bookmark or a rule
# file that is not one; then the files of `claims/`, by digest.
def side.read(+fields: Bool, +r: String) -> IO(Side):
  do IO<Side>:
    st : Prune.Stored <- Prune.read(r)
    +st2 : Prune.Stored = st
    Main.stated.io(Unit, fields, Arrange.opened.r(List.sort(~Store.Doc, ~(a => b => Arrange.doc_le(a, b)), stored.docs(st2))))
    bs : List<&2, Bm.Bookmark> <- Main.bookmarks(r)
    listed : List<&2, String> <- Store.claims_paths(r)
    +cl : List<&2, String> = Prune.not_platform(listed)
    stats : List<&2, String> <- Store.stats(r, cl)
    return Side{r, st2, bs, Arrange.zip.stats(cl, stats)}

# `named`: the directory given, or the store below it, as the Rust tool
# reads a source — a directory with a `historica.txt` in it, or one called
# `history`, is a store, and anything else has one below it.
def named.of(+given: String, header: Result<&1, &1, U32 & String, String>) -> String:
  match header:
    case Done{x}:
      given
    case Fail{e}:
      Bool.pick(String, String.eq(Naming.last(given), "history"), given, given ++ "/history")

def opened.header(+root: String, header: Result<&1, &1, U32 & String, String>) -> Result<&2, &2, Main.Refused, Unit>:
  match header:
    case Done{x}:
      Done{Unit{}}
    case Fail{e}:
      Fail{Main.Refused{1, root ++ " is not a store: no `historica.txt` file; `init` makes one"}}

def source.root(+fields: Bool, +source: String) -> IO(String):
  do IO<String>:
    here : Result<&1, &1, U32 & String, String> <- Store.really(SNil{})
    base : String <- Main.init.io(String, here)
    +given : String = Main.path_join(base, source)
    header : Result<&1, &1, U32 & String, String> <- Store.really(given ++ "/historica.txt")
    +root : String = named.of(given, header)
    again : Result<&1, &1, U32 & String, String> <- Store.really(root ++ "/historica.txt")
    Main.stated.io(Unit, fields, opened.header(root, again))
    return root

# The whole of `check`, asked of each side as the Rust tool's
# `receive_plan` asks it — this store, then the source — before anything is
# planned. `plan.r` holds each side to the part of it the laws read too.
def checked.r(ok: Bool, +side: String) -> Result<&2, &2, Main.Refused, Unit>:
  Bool.pick(Result<&2, &2, Main.Refused, Unit>, ok, Done{Unit{}},
    Fail{Main.Refused{1, "the " ++ side ++ " store does not pass `check`; receive writes nothing until its errors are repaired"}})

def receive.of(c: ReceiveCmd) -> IO(Unit):
  match c:
    case ReceiveCmd{+dry, +fields, +join, +source}:
      do IO<Unit>:
        found : Result<&1, &1, U32 & String, String> <- Store.root.found()
        root : String <- Prune.root.stated(fields, found)
        +root2 : String = root
        here : Side <- side.read(fields, root2)
        +here2 : Side = here
        sroot : String <- source.root(fields, source)
        +sroot2 : String = sroot
        there : Side <- side.read(fields, sroot2)
        +there2 : Side = there
        hok : Bool <- Check.passes(root2)
        Main.stated.io(Unit, fields, checked.r(hok, "receiving"))
        tok : Bool <- Check.passes(sroot2)
        Main.stated.io(Unit, fields, checked.r(tok, "source"))
        p : RPlan <- Main.stated.io(RPlan, fields, plan.r(here2, there2, join))
        planned.io(dry, fields, here2, there2, p)

def receive(+args: List<&2, String>) -> IO(Unit):
  do IO<Unit>:
    c : ReceiveCmd <- Main.refused.io(ReceiveCmd, args.r(args))
    receive.of(c)
