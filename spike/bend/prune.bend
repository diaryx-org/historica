# `prune [--dry-run] [--fields]`: the disk half of decision 0013.
#
# Abandoning is a fact recorded in the graph; pruning is disk. Exactly two
# kinds of file may go: a revision document superseded by a revision the
# store keeps and named as a parent by nothing it keeps, and a file of
# content nothing kept names. What may go is found to a fixed point, in the
# Rust tool's order — a revision at a time, by digest, each asked against
# what is kept at that moment — since removing one can free the next. A
# forgetting document stays while what it stands in for is named. Files
# are found by what they hold, never by name: two copies of one pruned
# revision are both that revision.
#
# Deletion is the one act that must not be aimed by files that cannot be
# trusted, so a store `check` calls broken is refused before the store is
# opened: the whole of `check` (`Check.passes`), as the Rust tool's `prune`
# asks it. `sound` below is the part of it the laws read — every document
# parses, no name claims a digest its bytes do not have, every bookmark and
# rule file says what its grammar allows, and every head's tree
# materialises — which `receive` also holds each side to as it plans.

import Base
import ./text.bend as T
import ./revision.bend as Rev
import ./store.bend as Store
import ./tree.bend as Tree
import ./ops.bend as Ops
import ./resolution.bend as Res
import ./naming.bend as Naming
import ./bookmark.bend as Bm
import ./folder.bend as Folder
import ./commands.bend as Main
import ./arrange.bend as Arrange
import ./standin.bend as Stand
import ./check.bend as Check

# The words
# ---------

type PruneCmd is Data:
  PruneCmd{dry: Bool, fields: Bool}

def is_dry(+w: String) -> Bool:
  Bool.or(String.eq(w, "-n"), String.eq(w, "--dry-run"))

def is_fields(+w: String) -> Bool:
  String.eq(w, "--fields")

def is_flag(+w: String) -> Bool:
  Bool.or(is_dry(w), is_fields(w))

def any_dry(ws: List<&2, String>) -> Bool:
  match ws:
    case Nil{}:
      False{}
    case +w <> rest:
      Bool.or(is_dry(w), any_dry(rest))

def any_fields(ws: List<&2, String>) -> Bool:
  match ws:
    case Nil{}:
      False{}
    case +w <> rest:
      Bool.or(is_fields(w), any_fields(rest))

def first_other(ws: List<&2, String>) -> Maybe<&2, String>:
  match ws:
    case Nil{}:
      None{}
    case +w <> rest:
      Bool.pick(Maybe<&2, String>, is_flag(w), first_other(rest), Some{w})

# A plan is not on disk, so `--fields`, which states what is, has nothing to
# say of one.
def args.planned(+dry: Bool, +fields: Bool) -> Result<&2, &2, Main.Refused, PruneCmd>:
  Bool.pick(Result<&2, &2, Main.Refused, PruneCmd>, Bool.and(dry, fields),
    Fail{Main.Refused{2, "`prune --dry-run --fields` is refused: `--fields` states what is on disk, and a plan is not on disk. ask for one or the other"}},
    Done{PruneCmd{dry, fields}})

def args.of(+dry: Bool, +fields: Bool, extra: Maybe<&2, String>) -> Result<&2, &2, Main.Refused, PruneCmd>:
  match extra:
    case Some{x}:
      Fail{Main.Refused{2, "`" ++ x ++ "` is not an argument `prune` takes"}}
    case None{}:
      args.planned(dry, fields)

# Every flag wherever it stands; the first other word refused.
def args.r(+ws: List<&2, String>) -> Result<&2, &2, Main.Refused, PruneCmd>:
  args.of(any_dry(ws), any_fields(ws), first_other(ws))

# The store as the check reads it
# -------------------------------

# One file of `operations/` that claims to be a document: where it is, its
# digest, whether it parses in the grammar its body says it is written in,
# and what it forgets.
type Body is Data:
  Body{path: String, id: String, parsed: Bool, forgets: Maybe<&2, String>}

def ops.forgets(r: Result<&2, &2, String, Ops.Doc>) -> Maybe<&2, String>:
  match r:
    case Done{Ops.Doc{forgets, result, ops}}:
      forgets
    case Fail{e}:
      None{}

def res.forgets(r: Result<&2, &2, String, Res.Doc>) -> Maybe<&2, String>:
  match r:
    case Done{Res.Doc{forgets, result, pieces}}:
      forgets
    case Fail{e}:
      None{}

def ops.parsed(r: Result<&2, &2, String, Ops.Doc>) -> Bool:
  match r:
    case Done{d}:
      True{}
    case Fail{e}:
      False{}

def res.parsed(r: Result<&2, &2, String, Res.Doc>) -> Bool:
  match r:
    case Done{d}:
      True{}
    case Fail{e}:
      False{}

# Decision 0032: two grammars share the suffix, and the body says which.
def body.of.two(+path: String, +id: String, +text: String, resolution: Bool) -> Body:
  match resolution:
    case True{}:
      Body{path, id, res.parsed(Res.parse(text)), res.forgets(Res.parse(text))}
    case False{}:
      Body{path, id, ops.parsed(Ops.parse(text)), ops.forgets(Ops.parse(text))}

# Decision 0066 adds a third: what stands in for a payload of bytes, told
# apart by the `length` header no other document carries — a header line,
# before the first empty line, after the preamble — and asked about first,
# as the Rust tool asks.
def headers.length(ls: List<&2, T.Line>) -> Bool:
  match ls:
    case Nil{}:
      False{}
    case T.Line{+t, n} <> rest:
      Bool.pick(Bool, String.is_empty(t), False{}, Bool.or(String.starts_with(t, "length "), headers.length(rest)))

def forgotten.payload(ls: List<&2, T.Line>) -> Bool:
  match ls:
    case Nil{}:
      False{}
    case T.Line{+p, n} <> rest:
      Bool.and(T.same(p, "historica"), headers.length(rest))

def body.of(+path: String, +id: String, +text: String, forgotten: Bool) -> Body:
  match forgotten:
    case True{}:
      Body{path, id, Maybe.is_some(&2, Stand.Payload, Stand.payload.parse(text)), Stand.payload.forgets(Stand.payload.parse(text))}
    case False{}:
      body.of.two(path, id, text, Res.is_resolution(text))

def bodies(+root: String, ds: List<&2, Store.Doc>) -> List<&2, Body>:
  match ds:
    case Nil{}:
      Nil{}
    case Store.Doc{+path, +id, size, +text} <> rest:
      body.of(Store.relative(root, path), id, text, forgotten.payload(T.lines(text))) <> bodies(root, rest)

def body.path(b: Body) -> String:
  match b:
    case Body{path, id, p, f}:
      path

def body.id(b: Body) -> String:
  match b:
    case Body{path, id, p, f}:
      id

def body_le(+a: Body, +b: Body) -> Bool:
  Arrange.walk_le(body.path(a), body.path(b))

def unrevision(+s: String) -> String:
  Bool.pick(String, String.ends_with(s, ".rev.txt"), String.take(s, Nat.sub(String.length(s), 8n)), s)

# What a file's name claims it holds: the digest its name spells, where it
# spells one, less a document's suffix.
def claimed(+path: String) -> Maybe<&2, String>:
  +name = Naming.last(path)
  +stem = Naming.unsuffixed(unrevision(name))
  Bool.pick(Maybe<&2, String>, T.is_digest(stem), Some{stem}, None{})

def lies.of(+id: String, claim: Maybe<&2, String>) -> Bool:
  match claim:
    case None{}:
      False{}
    case Some{c}:
      Bool.not(String.eq(c, id))

# Whether a file's name claims a digest its bytes do not have.
def lies(+path: String, +id: String) -> Bool:
  lies.of(id, claimed(path))

def platform(+path: String) -> Bool:
  Naming.platform_name(Naming.last(path))

def revs.sound(ds: List<&2, T.Split>) -> Bool:
  match ds:
    case Nil{}:
      True{}
    case T.Split{+path, +id} <> rest:
      Bool.and(Bool.or(platform(path), Bool.not(lies(path, id))), revs.sound(rest))

def bodies.sound(bs: List<&2, Body>) -> Bool:
  match bs:
    case Nil{}:
      True{}
    case Body{+path, +id, parsed, f} <> rest:
      Bool.and(Bool.and(parsed, Bool.not(lies(path, id))), bodies.sound(rest))

def bm.parsed(r: Result<&2, &2, String, Bm.Stated>) -> Bool:
  match r:
    case Done{d}:
      True{}
    case Fail{e}:
      False{}

def texts.bookmarks(ts: List<&2, String>) -> Bool:
  match ts:
    case Nil{}:
      True{}
    case t <> rest:
      Bool.and(bm.parsed(Bm.parse(t)), texts.bookmarks(rest))

def stated.ok(s: Folder.Stated) -> Bool:
  match s:
    case Folder.Stated.Wrong{e}:
      False{}
    case _:
      True{}

def texts.rules(ts: List<&2, T.Split>) -> Bool:
  match ts:
    case Nil{}:
      True{}
    case T.Split{p, t} <> rest:
      Bool.and(stated.ok(Folder.rule_in(t)), texts.rules(rest))

def tree.ok(r: Result<&2, &2, Main.Refused, Tree.Tree()>) -> Bool:
  match r:
    case Done{t}:
      True{}
    case Fail{e}:
      False{}

def heads.sound(hs: List<&2, String>, +fs: List<&2, Main.Full>) -> Bool:
  match hs:
    case Nil{}:
      True{}
    case +h <> rest:
      Bool.and(tree.ok(Main.tree.r(fs, h)), heads.sound(rest, fs))

# The revisions among documents read from `revisions/`: those that parse.
def fulls(ds: List<&2, Store.Doc>) -> List<&2, Main.Full>:
  match ds:
    case Nil{}:
      Nil{}
    case Store.Doc{path, +id, size, +text} <> rest:
      Main.push_full(Main.full(id, Rev.parse(text)), fulls(rest))

# What a store is read as, for the part of `check` a writer that destroys or
# copies asks first: every revision document, and each file of content with
# its digest, in the walk's order; and the text of every bookmark file and
# every rule file.
type Stored is Data:
  Stored{docs: List<&2, Store.Doc>, revs: List<&2, T.Split>, odocs: List<&2, Store.Doc>, bodies: List<&2, Body>, payloads: List<&2, T.Split>, names: List<&2, String>, rules: List<&2, T.Split>}

# Whether the Rust tool's `check` would pass this store, as far as the port
# reads it: every revision and every document parses, no file's name lies
# about its digest, every bookmark and rule file is one, and every head has
# a tree.
def sound(s: Stored) -> Bool:
  match s:
    case Stored{+docs, +revs, od, +bs, +ps, +names, +rules}:
      +fs = Arrange.distinct(fulls(Arrange.revision_docs(docs)))
      Bool.and(Bool.and(Bool.and(Arrange.all_parse(Arrange.revision_docs(docs)), revs.sound(revs)), Bool.and(bodies.sound(bs), revs.sound(ps))),
        Bool.and(Bool.and(texts.bookmarks(names), texts.rules(rules)), heads.sound(Rev.heads(Main.history(fs)), fs)))

# What may go
# -----------

def supersedes_of(f: Main.Full) -> List<&2, String>:
  match f:
    case Main.Full{id, change, parents, supersedes, author, when, revised_by, revised, facts, message}:
      supersedes

# Whether a revision kept names this one as a parent: work that still
# stands on it.
def stood_on(kept: List<&2, Main.Full>, +id: String) -> Bool:
  match kept:
    case Nil{}:
      False{}
    case +k <> rest:
      Bool.or(Rev.member(Main.parents_of(k), id), stood_on(rest, id))

# Whether a revision kept says it supersedes this one.
def superseded(kept: List<&2, Main.Full>, +id: String) -> Bool:
  match kept:
    case Nil{}:
      False{}
    case +k <> rest:
      Bool.or(Rev.member(supersedes_of(k), id), superseded(rest, id))

# Whether a revision is the evidence that something kept was superseded:
# decision 0001 puts that on the successor, and deleting it would bring
# the kept revision back as current work.
def evidence(ss: List<&2, String>, +kept: List<&2, String>) -> Bool:
  match ss:
    case Nil{}:
      False{}
    case +s <> rest:
      Bool.or(Rev.member(kept, s), evidence(rest, kept))

# Whether one revision may go, asked against what is kept now.
def goes(+kept: List<&2, Main.Full>, +f: Main.Full) -> Bool:
  Bool.and(superseded(kept, Main.id_of(f)), Bool.and(Bool.not(stood_on(kept, Main.id_of(f))), Bool.not(evidence(supersedes_of(f), Main.ids(kept)))))

# What is kept, less one revision.
def without(kept: List<&2, Main.Full>, +id: String) -> List<&2, Main.Full>:
  match kept:
    case Nil{}:
      Nil{}
    case +k <> rest:
      Main.keep_full(Bool.not(String.eq(Main.id_of(k), id)), k, without(rest, id))

def drop.if(b: Bool, kept: List<&2, Main.Full>, +id: String) -> List<&2, Main.Full>:
  match b:
    case True{}:
      without(kept, id)
    case False{}:
      kept

# One pass: each revision of what was kept at its start, in digest order,
# asked against what is kept at its own turn — so a revision let go early
# in a pass counts for none after it, as in the Rust tool's loop.
def pass(snap: List<&2, Main.Full>, +kept: List<&2, Main.Full>) -> List<&2, Main.Full>:
  match snap:
    case Nil{}:
      kept
    case +f <> rest:
      pass(rest, drop.if(goes(kept, f), kept, Main.id_of(f)))

# What a pass left, and whether it let anything go.
type Passed is Data:
  Passed{kept: List<&2, Main.Full>, shrank: Bool}

def passed(+before: List<&2, Main.Full>, +after: List<&2, Main.Full>) -> Passed:
  Passed{after, Nat.is_lt(List.length(&2, Main.Full, after), List.length(&2, Main.Full, before))}

def passed.kept(p: Passed) -> List<&2, Main.Full>:
  match p:
    case Passed{kept, s}:
      kept

# Passes until one lets nothing go: a superseded run clears in one pruning.
# Each pass that shrinks lets one revision go at least, so a revision more
# than the store holds is fuel enough.
def fix(fuel: Nat, p: Passed) -> List<&2, Main.Full>:
  match fuel:
    case 0n:
      passed.kept(p)
    case 1n+more:
      match p:
        case Passed{+kept, shrank}:
          match shrank:
            case False{}:
              kept
            case True{}:
              fix(more, passed(kept, pass(kept, kept)))

# What pruning keeps of the revisions, each once and in digest order.
def kept(+fs: List<&2, Main.Full>) -> List<&2, Main.Full>:
  fix(List.length(&2, Main.Full, fs), passed(fs, pass(fs, fs)))

def fact_digests(fs: List<&2, Tree.Fact>) -> List<&2, String>:
  match fs:
    case Nil{}:
      Nil{}
    case Tree.Fact{f, d} <> rest:
      d <> fact_digests(rest)

# Every digest one revision names content by.
def named_by(f: Main.Full) -> List<&2, String>:
  match f:
    case Main.Full{id, change, parents, supersedes, author, when, revised_by, revised, +facts, message}:
      List.append(&2, String, fact_digests(Tree.facts_of(facts, "edit")), List.append(&2, String, fact_digests(Tree.facts_of(facts, "text")), fact_digests(Tree.facts_of(facts, "bytes"))))

def named_all(fs: List<&2, Main.Full>) -> List<&2, String>:
  match fs:
    case Nil{}:
      Nil{}
    case f <> rest:
      List.append(&2, String, named_by(f), named_all(rest))

def forgetting.of(+id: String, +named: Set(), forgets: Maybe<&2, String>, rest: List<&2, String>) -> List<&2, String>:
  match forgets:
    case None{}:
      rest
    case Some{+t}:
      Rev.keep(Arrange.has(named, t), id, rest)

# The forgetting documents standing in for something still named, which
# stay with it (decision 0014): a revision's line still names what was
# destroyed, and the forgetting document is what answers for it.
def forgetting(bs: List<&2, Body>, +named: Set()) -> List<&2, String>:
  match bs:
    case Nil{}:
      Nil{}
    case Body{p, +id, parsed, forgets} <> rest:
      forgetting.of(id, named, forgets, forgetting(rest, named))

# Every digest of content what is kept still needs.
def referenced(+kept: List<&2, Main.Full>, +bs: List<&2, Body>) -> Set():
  +named = named_all(kept)
  Set.from_list(List.append(&2, String, named, forgetting(bs, Set.from_list(named))))

def gone.of(ds: List<&2, T.Split>, +keep: Set()) -> List<&2, T.Split>:
  match ds:
    case Nil{}:
      Nil{}
    case T.Split{+path, +id} <> rest:
      Tree.keep(~T.Split, Bool.not(Arrange.has(keep, id)), T.Split{path, id}, gone.of(rest, keep))

def gone.revs(ds: List<&2, T.Split>, +dead: Set()) -> List<&2, T.Split>:
  match ds:
    case Nil{}:
      Nil{}
    case T.Split{+path, +id} <> rest:
      Tree.keep(~T.Split, Arrange.has(dead, id), T.Split{path, id}, gone.revs(rest, dead))

def body.split(b: Body) -> T.Split:
  match b:
    case Body{path, id, p, f}:
      T.Split{path, id}

def unique.go(ds: List<&2, T.Split>, +seen: List<&2, String>) -> List<&2, String>:
  match ds:
    case Nil{}:
      Nil{}
    case T.Split{p, +id} <> rest:
      Rev.keep(Bool.not(Rev.member(seen, id)), id, unique.go(rest, id <> seen))

# Each digest once, in the order its first file came.
def unique(ds: List<&2, T.Split>) -> List<&2, String>:
  unique.go(ds, Nil{})

# Whether none of these digests is one the store still needs.
def unneeded(ds: List<&2, String>, +refs: Set()) -> Bool:
  match ds:
    case Nil{}:
      True{}
    case +d <> rest:
      Bool.and(Bool.not(Arrange.has(refs, d)), unneeded(rest, refs))

def split.path(s: T.Split) -> String:
  match s:
    case T.Split{p, d}:
      p

# What pruning removes: the digests of each kind, and every file, in the
# order they go — revisions, then documents, then payloads.
type Pruned is Data:
  Pruned{revisions: List<&2, String>, operations: List<&2, String>, payloads: List<&2, String>, files: List<&2, String>}

def pruned.content(p: Pruned) -> List<&2, String>:
  match p:
    case Pruned{r, o, y, f}:
      List.append(&2, String, o, y)

def pruned.of(+r: List<&2, T.Split>, +o: List<&2, T.Split>, +p: List<&2, T.Split>) -> Pruned:
  Pruned{unique(r), unique(o), unique(p), T.map(~T.Split, ~String, ~(s => split.path(s)), List.append(&2, T.Split, r, List.append(&2, T.Split, o, p)))}

# `Store::prunable`, over the revisions and each directory's files in the
# walk's order: what is let go of, what is still needed, and the files
# holding the rest.
def plan(+fs: List<&2, Main.Full>, +revs: List<&2, T.Split>, +bs: List<&2, Body>, +ps: List<&2, T.Split>) -> Pruned:
  +k = kept(fs)
  +refs = referenced(k, bs)
  pruned.of(gone.revs(revs, Set.from_list(Rev.without(Main.ids(fs), Main.ids(k)))), gone.of(T.map(~Body, ~T.Split, ~(b => body.split(b)), bs), refs), gone.of(ps, refs))

# Reading
# -------

def named.path(n: Main.Named) -> String:
  match n:
    case Main.Named{name, path}:
      path

def read_splits(+r: String, ps: List<&2, String>) -> IO(List<&2, T.Split>):
  match ps:
    case Nil{}:
      IO.pure(List<&2, T.Split>, Nil{})
    case +p <> rest:
      do IO<List<&2, T.Split>>:
        t : String <- Store.read_text(r ++ "/" ++ p)
        ts : List<&2, T.Split> <- read_splits(r, rest)
        return T.Split{p, t} <> ts

def read_texts(+r: String, ps: List<&2, String>) -> IO(List<&2, String>):
  match ps:
    case Nil{}:
      IO.pure(List<&2, String>, Nil{})
    case p <> rest:
      do IO<List<&2, String>>:
        t : String <- Store.read_text(r ++ "/" ++ p)
        ts : List<&2, String> <- read_texts(r, rest)
        return t <> ts

def not_platform(ps: List<&2, String>) -> List<&2, String>:
  match ps:
    case Nil{}:
      Nil{}
    case +p <> rest:
      Rev.keep(Bool.not(platform(p)), p, not_platform(rest))

def splits.walked(+ss: List<&2, T.Split>) -> List<&2, T.Split>:
  List.sort(~T.Split, ~(a => b => Arrange.split_le(a, b)), ss)

# A store as a writer that destroys or copies reads it: every revision
# document, read and hashed here; every operation document the same; each
# payload's digest from the host, the platform's own files passed over as
# the Rust tool passes them; and the bookmark and rule files as text.
def read(+r: String) -> IO(Stored):
  do IO<Stored>:
    rs : List<&2, Store.Doc> <- Store.revisions(r)
    +rs2 : List<&2, Store.Doc> = rs
    ls : List<&2, String> <- Store.listing(r)
    +ls2 : List<&2, String> = ls
    ods : List<&2, Store.Doc> <- Store.read_docs(Store.under(r, not_platform(Arrange.in_operations(ls2, True{}))))
    +pay : List<&2, String> = not_platform(Arrange.in_operations(ls2, False{}))
    stats : List<&2, String> <- Store.stats(r, pay)
    nps : List<&2, String> <- Store.name_paths(r)
    names : List<&2, String> <- read_texts(r, T.map(~Main.Named, ~String, ~(n => named.path(n)), Main.named(nps)))
    sps : List<&2, String> <- Store.skipped_paths(r)
    rules : List<&2, T.Split> <- read_splits(r, Arrange.walked(Folder.rules.kept(sps)))
    +ods2 : List<&2, Store.Doc> = ods
    return Stored{rs2, splits.walked(Arrange.rev.digests(r, rs2)), ods2, List.sort(~Body, ~(a => b => body_le(a, b)), bodies(r, ods2)), splits.walked(Arrange.zip.stats(pay, stats)), names, rules}

def stored.plan(s: Stored) -> Pruned:
  match s:
    case Stored{docs, +revs, od, +bs, +ps, names, rules}:
      plan(Arrange.distinct(fulls(Arrange.revision_docs(docs))), revs, bs, ps)

# The refusal a store `check` calls broken gets: asked of the whole of
# `check`, before the store is opened, as the Rust tool's `prune` asks it.
def sound.r(ok: Bool) -> Result<&2, &2, Main.Refused, Unit>:
  Bool.pick(Result<&2, &2, Main.Refused, Unit>, ok, Done{Unit{}},
    Fail{Main.Refused{1, "this store does not pass `check`, and prune deletes nothing from a store it cannot trust; `historica check` says what is wrong"}})

# The report
# ----------

def pruned.all(p: Pruned) -> List<&2, String>:
  match p:
    case Pruned{r, o, y, f}:
      List.append(&2, String, r, List.append(&2, String, o, y))

def pruned.files(p: Pruned) -> List<&2, String>:
  match p:
    case Pruned{r, o, y, f}:
      f

def said.files(fs: List<&2, String>, +verb: String) -> List<&2, String>:
  match fs:
    case Nil{}:
      Nil{}
    case f <> rest:
      (verb ++ " history/" ++ f) <> said.files(rest, verb)

def said.gone(ds: List<&2, String>) -> List<&2, String>:
  match ds:
    case Nil{}:
      Nil{}
    case d <> rest:
      ("gone " ++ d) <> said.gone(rest)

def said.listed(fs: List<&2, String>, +verb: String) -> List<&2, String>:
  match fs:
    case Nil{}:
      ["nothing here is prunable: nothing superseded is unreferenced"]
    case +some:
      said.files(some, verb)

# What `prune` prints: each file, as it goes or would; or, with `--fields`,
# decision 0074's statement — each digest nothing is there under any more,
# once, in order.
def said(+dry: Bool, +fields: Bool, +p: Pruned) -> List<&2, String>:
  match fields:
    case True{}:
      Main.WROTE() <> said.gone(Main.sorted_distinct(pruned.all(p)))
    case False{}:
      said.listed(pruned.files(p), Bool.pick(String, dry, "would remove", "removed"))

# Removing
# --------

def removed(+r: String, fs: List<&2, String>) -> IO(Unit):
  match fs:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case +f <> rest:
      do IO<Unit>:
        w : Result<&1, &1, U32 & String, String> <- Store.removed(r ++ "/" ++ Arrange.parent_of(f) ++ "\n" ++ r ++ "/" ++ f)
        done : String <- Main.name.io(w)
        removed(r, rest)

# The name a `Store.folder` line gives a file: after `f`, the execute bit
# and the length.
def entry_name(+line: String) -> String:
  String.join(List.drop(&2, String, String.split(line, ' '), 3n), " ")

# The files of `cache/` named by a digest: what any reader rebuilds, and
# what may hold content pruning has just destroyed. Anything else there —
# the note `init` writes — is somebody's.
def cached(ls: List<&2, String>) -> List<&2, String>:
  match ls:
    case Nil{}:
      Nil{}
    case +l <> rest:
      Rev.keep(Bool.and(String.starts_with(l, "f "), T.is_digest(entry_name(l))), entry_name(l), cached(rest))

def cleared.of(+r: String, listed: Result<&1, &1, U32 & String, String>) -> IO(Unit):
  match listed:
    case Fail{e}:
      IO.pure(Unit, Unit{})
    case Done{text}:
      removed(r, T.map(~String, ~String, ~(n => "cache/" ++ n), cached(String.lines(text))))

# `cache/` cleared of what it derived, quietly: nothing there is lost.
def cleared(+r: String) -> IO(Unit):
  do IO<Unit>:
    listed : Result<&1, &1, U32 & String, String> <- Store.listing_of(r ++ "/cache")
    cleared.of(r, listed)

def swept(+r: String) -> IO(Unit):
  do IO<Unit>:
    a : Result<&1, &1, U32 & String, String> <- Store.swept(r ++ "/revisions")
    b : Result<&1, &1, U32 & String, String> <- Store.swept(r ++ "/operations")
    IO.pure(Unit, Unit{})

def print_lines(ls: List<&2, String>) -> IO(Unit):
  Arrange.print_lines(ls)

def prune.act(dry: Bool, +fields: Bool, +r: String, +p: Pruned) -> IO(Unit):
  match dry:
    case True{}:
      print_lines(said(True{}, fields, p))
    case False{}:
      do IO<Unit>:
        removed(r, pruned.files(p))
        cleared(r)
        swept(r)
        print_lines(said(False{}, fields, p))

# No store to open: `--fields`'s header goes out before the refusal, as the
# Rust tool's `prune` and `receive` owe it (its `record` does not).
def root.stated(+st: Bool, r: Result<&1, &1, U32 & String, String>) -> IO(String):
  match r:
    case Fail{Tuple{code, msg}}:
      Main.stated.io(String, st, Fail{Main.Refused{1, msg}})
    case Done{found}:
      IO.pure(String, found)

def prune.of(c: PruneCmd) -> IO(Unit):
  match c:
    case PruneCmd{+dry, +fields}:
      do IO<Unit>:
        found : Result<&1, &1, U32 & String, String> <- Store.root.found()
        root : String <- root.stated(fields, found)
        +r : String = root
        ok : Bool <- Check.passes(r)
        Main.stated.io(Unit, fields, sound.r(ok))
        s : Stored <- read(r)
        +s2 : Stored = s
        prune.act(dry, fields, r, stored.plan(s2))

def prune(+args: List<&2, String>) -> IO(Unit):
  do IO<Unit>:
    c : PruneCmd <- Main.refused.io(PruneCmd, args.r(args))
    prune.of(c)
