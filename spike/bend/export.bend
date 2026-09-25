# `export <dir> [<target>] [--files-only] [-n|--dry-run]`: the copy a
# person takes away.
#
# Decision 0042. There is no directory on disk whose bytes are what a
# stranger should have — the folder holds unrecorded edits and every file a
# `skip` rule keeps private — so the copy is assembled rather than mirrored:
# a fresh repository at `<dir>`, holding the folder as the target has it and
# the target's own ancestry, closed over parent edges. Every document and
# payload those revisions name travels, followed through a resolution's
# `keep` lines, and every forgetting document standing in for any of it
# (decision 0014). Every shared rule travels (0051), every shared bookmark
# whose target the copy holds (0062), and the files of `claims/`, whole and
# unread (0053). A private rule or bookmark stays behind, and so does a
# bookmark pointing past the target, each counted apart.
#
# `--files-only` is the same folder with no store beside it, laid out into
# a directory that holds nothing.
#
# The copy's files are named as `arrange` names them, over what travels. The
# folder is laid out path by path — a file of lines replayed here, a file of
# bytes copied by the host, a link made where it sits, a runnable file made
# runnable — and a tree the folder cannot take whole is refused, path by
# path. An export onto a copy this store already made (decision 0052) is not
# ported: the port writes into an empty directory, or none.

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
import ./check.bend as Check
import ./folder.bend as Folder
import ./tree.bend as Tree
import ./resolution.bend as Res
import ./notes.bend as Notes
import ./ops.bend as Ops
import ./sha256.bend as Sha
import ./utf8.bend as Utf8
import ./update.bend as Upd

# The words
# ---------

type ExportCmd is Data:
  ExportCmd{dry: Bool, files: Bool, dir: String, target: Maybe<&2, String>}

def is_dry(+w: String) -> Bool:
  Bool.or(String.eq(w, "-n"), String.eq(w, "--dry-run"))

def is_files(+w: String) -> Bool:
  String.eq(w, "--files-only")

def is_flag(+w: String) -> Bool:
  Bool.or(is_dry(w), is_files(w))

# The first word starting `-` that is no flag `export` takes: refused where
# it stands, before the count of the rest is asked.
def stray(ws: List<&2, String>) -> Maybe<&2, String>:
  match ws:
    case Nil{}:
      None{}
    case +w <> rest:
      Bool.pick(Maybe<&2, String>, Bool.and(String.starts_with(w, "-"), Bool.not(is_flag(w))), Some{w}, stray(rest))

def any_dry(ws: List<&2, String>) -> Bool:
  match ws:
    case Nil{}:
      False{}
    case +w <> rest:
      Bool.or(is_dry(w), any_dry(rest))

def any_files(ws: List<&2, String>) -> Bool:
  match ws:
    case Nil{}:
      False{}
    case +w <> rest:
      Bool.or(is_files(w), any_files(rest))

def plain(ws: List<&2, String>) -> List<&2, String>:
  match ws:
    case Nil{}:
      Nil{}
    case +w <> rest:
      Tree.keep(~String, Bool.not(String.starts_with(w, "-")), w, plain(rest))

def args.words(+dry: Bool, +files: Bool, ws: List<&2, String>) -> Result<&2, &2, Main.Refused, ExportCmd>:
  match ws:
    case Nil{}:
      Fail{Main.Refused{2, "`export` wants a directory to write the copy into"}}
    case d <> Nil{}:
      Done{ExportCmd{dry, files, d, None{}}}
    case d <> t <> Nil{}:
      Done{ExportCmd{dry, files, d, Some{t}}}
    case d <> t <> extra <> more:
      Fail{Main.Refused{2, "`export` takes a directory and one target, and `" ++ extra ++ "` is a third argument"}}

def args.of(+ws: List<&2, String>, s: Maybe<&2, String>) -> Result<&2, &2, Main.Refused, ExportCmd>:
  match s:
    case Some{w}:
      Fail{Main.Refused{2, "`" ++ w ++ "` is not an argument `export` takes"}}
    case None{}:
      args.words(any_dry(ws), any_files(ws), plain(ws))

def args.r(+ws: List<&2, String>) -> Result<&2, &2, Main.Refused, ExportCmd>:
  args.of(ws, stray(ws))

# What a command `export` read says, written back as words: whether to plan
# only, whether to write the files alone, and the directory followed by the
# target, if one was given.
type Said is Data:
  Said{dry: Bool, files: Bool, words: List<&2, String>}

def said.target(t: Maybe<&2, String>) -> List<&2, String>:
  match t:
    case None{}:
      Nil{}
    case Some{x}:
      [x]

def args.read(r: Result<&2, &2, Main.Refused, ExportCmd>) -> Maybe<&2, Said>:
  match r:
    case Fail{e}:
      None{}
    case Done{ExportCmd{dry, files, dir, target}}:
      Some{Said{dry, files, dir <> said.target(target)}}

# What travels
# ------------

# Every digest these revisions name for content: what `edit`, `text` and
# `bytes` say.
def fact.rests(fs: List<&2, Tree.Fact>) -> List<&2, String>:
  match fs:
    case Nil{}:
      Nil{}
    case Tree.Fact{f, r} <> rest:
      r <> fact.rests(rest)

def fact.files(fs: List<&2, Tree.Fact>) -> List<&2, String>:
  match fs:
    case Nil{}:
      Nil{}
    case Tree.Fact{f, r} <> rest:
      f <> fact.files(rest)

def named.by(fs: List<&2, Main.Full>) -> List<&2, String>:
  match fs:
    case Nil{}:
      Nil{}
    case +f <> rest:
      +hs = Main.facts_of(f)
      List.concat(&2, String, [fact.rests(Tree.facts_of(hs, "edit")), fact.rests(Tree.facts_of(hs, "text")), fact.rests(Tree.facts_of(hs, "bytes")), named.by(rest)])

def doc.find(ds: List<&2, Store.Doc>, +id: String) -> Maybe<&2, Store.Doc>:
  match ds:
    case Nil{}:
      None{}
    case Store.Doc{p, +i, n, t} <> rest:
      Bool.pick(Maybe<&2, Store.Doc>, String.eq(i, id), Some{Store.Doc{p, i, n, t}}, doc.find(rest, id))

# What a resolution keeps items of: documents that have to travel with it.
def keeps.of(d: Maybe<&2, Store.Doc>) -> List<&2, String>:
  match d:
    case None{}:
      Nil{}
    case Some{Store.Doc{p, i, n, +text}}:
      Bool.pick(List<&2, String>, Res.is_resolution(text), Res.keeps(Res.parse(text)), Nil{})

def keeps.all(ds: List<&2, Store.Doc>) -> Nat:
  match ds:
    case Nil{}:
      0n
    case +d <> rest:
      Nat.add(List.length(&2, String, keeps.of(Some{d})), keeps.all(rest))

def next.frontier(already: Bool, +id: String, rest: List<&2, String>, +ds: List<&2, Store.Doc>) -> List<&2, String>:
  match already:
    case True{}:
      rest
    case False{}:
      List.append(&2, String, rest, keeps.of(doc.find(ds, id)))

def next.seen(already: Bool, +id: String, seen: List<&2, String>) -> List<&2, String>:
  match already:
    case True{}:
      seen
    case False{}:
      id <> seen

# Every digest named, and every one a named resolution keeps, each once.
def closure(fuel: Nat, +ds: List<&2, Store.Doc>, frontier: List<&2, String>, +seen: List<&2, String>) -> List<&2, String>:
  match fuel frontier:
    case 0n _:
      seen
    case 1n+n Nil{}:
      seen
    case 1n+n +id <> rest:
      +already = Rev.member(seen, id)
      closure(n, ds, next.frontier(already, id, rest, ds), next.seen(already, id, seen))

def doc.push(d: Maybe<&2, Store.Doc>, rest: List<&2, Store.Doc>) -> List<&2, Store.Doc>:
  match d:
    case None{}:
      rest
    case Some{x}:
      x <> rest

def doc.ids(ds: List<&2, Store.Doc>) -> List<&2, String>:
  match ds:
    case Nil{}:
      Nil{}
    case Store.Doc{p, i, n, t} <> rest:
      i <> doc.ids(rest)

def docs.among(ids: List<&2, String>, +ds: List<&2, Store.Doc>) -> List<&2, Store.Doc>:
  match ids:
    case Nil{}:
      Nil{}
    case +id <> rest:
      doc.push(doc.find(ds, id), docs.among(rest, ds))

def split.find(ss: List<&2, T.Split>, +digest: String) -> Maybe<&2, String>:
  match ss:
    case Nil{}:
      None{}
    case T.Split{+p, +d} <> rest:
      Bool.pick(Maybe<&2, String>, String.eq(d, digest), Some{p}, split.find(rest, digest))

def payload.push(+id: String, found: Maybe<&2, String>, rest: List<&2, T.Split>) -> List<&2, T.Split>:
  match found:
    case None{}:
      rest
    case Some{p}:
      T.Split{p, id} <> rest

def payloads.among(ids: List<&2, String>, +docs: Set(), +ps: List<&2, T.Split>) -> List<&2, T.Split>:
  match ids:
    case Nil{}:
      Nil{}
    case +id <> rest:
      +later = payloads.among(rest, docs, ps)
      Bool.pick(List<&2, T.Split>, Arrange.has(docs, id), later, payload.push(id, split.find(ps, id), later))

def forgets.in(f: Maybe<&2, String>, +named: Set()) -> Bool:
  match f:
    case None{}:
      False{}
    case Some{+t}:
      Arrange.has(named, t)

# The forgetting documents standing in for anything named, that are not
# themselves among the documents named.
def forgetting.of(bs: List<&2, Prune.Body>, +named: Set(), +docs: Set()) -> List<&2, String>:
  match bs:
    case Nil{}:
      Nil{}
    case Prune.Body{p, +id, ok, f} <> rest:
      Tree.keep(~String, Bool.and(Bool.not(Arrange.has(docs, id)), forgets.in(f, named)), id, forgetting.of(rest, named, docs))

# What a bookmark in the copy could find: the revisions, their changes, and
# every file one of them says anything about (decision 0024).
type Pointed is Data:
  Pointed{revisions: List<&2, String>, changes: List<&2, String>, files: List<&2, String>}

def touched(fs: List<&2, Main.Full>) -> List<&2, String>:
  match fs:
    case Nil{}:
      Nil{}
    case +f <> rest:
      +hs = Main.facts_of(f)
      List.concat(&2, String, [fact.files(Tree.facts_of(hs, "add")), fact.files(Tree.facts_of(hs, "move")), fact.files(Tree.facts_of(hs, "drop")), fact.files(Tree.facts_of(hs, "edit")), fact.files(Tree.facts_of(hs, "text")), fact.files(Tree.facts_of(hs, "bytes")), touched(rest)])

def pointed.over(+fs: List<&2, Main.Full>) -> Pointed:
  Pointed{Main.ids(fs), T.map(~Main.Full, ~String, ~(f => Main.change_of(f)), fs), touched(fs)}

def pointed.holds(pt: Pointed, g: Bm.Target) -> Bool:
  match pt g:
    case Pointed{rs, cs, fs} Bm.Target.Revision{+r}:
      Rev.member(rs, r)
    case Pointed{rs, cs, fs} Bm.Target.Change{+c}:
      Rev.member(cs, c)
    case Pointed{rs, cs, fs} Bm.Target.File{+f}:
      Rev.member(fs, f)

# The bookmarks that travel, and how many stay behind for each reason.
type Travel is Data:
  Travel{names: List<&2, Bm.Bookmark>, withheld: Nat, beyond: Nat}

def travel.names(t: Travel) -> List<&2, Bm.Bookmark>:
  match t:
    case Travel{ns, w, y}:
      ns

def travel.withheld(t: Travel) -> Travel:
  match t:
    case Travel{ns, w, y}:
      Travel{ns, 1n+w, y}

def travel.held(b: Bm.Bookmark, held: Bool, t: Travel) -> Travel:
  match held t:
    case True{} Travel{ns, w, y}:
      Travel{b <> ns, w, y}
    case False{} Travel{ns, w, y}:
      Travel{ns, w, 1n+y}

def travel.push(b: Bm.Bookmark, +pt: Pointed, t: Travel) -> Travel:
  match b:
    case Bm.Bookmark{+n, +g, p}:
      match p:
        case True{}:
          travel.withheld(t)
        case False{}:
          travel.held(Bm.Bookmark{n, g, False{}}, pointed.holds(pt, g), t)

# Decision 0062's two axes: a name that is the exporter's to give away, and
# a target the copy holds, since an export never manufactures a finding the
# origin did not have.
def travel.of(bs: List<&2, Bm.Bookmark>, +pt: Pointed) -> Travel:
  match bs:
    case Nil{}:
      Travel{Nil{}, 0n, 0n}
    case b <> rest:
      travel.push(b, pt, travel.of(rest, pt))

# Whether every bookmark here may travel and finds what it names.
def travels(bs: List<&2, Bm.Bookmark>, +pt: Pointed) -> Bool:
  match bs:
    case Nil{}:
      True{}
    case Bm.Bookmark{n, +g, p} <> rest:
      Bool.and(Bool.and(Bool.not(p), pointed.holds(pt, g)), travels(rest, pt))

def ruled.private(r: Receive.Ruled) -> Bool:
  match r:
    case Receive.Ruled{f, +line, l}:
      String.starts_with(line, "private")

# The rules that travel: every shared one (decision 0051).
def rules.shared(rs: List<&2, Receive.Ruled>) -> List<&2, Receive.Ruled>:
  match rs:
    case Nil{}:
      Nil{}
    case +r <> rest:
      Tree.keep(~Receive.Ruled, Bool.not(ruled.private(r)), r, rules.shared(rest))

def rules.withheld(rs: List<&2, Receive.Ruled>) -> Nat:
  match rs:
    case Nil{}:
      0n
    case +r <> rest:
      +later = rules.withheld(rest)
      Bool.pick(Nat, ruled.private(r), 1n+later, later)

# Whether every rule file here states a shared rule.
def lines.shared(ws: List<&2, T.Split>) -> Bool:
  match ws:
    case Nil{}:
      True{}
    case T.Split{l, +line} <> rest:
      Bool.and(Bool.not(String.starts_with(line, "private")), lines.shared(rest))

# The rule files a fresh copy is given: every shared rule, under the label
# `Rule::label` gives, beside the note `init` writes.
def rules.files(rs: List<&2, Receive.Ruled>) -> List<&2, T.Split>:
  Receive.rules.written(rules.shared(rs), Set.from_list(["README.txt"]), Nil{}, Nil{})

# The plan
# --------

type Plan is Data:
  Plan{revisions: List<&2, Main.Full>, documents: List<&2, Store.Doc>, payloads: List<&2, T.Split>, forgetting: List<&2, Store.Doc>, paths: List<&2, String>, rules: List<&2, Receive.Ruled>, withheld: Nat, names: Travel, reserved: List<&2, T.Split>}

def entry.paths(t: Tree.Tree()) -> List<&2, String>:
  match t:
    case Nil{}:
      Nil{}
    case Tree.Entry{f, p, k, y, g, m} <> rest:
      p <> entry.paths(rest)

def plan.named(+held: List<&2, Main.Full>, +t: Tree.Tree(), +ds: List<&2, Store.Doc>, +ps: List<&2, T.Split>, +bodies: List<&2, Prune.Body>, +rs: List<&2, Receive.Ruled>, +bs: List<&2, Bm.Bookmark>, +claims: List<&2, T.Split>, named: List<&2, String>) -> Plan:
  +ns = Main.sorted_distinct(named)
  +documents = docs.among(ns, ds)
  +dset = Set.from_list(doc.ids(documents))
  Plan{held, documents, payloads.among(ns, dset, ps), docs.among(Main.sorted_distinct(forgetting.of(bodies, Set.from_list(ns), dset)), ds), Main.sorted_distinct(entry.paths(t)), rules.shared(rs), rules.withheld(rs), travel.of(bs, pointed.over(held)), claims}

# Everything one export writes, worked out before anything is written.
def plan.of(+held: List<&2, Main.Full>, +t: Tree.Tree(), +ds: List<&2, Store.Doc>, +ps: List<&2, T.Split>, +bodies: List<&2, Prune.Body>, +rs: List<&2, Receive.Ruled>, +bs: List<&2, Bm.Bookmark>, +claims: List<&2, T.Split>) -> Plan:
  +start = named.by(held)
  plan.named(held, t, ds, ps, bodies, rs, bs, claims, closure(Nat.mul(2n, 1n+Nat.add(List.length(&2, String, start), keeps.all(ds))), ds, start, Nil{}))

# The folder
# ----------

# One file the folder is given: lines replayed here, bytes the host copies
# from the store, or a link, each where the tree puts it.
type Put is Data:
  Put.Text{path: String, text: String, runs: Bool}
  Put.Bytes{path: String, from: String, digest: String, runs: Bool}
  Put.Link{path: String, target: String}

# What becomes of one path: laid out, or why it cannot be.
type Outcome is Data:
  Outcome.Laid{put: Put}
  Outcome.Refused{path: String, because: String}

def put.path(p: Put) -> String:
  match p:
    case Put.Text{path, t, r}:
      path
    case Put.Bytes{path, f, d, r}:
      path
    case Put.Link{path, t}:
      path

def outcome.path(o: Outcome) -> String:
  match o:
    case Outcome.Laid{p}:
      put.path(p)
    case Outcome.Refused{path, b}:
      path

def outcome.paths(os: List<&2, Outcome>) -> List<&2, String>:
  match os:
    case Nil{}:
      Nil{}
    case o <> rest:
      outcome.path(o) <> outcome.paths(rest)

# One path of the tree, with every file claiming it: a merge can record
# two, and a folder can hold one.
type Placed is Data:
  Placed{path: String, entries: List<&2, Tree.Entry>}

def placed.path(p: Placed) -> String:
  match p:
    case Placed{path, es}:
      path

def placed.paths(ps: List<&2, Placed>) -> List<&2, String>:
  match ps:
    case Nil{}:
      Nil{}
    case p <> rest:
      placed.path(p) <> placed.paths(rest)

def runs(m: Tree.Mode) -> Bool:
  match m:
    case Tree.Executable{}:
      True{}
    case Tree.Plain{}:
      False{}

# Decision 0040: a `file:` target is the path from the link's own directory
# to where the file is now; a verbatim one is exactly its bytes.
def lay.reference(+path: String, found: Maybe<&2, String>) -> Outcome:
  match found:
    case None{}:
      Outcome.Refused{path, "it names a file this tree does not hold"}
    case Some{to}:
      Outcome.Laid{Put.Link{path, Main.relative_path(Main.directory_of(path), to)}}

def lay.link(+path: String, +t: Tree.Tree(), target: Maybe<&2, Tree.Target>) -> Outcome:
  match target:
    case None{}:
      Outcome.Refused{path, "it is a link that names nowhere"}
    case Some{Tree.Verbatim{s}}:
      Outcome.Laid{Put.Link{path, s}}
    case Some{Tree.Reference{f}}:
      lay.reference(path, Tree.path(t, f))

# Decision 0066: bytes somebody destroyed are told apart from bytes still
# in transit.
def lay.absent(+path: String, +d: String, forgotten: Bool) -> Outcome:
  match forgotten:
    case True{}:
      Outcome.Refused{path, "its content " ++ d ++ " was forgotten; record the `drop` that makes that true"}
    case False{}:
      Outcome.Refused{path, "this store does not hold the content " ++ d ++ "; receive the rest first"}

def lay.held(+path: String, +d: String, found: Maybe<&2, String>, forgotten: Bool, r: Bool) -> Outcome:
  match found:
    case Some{from}:
      Outcome.Laid{Put.Bytes{path, from, d, r}}
    case None{}:
      lay.absent(path, d, forgotten)

def forgets.is(f: Maybe<&2, String>, +d: String) -> Bool:
  match f:
    case None{}:
      False{}
    case Some{+t}:
      String.eq(t, d)

def forgets(bs: List<&2, Prune.Body>, +d: String) -> Bool:
  match bs:
    case Nil{}:
      False{}
    case Prune.Body{p, i, ok, f} <> rest:
      Bool.or(forgets.is(f, d), forgets(rest, d))

def lay.whole(+path: String, payload: Maybe<&2, String>, +ps: List<&2, T.Split>, +bs: List<&2, Prune.Body>, r: Bool) -> Outcome:
  match payload:
    case None{}:
      Outcome.Refused{path, "concurrent revisions each state its whole content, and neither is a winner"}
    case Some{+d}:
      lay.held(path, d, split.find(ps, d), forgets(bs, d), r)

def lay.lines(+path: String, content: Result<&2, &2, String, List<&2, Ops.Item>>, r: Bool) -> Outcome:
  match content:
    case Fail{e}:
      Outcome.Refused{path, e}
    case Done{items}:
      Outcome.Laid{Put.Text{path, Ops.text(items), r}}

def lay.entry(+path: String, e: Tree.Entry, +t: Tree.Tree(), +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +id: String, +ps: List<&2, T.Split>, +bs: List<&2, Prune.Body>) -> Outcome:
  match e:
    case Tree.Entry{+file, p, kind, payload, target, mode}:
      match kind:
        case Tree.Link{}:
          lay.link(path, t, target)
        case Tree.Whole{}:
          lay.whole(path, payload, ps, bs, runs(mode))
        case Tree.Lines{}:
          lay.lines(path, Main.content(fs, ds, id, file), runs(mode))

def lay.one(p: Placed, +t: Tree.Tree(), +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +id: String, +ps: List<&2, T.Split>, +bs: List<&2, Prune.Body>) -> Outcome:
  match p:
    case Placed{+path, es}:
      match es:
        case e <> Nil{}:
          lay.entry(path, e, t, fs, ds, id, ps, bs)
        case _:
          Outcome.Refused{path, "two files hold this path; record the move that settles it first"}

# The folder, path by path, in path order.
def lay(ps: List<&2, Placed>, +t: Tree.Tree(), +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +id: String, +pays: List<&2, T.Split>, +bs: List<&2, Prune.Body>) -> List<&2, Outcome>:
  match ps:
    case Nil{}:
      Nil{}
    case p <> rest:
      lay.one(p, t, fs, ds, id, pays, bs) <> lay(rest, t, fs, ds, id, pays, bs)

def entry_le(+a: Tree.Entry, +b: Tree.Entry) -> Bool:
  String.is_le(Tree.entry_path(a), Tree.entry_path(b))

def placed.push(+e: Tree.Entry, ps: List<&2, Placed>) -> List<&2, Placed>:
  match ps:
    case Placed{+path, +es} <> +rest:
      Bool.pick(List<&2, Placed>, String.eq(path, Tree.entry_path(e)), Placed{path, e <> es} <> rest, Placed{Tree.entry_path(e), [e]} <> Placed{path, es} <> rest)
    case Nil{}:
      [Placed{Tree.entry_path(e), [e]}]

def placed.go(es: List<&2, Tree.Entry>) -> List<&2, Placed>:
  match es:
    case Nil{}:
      Nil{}
    case e <> rest:
      placed.push(e, placed.go(rest))

# The tree by path, each path once with every file claiming it, in file
# order within a path.
def placed(+t: Tree.Tree()) -> List<&2, Placed>:
  placed.go(List.sort(~Tree.Entry, ~(a => b => entry_le(a, b)), t))

def prefixes.of(parts: List<&2, String>, +acc: String) -> List<&2, String>:
  match parts:
    case Nil{}:
      Nil{}
    case p <> Nil{}:
      Nil{}
    case +p <> q <> rest:
      +here = Bool.pick(String, String.is_empty(acc), p, acc ++ "/" ++ p)
      here <> prefixes.of(q <> rest, here)

def directories(ps: List<&2, Placed>) -> List<&2, String>:
  match ps:
    case Nil{}:
      Nil{}
    case Placed{+path, es} <> rest:
      List.append(&2, String, prefixes.of(String.split(path, '/'), ""), directories(rest))

def refuse.if(b: Bool, +path: String, +because: String, rest: List<&2, T.Split>) -> List<&2, T.Split>:
  Tree.keep(~T.Split, b, T.Split{path, because}, rest)

# What the tree itself refuses, before the folder is asked: a path that is
# also another file's directory, one in the store, and one a rule covers.
def refused.tree(ps: List<&2, Placed>, +dirs: Set(), +rules: List<&2, Folder.Scope>) -> List<&2, T.Split>:
  match ps:
    case Nil{}:
      Nil{}
    case Placed{+path, es} <> rest:
      refuse.if(Arrange.has(dirs, path), path, "it is also a directory of another file here, and a folder cannot hold both",
        refuse.if(Bool.or(String.eq(path, "history"), String.starts_with(path, "history/")), path, "it would write a working file into the store",
          refuse.if(Folder.skips(rules, path), path, "a `skip` rule in history/skipped.txt covers it, so the walk could never offer it back",
            refused.tree(rest, dirs, rules))))

def refused.laid(os: List<&2, Outcome>) -> List<&2, T.Split>:
  match os:
    case Nil{}:
      Nil{}
    case Outcome.Refused{p, b} <> rest:
      T.Split{p, b} <> refused.laid(rest)
    case Outcome.Laid{p} <> rest:
      refused.laid(rest)

def puts(os: List<&2, Outcome>) -> List<&2, Put>:
  match os:
    case Nil{}:
      Nil{}
    case Outcome.Laid{p} <> rest:
      p <> puts(rest)
    case Outcome.Refused{p, b} <> rest:
      puts(rest)

def split_le(+a: T.Split, +b: T.Split) -> Bool:
  match a b:
    case T.Split{+p1, +b1} T.Split{+p2, +b2}:
      Arrange.cmp.then(String.order(p1, p2), String.is_le(b1, b2))

def dedup.push(+x: T.Split, tail: List<&2, T.Split>) -> List<&2, T.Split>:
  match tail:
    case Nil{}:
      [x]
    case +y <> +more:
      Bool.pick(List<&2, T.Split>, Bool.and(split_le(x, y), split_le(y, x)), y <> more, x <> y <> more)

def splits.dedup(ss: List<&2, T.Split>) -> List<&2, T.Split>:
  match ss:
    case Nil{}:
      Nil{}
    case x <> rest:
      dedup.push(x, splits.dedup(rest))

def refusal.lines(ss: List<&2, T.Split>) -> String:
  match ss:
    case Nil{}:
      SNil{}
    case T.Split{p, b} <> rest:
      "\n  " ++ p ++ ": " ++ b ++ refusal.lines(rest)

def laid.r(+os: List<&2, Outcome>, refused: List<&2, T.Split>) -> Result<&2, &2, Main.Refused, List<&2, Put>>:
  match refused:
    case Nil{}:
      Done{puts(os)}
    case +some:
      Fail{Main.Refused{1, "the folder cannot take this tree whole, so nothing was written:" ++ refusal.lines(splits.dedup(List.sort(~T.Split, ~(a => b => split_le(a, b)), some)))}}

# Every file the folder is given, or every path in the way and why.
def folder.r(+t: Tree.Tree(), +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +id: String, +pays: List<&2, T.Split>, +bs: List<&2, Prune.Body>, +rules: List<&2, Folder.Scope>) -> Result<&2, &2, Main.Refused, List<&2, Put>>:
  +ps = placed(t)
  +os = lay(ps, t, fs, ds, id, pays, bs)
  laid.r(os, List.append(&2, T.Split, refused.tree(ps, Set.from_list(directories(ps)), rules), refused.laid(os)))

def rule.private(r: Maybe<&2, Receive.Ruled>) -> Bool:
  match r:
    case None{}:
      False{}
    case Some{Receive.Ruled{f, +line, l}}:
      String.starts_with(line, "private")

# The rules a folder is read through: every rule, or the shared ones, which
# are the rules a copy states.
def scope.of(st: Folder.Stated) -> List<&2, Folder.Scope>:
  match st:
    case Folder.Stated.One{sc}:
      [sc]
    case _:
      Nil{}

def scopes(rs: List<&2, T.Split>, +shared: Bool) -> List<&2, Folder.Scope>:
  match rs:
    case Nil{}:
      Nil{}
    case T.Split{+path, +text} <> rest:
      +later = scopes(rest, shared)
      Bool.pick(List<&2, Folder.Scope>, Bool.and(shared, rule.private(Receive.ruled.of(Receive.skipped_file(path), text, Folder.rule_in(text)))), later, List.append(&2, Folder.Scope, scope.of(Folder.rule_in(text)), later))

# What is said
# ------------

def count.line(+verb: String, +n: Nat, +what: String) -> String:
  verb ++ " " ++ Nat.show(n) ++ " " ++ what

def line.if(b: Bool, +l: String) -> List<&2, String>:
  Bool.pick(List<&2, String>, b, [l], Nil{})

def nonzero(+n: Nat) -> Bool:
  Bool.not(Nat.is_eq(n, 0n))

def paths.said(+verb: String, ps: List<&2, String>) -> List<&2, String>:
  match ps:
    case Nil{}:
      Nil{}
    case p <> rest:
      (verb ++ " " ++ p) <> paths.said(verb, rest)

# How many of each kind of file one export writes: for a fresh copy the
# whole set, and for a copy being updated what it does not hold.
type Counts is Data:
  Counts{revisions: Nat, documents: Nat, payloads: Nat, forgetting: Nat}

def plan.counts(p: Plan) -> Counts:
  match p:
    case Plan{revs, docs, pays, forg, paths, rules, w, n, res}:
      Counts{List.length(&2, Main.Full, revs), List.length(&2, Store.Doc, docs), List.length(&2, T.Split, pays), List.length(&2, Store.Doc, forg)}

# The counts, the same numbers a dry run and the real thing report. `verbs`
# are what a sentence takes, `would export`, `would hold back`, `would
# leave` and `would carry`, or what they became.
def said.counts(+export: String, +hold: String, +leave: String, +carry: String, c: Counts, p: Plan, +carried: Nat) -> List<&2, String>:
  match c p:
    case Counts{+nr, +nd, +np, +nf} Plan{revs, docs, pays, forg, paths, +rules, +w, Travel{+ns, +wn, +y}, res}:
      List.concat(&2, String, [
        [count.line(export, nr, "revisions"),
         count.line(export, nd, "operation documents"),
         count.line(export, np, "payloads")],
        line.if(nonzero(nf), count.line(export, nf, "forgetting documents")),
        line.if(Bool.or(nonzero(List.length(&2, Receive.Ruled, rules)), nonzero(w)), count.line(export, List.length(&2, Receive.Ruled, rules), "rules")),
        line.if(nonzero(w), count.line(hold, w, "private rules")),
        line.if(Bool.or(nonzero(List.length(&2, Bm.Bookmark, ns)), nonzero(wn)), count.line(export, List.length(&2, Bm.Bookmark, ns), "bookmarks")),
        line.if(nonzero(wn), count.line(hold, wn, "private bookmarks")),
        line.if(nonzero(y), count.line(leave, y, "bookmarks pointing past this target")),
        line.if(nonzero(carried), count.line(carry, carried, "files another tool wrote"))])

def plan.paths(p: Plan) -> List<&2, String>:
  match p:
    case Plan{r, d, y, f, paths, rs, w, n, res}:
      paths

def plan.reserved(p: Plan) -> List<&2, T.Split>:
  match p:
    case Plan{r, d, y, f, paths, rs, w, n, res}:
      res

def withdrawn.said(ws: List<&2, String>) -> List<&2, String>:
  match ws:
    case Nil{}:
      Nil{}
    case w <> rest:
      ("would withdraw history/" ++ w) <> withdrawn.said(rest)

def updating.said(u: Bool) -> String:
  match u:
    case True{}:
      "update the copy"
    case False{}:
      "make a copy"

# What `export -n` prints: the counts, every file a copy being updated
# gives up, the forgotten originals it destroys, and the folder's paths.
def said.plan(+p: Plan, c: Counts, +withdraws: List<&2, String>, +destroys: Nat, +updating: Bool, +spelled: String, +into: String) -> List<&2, String>:
  List.concat(&2, String, [
    said.counts("would export", "would hold back", "would leave", "would carry", c, p, List.length(&2, T.Split, plan.reserved(p))),
    withdrawn.said(withdraws),
    line.if(nonzero(destroys), count.line("would destroy", destroys, "forgotten originals")),
    paths.said("write  ", plan.paths(p)),
    ["would " ++ updating.said(updating) ++ " of " ++ spelled ++ " at " ++ into]])

# What a folder laid out without a store beside it plans, as `update -n`
# says it.
def put.said(p: Put) -> List<&2, String>:
  match p:
    case Put.Text{path, t, r}:
      ["write   " ++ path]
    case Put.Bytes{path, f, d, r}:
      ["write   " ++ path]
    case Put.Link{path, t}:
      Nil{}

def link.said(+verb: String, p: Put) -> List<&2, String>:
  match p:
    case Put.Link{path, t}:
      [verb ++ path ++ "  (" ++ t ++ ")"]
    case _:
      Nil{}

def puts.said(ps: List<&2, Put>) -> List<&2, String>:
  match ps:
    case Nil{}:
      Nil{}
    case +p <> rest:
      List.append(&2, String, put.said(p), puts.said(rest))

def links.said(+verb: String, ps: List<&2, Put>) -> List<&2, String>:
  match ps:
    case Nil{}:
      Nil{}
    case +p <> rest:
      List.append(&2, String, link.said(verb, p), links.said(verb, rest))

# Laying out
# ----------

def io.ok(r: Result<&1, &1, U32 & String, String>) -> IO(String):
  Main.name.io(r)

def runnable(+at: String, r: Bool) -> IO(Bool):
  match r:
    case False{}:
      IO.pure(Bool, False{})
    case True{}:
      do IO<Bool>:
        m : Result<&1, &1, U32 & String, String> <- Store.made_runnable(at ++ "\nexecutable")
        said : String <- io.ok(m)
        return String.eq(said, "set")

# The files, in path order, then the links: each written where nothing
# stood, and made runnable where the tree says it can be run. What comes
# back is every path whose mode was set, as the Rust tool's `update::apply`
# reports it; the files written are the folder's files, in path order.
def apply.files(+root: String, +into: String, ps: List<&2, Put>, +set: List<&2, String>) -> IO(List<&2, String>):
  match ps:
    case Nil{}:
      IO.pure(List<&2, String>, set)
    case Put.Text{+path, text, r} <> rest:
      do IO<List<&2, String>>:
        w : Result<&1, &1, U32 & String, String> <- Store.filed(into ++ "/" ++ path ++ "\n" ++ text)
        x : String <- io.ok(w)
        m : Bool <- runnable(into ++ "/" ++ path, r)
        apply.files(root, into, rest, Bool.pick(List<&2, String>, m, path <> set, set))
    case Put.Bytes{+path, from, +d, r} <> rest:
      do IO<List<&2, String>>:
        w : Result<&1, &1, U32 & String, String> <- Store.copied(root ++ "/" ++ from ++ "\n" ++ into ++ "/" ++ path ++ "\n" ++ d)
        x : String <- io.ok(w)
        m : Bool <- runnable(into ++ "/" ++ path, r)
        apply.files(root, into, rest, Bool.pick(List<&2, String>, m, path <> set, set))
    case Put.Link{path, t} <> rest:
      apply.files(root, into, rest, set)

def apply.links(+into: String, ps: List<&2, Put>) -> IO(Unit):
  match ps:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case Put.Link{+path, t} <> rest:
      do IO<Unit>:
        w : Result<&1, &1, U32 & String, String> <- Store.linked(into ++ "/" ++ path ++ "\n" ++ t)
        x : String <- io.ok(w)
        apply.links(into, rest)
    case p <> rest:
      apply.links(into, rest)

def apply(+root: String, +into: String, +ps: List<&2, Put>) -> IO(List<&2, String>):
  do IO<List<&2, String>>:
    set : List<&2, String> <- apply.files(root, into, ps, Nil{})
    apply.links(into, ps)
    return List.reverse(&2, String, set)

def modes.said(ps: List<&2, String>) -> List<&2, String>:
  match ps:
    case Nil{}:
      Nil{}
    case p <> rest:
      ("mode    " ++ p ++ "  (executable)") <> modes.said(rest)

# Writing the copy
# ----------------

def name_of(+filed: List<&2, T.Split>, +id: String, doc: Bool) -> String:
  match doc:
    case True{}:
      Maybe.default(&2, String, Arrange.lookup(filed, id), id ++ ".ops.txt")
    case False{}:
      Maybe.default(&2, String, Arrange.lookup(filed, id), id)

def copied.payloads(+from: String, +to: String, +filed: List<&2, T.Split>, ps: List<&2, T.Split>) -> IO(Unit):
  match ps:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case T.Split{+p, +d} <> rest:
      do IO<Unit>:
        w : Result<&1, &1, U32 & String, String> <- Store.copied(from ++ "/" ++ p ++ "\n" ++ to ++ "/operations/" ++ name_of(filed, d, False{}) ++ "\n" ++ d)
        x : String <- io.ok(w)
        copied.payloads(from, to, filed, rest)

def filed.docs(+to: String, +filed: List<&2, T.Split>, ds: List<&2, Store.Doc>) -> IO(Unit):
  match ds:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case Store.Doc{p, +id, n, text} <> rest:
      do IO<Unit>:
        w : Result<&1, &1, U32 & String, String> <- Store.filed(to ++ "/operations/" ++ name_of(filed, id, True{}) ++ "\n" ++ text)
        x : String <- io.ok(w)
        filed.docs(to, filed, rest)

def filed.revisions(+to: String, +stems: List<&2, T.Split>, +rds: List<&2, Store.Doc>, fs: List<&2, Main.Full>) -> IO(Unit):
  match fs:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case +f <> rest:
      +id = Main.id_of(f)
      do IO<Unit>:
        w : Result<&1, &1, U32 & String, String> <- Store.filed(to ++ "/revisions/" ++ Maybe.default(&2, String, Arrange.lookup(stems, id), id) ++ ".rev.txt\n" ++ Maybe.default(&2, String, Maybe.map(&2, Store.Doc, String, d => Store.text_of(d), doc.find(rds, id)), SNil{}))
        x : String <- io.ok(w)
        filed.revisions(to, stems, rds, rest)

def plus_if(+said: String, +n: Nat) -> Nat:
  Bool.pick(Nat, String.eq(said, "written"), 1n+n, n)

# The files of `claims/`, each under the name it had and unread: how many
# were not there already.
def carried(+from: String, +to: String, cs: List<&2, T.Split>) -> IO(Nat):
  match cs:
    case Nil{}:
      IO.pure(Nat, 0n)
    case T.Split{+label, +d} <> rest:
      do IO<Nat>:
        w : Result<&1, &1, U32 & String, String> <- Store.copied(from ++ "/" ++ label ++ "\n" ++ to ++ "/" ++ label ++ "\n" ++ d)
        x : String <- io.ok(w)
        more : Nat <- carried(from, to, rest)
        return plus_if(x, more)

# `init`'s layout, and its four notes: a copy explains itself (decision
# 0021) and states nothing of the exporter's.
def copy.init(+root: String) -> IO(Unit):
  do IO<Unit>:
    m : Result<&1, &1, U32 & String, String> <- Store.made(Main.init.dirs(root, ["revisions", "operations", "names", "cache", "skipped"]))
    done : String <- Main.init.io(String, m)
    Main.init.write(root ++ "/historica.txt", Notes.HEADER_NOTE())
    Main.init.write(root ++ "/skipped/README.txt", Notes.SKIPPED_NOTE())
    Main.init.write(root ++ "/format.txt", Notes.FORMAT_NOTE())
    Main.init.write(root ++ "/cache/README.txt", Notes.CACHE_NOTE())

# Reading
# -------

# The origin, as `receive` reads a side: opened as the Rust tool opens a
# store, with its bookmarks and the files of `claims/`.
type Origin is Data:
  Origin{side: Receive.Side, fs: List<&2, Main.Full>}

def listed.lines(r: Result<&1, &1, U32 & String, String>) -> Maybe<&2, List<&2, String>>:
  match r:
    case Fail{e}:
      None{}
    case Done{+text}:
      Some{Bool.pick(List<&2, String>, String.is_empty(text), Nil{}, String.split(text, '\n'))}

# The names one directory holds, from `Store.folder`'s lines: a file's
# line carries whether it runs and its size before the name, and a link's
# is followed by where it points.
def entry.file_name(cut: Maybe<&2, T.Split>) -> Maybe<&2, String>:
  match cut:
    case None{}:
      None{}
    case Some{T.Split{size, name}}:
      Some{name}

def entry.file(cut: Maybe<&2, T.Split>) -> Maybe<&2, String>:
  match cut:
    case None{}:
      None{}
    case Some{T.Split{x, +rest}}:
      entry.file_name(T.split_once(rest))

def entry.name(+kind: String, +rest: String) -> Maybe<&2, String>:
  Bool.pick(Maybe<&2, String>, String.eq(kind, "f"), entry.file(T.split_once(rest)), Some{rest})

def name.push(n: Maybe<&2, String>, rest: List<&2, String>) -> List<&2, String>:
  match n:
    case None{}:
      rest
    case Some{x}:
      x <> rest

def entry.push(cut: Maybe<&2, T.Split>, rest: List<&2, String>) -> List<&2, String>:
  match cut:
    case None{}:
      rest
    case Some{T.Split{+kind, +name}}:
      name.push(entry.name(kind, name), rest)

def entry.names(ls: List<&2, String>, skip: Bool) -> List<&2, String>:
  match ls skip:
    case Nil{} _:
      Nil{}
    case l <> rest True{}:
      entry.names(rest, False{})
    case +l <> rest False{}:
      entry.push(T.split_once(l), entry.names(rest, String.starts_with(l, "l ")))

# Where an export goes: nowhere yet, or a directory holding nothing, gets a
# fresh copy; one holding a store gets that copy brought up to date
# (decision 0052); one holding anything else is somebody's. A directory
# that cannot be listed, for a reason other than not being there, is not
# knowing, and says why in the host's words.
type Dest is Data:
  Dest.Fresh{}
  Dest.Copy{}

# What listing the destination found: nothing there, something that could
# not be listed and why, or what it holds.
type Lst is Data:
  Lst.Absent{}
  Lst.Unreadable{msg: String}
  Lst.Listed{text: String}

def lst.of(listed: Result<&1, &1, U32 & String, String>) -> Lst:
  match listed:
    case Fail{Tuple{code, msg}}:
      Bool.pick(Lst, U32.is_eq(code, 2), Lst.Absent{}, Lst.Unreadable{msg})
    case Done{text}:
      Lst.Listed{text}

def dest.held(+into: String, empty: Bool, store: Bool) -> Result<&2, &2, Main.Refused, Dest>:
  match empty store:
    case True{} _:
      Done{Dest.Fresh{}}
    case False{} True{}:
      Done{Dest.Copy{}}
    case False{} False{}:
      Fail{Main.Refused{1, into ++ " already holds something that is not a copy of this store; an export writes a fresh repository into an empty directory and updates a copy it made, and combining a copy with what is already there is `receive`"}}

def dest.decide(+into: String, l: Lst, store: Bool) -> Result<&2, &2, Main.Refused, Dest>:
  match l:
    case Lst.Absent{}:
      Done{Dest.Fresh{}}
    case Lst.Unreadable{msg}:
      Fail{Main.Refused{1, msg}}
    case Lst.Listed{+text}:
      dest.held(into, String.is_empty(text), store)

def dest.r(+into: String, listed: Result<&1, &1, U32 & String, String>, header: Result<&1, &1, U32 & String, String>) -> Result<&2, &2, Main.Refused, Dest>:
  dest.decide(into, lst.of(listed), Result.is_done(&1, &1, U32 & String, String, header))

def more.said(+n: Nat) -> String:
  Bool.pick(String, Nat.is_lt(3n, n), " and " ++ Nat.show(Nat.sub(n, 3n)) ++ " more", SNil{})

def holding.r(+into: String, names: List<&2, String>) -> Result<&2, &2, Main.Refused, Unit>:
  match names:
    case Nil{}:
      Done{Unit{}}
    case +some:
      Fail{Main.Refused{1, into ++ " already holds " ++ String.join(List.take(&2, String, some, 3n), ", ") ++ "; laying a revision out wants a directory holding nothing, because nothing afterwards could say which files it put there" ++ more.said(List.length(&2, String, some))}}

# The names a directory holds, read from `Store.folder`'s answer.
def dir.names(+text: String) -> List<&2, String>:
  entry.names(Bool.pick(List<&2, String>, String.is_empty(text), Nil{}, String.split(text, '\n')), False{})

# `--files-only` lays the folder out into a directory that holds nothing,
# made first; one that cannot be listed says why.
def empty.r(+into: String, listed: Result<&1, &1, U32 & String, String>) -> Result<&2, &2, Main.Refused, Unit>:
  match listed:
    case Fail{Tuple{code, msg}}:
      Fail{Main.Refused{1, msg}}
    case Done{+text}:
      holding.r(into, dir.names(text))

def sound.r(ok: Bool) -> Result<&2, &2, Main.Refused, Unit>:
  Bool.pick(Result<&2, &2, Main.Refused, Unit>, ok, Done{Unit{}},
    Fail{Main.Refused{1, "this store does not pass `check`, and a copy of a fault is two faults; `historica check` says what is wrong"}})

def plan.documents(p: Plan) -> List<&2, Store.Doc>:
  match p:
    case Plan{r, d, y, f, paths, rs, w, n, res}:
      d

def plan.payloads(p: Plan) -> List<&2, T.Split>:
  match p:
    case Plan{r, d, y, f, paths, rs, w, n, res}:
      y

def plan.forgetting(p: Plan) -> List<&2, Store.Doc>:
  match p:
    case Plan{r, d, y, f, paths, rs, w, n, res}:
      f

def plan.names(p: Plan) -> Travel:
  match p:
    case Plan{r, d, y, f, paths, rs, w, n, res}:
      n

# Onto a copy it made
# -------------------
#
# Decision 0052: a destination holding a copy of this store is brought up to
# date rather than refused. The set is the same; what is new is the diff —
# each file of the copy's is held, withdrawn or destroyed — and a folder
# that is caught up rather than laid out into nothing.

def BROKEN_COPY(+into: String) -> String:
  into ++ " holds a copy that does not pass `check`, and an export writes nothing into a store whose faults it would build on; `historica check` there says what is wrong"

def UNRELATED(+into: String) -> String:
  into ++ " holds a store that shares no revision or graph edge with this one; an export updates a copy it made and refuses anything else"

def RECORDED_IN(+into: String, +id: String) -> String:
  into ++ " holds " ++ String.take(id, 12n) ++ ", which this store does not: somebody recorded in the copy, and an export assembles rather than merges; `historica receive` in this direction first"

# Every digest this store's revisions name as a parent or as superseded.
def named.edges(fs: List<&2, Main.Full>) -> List<&2, String>:
  match fs:
    case Nil{}:
      Nil{}
    case Main.Full{id, c, parents, supersedes, a, w, rb, rv, facts, m} <> rest:
      List.concat(&2, String, [parents, supersedes, named.edges(rest)])

# The first revision, by digest, the copy holds and this store neither
# holds nor names: somebody recorded it in the copy.
def stranger(cfs: List<&2, Main.Full>, +here: Set()) -> Maybe<&2, String>:
  match cfs:
    case Nil{}:
      None{}
    case +f <> rest:
      +id = Main.id_of(f)
      Bool.pick(Maybe<&2, String>, Arrange.has(here, id), stranger(rest, here), Some{id})

def stranger.r(+into: String, s: Maybe<&2, String>) -> Result<&2, &2, Main.Refused, Unit>:
  match s:
    case None{}:
      Done{Unit{}}
    case Some{+id}:
      Fail{Main.Refused{1, RECORDED_IN(into, id)}}

# What a copy must be for an export to write into it: a store `check`
# passes — asked before the copy is opened, as the Rust tool asks it —
# related to this one, with nothing recorded in it this store has not heard
# of.
def copy.sound.r(+into: String, ok: Bool) -> Result<&2, &2, Main.Refused, Unit>:
  Bool.pick(Result<&2, &2, Main.Refused, Unit>, ok, Done{Unit{}}, Fail{Main.Refused{1, BROKEN_COPY(into)}})

def copy.r(+into: String, +fs: List<&2, Main.Full>, +cfs: List<&2, Main.Full>) -> Result<&2, &2, Main.Refused, Unit>:
  do Result<&2, &2, Main.Refused, Unit>:
    Bool.pick(Result<&2, &2, Main.Refused, Unit>, Receive.related(fs, cfs), Done{Unit{}}, Fail{Main.Refused{1, UNRELATED(into)}})
    stranger.r(into, stranger(cfs, Set.from_list(List.append(&2, String, Main.ids(fs), named.edges(fs)))))

# What the copy holds of the set, what it holds that the set no longer
# names — files withdrawn, rule files and bookmarks retired — and what a
# forgetting document on either side says is gone.
type Onto is Data:
  Onto{holds: List<&2, String>, stems: List<&2, T.Split>, withdraws: List<&2, String>, retired: List<&2, String>, names: List<&2, String>, destroys: List<&2, String>, forgotten: List<&2, String>}

def maybe.push(m: Maybe<&2, String>, rest: List<&2, String>) -> List<&2, String>:
  match m:
    case None{}:
      rest
    case Some{x}:
      x <> rest

def stored.revs(s: Prune.Stored) -> List<&2, T.Split>:
  match s:
    case Prune.Stored{docs, revs, od, bs, ps, names, rules}:
      revs

# What either side forgets: what the documents that travel forget, and
# everything the copy forgets, since a store that destroyed something must
# not be handed it back.
def forgets.here(bs: List<&2, Prune.Body>, +docs: Set()) -> List<&2, String>:
  match bs:
    case Nil{}:
      Nil{}
    case Prune.Body{p, +id, ok, f} <> rest:
      +later = forgets.here(rest, docs)
      Bool.pick(List<&2, String>, Arrange.has(docs, id), maybe.push(f, later), later)

def forgets.all(bs: List<&2, Prune.Body>) -> List<&2, String>:
  match bs:
    case Nil{}:
      Nil{}
    case Prune.Body{p, id, ok, f} <> rest:
      maybe.push(f, forgets.all(rest))

# A revision file's stem: its path under `revisions/`, less the suffix.
def rev.stem(+path: String) -> Maybe<&2, String>:
  Bool.pick(Maybe<&2, String>, String.ends_with(path, ".rev.txt"), Some{Prune.unrevision(String.drop(path, 10n))}, None{})

def stem.push(+id: String, s: Maybe<&2, String>, rest: List<&2, T.Split>) -> List<&2, T.Split>:
  match s:
    case None{}:
      rest
    case Some{x}:
      T.Split{id, x} <> rest

def revs.holds(ss: List<&2, T.Split>, +set: Set()) -> List<&2, String>:
  match ss:
    case Nil{}:
      Nil{}
    case T.Split{p, +d} <> rest:
      Tree.keep(~String, Arrange.has(set, d), d, revs.holds(rest, set))

# Each held revision's stem, the last file of it the walk reaches winning.
def revs.stems(ss: List<&2, T.Split>, +set: Set()) -> List<&2, T.Split>:
  match ss:
    case Nil{}:
      Nil{}
    case T.Split{+p, +d} <> rest:
      +later = revs.stems(rest, set)
      Bool.pick(List<&2, T.Split>, Arrange.has(set, d), List.append(&2, T.Split, later, stem.push(d, rev.stem(p), Nil{})), later)

def revs.gone(ss: List<&2, T.Split>, +set: Set()) -> List<&2, String>:
  match ss:
    case Nil{}:
      Nil{}
    case T.Split{p, +d} <> rest:
      Tree.keep(~String, Bool.not(Arrange.has(set, d)), p, revs.gone(rest, set))

# A stand-in the origin does not have, for a document or a payload the set
# still names, is kept: decision 0014 travels one way only.
def stands.in(f: Maybe<&2, String>, +content: Set()) -> Bool:
  match f:
    case None{}:
      False{}
    case Some{+t}:
      Arrange.has(content, t)

def body.kept(+id: String, +f: Maybe<&2, String>, +docs: Set(), +content: Set()) -> Bool:
  Bool.or(Arrange.has(docs, id), stands.in(f, content))

def bodies.holds(bs: List<&2, Prune.Body>, +forgotten: Set(), +docs: Set(), +content: Set()) -> List<&2, String>:
  match bs:
    case Nil{}:
      Nil{}
    case Prune.Body{p, +id, ok, +f} <> rest:
      Tree.keep(~String, Bool.and(Bool.not(Arrange.has(forgotten, id)), body.kept(id, f, docs, content)), id, bodies.holds(rest, forgotten, docs, content))

def bodies.gone(bs: List<&2, Prune.Body>, +forgotten: Set(), +docs: Set(), +content: Set()) -> List<&2, String>:
  match bs:
    case Nil{}:
      Nil{}
    case Prune.Body{+p, +id, ok, +f} <> rest:
      Tree.keep(~String, Bool.not(Bool.or(Arrange.has(forgotten, id), body.kept(id, f, docs, content))), p, bodies.gone(rest, forgotten, docs, content))

def pays.holds(ss: List<&2, T.Split>, +forgotten: Set(), +pays: Set()) -> List<&2, String>:
  match ss:
    case Nil{}:
      Nil{}
    case T.Split{p, +d} <> rest:
      Tree.keep(~String, Bool.and(Bool.not(Arrange.has(forgotten, d)), Arrange.has(pays, d)), d, pays.holds(rest, forgotten, pays))

def pays.gone(ss: List<&2, T.Split>, +forgotten: Set(), +pays: Set()) -> List<&2, String>:
  match ss:
    case Nil{}:
      Nil{}
    case T.Split{+p, +d} <> rest:
      Tree.keep(~String, Bool.not(Bool.or(Arrange.has(forgotten, d), Arrange.has(pays, d))), p, pays.gone(rest, forgotten, pays))

def ruled.line(r: Receive.Ruled) -> String:
  match r:
    case Receive.Ruled{f, line, l}:
      line

def ruled.file(r: Receive.Ruled) -> String:
  match r:
    case Receive.Ruled{f, line, l}:
      f

# A rule the copy states and the origin no longer shares retires its file.
def rules.retired(rs: List<&2, Receive.Ruled>, +shared: Set()) -> List<&2, String>:
  match rs:
    case Nil{}:
      Nil{}
    case Receive.Ruled{+f, +line, l} <> rest:
      Tree.keep(~String, Bool.not(Arrange.has(shared, line)), "skipped/" ++ f, rules.retired(rest, shared))

# A bookmark the copy holds and the set no longer names goes (decision 0062).
def names.retired(bs: List<&2, Bm.Bookmark>, +kept: Set()) -> List<&2, String>:
  match bs:
    case Nil{}:
      Nil{}
    case Bm.Bookmark{+n, t, p} <> rest:
      Tree.keep(~String, Bool.not(Arrange.has(kept, n)), n, names.retired(rest, kept))

def names.files(ns: List<&2, String>) -> List<&2, String>:
  match ns:
    case Nil{}:
      Nil{}
    case n <> rest:
      ("names/" ++ n ++ ".txt") <> names.files(rest)

def marks.names(bs: List<&2, Bm.Bookmark>) -> List<&2, String>:
  match bs:
    case Nil{}:
      Nil{}
    case b <> rest:
      Bm.name_of(b) <> marks.names(rest)

def plan.revisions(p: Plan) -> List<&2, Main.Full>:
  match p:
    case Plan{r, d, y, f, paths, rs, w, n, res}:
      r

def plan.rules(p: Plan) -> List<&2, Receive.Ruled>:
  match p:
    case Plan{r, d, y, f, paths, rs, w, n, res}:
      rs

def rules.lines(rs: List<&2, Receive.Ruled>) -> List<&2, String>:
  match rs:
    case Nil{}:
      Nil{}
    case r <> rest:
      ruled.line(r) <> rules.lines(rest)

# The diff of the copy against the set: `diff_onto`. Revisions the set
# names are held, with the stems they already have, and the rest withdrawn;
# a document or payload either side forgets is destroyed, one the set names
# — or a stand-in for one — held, and the rest withdrawn; then the rule
# files and bookmarks the origin no longer shares.
def split.digests(ss: List<&2, T.Split>) -> List<&2, String>:
  match ss:
    case Nil{}:
      Nil{}
    case T.Split{p, d} <> rest:
      d <> split.digests(rest)

def plan.docset(+p: Plan) -> Set():
  Set.from_list(List.append(&2, String, doc.ids(plan.documents(p)), doc.ids(plan.forgetting(p))))

# What either side forgets: what the documents that travel forget, and
# everything the copy forgets.
def onto.forgotten.of(+p: Plan, +here: List<&2, Prune.Body>, +cst: Prune.Stored) -> List<&2, String>:
  Main.sorted_distinct(List.append(&2, String, forgets.here(here, plan.docset(p)), forgets.all(Receive.stored.bodies(cst))))

def body.digests(bs: List<&2, Prune.Body>) -> List<&2, String>:
  match bs:
    case Nil{}:
      Nil{}
    case Prune.Body{p, i, ok, f} <> rest:
      i <> body.digests(rest)

# The originals the copy holds that either side forgets, each once.
def onto.destroys.of(+forgotten: List<&2, String>, +cst: Prune.Stored) -> List<&2, String>:
  Main.sorted_distinct(Receive.among(forgotten, Set.from_list(List.append(&2, String, body.digests(Receive.stored.bodies(cst)), split.digests(Receive.stored.payloads(cst))))))

def onto.of(+p: Plan, +here: List<&2, Prune.Body>, +cst: Prune.Stored, +marks: List<&2, Bm.Bookmark>) -> Onto:
  +revset = Set.from_list(Main.ids(plan.revisions(p)))
  +docset = plan.docset(p)
  +payset = Set.from_list(split.digests(plan.payloads(p)))
  +content = Set.from_list(List.concat(&2, String, [doc.ids(plan.documents(p)), doc.ids(plan.forgetting(p)), split.digests(plan.payloads(p))]))
  +forgotten = onto.forgotten.of(p, here, cst)
  +fset = Set.from_list(forgotten)
  +revs = stored.revs(cst)
  +bodies = Receive.stored.bodies(cst)
  +pays = Receive.stored.payloads(cst)
  Onto{List.concat(&2, String, [revs.holds(revs, revset), bodies.holds(bodies, fset, docset, content), pays.holds(pays, fset, payset)]),
    List.reverse(&2, T.Split, revs.stems(revs, revset)),
    List.concat(&2, String, [revs.gone(revs, revset), bodies.gone(bodies, fset, docset, content), pays.gone(pays, fset, payset)]),
    rules.retired(Receive.ruled(Receive.stored.rules(cst)), Set.from_list(rules.lines(plan.rules(p)))),
    names.retired(marks, Set.from_list(marks.names(travel.names(plan.names(p))))),
    onto.destroys.of(forgotten, cst),
    forgotten}

def onto.holds(o: Onto) -> List<&2, String>:
  match o:
    case Onto{h, s, w, r, n, d, f}:
      h

def onto.stems(o: Onto) -> List<&2, T.Split>:
  match o:
    case Onto{h, s, w, r, n, d, f}:
      s

def onto.withdraws(o: Onto) -> List<&2, String>:
  match o:
    case Onto{h, s, w, r, n, d, f}:
      w

def onto.retired(o: Onto) -> List<&2, String>:
  match o:
    case Onto{h, s, w, r, n, d, f}:
      r

def onto.names(o: Onto) -> List<&2, String>:
  match o:
    case Onto{h, s, w, r, n, d, f}:
      n

def onto.destroys(o: Onto) -> List<&2, String>:
  match o:
    case Onto{h, s, w, r, n, d, f}:
      d

def onto.forgotten(o: Onto) -> List<&2, String>:
  match o:
    case Onto{h, s, w, r, n, d, f}:
      f

# Every file the copy gives up, in the order they go: store content, then
# the rule files, then the bookmarks.
def onto.all(+o: Onto) -> List<&2, String>:
  List.concat(&2, String, [onto.withdraws(o), onto.retired(o), names.files(onto.names(o))])

# What is new to the copy: neither held there nor forgotten by either side.
def fresh.ids(ids: List<&2, String>, +gone: Set()) -> List<&2, String>:
  match ids:
    case Nil{}:
      Nil{}
    case +id <> rest:
      Tree.keep(~String, Bool.not(Arrange.has(gone, id)), id, fresh.ids(rest, gone))

def fresh.docs(ds: List<&2, Store.Doc>, +gone: Set()) -> List<&2, Store.Doc>:
  match ds:
    case Nil{}:
      Nil{}
    case +d <> rest:
      Tree.keep(~Store.Doc, Bool.not(Arrange.has(gone, Store.id_of(d))), d, fresh.docs(rest, gone))

def fresh.splits(ss: List<&2, T.Split>, +gone: Set()) -> List<&2, T.Split>:
  match ss:
    case Nil{}:
      Nil{}
    case T.Split{+p, +d} <> rest:
      Tree.keep(~T.Split, Bool.not(Arrange.has(gone, d)), T.Split{p, d}, fresh.splits(rest, gone))

def fresh.fulls(fs: List<&2, Main.Full>, +gone: Set()) -> List<&2, Main.Full>:
  match fs:
    case Nil{}:
      Nil{}
    case +f <> rest:
      Tree.keep(~Main.Full, Bool.not(Arrange.has(gone, Main.id_of(f))), f, fresh.fulls(rest, gone))

def onto.gone(+o: Onto) -> Set():
  Set.from_list(List.append(&2, String, onto.holds(o), onto.forgotten(o)))

# What an update writes into the copy's store: every revision, document,
# forgetting document and payload of the set that the copy does not hold
# and neither side forgets — and so what it counts, as the Rust tool's
# `plan.writes` does.
type Writes is Data:
  Writes{revisions: List<&2, Main.Full>, documents: List<&2, Store.Doc>, forgetting: List<&2, Store.Doc>, payloads: List<&2, T.Split>}

def onto.writes(+p: Plan, +o: Onto) -> Writes:
  +gone = onto.gone(o)
  Writes{fresh.fulls(plan.revisions(p), gone), fresh.docs(plan.documents(p), gone), fresh.docs(plan.forgetting(p), gone), fresh.splits(plan.payloads(p), gone)}

def writes.revisions(w: Writes) -> List<&2, Main.Full>:
  match w:
    case Writes{r, d, f, y}:
      r

def writes.documents(w: Writes) -> List<&2, Store.Doc>:
  match w:
    case Writes{r, d, f, y}:
      d

def writes.forgetting(w: Writes) -> List<&2, Store.Doc>:
  match w:
    case Writes{r, d, f, y}:
      f

def writes.payloads(w: Writes) -> List<&2, T.Split>:
  match w:
    case Writes{r, d, f, y}:
      y

def writes.counts(w: Writes) -> Counts:
  match w:
    case Writes{r, d, f, y}:
      Counts{List.length(&2, Main.Full, r), List.length(&2, Store.Doc, d), List.length(&2, T.Split, y), List.length(&2, Store.Doc, f)}

def onto.counts(+p: Plan, +o: Onto) -> Counts:
  writes.counts(onto.writes(p, o))

# `stems_around`: a revision the copy holds keeps the stem it was written
# under, and a newcomer — in digest order — takes the name `record` would
# give it beside everything the copy holds and every newcomer named before.
def named.of(f: Main.Full) -> Naming.Named:
  match f:
    case Main.Full{id, c, parents, supersedes, a, w, rb, rv, facts, m}:
      Naming.Named{w, m, c}

def stems.around(fs: List<&2, Main.Full>, +held: List<&2, T.Split>, +existing: List<&2, Naming.Named>) -> List<&2, T.Split>:
  match fs:
    case Nil{}:
      Nil{}
    case Main.Full{+id, +c, parents, supersedes, a, +w, rb, rv, facts, +m} <> +rest:
      +kept = Arrange.lookup(held, id)
      T.Split{id, Maybe.default(&2, String, kept, Naming.stem(w, m, c, id, existing))} <> stems.around(rest, held, Bool.pick(List<&2, Naming.Named>, Maybe.is_some(&2, String, kept), existing, Naming.Named{w, m, c} <> existing))

def keep.unretired(rs: List<&2, T.Split>, +retired: Set()) -> List<&2, T.Split>:
  match rs:
    case Nil{}:
      Nil{}
    case T.Split{+path, +text} <> rest:
      Tree.keep(~T.Split, Bool.not(Arrange.has(retired, path)), T.Split{path, text}, keep.unretired(rest, retired))

def rules.unstated(rs: List<&2, Receive.Ruled>, +stated: Set()) -> List<&2, Receive.Ruled>:
  match rs:
    case Nil{}:
      Nil{}
    case +r <> rest:
      Tree.keep(~Receive.Ruled, Bool.not(Arrange.has(stated, ruled.line(r))), r, rules.unstated(rest, stated))

def rule.labels(rs: List<&2, T.Split>) -> List<&2, String>:
  match rs:
    case Nil{}:
      Nil{}
    case T.Split{+path, t} <> rest:
      Receive.skipped_file(path) <> rule.labels(rest)

# The rule files a copy is given: every shared rule it does not state yet,
# under `Rule::label`'s name, a rule's digest where a file there has it.
def rules.added(+p: Plan, +cst: Prune.Stored, +retired: Set()) -> List<&2, T.Split>:
  +kept = keep.unretired(Receive.stored.rules(cst), retired)
  +stated = Set.from_list(rules.lines(Receive.ruled(kept)))
  Receive.rules.written(rules.unstated(plan.rules(p), stated), Set.from_list(rule.labels(kept)), Nil{}, Nil{})

# The folder, caught up
# ---------------------
#
# `update::plan_at` over a folder that holds something: what stands at each
# path the tree places is kept where it is already that, replaced where
# some revision of the copy records it, and refused where nothing does —
# the folder's own work is never written over — and what stands at a path
# the tree does not place goes where some revision records it. A copy an
# export left untouched, and is about to take something away from, is
# rewritten whole.

# What the walk found at one path.
type Seen is Data:
  Seen.File{path: String, digest: String, runs: Bool}
  Seen.Link{path: String, target: String}

# What stands at a path the walk did not offer.
type Probe is Data:
  Probe.Nothing{}
  Probe.Dir{}
  Probe.Other{}

# The contents and link targets some revision records at one path.
type Rec is Data:
  Rec{path: String, digests: List<&2, String>, links: List<&2, String>}

type Step is Data:
  Step.Keep{}
  Step.Write{put: Put, replaces: Bool}
  Step.Link{put: Put}
  Step.Mode{path: String, runs: Bool}
  Step.Refuse{path: String, because: String}

def UNRECORDED() -> String:
  "it holds work nothing has recorded"

def seen.path(s: Seen) -> String:
  match s:
    case Seen.File{p, d, r}:
      p
    case Seen.Link{p, t}:
      p

def seen.find(ss: List<&2, Seen>, +path: String) -> Maybe<&2, Seen>:
  match ss:
    case Nil{}:
      None{}
    case +s <> rest:
      Bool.pick(Maybe<&2, Seen>, String.eq(seen.path(s), path), Some{s}, seen.find(rest, path))

def rec.find(rs: List<&2, Rec>, +path: String) -> Maybe<&2, Rec>:
  match rs:
    case Nil{}:
      None{}
    case Rec{+p, +ds, +ls} <> rest:
      Bool.pick(Maybe<&2, Rec>, String.eq(p, path), Some{Rec{p, ds, ls}}, rec.find(rest, path))

def rec.digests(r: Maybe<&2, Rec>) -> List<&2, String>:
  match r:
    case None{}:
      Nil{}
    case Some{Rec{p, ds, ls}}:
      ds

def rec.links(r: Maybe<&2, Rec>) -> List<&2, String>:
  match r:
    case None{}:
      Nil{}
    case Some{Rec{p, ds, ls}}:
      ls

# Whether bytes at a path may be written over: some revision records them,
# or the folder is the export's own output and wholly its to rewrite.
def recorded(+whole: Bool, +rs: List<&2, Rec>, +path: String, +digest: String) -> Bool:
  Bool.or(whole, Rev.member(rec.digests(rec.find(rs, path)), digest))

def recorded.link(+whole: Bool, +rs: List<&2, Rec>, +path: String, +target: String) -> Bool:
  Bool.or(whole, Rev.member(rec.links(rec.find(rs, path)), target))

def put.digest(p: Put) -> String:
  match p:
    case Put.Text{path, +text, r}:
      Sha.digest(Utf8.encode(text))
    case Put.Bytes{path, f, d, r}:
      d
    case Put.Link{path, t}:
      SNil{}

def put.runs(p: Put) -> Bool:
  match p:
    case Put.Text{path, t, r}:
      r
    case Put.Bytes{path, f, d, r}:
      r
    case Put.Link{path, t}:
      False{}

def put.target(p: Put) -> String:
  match p:
    case Put.Link{path, t}:
      t
    case _:
      SNil{}

def is.link(p: Put) -> Bool:
  match p:
    case Put.Link{path, t}:
      True{}
    case _:
      False{}

def step.absent(+put: Put, +path: String, pr: Probe, link: Bool) -> Step:
  match pr:
    case Probe.Nothing{}:
      Bool.pick(Step, link, Step.Link{put}, Step.Write{put, False{}})
    case Probe.Dir{}:
      Step.Refuse{path, "a directory stands there"}
    case Probe.Other{}:
      Bool.pick(Step, link, Step.Refuse{path, UNRECORDED()}, Step.Refuse{path, "something stands there the walk did not offer"})

def step.same(+path: String, same: Bool, held: Bool, +wanted: Bool, over: Step) -> Step:
  match same:
    case True{}:
      Bool.pick(Step, Bool.xor(held, wanted), Step.Mode{path, wanted}, Step.Keep{})
    case False{}:
      over

# One path the tree places, against what stands there.
def step.held(+put: Put, +path: String, +link: Bool, s: Maybe<&2, Seen>, pr: Probe, +whole: Bool, +rs: List<&2, Rec>) -> Step:
  match s:
    case None{}:
      step.absent(put, path, pr, link)
    case Some{Seen.Link{p, +t}}:
      Bool.pick(Step, link,
        Bool.pick(Step, String.eq(t, put.target(put)), Step.Keep{}, Step.Link{put}),
        Step.Refuse{path, "a symbolic link stands there"})
    case Some{Seen.File{p, +d, runs}}:
      +over = Bool.pick(Step, recorded(whole, rs, path, d), Bool.pick(Step, link, Step.Link{put}, Step.Write{put, True{}}), Step.Refuse{path, UNRECORDED()})
      Bool.pick(Step, link, over, step.same(path, String.eq(d, put.digest(put)), runs, put.runs(put), over))

def step.put(+put: Put, +path: String, s: Maybe<&2, Seen>, pr: Probe, +whole: Bool, +rs: List<&2, Rec>) -> Step:
  step.held(put, path, is.link(put), s, pr, whole, rs)

def probe.of(dir: Bool, other: Bool) -> Probe:
  match dir other:
    case True{} _:
      Probe.Dir{}
    case False{} True{}:
      Probe.Other{}
    case False{} False{}:
      Probe.Nothing{}

def step.of(o: Outcome, +ss: List<&2, Seen>, +dirs: Set(), +others: Set(), +whole: Bool, +rs: List<&2, Rec>) -> Step:
  match o:
    case Outcome.Refused{p, b}:
      Step.Refuse{p, b}
    case Outcome.Laid{+put}:
      +path = put.path(put)
      step.put(put, path, seen.find(ss, path), probe.of(Arrange.has(dirs, path), Arrange.has(others, path)), whole, rs)

def steps(os: List<&2, Outcome>, +ss: List<&2, Seen>, +dirs: Set(), +others: Set(), +whole: Bool, +rs: List<&2, Rec>) -> List<&2, Step>:
  match os:
    case Nil{}:
      Nil{}
    case o <> rest:
      step.of(o, ss, dirs, others, whole, rs) <> steps(rest, ss, dirs, others, whole, rs)

# What stands at a path the tree does not place goes where some revision
# records it; anything else stays, unmentioned.
def seen.gone(s: Seen, +whole: Bool, +rs: List<&2, Rec>) -> Bool:
  match s:
    case Seen.File{+p, +d, r}:
      recorded(whole, rs, p, d)
    case Seen.Link{+p, +t}:
      recorded.link(whole, rs, p, t)

def removes(ss: List<&2, Seen>, +placed: Set(), +whole: Bool, +rs: List<&2, Rec>) -> List<&2, String>:
  match ss:
    case Nil{}:
      Nil{}
    case +s <> rest:
      +p = seen.path(s)
      Tree.keep(~String, Bool.and(Bool.not(Arrange.has(placed, p)), seen.gone(s, whole, rs)), p, removes(rest, placed, whole, rs))

def steps.refused(ss: List<&2, Step>) -> List<&2, T.Split>:
  match ss:
    case Nil{}:
      Nil{}
    case Step.Refuse{p, b} <> rest:
      T.Split{p, b} <> steps.refused(rest)
    case s <> rest:
      steps.refused(rest)

def steps.settled(ss: List<&2, Step>) -> Bool:
  match ss:
    case Nil{}:
      True{}
    case Step.Keep{} <> rest:
      steps.settled(rest)
    case s <> rest:
      False{}

# A path the walk could not offer refuses every path the tree places at or
# beneath it.
def beneath(+held: String, +path: String) -> Bool:
  Bool.or(String.eq(held, path), String.starts_with(held, path ++ "/"))

def refused.walk.one(ps: List<&2, String>, +path: String, +because: String) -> List<&2, T.Split>:
  match ps:
    case Nil{}:
      Nil{}
    case +h <> rest:
      Tree.keep(~T.Split, beneath(h, path), T.Split{h, "the folder cannot offer what stands at " ++ path ++ ": " ++ because}, refused.walk.one(rest, path, because))

def refused.walk(+ps: List<&2, String>, ws: List<&2, T.Split>) -> List<&2, T.Split>:
  match ws:
    case Nil{}:
      Nil{}
    case T.Split{+p, +b} <> rest:
      List.append(&2, T.Split, refused.walk.one(ps, p, b), refused.walk(ps, rest))

# The folder's plan: every step, every path to remove, or every path in the
# way and why.
type Caught is Data:
  Caught{steps: List<&2, Step>, removes: List<&2, String>}

def caught.of(+ss: List<&2, Step>, +rm: List<&2, String>, refused: List<&2, T.Split>) -> Result<&2, &2, Main.Refused, Caught>:
  match refused:
    case Nil{}:
      Done{Caught{ss, rm}}
    case +some:
      Fail{Main.Refused{1, "the folder cannot take this tree whole, so nothing was written:" ++ refusal.lines(splits.dedup(List.sort(~T.Split, ~(a => b => split_le(a, b)), some)))}}

def caught.r(+t: Tree.Tree(), +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +id: String, +pays: List<&2, T.Split>, +bs: List<&2, Prune.Body>, +rules: List<&2, Folder.Scope>, +seen: List<&2, Seen>, +walk: List<&2, T.Split>, +dirs: Set(), +others: Set(), +whole: Bool, +rs: List<&2, Rec>) -> Result<&2, &2, Main.Refused, Caught>:
  +ps = placed(t)
  +names = placed.paths(ps)
  +ss = steps(lay(ps, t, fs, ds, id, pays, bs), seen, dirs, others, whole, rs)
  caught.of(ss, removes(seen, Set.from_list(names), whole, rs), List.concat(&2, T.Split, [refused.tree(ps, Set.from_list(directories(ps)), rules), refused.walk(names, walk), steps.refused(ss)]))

# Whether the folder holds exactly what a revision records there: nothing
# to write, link, set or remove, and nothing in the way.
def caught.settled(r: Result<&2, &2, Main.Refused, Caught>) -> Bool:
  match r:
    case Fail{e}:
      False{}
    case Done{Caught{ss, rm}}:
      Bool.and(steps.settled(ss), List.is_empty(&2, String, rm))

# What a law says of the folder's plan
# ------------------------------------

def held.digest(s: Maybe<&2, Seen>) -> Maybe<&2, String>:
  match s:
    case Some{Seen.File{p, d, r}}:
      Some{d}
    case _:
      None{}

# Whether some revision's record of this path holds these bytes, or this
# link: said of the records themselves, whichever of them it is.
def recs.hold(rs: List<&2, Rec>, +path: String, +d: String) -> Bool:
  match rs:
    case Nil{}:
      False{}
    case Rec{+p, ds, ls} <> rest:
      Bool.or(Bool.and(String.eq(p, path), Rev.member(ds, d)), recs.hold(rest, path, d))

def recs.link(rs: List<&2, Rec>, +path: String, +t: String) -> Bool:
  match rs:
    case Nil{}:
      False{}
    case Rec{+p, ds, ls} <> rest:
      Bool.or(Bool.and(String.eq(p, path), Rev.member(ls, t)), recs.link(rest, path, t))

# Whether what stands at a path may be written over: the folder is the
# export's own output, or some revision records it there.
def over.ok(+whole: Bool, +rs: List<&2, Rec>, +path: String, h: Maybe<&2, String>) -> Bool:
  match h:
    case None{}:
      True{}
    case Some{+d}:
      Bool.or(whole, recs.hold(rs, path, d))

def seen.recorded(s: Seen, +whole: Bool, +rs: List<&2, Rec>) -> Bool:
  match s:
    case Seen.File{+p, +d, r}:
      Bool.or(whole, recs.hold(rs, p, d))
    case Seen.Link{+p, +t}:
      Bool.or(whole, recs.link(rs, p, t))

# A step that writes or links over a regular file lands only where some
# revision records what the file holds: the folder's own work is never
# written over.
def step.safe(s: Step, +ss: List<&2, Seen>, +whole: Bool, +rs: List<&2, Rec>) -> Bool:
  match s:
    case Step.Write{+put, r}:
      over.ok(whole, rs, put.path(put), held.digest(seen.find(ss, put.path(put))))
    case Step.Link{+put}:
      over.ok(whole, rs, put.path(put), held.digest(seen.find(ss, put.path(put))))
    case _:
      True{}

def steps.safe(xs: List<&2, Step>, +ss: List<&2, Seen>, +whole: Bool, +rs: List<&2, Rec>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case x <> rest:
      Bool.and(step.safe(x, ss, whole, rs), steps.safe(rest, ss, whole, rs))

# Whether the walk found something at this path that some revision
# records, or that is the export's own to rewrite.
def witness(ss: List<&2, Seen>, +p: String, +whole: Bool, +rs: List<&2, Rec>) -> Bool:
  match ss:
    case Nil{}:
      False{}
    case +s <> rest:
      Bool.or(Bool.and(String.eq(seen.path(s), p), seen.recorded(s, whole, rs)), witness(rest, p, whole, rs))

def removed.ok(ps: List<&2, String>, +ss: List<&2, Seen>, +whole: Bool, +rs: List<&2, Rec>) -> Bool:
  match ps:
    case Nil{}:
      True{}
    case +p <> rest:
      Bool.and(witness(ss, p, whole, rs), removed.ok(rest, ss, whole, rs))

# What revisions record at one path
# ---------------------------------

# Every file some revision put at this path.
def placed.at(fs: List<&2, Tree.Fact>, +path: String) -> List<&2, String>:
  match fs:
    case Nil{}:
      Nil{}
    case Tree.Fact{+f, +r} <> rest:
      Tree.keep(~String, String.eq(r, path), f, placed.at(rest, path))

def ever.at(fs: List<&2, Main.Full>, +path: String) -> List<&2, String>:
  match fs:
    case Nil{}:
      Nil{}
    case +f <> rest:
      +hs = Main.facts_of(f)
      List.concat(&2, String, [placed.at(Tree.facts_of(hs, "add"), path), placed.at(Tree.facts_of(hs, "move"), path), ever.at(rest, path)])

# Whether a revision says anything of a file's content: it adds it, edits
# it, states it whole, or joins more than one parent.
def touches(+f: Main.Full, +file: String) -> Bool:
  +hs = Main.facts_of(f)
  Bool.or(Bool.or(Rev.member(Rev.files_of(hs, "add"), file), Rev.member(Rev.files_of(hs, "edit"), file)),
    Bool.or(Bool.or(Rev.member(Rev.files_of(hs, "text"), file), Rev.member(Rev.files_of(hs, "bytes"), file)), Nat.is_lt(1n, List.length(&2, String, Main.parents_of(f)))))

def links.stated(+f: Main.Full, +file: String) -> Bool:
  Rev.member(Rev.files_of(Main.facts_of(f), "link"), file)

def rec.items(r: Result<&2, &2, String, List<&2, Ops.Item>>) -> Maybe<&2, String>:
  match r:
    case Fail{e}:
      None{}
    case Done{items}:
      Some{Sha.digest(Utf8.encode(Ops.text(items)))}

def rec.entry(+fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +cs: List<&2, Main.Contents>, +file: String, +id: String, e: Maybe<&2, Tree.Entry>) -> Maybe<&2, String>:
  match e:
    case None{}:
      None{}
    case Some{Tree.Entry{f, p, kind, payload, target, mode}}:
      match kind:
        case Tree.Whole{}:
          payload
        case Tree.Lines{}:
          rec.items(Main.content.found(fs, ds, id, file, Main.content_of(cs, id)))
        case Tree.Link{}:
          None{}

def rec.tree(+fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +cs: List<&2, Main.Contents>, +file: String, +id: String, t: Result<&2, &2, Main.Refused, Tree.Tree()>) -> Maybe<&2, String>:
  match t:
    case Fail{e}:
      None{}
    case Done{+tree}:
      rec.entry(fs, ds, cs, file, id, Tree.lookup(tree, file))

def rec.spelled(+tree: Tree.Tree(), g: Tree.Target, at: Maybe<&2, String>) -> Maybe<&2, String>:
  match at:
    case None{}:
      None{}
    case Some{+a}:
      Some{Main.materialise(tree, a, g)}

def rec.target(+tree: Tree.Tree(), +file: String, e: Maybe<&2, Tree.Entry>) -> Maybe<&2, String>:
  match e:
    case None{}:
      None{}
    case Some{Tree.Entry{f, p, kind, payload, target, mode}}:
      match target:
        case None{}:
          None{}
        case Some{g}:
          rec.spelled(tree, g, Tree.path(tree, file))

def rec.link(+file: String, t: Result<&2, &2, Main.Refused, Tree.Tree()>) -> Maybe<&2, String>:
  match t:
    case Fail{e}:
      None{}
    case Done{+tree}:
      rec.target(tree, file, Tree.lookup(tree, file))

def rec.join(d: Maybe<&2, String>, l: Maybe<&2, String>, r: Rec) -> Rec:
  match r:
    case Rec{p, ds, ls}:
      Rec{p, maybe.push(d, ds), maybe.push(l, ls)}

def rec.content(touch: Bool, +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +cs: List<&2, Main.Contents>, +file: String, +id: String, +tree: Tree.Tree()) -> Maybe<&2, String>:
  match touch:
    case True{}:
      rec.entry(fs, ds, cs, file, id, Tree.lookup(tree, file))
    case False{}:
      None{}

def rec.laid(link: Bool, +file: String, +tree: Tree.Tree()) -> Maybe<&2, String>:
  match link:
    case True{}:
      rec.target(tree, file, Tree.lookup(tree, file))
    case False{}:
      None{}

def rec.at(t: Result<&2, &2, Main.Refused, Tree.Tree()>, +touch: Bool, +link: Bool, +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +cs: List<&2, Main.Contents>, +file: String, +id: String, r: Rec) -> Rec:
  match t:
    case Fail{e}:
      r
    case Done{+tree}:
      rec.join(rec.content(touch, fs, ds, cs, file, id, tree), rec.laid(link, file, tree), r)

def rec.when(any: Bool, +touch: Bool, +link: Bool, +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +cs: List<&2, Main.Contents>, +file: String, +id: String, r: Rec) -> Rec:
  match any:
    case True{}:
      rec.at(Main.tree.r(fs, id), touch, link, fs, ds, cs, file, id, r)
    case False{}:
      r

# What each revision says of a file: its content where it says anything of
# it, and the link it laid where it states one.
def rec.file(revs: List<&2, Main.Full>, +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +cs: List<&2, Main.Contents>, +file: String) -> Rec:
  match revs:
    case Nil{}:
      Rec{SNil{}, Nil{}, Nil{}}
    case +f <> rest:
      +touch = touches(f, file)
      +link = links.stated(f, file)
      rec.when(Bool.or(touch, link), touch, link, fs, ds, cs, file, Main.id_of(f), rec.file(rest, fs, ds, cs, file))

def rec.merge(a: Rec, b: Rec) -> Rec:
  match a b:
    case Rec{p, ds, ls} Rec{q, es, ms}:
      Rec{p, List.append(&2, String, ds, es), List.append(&2, String, ls, ms)}

def rec.files(files: List<&2, String>, +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +path: String) -> Rec:
  match files:
    case Nil{}:
      Rec{path, Nil{}, Nil{}}
    case +file <> rest:
      rec.merge(rec.files(rest, fs, ds, path), rec.file(fs, fs, ds, Main.contents.go(List.reverse(&2, Main.Full, Main.presentation(fs)), ds, file, Nil{}), file))

def recs(ps: List<&2, String>, +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>) -> List<&2, Rec>:
  match ps:
    case Nil{}:
      Nil{}
    case +p <> rest:
      rec.files(Main.sorted_distinct(ever.at(fs, p)), fs, ds, p) <> recs(rest, fs, ds)

def seen.paths(ss: List<&2, Seen>) -> List<&2, String>:
  match ss:
    case Nil{}:
      Nil{}
    case s <> rest:
      seen.path(s) <> seen.paths(rest)

def ever.all(ps: List<&2, String>, +fs: List<&2, Main.Full>) -> List<&2, String>:
  match ps:
    case Nil{}:
      Nil{}
    case +p <> rest:
      List.append(&2, String, ever.at(fs, p), ever.all(rest, fs))

def origin.fulls(+st: Prune.Stored) -> List<&2, Main.Full>:
  Arrange.distinct(Prune.fulls(Arrange.revision_docs(Receive.stored.docs(st))))

# What the laws say of an export
# ------------------------------

# A file of the store holding a digest.
def split.held(ss: List<&2, T.Split>, +path: String, +digest: String) -> Bool:
  match ss:
    case Nil{}:
      False{}
    case T.Split{+p, +d} <> rest:
      Bool.or(Bool.and(String.eq(p, path), String.eq(d, digest)), split.held(rest, path, digest))

def doc.has(ds: List<&2, Store.Doc>, +id: String) -> Bool:
  match ds:
    case Nil{}:
      False{}
    case Store.Doc{p, +i, n, t} <> rest:
      Bool.or(String.eq(i, id), doc.has(rest, id))

def docs.from(xs: List<&2, Store.Doc>, +ds: List<&2, Store.Doc>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Store.Doc{p, +i, n, t} <> rest:
      Bool.and(doc.has(ds, i), docs.from(rest, ds))

def pays.from(ys: List<&2, T.Split>, +ps: List<&2, T.Split>) -> Bool:
  match ys:
    case Nil{}:
      True{}
    case T.Split{+p, +d} <> rest:
      Bool.and(split.held(ps, p, d), pays.from(rest, ps))

# A copy is assembled from this store's own files: every document and
# forgetting document it carries is one this store holds under that
# digest, and every payload is a file of this store holding it.
def plan.from(p: Plan, +ds: List<&2, Store.Doc>, +ps: List<&2, T.Split>) -> Bool:
  match p:
    case Plan{r, docs, pays, forg, paths, rs, w, n, res}:
      Bool.and(docs.from(docs, ds), Bool.and(pays.from(pays, ps), docs.from(forg, ds)))

# Where an export writes: nowhere yet, or a directory holding nothing, gets
# a fresh copy, and only a directory holding a store is updated.
def lst.empty(l: Lst) -> Bool:
  match l:
    case Lst.Absent{}:
      True{}
    case Lst.Unreadable{m}:
      False{}
    case Lst.Listed{+tx}:
      String.is_empty(tx)

def dest.as(+l: Lst, +store: Bool, dd: Dest) -> Bool:
  match dd:
    case Dest.Fresh{}:
      lst.empty(l)
    case Dest.Copy{}:
      Bool.and(store, Bool.not(lst.empty(l)))

# Where an export writes: a fresh copy only where nothing is or nothing is
# held, and an update only into a directory holding something that is a
# store.
def dest.ok(+l: Lst, +store: Bool, r: Result<&2, &2, Main.Refused, Dest>) -> Bool:
  match r:
    case Fail{e}:
      True{}
    case Done{dd}:
      dest.as(l, store, dd)

# Whether some revision of this store names a digest as a parent, or as
# one it supersedes.
def named.edge(fs: List<&2, Main.Full>, +id: String) -> Bool:
  match fs:
    case Nil{}:
      False{}
    case Main.Full{i, c, +parents, +supersedes, a, w, rb, rv, facts, m} <> rest:
      Bool.or(Bool.or(Rev.member(parents, id), Rev.member(supersedes, id)), named.edge(rest, id))

# Whether this store has heard of every revision a copy holds: it holds
# each, or some revision of it names each.
def heard.all(cfs: List<&2, Main.Full>, +fs: List<&2, Main.Full>) -> Bool:
  match cfs:
    case Nil{}:
      True{}
    case +f <> rest:
      Bool.and(Bool.or(Rev.member(Main.ids(fs), Main.id_of(f)), named.edge(fs, Main.id_of(f))), heard.all(rest, fs))

# Whether a file of the store listed holds this digest.
def split.has(ss: List<&2, T.Split>, +d: String) -> Bool:
  match ss:
    case Nil{}:
      False{}
    case T.Split{p, +x} <> rest:
      Bool.or(String.eq(x, d), split.has(rest, d))

def body.has(bs: List<&2, Prune.Body>, +d: String) -> Bool:
  match bs:
    case Nil{}:
      False{}
    case Prune.Body{p, +i, ok, f} <> rest:
      Bool.or(String.eq(i, d), body.has(rest, d))

# Whether the copy's store holds a file hashing to this digest: a revision,
# a document, or a payload.
def copy.has(+cst: Prune.Stored, +d: String) -> Bool:
  Bool.or(split.has(stored.revs(cst), d), Bool.or(body.has(Receive.stored.bodies(cst), d), split.has(Receive.stored.payloads(cst), d)))

# Whether an update writes a file hashing to this digest into the copy.
def writes.has(w: Writes, +d: String) -> Bool:
  match w:
    case Writes{rs, ds, fs, ys}:
      Bool.or(Rev.member(Main.ids(rs), d), Bool.or(doc.has(ds, d), Bool.or(doc.has(fs, d), split.has(ys, d))))

# Every digest the set names: its revisions, documents, forgetting
# documents and payloads.
def set.named(p: Plan) -> List<&2, String>:
  match p:
    case Plan{r, d, y, f, paths, rs, w, n, res}:
      List.concat(&2, String, [Main.ids(r), doc.ids(d), doc.ids(f), split.digests(y)])

# What the host's listing of a directory says of one entry (`Store.folder`):
# a directory, a file with whether it runs and its size, a link and where
# it points, or anything else.
type Listed is Data:
  Listed.Dir{name: String}
  Listed.File{runs: Bool, size: String, name: String}
  Listed.Link{name: String, target: String}
  Listed.Other{name: String}

# One entry's lines, then the rest of the listing, as the host writes them:
# `d <name>`, `f <x> <size> <name>`, `l <name>` and its target on the next
# line, `o <name>`.
def listed.then(e: Listed, +tail: String) -> String:
  match e:
    case Listed.Dir{name}:
      "d " ++ (name ++ tail)
    case Listed.File{runs, size, name}:
      "f " ++ (Bool.pick(String, runs, "1", "0") ++ (" " ++ (size ++ (" " ++ (name ++ tail)))))
    case Listed.Link{name, target}:
      "l " ++ (name ++ SCon{'\n', target ++ tail})
    case Listed.Other{name}:
      "o " ++ (name ++ tail)

def listed.more(es: List<&2, Listed>) -> String:
  match es:
    case Nil{}:
      SNil{}
    case e <> rest:
      SCon{'\n', listed.then(e, listed.more(rest))}

# A directory's listing: an entry a line, joined by newlines.
def listing(es: List<&2, Listed>) -> String:
  match es:
    case Nil{}:
      SNil{}
    case e <> rest:
      listed.then(e, listed.more(rest))

def listed.names(es: List<&2, Listed>) -> List<&2, String>:
  match es:
    case Nil{}:
      Nil{}
    case Listed.Dir{name} <> rest:
      name <> listed.names(rest)
    case Listed.File{r, z, name} <> rest:
      name <> listed.names(rest)
    case Listed.Link{name, t} <> rest:
      name <> listed.names(rest)
    case Listed.Other{name} <> rest:
      name <> listed.names(rest)

def line.char(c: Char) -> Bool:
  Bool.not(Char.is_eq(c, '\n'))

def size.char(+c: Char) -> Bool:
  Bool.not(Bool.or(Char.is_eq(c, ' '), Char.is_eq(c, '\n')))

# What the host spells: no name or target holds a newline, and a size is a
# number, with no space in it either.
def listed.ok(es: List<&2, Listed>) -> Bool:
  match es:
    case Nil{}:
      True{}
    case Listed.Dir{name} <> rest:
      Bool.and(T.all_chars(~(c => line.char(c)), name), listed.ok(rest))
    case Listed.File{r, size, name} <> rest:
      Bool.and(T.all_chars(~(c => size.char(c)), size), Bool.and(T.all_chars(~(c => line.char(c)), name), listed.ok(rest)))
    case Listed.Link{name, target} <> rest:
      Bool.and(T.all_chars(~(c => line.char(c)), name), Bool.and(T.all_chars(~(c => line.char(c)), target), listed.ok(rest)))
    case Listed.Other{name} <> rest:
      Bool.and(T.all_chars(~(c => line.char(c)), name), listed.ok(rest))

# Whether a directory, listed, is a fresh copy's to be made in.
def dest.fresh(r: Result<&2, &2, Main.Refused, Dest>) -> Bool:
  match r:
    case Done{Dest.Fresh{}}:
      True{}
    case _:
      False{}

# Whether a file of `claims/` goes by this name.
def claim.named(cs: List<&2, T.Split>, +l: String) -> Bool:
  match cs:
    case Nil{}:
      False{}
    case T.Split{+x, d} <> rest:
      Bool.or(String.eq(x, l), claim.named(rest, l))

# What `cat` prints of a file at a revision.
def cat.of(r: Result<&2, &2, String, List<&2, Ops.Item>>) -> Maybe<&2, String>:
  match r:
    case Fail{e}:
      None{}
    case Done{items}:
      Some{Ops.text(items)}

def cat.text(+fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +id: String, +file: String) -> Maybe<&2, String>:
  cat.of(Main.content(fs, ds, id, file))

def maybe.is(m: Maybe<&2, String>, +x: String) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{+y}:
      String.eq(y, x)

def bool.same(a: Bool, b: Bool) -> Bool:
  Bool.not(Bool.xor(a, b))

def link.as(target: Maybe<&2, Tree.Target>, +g: String, +t: Tree.Tree(), +path: String) -> Bool:
  match target:
    case None{}:
      False{}
    case Some{tg}:
      String.eq(Main.materialise(t, path, tg), g)

# One file as the tree has it: a file of lines holds what `cat` prints
# there, a file of bytes the payload its entry names, copied from a file of
# the store holding it, a link is spelled as decision 0040 spells it, and
# each runs exactly where the tree says.
def text.as(+text: String, +r: Bool, en: Tree.Entry, +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +id: String) -> Bool:
  match en:
    case Tree.Entry{+f, ep, kind, payload, target, mode}:
      Bool.and(Tree.kind_eq(kind, Tree.Lines{}), Bool.and(maybe.is(cat.text(fs, ds, id, f), text), bool.same(r, runs(mode))))

def bytes.as(+from: String, +d: String, +r: Bool, en: Tree.Entry, +pays: List<&2, T.Split>) -> Bool:
  match en:
    case Tree.Entry{f, ep, kind, payload, target, mode}:
      Bool.and(Tree.kind_eq(kind, Tree.Whole{}), Bool.and(maybe.is(payload, d), Bool.and(split.held(pays, from, d), bool.same(r, runs(mode)))))

def link.entry.as(+g: String, en: Tree.Entry, +t: Tree.Tree(), +path: String) -> Bool:
  match en:
    case Tree.Entry{f, ep, kind, payload, target, mode}:
      Bool.and(Tree.kind_eq(kind, Tree.Link{}), link.as(target, g, t, path))

# One file as the tree has it: a file of lines holds what `cat` prints
# there, a file of bytes the payload its entry names, copied from a file of
# the store holding it, a link is spelled as decision 0040 spells it, and
# each runs exactly where the tree says.
def put.as(pt: Put, +path: String, en: Tree.Entry, +t: Tree.Tree(), +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +id: String, +pays: List<&2, T.Split>) -> Bool:
  match pt:
    case Put.Text{q, +text, r}:
      text.as(text, r, en, fs, ds, id)
    case Put.Bytes{q, +from, +d, r}:
      bytes.as(from, d, r, en, pays)
    case Put.Link{q, +g}:
      link.entry.as(g, en, t, path)

def laid.as(o: Outcome, +path: String, e: Tree.Entry, +t: Tree.Tree(), +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +id: String, +pays: List<&2, T.Split>) -> Bool:
  match o:
    case Outcome.Refused{p, b}:
      True{}
    case Outcome.Laid{put}:
      put.as(put, path, e, t, fs, ds, id, pays)

def placed.as(p: Placed, o: Outcome, +t: Tree.Tree(), +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +id: String, +pays: List<&2, T.Split>) -> Bool:
  match p:
    case Placed{+path, es}:
      match es:
        case e <> Nil{}:
          laid.as(o, path, e, t, fs, ds, id, pays)
        case _:
          True{}

def laid.all(ps: List<&2, Placed>, os: List<&2, Outcome>, +t: Tree.Tree(), +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +id: String, +pays: List<&2, T.Split>) -> Bool:
  match ps os:
    case p <> prest o <> orest:
      Bool.and(placed.as(p, o, t, fs, ds, id, pays), laid.all(prest, orest, t, fs, ds, id, pays))
    case _ _:
      True{}

# A path a folder may be given: outside the store, not a directory another
# of the tree's files needs, and not one a rule covers.
def path.clear(+path: String, +dirs: Set(), +rules: List<&2, Folder.Scope>) -> Bool:
  Bool.and(Bool.not(Arrange.has(dirs, path)), Bool.and(Bool.not(Bool.or(String.eq(path, "history"), String.starts_with(path, "history/"))), Bool.not(Folder.skips(rules, path))))

def puts.clear(ps: List<&2, Put>, +dirs: Set(), +rules: List<&2, Folder.Scope>) -> Bool:
  match ps:
    case Nil{}:
      True{}
    case +p <> rest:
      Bool.and(path.clear(put.path(p), dirs, rules), puts.clear(rest, dirs, rules))

def folder.clear(+t: Tree.Tree(), +rules: List<&2, Folder.Scope>, r: Result<&2, &2, Main.Refused, List<&2, Put>>) -> Bool:
  match r:
    case Fail{e}:
      True{}
    case Done{ps}:
      puts.clear(ps, Set.from_list(directories(placed(t))), rules)

# What a law says of what `export` prints
# ---------------------------------------

def said.keep(b: Bool, +l: String, +n: Nat, rest: List<&2, String>) -> List<&2, String>:
  match b:
    case True{}:
      String.drop(l, n) <> rest
    case False{}:
      rest

# The lines that begin with a prefix, each less the prefix: what the output
# says of one kind of thing, read back.
def said.after(ls: List<&2, String>, +prefix: String) -> List<&2, String>:
  match ls:
    case Nil{}:
      Nil{}
    case +l <> rest:
      said.keep(String.starts_with(l, prefix), l, String.length(prefix), said.after(rest, prefix))

# Whether some file of a tree sits at a path.
def tree.holds(t: Tree.Tree(), +path: String) -> Bool:
  match t:
    case Nil{}:
      False{}
    case +e <> rest:
      Bool.or(String.eq(Tree.entry_path(e), path), tree.holds(rest, path))

# What a law says of a folder caught up
# -------------------------------------

# Whether bytes the folder holds can be had back from a history: `cat` of
# some revision of it reads them for some file of its tree, or its tree
# names them as a file's payload — the question `update` asks of its store.
def given.back(+fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, h: Maybe<&2, String>) -> Bool:
  match h:
    case None{}:
      True{}
    case Some{+d}:
      Upd.recoverable(fs, ds, d)

def step.spares(s: Step, +ss: List<&2, Seen>, +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>) -> Bool:
  match s:
    case Step.Write{+put, r}:
      given.back(fs, ds, held.digest(seen.find(ss, put.path(put))))
    case Step.Link{+put}:
      given.back(fs, ds, held.digest(seen.find(ss, put.path(put))))
    case _:
      True{}

def steps.spare(xs: List<&2, Step>, +ss: List<&2, Seen>, +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case x <> rest:
      Bool.and(step.spares(x, ss, fs, ds), steps.spare(rest, ss, fs, ds))

# A link the walk found is read from the revisions' link statements, as the
# Rust tool reads it, and is not asked about here.
def seen.spared(s: Seen, +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>) -> Bool:
  match s:
    case Seen.File{p, +d, r}:
      Upd.recoverable(fs, ds, d)
    case Seen.Link{p, t}:
      True{}

def spared.at(ss: List<&2, Seen>, +p: String, +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>) -> Bool:
  match ss:
    case Nil{}:
      False{}
    case +s <> rest:
      Bool.or(Bool.and(String.eq(seen.path(s), p), seen.spared(s, fs, ds)), spared.at(rest, p, fs, ds))

def removed.spare(ps: List<&2, String>, +ss: List<&2, Seen>, +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>) -> Bool:
  match ps:
    case Nil{}:
      True{}
    case +p <> rest:
      Bool.and(spared.at(ss, p, fs, ds), removed.spare(rest, ss, fs, ds))

# What the walk would find at the file a fresh export lays: a file of lines
# is the bytes of its text, a file of bytes its payload, each with the mode
# it is given, and a link points where it says.
def put.seen(p: Put) -> Seen:
  match p:
    case Put.Text{path, +text, r}:
      Seen.File{path, Sha.digest(Utf8.encode(text)), r}
    case Put.Bytes{path, f, d, r}:
      Seen.File{path, d, r}
    case Put.Link{path, t}:
      Seen.Link{path, t}

def seen.same(a: Seen, b: Seen) -> Bool:
  match a b:
    case Seen.File{p, d, r} Seen.File{q, e, s}:
      Bool.and(String.eq(p, q), Bool.and(String.eq(d, e), bool.same(r, s)))
    case Seen.Link{p, t} Seen.Link{q, u}:
      Bool.and(String.eq(p, q), String.eq(t, u))
    case _ _:
      False{}

def seen.is(m: Maybe<&2, Seen>, +s: Seen) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{a}:
      seen.same(a, s)

def seen.moded(found: Maybe<&2, Seen>, r: Bool) -> Maybe<&2, Seen>:
  match found:
    case Some{Seen.File{p, d, s}}:
      Some{Seen.File{p, d, r}}
    case other:
      other

# What stands at a path once a step is taken: a write or a link lays its
# file where the file says, a mode is set on the file where the step says,
# and anything else leaves what the walk found.
def step.after(x: Step, +at: String, +found: Maybe<&2, Seen>) -> Maybe<&2, Seen>:
  match x:
    case Step.Write{+put, r}:
      Bool.pick(Maybe<&2, Seen>, String.eq(put.path(put), at), Some{put.seen(put)}, found)
    case Step.Link{+put}:
      Bool.pick(Maybe<&2, Seen>, String.eq(put.path(put), at), Some{put.seen(put)}, found)
    case Step.Mode{+p, r}:
      Bool.pick(Maybe<&2, Seen>, String.eq(p, at), seen.moded(found, r), found)
    case _:
      found

# Each path a fresh export lays a file at, once its step is taken, holds
# that file: the steps and the files pair off one to one.
def lands(ps: List<&2, Put>, xs: List<&2, Step>, +ss: List<&2, Seen>) -> Bool:
  match ps xs:
    case +p <> prest x <> xrest:
      Bool.and(seen.is(step.after(x, put.path(p), seen.find(ss, put.path(p))), put.seen(p)), lands(prest, xrest, ss))
    case Nil{} Nil{}:
      True{}
    case _ _:
      False{}

def put.paths(ps: List<&2, Put>) -> List<&2, String>:
  match ps:
    case Nil{}:
      Nil{}
    case p <> rest:
      put.path(p) <> put.paths(rest)

# The files of a folder, less its links.
def file.puts(ps: List<&2, Put>) -> List<&2, Put>:
  match ps:
    case Nil{}:
      Nil{}
    case Put.Link{path, t} <> rest:
      file.puts(rest)
    case p <> rest:
      p <> file.puts(rest)

def none.of(ps: List<&2, String>, +placed: List<&2, String>) -> Bool:
  match ps:
    case Nil{}:
      True{}
    case +p <> rest:
      Bool.and(Bool.not(Rev.member(placed, p)), none.of(rest, placed))

# The folder's plan against the folder a fresh export lays out: where the
# plan is made, so is the fresh folder, every path of it holds its file once
# the steps are taken, and nothing removed is one of those paths.
def caught.lands(+ss: List<&2, Seen>, r: Result<&2, &2, Main.Refused, Caught>, fresh: Result<&2, &2, Main.Refused, List<&2, Put>>) -> Bool:
  match r fresh:
    case Fail{e} _:
      True{}
    case Done{Caught{xs, rm}} Done{+ps}:
      Bool.and(lands(ps, xs, ss), none.of(rm, put.paths(ps)))
    case Done{c} Fail{e}:
      False{}

# Whether the walk found, at each path of a fresh folder, that path's file.
def holds.all(ps: List<&2, Put>, +ss: List<&2, Seen>) -> Bool:
  match ps:
    case Nil{}:
      True{}
    case +p <> rest:
      Bool.and(seen.is(seen.find(ss, put.path(p)), put.seen(p)), holds.all(rest, ss))

def fresh.held(+ss: List<&2, Seen>, fresh: Result<&2, &2, Main.Refused, List<&2, Put>>) -> Bool:
  match fresh:
    case Fail{e}:
      False{}
    case Done{ps}:
      holds.all(ps, ss)

# Every file the folder's plan writes or links over, and every file it
# removes, holds bytes the history can give back.
def caught.spares(+ss: List<&2, Seen>, +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, r: Result<&2, &2, Main.Refused, Caught>) -> Bool:
  match r:
    case Fail{e}:
      True{}
    case Done{Caught{xs, rm}}:
      Bool.and(steps.spare(xs, ss, fs, ds), removed.spare(rm, ss, fs, ds))


# The whole
# ---------

# The files of lines whose whole text a revision stored: read so they can
# be replayed, as `cat` reads them, since what `operations/` holds under no
# suffix is not read until something names it.
def texts.named(fs: List<&2, Main.Full>) -> List<&2, String>:
  match fs:
    case Nil{}:
      Nil{}
    case +f <> rest:
      List.append(&2, String, fact.rests(Tree.facts_of(Main.facts_of(f), "text")), texts.named(rest))

def texts.read(+r: String, +fs: List<&2, Main.Full>, +id: String) -> IO(List<&2, Store.Doc>):
  Store.fetch(r, Main.sorted_distinct(texts.named(Main.ancestry(fs, id))))

# The copy written, content before the revisions naming it and the folder
# last, out of the copy's own history, as the Rust tool orders it.
def export.write(+r: String, +into: String, +st: Prune.Stored, +fs: List<&2, Main.Full>, +bs: List<&2, Bm.Bookmark>, +id: String, +t: Tree.Tree(), +held: List<&2, Main.Full>, +p: Plan) -> IO(Unit):
  +cr = into ++ "/history"
  +stems = Arrange.stems(held)
  do IO<Unit>:
    filed : List<&2, T.Split> <- Main.refused.io(List<&2, T.Split>, Arrange.operation_names(held, stems))
    +fl : List<&2, T.Split> = filed
    copy.init(cr)
    Receive.written.rules(cr, rules.files(Receive.ruled(Receive.stored.rules(st))))
    Receive.written.names(cr, travel.names(plan.names(p)))
    copied.payloads(r, cr, fl, plan.payloads(p))
    filed.docs(cr, fl, plan.documents(p))
    filed.docs(cr, fl, plan.forgetting(p))
    filed.revisions(cr, stems, Receive.stored.docs(st), held)
    n : Nat <- carried(r, cr, plan.reserved(p))
    texts : List<&2, Store.Doc> <- texts.read(r, fs, id)
    ps : List<&2, Put> <- Main.refused.io(List<&2, Put>, folder.r(t, fs, List.append(&2, Store.Doc, Receive.stored.odocs(st), texts), id, Receive.stored.payloads(st), Receive.stored.bodies(st), scopes(Receive.stored.rules(st), True{})))
    +ps2 : List<&2, Put> = ps
    set : List<&2, String> <- apply(r, into, ps2)
    real : Result<&1, &1, U32 & String, String> <- Store.really(into)
    Arrange.print_lines(List.concat(&2, String, [
      said.counts("exported", "held back", "left", "carried", plan.counts(p), p, n),
      paths.said("wrote  ", put.paths(file.puts(ps2))),
      ["made a copy of " ++ Main.spelled(fs, bs, id) ++ " at " ++ Main.init.said(into, real)]]))

def export.planned(dry: Bool, +r: String, +into: String, +st: Prune.Stored, +fs: List<&2, Main.Full>, +bs: List<&2, Bm.Bookmark>, +id: String, +t: Tree.Tree(), +held: List<&2, Main.Full>, +p: Plan) -> IO(Unit):
  match dry:
    case True{}:
      Arrange.print_lines(said.plan(p, plan.counts(p), Nil{}, 0n, False{}, Main.spelled(fs, bs, id), into))
    case False{}:
      export.write(r, into, st, fs, bs, id, t, held, p)

# Reading the copy
# ----------------

# A copy, read as `receive` reads a side, and not yet opened: whether it
# passes `check` is asked first, as the Rust tool asks it before opening.
def copy.read(+r: String) -> IO(Receive.Side):
  do IO<Receive.Side>:
    st : Prune.Stored <- Prune.read(r)
    bs : List<&2, Bm.Bookmark> <- Main.bookmarks(r)
    listed : List<&2, String> <- Store.claims_paths(r)
    +cl : List<&2, String> = Prune.not_platform(listed)
    stats : List<&2, String> <- Store.stats(r, cl)
    return Receive.Side{r, st, bs, Arrange.zip.stats(cl, stats)}

def stat.digest(cut: Maybe<&2, T.Split>) -> String:
  match cut:
    case None{}:
      SNil{}
    case Some{T.Split{d, n}}:
      d

def found.files(fs: List<&2, Folder.Found>) -> List<&2, String>:
  match fs:
    case Nil{}:
      Nil{}
    case Folder.Found.File{p, r, n} <> rest:
      p <> found.files(rest)
    case Folder.Found.Link{p, t} <> rest:
      found.files(rest)

# What the walk found, each file beside the digest its bytes have.
def seen.build(fs: List<&2, Folder.Found>, stats: List<&2, String>) -> List<&2, Seen>:
  match fs stats:
    case Nil{} _:
      Nil{}
    case Folder.Found.Link{p, t} <> rest _:
      Seen.Link{p, t} <> seen.build(rest, stats)
    case Folder.Found.File{p, r, n} <> rest +st <> more:
      Seen.File{p, stat.digest(T.split_once(st)), r} <> seen.build(rest, more)
    case Folder.Found.File{p, r, n} <> rest Nil{}:
      Seen.File{p, SNil{}, r} <> seen.build(rest, Nil{})

type Looked is Data:
  Looked{seen: List<&2, Seen>, refused: List<&2, T.Split>}

def looked.seen(l: Looked) -> List<&2, Seen>:
  match l:
    case Looked{s, r}:
      s

def looked.refused(l: Looked) -> List<&2, T.Split>:
  match l:
    case Looked{s, r}:
      r

# The folder a copy has, walked through the rules given.
def folder.look(+into: String, +rules: List<&2, Folder.Scope>) -> IO(Looked):
  do IO<Looked>:
    w : Folder.Walked <- Folder.walk.all(into, rules)
    +w2 : Folder.Walked = w
    +found : List<&2, Folder.Found> = Folder.walked.found(w2)
    stats : List<&2, String> <- Store.stats(into, found.files(found))
    return Looked{seen.build(found, stats), Folder.walked.refused(w2)}

# What stands at each path the tree places and the walk did not offer.
type Probed is Data:
  Probed{dirs: List<&2, String>, others: List<&2, String>}

def probed.dirs(p: Probed) -> List<&2, String>:
  match p:
    case Probed{ds, os}:
      ds

def probed.others(p: Probed) -> List<&2, String>:
  match p:
    case Probed{ds, os}:
      os

def probed.push(+p: String, listed: Result<&1, &1, U32 & String, String>, acc: Probed) -> Probed:
  match listed acc:
    case Done{x} Probed{ds, os}:
      Probed{p <> ds, os}
    case Fail{Tuple{code, msg}} Probed{+ds, +os}:
      Bool.pick(Probed, U32.is_eq(code, 2), Probed{ds, os}, Probed{ds, p <> os})

def probes(+into: String, ps: List<&2, String>, acc: Probed) -> IO(Probed):
  match ps:
    case Nil{}:
      IO.pure(Probed, acc)
    case +p <> rest:
      do IO<Probed>:
        listed : Result<&1, &1, U32 & String, String> <- Store.listing_of(into ++ "/" ++ p)
        probes(into, rest, probed.push(p, listed, acc))

def unseen(ps: List<&2, String>, +seen: Set()) -> List<&2, String>:
  match ps:
    case Nil{}:
      Nil{}
    case +p <> rest:
      Tree.keep(~String, Bool.not(Arrange.has(seen, p)), p, unseen(rest, seen))

# What the copy's revisions record at each path the walk found, read from
# the copy: every document the files ever there were said with.
def recs.read(+root: String, +fs: List<&2, Main.Full>, +paths: List<&2, String>) -> IO(List<&2, Rec>):
  +files = Main.sorted_distinct(ever.all(paths, fs))
  do IO<List<&2, Rec>>:
    ds : List<&2, Store.Doc> <- Store.fetch(root, Main.sorted_distinct(Main.wanted_all(fs, files)))
    +ds2 : List<&2, Store.Doc> = ds
    more : List<&2, Store.Doc> <- Store.fetch(root, Main.kept_digests(ds2))
    return recs(paths, fs, List.append(&2, Store.Doc, ds2, more))

def recs.if(asked: Bool, +root: String, +fs: List<&2, Main.Full>, +paths: List<&2, String>) -> IO(List<&2, Rec>):
  match asked:
    case True{}:
      recs.read(root, fs, paths)
    case False{}:
      IO.pure(List<&2, Rec>, Nil{})

# `undisturbed`: whether the copy's folder still holds exactly what its own
# one head records, asked before anything is taken away.
def undisturbed.at(+into: String, +root: String, +cst: Prune.Stored, +cfs: List<&2, Main.Full>, +rules: List<&2, Folder.Scope>, heads: List<&2, String>) -> IO(Bool):
  match heads:
    case +h <> Nil{}:
      do IO<Bool>:
        t : Tree.Tree() <- Main.refused.io(Tree.Tree(), Main.tree.r(cfs, h))
        +tree : Tree.Tree() = t
        l : Looked <- folder.look(into, rules)
        +l2 : Looked = l
        texts : List<&2, Store.Doc> <- texts.read(root, cfs, h)
        rs : List<&2, Rec> <- recs.read(root, cfs, seen.paths(looked.seen(l2)))
        return caught.settled(caught.r(tree, cfs, List.append(&2, Store.Doc, Receive.stored.odocs(cst), texts), h, Receive.stored.payloads(cst), Receive.stored.bodies(cst), rules, looked.seen(l2), looked.refused(l2), Set.new(), Set.new(), False{}, rs))
    case _:
      IO.pure(Bool, False{})

def undisturbed(taking: Bool, +into: String, +root: String, +cst: Prune.Stored, +cfs: List<&2, Main.Full>, +rules: List<&2, Folder.Scope>) -> IO(Bool):
  match taking:
    case True{}:
      undisturbed.at(into, root, cst, cfs, rules, Main.current_heads(Main.history(cfs)))
    case False{}:
      IO.pure(Bool, False{})

# Catching the folder up
# ----------------------

def mode.word(r: Bool) -> String:
  match r:
    case True{}:
      "executable"
    case False{}:
      "plain"

def removed.all(+into: String, ps: List<&2, String>) -> IO(Unit):
  match ps:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case +p <> rest:
      do IO<Unit>:
        w : Result<&1, &1, U32 & String, String> <- Store.removed(into ++ "\n" ++ into ++ "/" ++ p)
        x : String <- io.ok(w)
        removed.all(into, rest)

def write.over(+into: String, +path: String, replaces: Bool) -> IO(Unit):
  match replaces:
    case True{}:
      do IO<Unit>:
        w : Result<&1, &1, U32 & String, String> <- Store.removed(into ++ "/" ++ Arrange.parent_of(path) ++ "\n" ++ into ++ "/" ++ path)
        x : String <- io.ok(w)
        IO.pure(Unit, Unit{})
    case False{}:
      IO.pure(Unit, Unit{})

def write.put(+r: String, +into: String, p: Put, replaces: Bool) -> IO(Unit):
  match p:
    case Put.Text{+path, text, run}:
      do IO<Unit>:
        w : Result<&1, &1, U32 & String, String> <- Store.written(into ++ "/" ++ path ++ "\n" ++ text)
        x : String <- io.ok(w)
        m : Result<&1, &1, U32 & String, String> <- Store.made_runnable(into ++ "/" ++ path ++ "\n" ++ mode.word(run))
        y : String <- io.ok(m)
        IO.pure(Unit, Unit{})
    case Put.Bytes{+path, from, +d, run}:
      do IO<Unit>:
        write.over(into, path, replaces)
        w : Result<&1, &1, U32 & String, String> <- Store.copied(r ++ "/" ++ from ++ "\n" ++ into ++ "/" ++ path ++ "\n" ++ d)
        x : String <- io.ok(w)
        m : Result<&1, &1, U32 & String, String> <- Store.made_runnable(into ++ "/" ++ path ++ "\n" ++ mode.word(run))
        y : String <- io.ok(m)
        IO.pure(Unit, Unit{})
    case Put.Link{path, t}:
      IO.pure(Unit, Unit{})

# The writes, in path order: what each wrote.
def caught.writes(+r: String, +into: String, ss: List<&2, Step>) -> IO(List<&2, String>):
  match ss:
    case Nil{}:
      IO.pure(List<&2, String>, Nil{})
    case Step.Write{+p, replaces} <> rest:
      do IO<List<&2, String>>:
        write.put(r, into, p, replaces)
        more : List<&2, String> <- caught.writes(r, into, rest)
        return put.path(p) <> more
    case s <> rest:
      caught.writes(r, into, rest)

def caught.links(+into: String, ss: List<&2, Step>) -> IO(Unit):
  match ss:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case Step.Link{Put.Link{+path, t}} <> rest:
      do IO<Unit>:
        w : Result<&1, &1, U32 & String, String> <- Store.linked(into ++ "/" ++ path ++ "\n" ++ t)
        x : String <- io.ok(w)
        caught.links(into, rest)
    case s <> rest:
      caught.links(into, rest)

def caught.modes(+into: String, ss: List<&2, Step>) -> IO(Unit):
  match ss:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case Step.Mode{path, run} <> rest:
      do IO<Unit>:
        m : Result<&1, &1, U32 & String, String> <- Store.made_runnable(into ++ "/" ++ path ++ "\n" ++ mode.word(run))
        y : String <- io.ok(m)
        caught.modes(into, rest)
    case s <> rest:
      caught.modes(into, rest)

# `update::apply`: the removals, the writes, the links, the modes. What it
# wrote is what the export says it wrote.
def caught.apply(+r: String, +into: String, c: Caught) -> IO(List<&2, String>):
  match c:
    case Caught{+ss, rm}:
      do IO<List<&2, String>>:
        removed.all(into, rm)
        wrote : List<&2, String> <- caught.writes(r, into, ss)
        caught.links(into, ss)
        caught.modes(into, ss)
        return wrote

# Updating the copy
# -----------------

def names.removed(+cr: String, ns: List<&2, String>) -> IO(Unit):
  match ns:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case n <> rest:
      do IO<Unit>:
        w : Result<&1, &1, U32 & String, String> <- Store.removed(cr ++ "/names\n" ++ cr ++ "/names/" ++ n ++ ".txt")
        x : String <- io.ok(w)
        names.removed(cr, rest)

def claims.fresh(cs: List<&2, T.Split>, +held: Set()) -> List<&2, T.Split>:
  match cs:
    case Nil{}:
      Nil{}
    case T.Split{+l, +d} <> rest:
      Tree.keep(~T.Split, Bool.not(Arrange.has(held, l)), T.Split{l, d}, claims.fresh(rest, held))

def split.labels(ss: List<&2, T.Split>) -> List<&2, String>:
  match ss:
    case Nil{}:
      Nil{}
    case T.Split{l, d} <> rest:
      l <> split.labels(rest)

def cleared.if(b: Bool, +cr: String) -> IO(Unit):
  match b:
    case True{}:
      Prune.cleared(cr)
    case False{}:
      IO.pure(Unit, Unit{})

def tree.paths(+t: Tree.Tree()) -> List<&2, String>:
  Main.sorted_distinct(entry.paths(t))

# `export_onto` for a copy this store made: its rules and bookmarks made
# the origin's, the content and revisions it lacks written, what either
# side forgets destroyed, the folder caught up, and what the set no longer
# names withdrawn — revisions first — with `cache/` cleared after.
def export.update(+r: String, +into: String, +st: Prune.Stored, +fs: List<&2, Main.Full>, +bs: List<&2, Bm.Bookmark>, +id: String, +t: Tree.Tree(), +held: List<&2, Main.Full>, +p: Plan, +c: Receive.Side, +o: Onto) -> IO(Unit):
  +cr = into ++ "/history"
  +cst = Receive.stored.of(c)
  +cfs = origin.fulls(cst)
  +all = onto.all(o)
  +taking = Bool.not(Bool.and(List.is_empty(&2, String, all), List.is_empty(&2, String, onto.destroys(o))))
  +stems = stems.around(held, onto.stems(o), T.map(~Main.Full, ~Naming.Named, ~(f => named.of(f)), cfs))
  +w = onto.writes(p, o)
  +rules = scopes(Receive.stored.rules(st), True{})
  do IO<Unit>:
    whole : Bool <- undisturbed(taking, into, cr, cst, cfs, scopes(Receive.stored.rules(cst), False{}))
    +whole2 : Bool = whole
    Prune.removed(cr, onto.retired(o))
    sk : Result<&1, &1, U32 & String, String> <- Store.swept(cr ++ "/skipped")
    Receive.written.rules(cr, rules.added(p, cst, Set.from_list(onto.retired(o))))
    names.removed(cr, onto.names(o))
    Receive.written.names(cr, travel.names(plan.names(p)))
    filed : List<&2, T.Split> <- Main.refused.io(List<&2, T.Split>, Arrange.operation_names(held, stems))
    +fl : List<&2, T.Split> = filed
    copied.payloads(r, cr, fl, writes.payloads(w))
    filed.docs(cr, fl, writes.documents(w))
    filed.docs(cr, fl, writes.forgetting(w))
    +destroyed : List<&2, String> = Receive.destroyed(Receive.stored.bodies(cst), Receive.stored.payloads(cst), onto.destroys(o))
    Prune.removed(cr, destroyed)
    so : Result<&1, &1, U32 & String, String> <- Store.swept(cr ++ "/operations")
    filed.revisions(cr, stems, Receive.stored.docs(st), writes.revisions(w))
    n : Nat <- carried(r, cr, claims.fresh(plan.reserved(p), Set.from_list(split.labels(Receive.side.claims(c)))))
    l : Looked <- folder.look(into, rules)
    +l2 : Looked = l
    +seen : List<&2, Seen> = looked.seen(l2)
    texts : List<&2, Store.Doc> <- texts.read(r, fs, id)
    pr : Probed <- probes(into, unseen(tree.paths(t), Set.from_list(seen.paths(seen))), Probed{Nil{}, Nil{}})
    +pr2 : Probed = pr
    rs : List<&2, Rec> <- recs.if(Bool.not(whole2), cr, Arrange.distinct(List.append(&2, Main.Full, cfs, held)), seen.paths(seen))
    ct : Caught <- Main.refused.io(Caught, caught.r(t, fs, List.append(&2, Store.Doc, Receive.stored.odocs(st), texts), id, Receive.stored.payloads(st), Receive.stored.bodies(st), rules, seen, looked.refused(l2), Set.from_list(probed.dirs(pr2)), Set.from_list(probed.others(pr2)), whole2, rs))
    wrote : List<&2, String> <- caught.apply(r, into, ct)
    +wrote2 : List<&2, String> = wrote
    Prune.removed(cr, onto.withdraws(o))
    Prune.swept(cr)
    cleared.if(Bool.or(Bool.not(List.is_empty(&2, String, all)), Bool.not(List.is_empty(&2, String, destroyed))), cr)
    real : Result<&1, &1, U32 & String, String> <- Store.really(into)
    Arrange.print_lines(List.concat(&2, String, [
      said.counts("exported", "held back", "left", "carried", onto.counts(p, o), p, n),
      line.if(nonzero(List.length(&2, String, all)), count.line("withdrew", List.length(&2, String, all), "files")),
      line.if(nonzero(List.length(&2, String, destroyed)), count.line("destroyed", List.length(&2, String, destroyed), "forgotten originals")),
      paths.said("wrote  ", wrote2),
      ["updated the copy of " ++ Main.spelled(fs, bs, id) ++ " at " ++ Main.init.said(into, real)]]))

def export.onto.planned(dry: Bool, +r: String, +into: String, +st: Prune.Stored, +fs: List<&2, Main.Full>, +bs: List<&2, Bm.Bookmark>, +id: String, +t: Tree.Tree(), +held: List<&2, Main.Full>, +p: Plan, +c: Receive.Side, +o: Onto) -> IO(Unit):
  match dry:
    case True{}:
      Arrange.print_lines(said.plan(p, onto.counts(p, o), onto.all(o), List.length(&2, String, onto.destroys(o)), True{}, Main.spelled(fs, bs, id), into))
    case False{}:
      export.update(r, into, st, fs, bs, id, t, held, p, c, o)

def export.onto(+dry: Bool, +r: String, +into: String, +st: Prune.Stored, +fs: List<&2, Main.Full>, +bs: List<&2, Bm.Bookmark>, +id: String, +t: Tree.Tree(), +held: List<&2, Main.Full>, +p: Plan) -> IO(Unit):
  do IO<Unit>:
    ok : Bool <- Check.passes(into ++ "/history")
    Main.refused.io(Unit, copy.sound.r(into, ok))
    c : Receive.Side <- copy.read(into ++ "/history")
    +c2 : Receive.Side = c
    +cst : Prune.Stored = Receive.stored.of(c2)
    Main.refused.io(Unit, copy.r(into, fs, origin.fulls(cst)))
    export.onto.planned(dry, r, into, st, fs, bs, id, t, held, p, c2, onto.of(p, Receive.stored.bodies(st), cst, Receive.side.marks(c2)))

def export.dest(d: Dest, +dry: Bool, +r: String, +into: String, +st: Prune.Stored, +fs: List<&2, Main.Full>, +bs: List<&2, Bm.Bookmark>, +id: String, +t: Tree.Tree(), +held: List<&2, Main.Full>, +p: Plan) -> IO(Unit):
  match d:
    case Dest.Fresh{}:
      export.planned(dry, r, into, st, fs, bs, id, t, held, p)
    case Dest.Copy{}:
      export.onto(dry, r, into, st, fs, bs, id, t, held, p)

def export.full(+dry: Bool, +r: String, +into: String, +s: Receive.Side, +fs: List<&2, Main.Full>, +bs: List<&2, Bm.Bookmark>, +id: String, +t: Tree.Tree()) -> IO(Unit):
  +held = Main.ancestry(fs, id)
  +st = Receive.stored.of(s)
  +p = plan.of(held, t, Receive.stored.odocs(st), Receive.stored.payloads(st), Receive.stored.bodies(st), Receive.ruled(Receive.stored.rules(st)), bs, Receive.side.claims(s))
  do IO<Unit>:
    listed : Result<&1, &1, U32 & String, String> <- Store.listing_of(into)
    header : Result<&1, &1, U32 & String, String> <- Store.really(into ++ "/history/historica.txt")
    d : Dest <- Main.refused.io(Dest, dest.r(into, listed, header))
    export.dest(d, dry, r, into, st, fs, bs, id, t, held, p)

# What a written file's bytes hash to when read back, where it is not what
# was written: the folder folded two of the tree's paths onto one file
# (decision 0027), and cannot represent this tree.
def folded(ps: List<&2, Put>, stats: List<&2, String>) -> List<&2, String>:
  match ps stats:
    case +p <> rest +st <> more:
      Tree.keep(~String, Bool.not(String.eq(stat.digest(T.split_once(st)), put.digest(p))), put.path(p), folded(rest, more))
    case _ _:
      Nil{}

def folded.lines(ps: List<&2, String>) -> String:
  match ps:
    case Nil{}:
      SNil{}
    case p <> rest:
      "\n  " ++ p ++ folded.lines(rest)

def folded.r(fs: List<&2, String>) -> Result<&2, &2, Main.Refused, Unit>:
  match fs:
    case Nil{}:
      Done{Unit{}}
    case +some:
      Fail{Main.Refused{1, "this folder folds paths the tree holds apart, and cannot represent it:" ++ folded.lines(some)}}

# What `export --files-only -n` prints: every file it would write, every
# link it would make and where it points, and what it would do.
def said.folder(+ps: List<&2, Put>, +spelled: String, +into: String) -> List<&2, String>:
  List.concat(&2, String, [puts.said(ps), links.said("link    ", ps), ["would write the folder " ++ spelled ++ " has at " ++ into ++ ", and no history beside it"]])

# What it prints having laid the folder out: the files it wrote, the modes
# it set, the links it made, and where the folder is.
def said.laid(+ps: List<&2, Put>, +set: List<&2, String>, +spelled: String, +at: String) -> List<&2, String>:
  List.concat(&2, String, [paths.said("wrote  ", put.paths(file.puts(ps))), modes.said(set), links.said("linked  ", ps), ["the folder " ++ spelled ++ " has, at " ++ at ++ ", and no history beside it"]])

def export.folder(+dry: Bool, +r: String, +into: String, +spelled: String, +ps: List<&2, Put>) -> IO(Unit):
  match dry:
    case True{}:
      Arrange.print_lines(said.folder(ps, spelled, into))
    case False{}:
      do IO<Unit>:
        set : List<&2, String> <- apply(r, into, ps)
        +set2 : List<&2, String> = set
        back : List<&2, String> <- Store.stats(into, put.paths(file.puts(ps)))
        real : Result<&1, &1, U32 & String, String> <- Store.really(into)
        Arrange.print_lines(said.laid(ps, set2, spelled, Main.init.said(into, real)))
        Main.refused.io(Unit, folded.r(folded(file.puts(ps), back)))

def export.files(+dry: Bool, +r: String, +into: String, +s: Receive.Side, +fs: List<&2, Main.Full>, +bs: List<&2, Bm.Bookmark>, +id: String, +t: Tree.Tree()) -> IO(Unit):
  +st = Receive.stored.of(s)
  do IO<Unit>:
    m : Result<&1, &1, U32 & String, String> <- Store.made(into ++ "\n")
    done : String <- Main.init.io(String, m)
    listed : Result<&1, &1, U32 & String, String> <- Store.listing_of(into)
    Main.refused.io(Unit, empty.r(into, listed))
    texts : List<&2, Store.Doc> <- texts.read(r, fs, id)
    ps : List<&2, Put> <- Main.refused.io(List<&2, Put>, folder.r(t, fs, List.append(&2, Store.Doc, Receive.stored.odocs(st), texts), id, Receive.stored.payloads(st), Receive.stored.bodies(st), scopes(Receive.stored.rules(st), False{})))
    +ps2 : List<&2, Put> = ps
    export.folder(dry, r, into, Main.spelled(fs, bs, id), ps2)

def export.which(files: Bool, +dry: Bool, +r: String, +into: String, +s: Receive.Side, +fs: List<&2, Main.Full>, +bs: List<&2, Bm.Bookmark>, +id: String, +t: Tree.Tree()) -> IO(Unit):
  match files:
    case True{}:
      export.files(dry, r, into, s, fs, bs, id, t)
    case False{}:
      export.full(dry, r, into, s, fs, bs, id, t)

def export.of(+r: String, c: ExportCmd) -> IO(Unit):
  match c:
    case ExportCmd{+dry, +files, +dir, target}:
      do IO<Unit>:
        side : Receive.Side <- Receive.side.read(False{}, r)
        +s : Receive.Side = side
        +st : Prune.Stored = Receive.stored.of(s)
        +fs : List<&2, Main.Full> = origin.fulls(st)
        +bs : List<&2, Bm.Bookmark> = Receive.side.marks(s)
        f : Main.Full <- Main.refused.io(Main.Full, Main.resolved.r(fs, bs, Maybe.default(&2, String, target, "head")))
        +id : String = Main.id_of(f)
        here : Result<&1, &1, U32 & String, String> <- Store.really(SNil{})
        base : String <- Main.init.io(String, here)
        +into : String = Main.path_join(base, dir)
        ok : Bool <- Check.passes(r)
        Main.refused.io(Unit, sound.r(ok))
        t : Tree.Tree() <- Main.refused.io(Tree.Tree(), Main.tree.r(fs, id))
        +tree : Tree.Tree() = t
        export.which(files, dry, r, into, s, fs, bs, id, tree)

# The store is found before the words are read, as the Rust tool's
# dispatch finds it.
def export(+args: List<&2, String>) -> IO(Unit):
  do IO<Unit>:
    root : String <- Store.root()
    +r : String = root
    c : ExportCmd <- Main.refused.io(ExportCmd, args.r(args))
    export.of(r, c)
