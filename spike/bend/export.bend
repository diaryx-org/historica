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
import ./folder.bend as Folder
import ./tree.bend as Tree
import ./resolution.bend as Res
import ./notes.bend as Notes
import ./ops.bend as Ops

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

# The counts, the same numbers a dry run and the real thing report: a
# fresh copy writes the whole plan. `verbs` are the three a sentence takes,
# `would export`, `would hold back` and `would leave`, or what they became.
def said.counts(+export: String, +hold: String, +leave: String, +carry: String, p: Plan, +carried: Nat) -> List<&2, String>:
  match p:
    case Plan{+revs, +docs, +pays, +forg, paths, +rules, +w, Travel{+ns, +wn, +y}, res}:
      List.concat(&2, String, [
        [count.line(export, List.length(&2, Main.Full, revs), "revisions"),
         count.line(export, List.length(&2, Store.Doc, docs), "operation documents"),
         count.line(export, List.length(&2, T.Split, pays), "payloads")],
        line.if(nonzero(List.length(&2, Store.Doc, forg)), count.line(export, List.length(&2, Store.Doc, forg), "forgetting documents")),
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

# What `export -n` prints.
def said.plan(+p: Plan, +spelled: String, +into: String) -> List<&2, String>:
  List.concat(&2, String, [
    said.counts("would export", "would hold back", "would leave", "would carry", p, List.length(&2, T.Split, plan.reserved(p))),
    paths.said("write  ", plan.paths(p)),
    ["would make a copy of " ++ spelled ++ " at " ++ into]])

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

# What the folder was given, as the Rust tool's `update::apply` reports it:
# the files written, the modes set, the links made.
type Applied is Data:
  Applied{wrote: List<&2, String>, set: List<&2, String>}

def applied.push(+path: String, set: Bool, a: Applied) -> Applied:
  match a:
    case Applied{w, +s}:
      Applied{path <> w, Bool.pick(List<&2, String>, set, path <> s, s)}

def io.ok(r: Result<&1, &1, U32 & String, String>) -> IO(String):
  Main.name.io(r)

def runnable(+at: String, r: Bool) -> IO(Bool):
  match r:
    case False{}:
      IO.pure(Bool, False{})
    case True{}:
      do IO<Bool>:
        m : Result<&1, &1, U32 & String, String> <- Store.made_runnable(at)
        said : String <- io.ok(m)
        return String.eq(said, "set")

# The files, in path order, then the links: each written where nothing
# stood, and made runnable where the tree says it can be run.
def apply.files(+root: String, +into: String, ps: List<&2, Put>, a: Applied) -> IO(Applied):
  match ps:
    case Nil{}:
      IO.pure(Applied, a)
    case Put.Text{+path, text, r} <> rest:
      do IO<Applied>:
        w : Result<&1, &1, U32 & String, String> <- Store.filed(into ++ "/" ++ path ++ "\n" ++ text)
        x : String <- io.ok(w)
        set : Bool <- runnable(into ++ "/" ++ path, r)
        apply.files(root, into, rest, applied.push(path, set, a))
    case Put.Bytes{+path, from, +d, r} <> rest:
      do IO<Applied>:
        w : Result<&1, &1, U32 & String, String> <- Store.copied(root ++ "/" ++ from ++ "\n" ++ into ++ "/" ++ path ++ "\n" ++ d)
        x : String <- io.ok(w)
        set : Bool <- runnable(into ++ "/" ++ path, r)
        apply.files(root, into, rest, applied.push(path, set, a))
    case Put.Link{path, t} <> rest:
      apply.files(root, into, rest, a)

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

def applied.of(a: Applied) -> Applied:
  match a:
    case Applied{w, s}:
      Applied{List.reverse(&2, String, w), List.reverse(&2, String, s)}

def apply(+root: String, +into: String, +ps: List<&2, Put>) -> IO(Applied):
  do IO<Applied>:
    a : Applied <- apply.files(root, into, ps, Applied{Nil{}, Nil{}})
    apply.links(into, ps)
    return applied.of(a)

def applied.wrote(a: Applied) -> List<&2, String>:
  match a:
    case Applied{w, s}:
      w

def applied.set(a: Applied) -> List<&2, String>:
  match a:
    case Applied{w, s}:
      s

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

# A fresh export goes where nothing is, or into a directory holding
# nothing. One holding a store is a copy to bring up to date, which decision
# 0052 allows and this port does not do; one holding anything else is
# somebody's.
def occupied.r(+into: String, lines: Maybe<&2, List<&2, String>>, header: Result<&1, &1, U32 & String, String>) -> Result<&2, &2, Main.Refused, Unit>:
  match lines header:
    case None{} _:
      Done{Unit{}}
    case Some{Nil{}} _:
      Done{Unit{}}
    case Some{l <> ls} Done{x}:
      Fail{Main.Refused{1, into ++ " holds a store already, and bringing a copy up to date in place (decision 0052) is not ported; export into an empty directory"}}
    case Some{l <> ls} Fail{e}:
      Fail{Main.Refused{1, into ++ " already holds something that is not a copy of this store; an export writes a fresh repository into an empty directory and updates a copy it made, and combining a copy with what is already there is `receive`"}}

def more.said(+n: Nat) -> String:
  Bool.pick(String, Nat.is_lt(3n, n), " and " ++ Nat.show(Nat.sub(n, 3n)) ++ " more", SNil{})

def holding.r(+into: String, names: List<&2, String>) -> Result<&2, &2, Main.Refused, Unit>:
  match names:
    case Nil{}:
      Done{Unit{}}
    case +some:
      Fail{Main.Refused{1, into ++ " already holds " ++ String.join(List.take(&2, String, some, 3n), ", ") ++ "; laying a revision out wants a directory holding nothing, because nothing afterwards could say which files it put there" ++ more.said(List.length(&2, String, some))}}

# `--files-only` lays the folder out into a directory that holds nothing.
def empty.r(+into: String, lines: Maybe<&2, List<&2, String>>) -> Result<&2, &2, Main.Refused, Unit>:
  match lines:
    case None{}:
      Done{Unit{}}
    case Some{ls}:
      holding.r(into, entry.names(ls, False{}))

def sound.r(+st: Prune.Stored) -> Result<&2, &2, Main.Refused, Unit>:
  Bool.pick(Result<&2, &2, Main.Refused, Unit>, Prune.sound(st), Done{Unit{}},
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
    a : Applied <- apply(r, into, ps2)
    real : Result<&1, &1, U32 & String, String> <- Store.really(into)
    Arrange.print_lines(List.concat(&2, String, [
      said.counts("exported", "held back", "left", "carried", p, n),
      paths.said("wrote  ", applied.wrote(a)),
      ["made a copy of " ++ Main.spelled(fs, bs, id) ++ " at " ++ Main.init.said(into, real)]]))

def export.planned(dry: Bool, +r: String, +into: String, +st: Prune.Stored, +fs: List<&2, Main.Full>, +bs: List<&2, Bm.Bookmark>, +id: String, +t: Tree.Tree(), +held: List<&2, Main.Full>, +p: Plan) -> IO(Unit):
  match dry:
    case True{}:
      Arrange.print_lines(said.plan(p, Main.spelled(fs, bs, id), into))
    case False{}:
      export.write(r, into, st, fs, bs, id, t, held, p)

def export.full(+dry: Bool, +r: String, +into: String, +s: Receive.Side, +fs: List<&2, Main.Full>, +bs: List<&2, Bm.Bookmark>, +id: String, +t: Tree.Tree()) -> IO(Unit):
  +held = Main.ancestry(fs, id)
  +st = Receive.stored.of(s)
  +p = plan.of(held, t, Receive.stored.odocs(st), Receive.stored.payloads(st), Receive.stored.bodies(st), Receive.ruled(Receive.stored.rules(st)), bs, Receive.side.claims(s))
  do IO<Unit>:
    listed : Result<&1, &1, U32 & String, String> <- Store.listing_of(into)
    header : Result<&1, &1, U32 & String, String> <- Store.really(into ++ "/history/historica.txt")
    Main.refused.io(Unit, occupied.r(into, listed.lines(listed), header))
    export.planned(dry, r, into, st, fs, bs, id, t, held, p)

def export.folder(+dry: Bool, +r: String, +into: String, +spelled: String, +ps: List<&2, Put>) -> IO(Unit):
  match dry:
    case True{}:
      Arrange.print_lines(List.concat(&2, String, [puts.said(ps), links.said("link    ", ps), ["would write the folder " ++ spelled ++ " has at " ++ into ++ ", and no history beside it"]]))
    case False{}:
      do IO<Unit>:
        a : Applied <- apply(r, into, ps)
        +a2 : Applied = a
        real : Result<&1, &1, U32 & String, String> <- Store.really(into)
        Arrange.print_lines(List.concat(&2, String, [paths.said("wrote  ", applied.wrote(a2)), modes.said(applied.set(a2)), links.said("linked  ", ps), ["the folder " ++ spelled ++ " has, at " ++ Main.init.said(into, real) ++ ", and no history beside it"]]))

def export.files(+dry: Bool, +r: String, +into: String, +s: Receive.Side, +fs: List<&2, Main.Full>, +bs: List<&2, Bm.Bookmark>, +id: String, +t: Tree.Tree()) -> IO(Unit):
  +st = Receive.stored.of(s)
  do IO<Unit>:
    m : Result<&1, &1, U32 & String, String> <- Store.made(into ++ "\n")
    done : String <- Main.init.io(String, m)
    listed : Result<&1, &1, U32 & String, String> <- Store.listing_of(into)
    Main.refused.io(Unit, empty.r(into, listed.lines(listed)))
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

def origin.fulls(+st: Prune.Stored) -> List<&2, Main.Full>:
  Arrange.distinct(Prune.fulls(Arrange.revision_docs(Receive.stored.docs(st))))

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
        Main.refused.io(Unit, sound.r(st))
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
