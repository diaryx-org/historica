# `check [<dir>] [--complete]`: the Rust tool's `Store::check` and its
# report, finding for finding.
#
# Decision 0006 splits what `check` finds in two. An error means the store
# contradicts itself and cannot be trusted; a note is an observation that
# never fails — a store mid-sync, or tidy in a way the default writer is
# not. The report says every error, then every note, each in the order the
# pass over the store found it, then a line saying how many; and where a
# head's history is not all here, how many heads that leaves unproducible.
# `check` fails where there is an error, and `--complete` makes it fail
# where a head cannot be produced too.
#
# The pass reads everything, as the Rust tool's does: the header; every
# file of `revisions/`, `operations/`, `skipped/` and `names/`, walked as the
# store walks them — a link found and never followed; each document hashed
# and parsed; each payload's digest asked of the host, and a `text` one read
# as well, since it is a file's lines. What each thing is and what it says
# about the store is decided here.
#
# Not here, and said in the README: a file the filesystem will not hand
# over, which run as root nothing is (`Unreadable` for a file of names or
# rules is its bytes not being UTF-8, and that is here).

import Base
import ./commands.bend as Main
import ./store.bend as Store
import ./folder.bend as Folder
import ./revision.bend as Rev
import ./ops.bend as Ops
import ./resolution.bend as Res
import ./bookmark.bend as Bm
import ./text.bend as T
import ./tree.bend as Tree
import ./merge.bend as Merge
import ./identity.bend as Identity
import ./skip.bend as Skip
import ./ident.bend as Id
import ./naming.bend as Naming
import ./utf8.bend as Utf8

# Findings
# --------

# One thing `check` found: whether it fails the store, what it says, and
# whether it is a head the store cannot produce.
type Finding is Data:
  Finding{error: Bool, text: String, head: Bool}

def error(+text: String) -> Finding:
  Finding{True{}, text, False{}}

def note(+text: String) -> Finding:
  Finding{False{}, text, False{}}

def is_error(f: Finding) -> Bool:
  match f:
    case Finding{e, t, h}:
      e

def is_head(f: Finding) -> Bool:
  match f:
    case Finding{e, t, h}:
      h

def said.of(+prefix: String, fs: List<&2, Finding>, +errors: Bool) -> String:
  match fs:
    case Nil{}:
      SNil{}
    case Finding{e, +t, h} <> rest:
      Bool.pick(String, Bool.not(Bool.xor(e, errors)), prefix ++ t ++ "\n", SNil{}) ++ said.of(prefix, rest, errors)

def count.of(fs: List<&2, Finding>, +errors: Bool) -> Nat:
  match fs:
    case Nil{}:
      0n
    case Finding{e, t, h} <> rest:
      Nat.add(Bool.pick(Nat, Bool.not(Bool.xor(e, errors)), 1n, 0n), count.of(rest, errors))

def heads.of(fs: List<&2, Finding>) -> Nat:
  match fs:
    case Nil{}:
      0n
    case Finding{e, t, h} <> rest:
      Nat.add(Bool.pick(Nat, h, 1n, 0n), heads.of(rest))

# `1 error`, `2 errors`, `no errors`.
def counted(n: Nat, +thing: String) -> String:
  match n:
    case 0n:
      "no " ++ thing ++ "s"
    case 1n:
      "1 " ++ thing
    case +many:
      Nat.show(many) ++ " " ++ thing ++ "s"

# `render::report`: the errors, the notes, the count, and what a head the
# store cannot produce costs — naming `--complete` to a caller who did not
# ask for it.
def report(+fs: List<&2, Finding>, +shown: String, complete: Bool) -> String:
  +errors = count.of(fs, True{})
  +notes = count.of(fs, False{})
  +heads = heads.of(fs)
  said.of("error: ", fs, True{}) ++ said.of("note: ", fs, False{})
    ++ shown ++ ": " ++ Bool.pick(String, Bool.and(Nat.is_eq(errors, 0n), Nat.is_eq(notes, 0n)), "nothing to report", counted(errors, "error") ++ ", " ++ counted(notes, "note")) ++ "\n"
    ++ Bool.pick(String, Nat.is_eq(heads, 0n), SNil{},
      shown ++ ": " ++ counted(heads, "head") ++ " here cannot be produced from what is here\n"
        ++ Bool.pick(String, complete, SNil{}, "`check --complete` is the run that fails on that\n"))

# Whether `check` fails: an error, or with `--complete`, a head it cannot
# produce.
def fails(+fs: List<&2, Finding>, complete: Bool) -> Bool:
  Bool.or(Bool.not(Nat.is_eq(count.of(fs, True{}), 0n)), Bool.and(complete, Bool.not(Nat.is_eq(heads.of(fs), 0n))))

# Every error first, each kind in the order found: the report's own sort.
def sorted(+fs: List<&2, Finding>) -> List<&2, Finding>:
  List.append(&2, Finding, List.filter(~Finding, ~(f => is_error(f)), fs), List.filter(~Finding, ~(f => Bool.not(is_error(f))), fs))

# Spelling
# --------

def ab12(+id: String) -> String:
  String.take(id, 12n)

def joined.go(ss: List<&2, String>) -> String:
  match ss:
    case Nil{}:
      SNil{}
    case s <> Nil{}:
      s
    case s <> rest:
      s ++ ", " ++ joined.go(rest)

# The digests a head waits on, said without becoming a wall of hex: three,
# and a count of the rest.
def missing.said(+ids: List<&2, String>) -> String:
  +n = List.length(&2, String, ids)
  joined.go(T.map(~String, ~String, ~(i => ab12(i)), List.take(&2, String, ids, 3n)))
    ++ Bool.pick(String, Nat.is_gt(n, 3n), " and " ++ Nat.show(Nat.sub(n, 3n)) ++ " more", SNil{})

def by_digest(+xs: List<&2, String>) -> List<&2, String>:
  List.sort(~String, ~(a => b => String.is_le(a, b)), xs)

def distinct.dup(xs: List<&2, String>, +last: Maybe<&2, String>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case +x <> rest:
      Maybe.default(&2, Bool, Maybe.map(&2, String, Bool, l => String.eq(l, x), last), False{})

def distinct.go(xs: List<&2, String>, +last: Maybe<&2, String>, dup: Bool) -> List<&2, String>:
  match xs dup:
    case Nil{} _:
      Nil{}
    case x <> +rest True{}:
      distinct.go(rest, last, distinct.dup(rest, last))
    case +x <> +rest False{}:
      x <> distinct.go(rest, Some{x}, distinct.dup(rest, Some{x}))

# A set of digests, as the Rust tool's `BTreeSet` holds one: sorted, once each.
def set.of(+xs: List<&2, String>) -> List<&2, String>:
  +sorted = by_digest(xs)
  distinct.go(sorted, None{}, False{})

# A file's own name, and whether the platform wrote it (decision 0022).
def platform(+path: String) -> Bool:
  Folder.platform_name(Folder.last_component(path))

# The digest a filename claims, where its name less a document suffix is
# one.
def stem.of(+name: String) -> String:
  Bool.pick(String, String.ends_with(name, ".rev.txt"), String.take(name, Nat.sub(String.length(name), 8n)),
    Bool.pick(String, String.ends_with(name, ".ops.txt"), String.take(name, Nat.sub(String.length(name), 8n)), name))

def claimed(+path: String) -> Maybe<&2, String>:
  +stem = stem.of(Folder.last_component(path))
  Bool.pick(Maybe<&2, String>, Id.is_digest(stem), Some{stem}, None{})

def lies(+path: String, +id: String, c: Maybe<&2, String>) -> List<&2, Finding>:
  match c:
    case None{}:
      Nil{}
    case Some{+claim}:
      Bool.pick(List<&2, Finding>, String.eq(claim, id), Nil{},
        [error(path ++ " claims " ++ ab12(claim) ++ " and hashes to " ++ id ++ "; the name is a claim and it is false")])

# The walk
# --------

# What one directory of the store holds, found as the store walks it: every
# file and every link, a link never followed, each a path under the root.
type Walked is Data:
  Walked{files: List<&2, String>, links: List<&2, String>}

type Entry is Data:
  Entry.Dir{}
  Entry.File{}
  Entry.Link{}
  Entry.Unspelled{}
  Entry.Other{}

def kind.of(+line: String) -> Entry:
  +k = String.take(line, 1n)
  Bool.pick(Entry, String.eq(k, "d"), Entry.Dir{},
  Bool.pick(Entry, String.eq(k, "f"), Entry.File{},
  Bool.pick(Entry, String.eq(k, "l"), Entry.Link{},
  Bool.pick(Entry, String.eq(k, "L"), Entry.Unspelled{}, Entry.Other{}))))

# One directory's listing, read: the directories to walk next, what was
# found, and whether the next line is a link's target, which it passes over.
type Seen is Data:
  Seen{dirs: List<&2, String>, files: List<&2, String>, links: List<&2, String>, target: Bool}

def file.name(cut: Maybe<&2, T.Split>) -> String:
  match cut:
    case None{}:
      SNil{}
    case Some{T.Split{size, name}}:
      name

def seen.kind(s: Seen, +prefix: String, +line: String, k: Entry) -> Seen:
  match s k:
    case Seen{ds, fs, ls, True{}} _:
      Seen{ds, fs, ls, False{}}
    case Seen{ds, fs, ls, False{}} Entry.Dir{}:
      Seen{(prefix ++ "/" ++ String.drop(line, 2n)) <> ds, fs, ls, False{}}
    case Seen{ds, fs, ls, False{}} Entry.File{}:
      Seen{ds, (prefix ++ "/" ++ file.name(T.split_once(String.drop(line, 4n)))) <> fs, ls, False{}}
    case Seen{ds, fs, ls, False{}} Entry.Link{}:
      Seen{ds, fs, (prefix ++ "/" ++ String.drop(line, 2n)) <> ls, True{}}
    case Seen{ds, fs, ls, False{}} Entry.Unspelled{}:
      Seen{ds, fs, (prefix ++ "/" ++ String.drop(line, 2n)) <> ls, False{}}
    case Seen{ds, fs, ls, False{}} Entry.Other{}:
      Seen{ds, fs, ls, False{}}

def seen.go(ls: List<&2, String>, +prefix: String, s: Seen) -> Seen:
  match ls:
    case Nil{}:
      s
    case +l <> rest:
      seen.go(rest, prefix, seen.kind(s, prefix, l, kind.of(l)))

def listed(r: Result<&1, &1, U32 & String, String>) -> String:
  match r:
    case Done{text}:
      text
    case Fail{e}:
      SNil{}

# What was found so far, and no directory yet to walk from this listing.
def seen.fresh(s: Seen) -> Seen:
  match s:
    case Seen{ds, fs, ls, t}:
      Seen{Nil{}, fs, ls, False{}}

def seen.pending(s: Seen) -> List<&2, String>:
  match s:
    case Seen{ds, fs, ls, t}:
      ds

# One directory's listing read, as the host lists it, onto what was found
# before (`LAWS.check_reads_each_line_of_a_listing`).
def walk.step(s: Seen, +dir: String, r: Result<&1, &1, U32 & String, String>) -> Seen:
  seen.go(String.split(listed(r), '\n'), dir, seen.fresh(s))

def walk.go(fuel: Nat, +root: String, pending: List<&2, String>, s: Seen) -> IO(Seen):
  match fuel pending:
    case 0n _:
      IO.pure(Seen, s)
    case 1n+q Nil{}:
      IO.pure(Seen, s)
    case 1n+q +dir <> rest:
      do IO<Seen>:
        r : Result<&1, &1, U32 & String, String> <- Store.listing_of(Identity.joined(root, dir))
        +got : Seen = walk.step(s, dir, r)
        walk.go(q, root, List.append(&2, String, seen.pending(got), rest), got)

def by_path(+ps: List<&2, String>) -> List<&2, String>:
  List.sort(~String, ~(a => b => Folder.walked_le(a, b)), ps)

def under(+root: String, ps: List<&2, String>) -> List<&2, String>:
  match ps:
    case Nil{}:
      Nil{}
    case p <> rest:
      Identity.joined(root, p) <> under(root, rest)

# `store::walk`: one directory, at any depth, sorted by path component.
def walked.of(+root: String, s: Seen) -> Walked:
  match s:
    case Seen{ds, fs, ls, t}:
      Walked{under(root, by_path(fs)), under(root, by_path(ls))}

def walk(+root: String, +dir: String) -> IO(Walked):
  do IO<Walked>:
    s : Seen <- walk.go(U32.to_nat(1000000), root, [dir], Seen{Nil{}, Nil{}, Nil{}, False{}})
    return walked.of(root, s)

def walked.files(w: Walked) -> List<&2, String>:
  match w:
    case Walked{fs, ls}:
      fs

def walked.links(w: Walked) -> List<&2, String>:
  match w:
    case Walked{fs, ls}:
      ls

def unfollowed(ls: List<&2, String>) -> List<&2, Finding>:
  match ls:
    case Nil{}:
      Nil{}
    case +l <> rest:
      note(l ++ " is a symbolic link, and a store reads the files it holds rather than the ones it points at") <> unfollowed(rest)

def foreign(+path: String) -> Finding:
  note(path ++ " carries neither `.rev.txt` nor `.txt` where its directory wants one, so nothing reads it")

# The header
# ----------

def header.layout(second: Maybe<&2, String>) -> List<&2, Finding>:
  match second:
    case None{}:
      Nil{}
    case Some{+rest}:
      +found = Store.line.cut(rest)
      Bool.pick(List<&2, Finding>, String.is_empty(found), Nil{},
        [error("`historica.txt` states `" ++ found ++ "` under its format line, where only a newer Historica writes; if that line is a note, put a blank line above it")])

def header.of(+text: String) -> List<&2, Finding>:
  +first = Store.line.cut(text)
  Bool.pick(List<&2, Finding>, String.eq(first, Store.PREAMBLE()), header.layout(Store.line.after(text)),
    [error("this store says `" ++ first ++ "` and this reader reads `" ++ Store.PREAMBLE() ++ "`")])

# `check`'s first question: whether this is a store this reader reads.
def header(h: Maybe<&2, String>) -> List<&2, Finding>:
  match h:
    case None{}:
      [error("no `historica.txt` file, so this is not a store")]
    case Some{+text}:
      header.of(text)

def header.read(+root: String, r: Result<&1, &1, U32 & String, File>) -> IO(Maybe<&2, String>):
  match r:
    case Fail{e}:
      IO.pure(Maybe<&2, String>, None{})
    case Done{f}:
      do IO<Maybe<&2, String>>:
        File.close(f)
        text : String <- Store.read_text(root ++ "/historica.txt")
        return Some{text}

# Revisions
# ---------

# A document of the store, read: where it was, what it hashes to, and what
# it says.
type Read is Data:
  Read{path: String, id: String, text: String}

def read.of(d: Store.Doc) -> Read:
  match d:
    case Store.Doc{p, i, n, t}:
      Read{p, i, t}

def read.path(r: Read) -> String:
  match r:
    case Read{p, i, t}:
      p

def read.id(r: Read) -> String:
  match r:
    case Read{p, i, t}:
      i

# The files of `revisions/`: the platform's passed over, a foreign name
# kept to say so, and every revision read.
type Filed is Data:
  Filed.Foreign{path: String}
  Filed.Doc{read: Read}

# What a file of `revisions/` is taken for, before it is opened.
type Class is Data:
  Class.Platform{}
  Class.Claimed{}
  Class.Foreign{}

def class.of(+p: String, +suffix: String) -> Class:
  Bool.pick(Class, platform(p), Class.Platform{}, Bool.pick(Class, String.ends_with(Folder.last_component(p), suffix), Class.Claimed{}, Class.Foreign{}))

def class(ps: List<&2, String>, +suffix: String) -> Class:
  match ps:
    case Nil{}:
      Class.Platform{}
    case +p <> rest:
      class.of(p, suffix)

def revisions.go(ps: List<&2, String>, k: Class) -> IO(List<&2, Filed>):
  match ps k:
    case Nil{} _:
      IO.pure(List<&2, Filed>, Nil{})
    case p <> +rest Class.Platform{}:
      revisions.go(rest, class(rest, ".rev.txt"))
    case +p <> +rest Class.Claimed{}:
      do IO<List<&2, Filed>>:
        d : Store.Doc <- Store.read_doc(p)
        more : List<&2, Filed> <- revisions.go(rest, class(rest, ".rev.txt"))
        return Filed.Doc{read.of(d)} <> more
    case +p <> +rest Class.Foreign{}:
      do IO<List<&2, Filed>>:
        more : List<&2, Filed> <- revisions.go(rest, class(rest, ".rev.txt"))
        return Filed.Foreign{p} <> more

def parsed.rev(r: Read) -> Maybe<&2, Main.Full>:
  match r:
    case Read{p, +i, +t}:
      Main.full(i, Rev.parse(t))

def unparsable(+p: String, r: Result<&2, &2, String, Rev.Rev>) -> List<&2, Finding>:
  match r:
    case Fail{e}:
      [error(p ++ ": " ++ e)]
    case Done{x}:
      Nil{}

def revfile.findings(f: Filed) -> List<&2, Finding>:
  match f:
    case Filed.Foreign{+p}:
      [foreign(p)]
    case Filed.Doc{Read{+p, +i, +t}}:
      List.append(&2, Finding, lies(p, i, claimed(p)), unparsable(p, Rev.parse(t)))


# The revisions that parse, by digest, each once.
def documents.go(fs: List<&2, Filed>) -> List<&2, Main.Full>:
  match fs:
    case Nil{}:
      Nil{}
    case Filed.Foreign{p} <> rest:
      documents.go(rest)
    case Filed.Doc{r} <> rest:
      Main.push_full(parsed.rev(r), documents.go(rest))

def full.le(+a: Main.Full, +b: Main.Full) -> Bool:
  String.is_le(Main.id_of(a), Main.id_of(b))

def fulls.distinct(fs: List<&2, Main.Full>, +last: String) -> List<&2, Main.Full>:
  match fs:
    case Nil{}:
      Nil{}
    case +f <> rest:
      +id = Main.id_of(f)
      +more = fulls.distinct(rest, id)
      Bool.pick(List<&2, Main.Full>, String.eq(id, last), more, f <> more)

def documents(fs: List<&2, Filed>) -> List<&2, Main.Full>:
  fulls.distinct(List.sort(~Main.Full, ~(a => b => full.le(a, b)), documents.go(fs)), SNil{})

# Where each digest is stored, in the order found.
type Stored is Data:
  Stored{id: String, path: String}

def stored.id(s: Stored) -> String:
  match s:
    case Stored{i, p}:
      i

def stored.path(s: Stored) -> String:
  match s:
    case Stored{i, p}:
      p

def paths.of(ss: List<&2, Stored>, +id: String) -> List<&2, String>:
  match ss:
    case Nil{}:
      Nil{}
    case Stored{+i, +p} <> rest:
      +more = paths.of(rest, id)
      Bool.pick(List<&2, String>, String.eq(i, id), p <> more, more)

def duplicates.go(ids: List<&2, String>, +ss: List<&2, Stored>) -> List<&2, Finding>:
  match ids:
    case Nil{}:
      Nil{}
    case +id <> rest:
      +ps = paths.of(ss, id)
      +n = List.length(&2, String, ps)
      +more = duplicates.go(rest, ss)
      Bool.pick(List<&2, Finding>, Nat.is_gt(n, 1n), note(ab12(id) ++ " is stored " ++ Nat.show(n) ++ " times: " ++ joined.go(ps)) <> more, more)

# One document stored under more than one name, which is harmless.
def duplicates(+ss: List<&2, Stored>) -> List<&2, Finding>:
  duplicates.go(set.of(T.map(~Stored, ~String, ~(s => stored.id(s)), ss)), ss)

def stored.revisions(fs: List<&2, Filed>) -> List<&2, Stored>:
  match fs:
    case Nil{}:
      Nil{}
    case Filed.Foreign{p} <> rest:
      stored.revisions(rest)
    case Filed.Doc{Read{p, i, t}} <> rest:
      Stored{i, p} <> stored.revisions(rest)

def revisions.findings(fs: List<&2, Filed>) -> List<&2, Finding>:
  match fs:
    case Nil{}:
      Nil{}
    case f <> rest:
      List.append(&2, Finding, revfile.findings(f), revisions.findings(rest))

# The graph
# ---------

def held(ds: List<&2, Main.Full>, +id: String) -> Bool:
  match ds:
    case Nil{}:
      False{}
    case +d <> rest:
      Bool.or(String.eq(Main.id_of(d), id), held(rest, id))

def parents.missing(+ds: List<&2, Main.Full>, +id: String, ps: List<&2, String>) -> List<&2, Finding>:
  match ps:
    case Nil{}:
      Nil{}
    case +p <> rest:
      +more = parents.missing(ds, id, rest)
      Bool.pick(List<&2, Finding>, held(ds, p), more, note(ab12(id) ++ " names parent " ++ ab12(p) ++ ", which is not here yet") <> more)

# A parent nothing here holds: transport has more to deliver.
def missing_parents(+all: List<&2, Main.Full>, ds: List<&2, Main.Full>) -> List<&2, Finding>:
  match ds:
    case Nil{}:
      Nil{}
    case +d <> rest:
      List.append(&2, Finding, parents.missing(all, Main.id_of(d), Main.parents_of(d)), missing_parents(all, rest))

def supersedes_of(f: Main.Full) -> List<&2, String>:
  match f:
    case Main.Full{id, change, parents, supersedes, author, when, revised_by, revised, facts, message}:
      supersedes

# What withdrew a revision: every document here saying it supersedes it.
def successors(ds: List<&2, Main.Full>, +id: String) -> List<&2, String>:
  match ds:
    case Nil{}:
      Nil{}
    case +d <> rest:
      +more = successors(rest, id)
      Bool.pick(List<&2, String>, Rev.member(supersedes_of(d), id), Main.id_of(d) <> more, more)

def stands.parents(+all: List<&2, Main.Full>, +id: String, ps: List<&2, String>) -> List<&2, Finding>:
  match ps:
    case Nil{}:
      Nil{}
    case +p <> rest:
      +by = set.of(successors(all, p))
      +more = stands.parents(all, id, rest)
      Bool.pick(List<&2, Finding>, List.is_empty(&2, String, by), more,
        note(ab12(id) ++ " stands on " ++ ab12(p) ++ ", which " ++ missing.said(by) ++ " supersedes; it was authored before the rewrite. Run `historica carry` to repair automatically") <> more)

# Work standing on a revision something has since superseded, where the
# work itself is not withdrawn (decision 0023).
def stands(+all: List<&2, Main.Full>, ds: List<&2, Main.Full>) -> List<&2, Finding>:
  match ds:
    case Nil{}:
      Nil{}
    case +d <> rest:
      +id = Main.id_of(d)
      List.append(&2, Finding, Bool.pick(List<&2, Finding>, List.is_empty(&2, String, successors(all, id)), stands.parents(all, id, Main.parents_of(d)), Nil{}), stands(all, rest))

# Operations
# ----------

# A file of `operations/`: a document read, or a payload, which is hashed by
# the host and not read here unless a revision says it is a file's lines.
type OpFiled is Data:
  OpFiled.Doc{read: Read}
  OpFiled.Payload{path: String, stat: String}

def operations.go(ps: List<&2, String>, k: Class) -> IO(List<&2, OpFiled>):
  match ps k:
    case Nil{} _:
      IO.pure(List<&2, OpFiled>, Nil{})
    case p <> +rest Class.Platform{}:
      operations.go(rest, class(rest, ".ops.txt"))
    case +p <> +rest Class.Claimed{}:
      do IO<List<&2, OpFiled>>:
        d : Store.Doc <- Store.read_doc(p)
        more : List<&2, OpFiled> <- operations.go(rest, class(rest, ".ops.txt"))
        return OpFiled.Doc{read.of(d)} <> more
    case +p <> +rest Class.Foreign{}:
      do IO<List<&2, OpFiled>>:
        more : List<&2, OpFiled> <- operations.go(rest, class(rest, ".ops.txt"))
        return OpFiled.Payload{p, SNil{}} <> more

def payload.paths(fs: List<&2, OpFiled>) -> List<&2, String>:
  match fs:
    case Nil{}:
      Nil{}
    case OpFiled.Doc{r} <> rest:
      payload.paths(rest)
    case OpFiled.Payload{p, s} <> rest:
      p <> payload.paths(rest)

# Each payload's `<digest> <size>`, asked in the order found.
def attach(fs: List<&2, OpFiled>, stats: List<&2, String>) -> List<&2, OpFiled>:
  match fs stats:
    case Nil{} _:
      Nil{}
    case OpFiled.Doc{r} <> rest _:
      OpFiled.Doc{r} <> attach(rest, stats)
    case OpFiled.Payload{p, x} <> rest Nil{}:
      OpFiled.Payload{p, x} <> attach(rest, Nil{})
    case OpFiled.Payload{p, x} <> rest s <> more:
      OpFiled.Payload{p, s} <> attach(rest, more)

# Each payload beside what the host answered for it, in order — what the
# pass reads of `attach`'s result (`LAWS.check_pairs_each_payload`).
def payload.pairs(fs: List<&2, OpFiled>) -> List<&2, T.Split>:
  match fs:
    case Nil{}:
      Nil{}
    case OpFiled.Doc{r} <> rest:
      payload.pairs(rest)
    case OpFiled.Payload{p, s} <> rest:
      T.Split{p, s} <> payload.pairs(rest)

def zip.pairs(ps: List<&2, String>, stats: List<&2, String>) -> List<&2, T.Split>:
  match ps stats:
    case p <> pr s <> sr:
      T.Split{p, s} <> zip.pairs(pr, sr)
    case _ _:
      Nil{}

def stat.id(+stat: String) -> String:
  T.word(stat)

# What an operation document says, in whichever of its three grammars.
type Parsed is Data:
  Parsed.Ops{doc: Ops.Doc}
  Parsed.Res{doc: Res.Doc}
  Parsed.Forgot{forgets: String}
  Parsed.Wrong{because: String}

# Decision 0066's document for a destroyed payload: the `length` no other
# document carries says which grammar it is.
def forgotten.is(ls: List<&2, String>) -> Bool:
  match ls:
    case Nil{}:
      False{}
    case +l <> rest:
      Bool.pick(Bool, String.is_empty(l), False{}, Bool.or(String.starts_with(l, "length "), forgotten.is(rest)))

def forgotten.lines(ls: List<&2, String>) -> Bool:
  match ls:
    case Nil{}:
      False{}
    case +first <> rest:
      Bool.and(String.eq(first, "historica"), forgotten.is(rest))

def is_forgotten(+text: String) -> Bool:
  forgotten.lines(Folder.lines.trimmed(String.split(text, '\n')))

def crlf() -> String:
  "a carriage return in the format's own line changes this document's identity; delete it — a `-` or `+` line may hold one, because that is content"

# `ForgottenPayload::parse`: `forgets` and a digest, `length` and a count,
# and nothing else.
type Forgetting is Data:
  Forgetting{forgets: Maybe<&2, String>, length: Bool}

def forgotten.forgets(+at: Nat, f: Maybe<&2, String>, l: Bool, +value: String) -> Result<&2, &2, String, Forgetting>:
  match f l:
    case Some{x} _:
      Fail{"line " ++ Nat.show(at) ++ ": `forgets` appears once in a revision; delete the second line"}
    case None{} True{}:
      Fail{"line " ++ Nat.show(at) ++ ": `forgets` comes before `length` in the fixed key order; move the line up"}
    case None{} False{}:
      Bool.pick(Result<&2, &2, String, Forgetting>, Id.is_digest(value), Done{Forgetting{Some{value}, False{}}},
        Fail{"line " ++ Nat.show(at) ++ ": `forgets` names a revision by digest, and `" ++ value ++ "` is not 64 lowercase hexadecimal characters; `shasum -a 256` on the revision you mean prints the right one"})

def forgotten.line(+at: Nat, st: Forgetting, +key: String, +value: String) -> Result<&2, &2, String, Forgetting>:
  match st:
    case Forgetting{+f, +l}:
      Bool.pick(Result<&2, &2, String, Forgetting>, String.is_empty(value), Fail{"line " ++ Nat.show(at) ++ ": a header with no value is an absent fact spelled ambiguously; delete the line or give it a value"},
      Bool.pick(Result<&2, &2, String, Forgetting>, String.eq(key, "forgets"), forgotten.forgets(at, f, l, value),
      Bool.pick(Result<&2, &2, String, Forgetting>, String.eq(key, "length"),
        Bool.pick(Result<&2, &2, String, Forgetting>, l, Fail{"line " ++ Nat.show(at) ++ ": `length` appears once in a revision; delete the second line"},
          Bool.pick(Result<&2, &2, String, Forgetting>, Maybe.is_some(&2, Nat, T.number(value)), Done{Forgetting{f, True{}}}, Fail{"line " ++ Nat.show(at) ++ ": `" ++ value ++ "` is not a position: decimal digits, no sign, and no leading zero, counted from zero into the parent; write it plainly"})),
      Bool.pick(Result<&2, &2, String, Forgetting>, String.eq(key, "result"), Fail{"line " ++ Nat.show(at) ++ ": a forgetting document states no result: a digest of the destroyed state would confirm a guess at what was destroyed; delete the line"},
        Fail{"line " ++ Nat.show(at) ++ ": `" ++ key ++ "` is not a header this format knows; spell it `<tool>." ++ key ++ "` if a reader may ignore it, or upgrade Historica if not"}))))

def forgotten.cut(+at: Nat, st: Forgetting, +line: String, cut: Maybe<&2, T.Split>) -> Result<&2, &2, String, Forgetting>:
  match cut:
    case None{}:
      forgotten.line(at, st, line, SNil{})
    case Some{T.Split{+k, +v}}:
      forgotten.line(at, st, k, v)

def forgotten.go(ls: List<&2, T.Line>, +at: Nat, st: Result<&2, &2, String, Forgetting>) -> Result<&2, &2, String, Forgetting>:
  match ls st:
    case _ Fail{e}:
      Fail{e}
    case Nil{} Done{x}:
      Done{x}
    case T.Line{+t, False{}} <> rest Done{x}:
      Fail{"line " ++ Nat.show(at) ++ ": every line the parser reads ends with a newline; add one"}
    case T.Line{+t, True{}} <> rest Done{x}:
      forgotten.go(rest, 1n+at, Bool.pick(Result<&2, &2, String, Forgetting>, T.has_char(t, '\r'), Fail{"line " ++ Nat.show(at) ++ ": " ++ crlf()},
        Bool.pick(Result<&2, &2, String, Forgetting>, String.is_empty(t),
        Fail{"line " ++ Nat.show(at) ++ ": a payload has no items, so the document standing in for a forgotten one is `forgets` and `length` and nothing else; delete the blank line and everything under it"},
        forgotten.cut(at, x, t, T.split_once(t)))))

def forgotten.end(+at: Nat, r: Result<&2, &2, String, Forgetting>) -> Parsed:
  match r:
    case Fail{e}:
      Parsed.Wrong{e}
    case Done{Forgetting{None{}, l}}:
      Parsed.Wrong{"line " ++ Nat.show(at) ++ ": a revision states `forgets`; add the line"}
    case Done{Forgetting{Some{f}, False{}}}:
      Parsed.Wrong{"line " ++ Nat.show(at) ++ ": a revision states `length`; add the line"}
    case Done{Forgetting{Some{f}, True{}}}:
      Parsed.Forgot{f}

# The preamble's line is held to the same rule as every other: `is_forgotten`
# reads it as `str::lines` does, less a carriage return, and the parser does
# not.
def forgotten.first(ls: List<&2, T.Line>) -> Bool:
  match ls:
    case Nil{}:
      False{}
    case T.Line{+t, e} <> rest:
      T.has_char(t, '\r')

def forgotten.parse(+text: String) -> Parsed:
  +ls = T.lines(text)
  Bool.pick(Parsed, forgotten.first(ls), Parsed.Wrong{"line 1: " ++ crlf()},
    forgotten.end(List.length(&2, T.Line, ls), forgotten.go(List.drop(&2, T.Line, ls, 1n), 2n, Done{Forgetting{None{}, False{}}})))

def parsed.ops(r: Result<&2, &2, String, Ops.Doc>) -> Parsed:
  match r:
    case Fail{e}:
      Parsed.Wrong{e}
    case Done{d}:
      Parsed.Ops{d}

def parsed.res(r: Result<&2, &2, String, Res.Doc>) -> Parsed:
  match r:
    case Fail{e}:
      Parsed.Wrong{e}
    case Done{d}:
      Parsed.Res{d}

# Which grammar the bytes are held to, and what they say in it.
def parsed(+text: String) -> Parsed:
  Bool.pick(Parsed, is_forgotten(text), forgotten.parse(text),
    Bool.pick(Parsed, Res.is_resolution(text), parsed.res(Res.parse(text)), parsed.ops(Ops.parse(text))))

# A document of `operations/`, by digest, as it was read.
type Content is Data:
  Content{id: String, parsed: Parsed}

def content.wrong(+p: String, x: Parsed) -> List<&2, Finding>:
  match x:
    case Parsed.Wrong{e}:
      [error(p ++ ": " ++ e)]
    case _:
      Nil{}

def op.findings(f: OpFiled) -> List<&2, Finding>:
  match f:
    case OpFiled.Doc{Read{+p, +i, +t}}:
      List.append(&2, Finding, lies(p, i, claimed(p)), content.wrong(p, parsed(t)))
    case OpFiled.Payload{+p, +s}:
      Bool.pick(List<&2, Finding>, String.eq(stat.id(s), "-"), Nil{}, lies(p, stat.id(s), claimed(p)))

def operations.findings(fs: List<&2, OpFiled>) -> List<&2, Finding>:
  match fs:
    case Nil{}:
      Nil{}
    case f <> rest:
      List.append(&2, Finding, op.findings(f), operations.findings(rest))

def stored.operations(fs: List<&2, OpFiled>) -> List<&2, Stored>:
  match fs:
    case Nil{}:
      Nil{}
    case OpFiled.Doc{Read{p, i, t}} <> rest:
      Stored{i, p} <> stored.operations(rest)
    case OpFiled.Payload{+p, +s} <> rest:
      +more = stored.operations(rest)
      Bool.pick(List<&2, Stored>, String.eq(stat.id(s), "-"), more, Stored{stat.id(s), p} <> more)

def contents.go(fs: List<&2, OpFiled>) -> List<&2, Content>:
  match fs:
    case Nil{}:
      Nil{}
    case OpFiled.Doc{Read{p, +i, +t}} <> rest:
      Content{i, parsed(t)} <> contents.go(rest)
    case OpFiled.Payload{p, s} <> rest:
      contents.go(rest)

def payloads.go(fs: List<&2, OpFiled>) -> List<&2, Stored>:
  match fs:
    case Nil{}:
      Nil{}
    case OpFiled.Doc{r} <> rest:
      payloads.go(rest)
    case OpFiled.Payload{+p, +s} <> rest:
      +more = payloads.go(rest)
      Bool.pick(List<&2, Stored>, String.eq(stat.id(s), "-"), more, Stored{stat.id(s), p} <> more)

# What the documents are
# ----------------------

def content.le(+a: Content, +b: Content) -> Bool:
  match a b:
    case Content{x, p} Content{y, q}:
      String.is_le(x, y)

def content.id(c: Content) -> String:
  match c:
    case Content{i, p}:
      i

def contents.distinct(cs: List<&2, Content>, +last: String) -> List<&2, Content>:
  match cs:
    case Nil{}:
      Nil{}
    case +c <> rest:
      +id = content.id(c)
      +more = contents.distinct(rest, id)
      Bool.pick(List<&2, Content>, String.eq(id, last), more, c <> more)

# Every document of `operations/`, by digest, each once.
def contents(fs: List<&2, OpFiled>) -> List<&2, Content>:
  contents.distinct(List.sort(~Content, ~(a => b => content.le(a, b)), contents.go(fs)), SNil{})

def opdoc.of(cs: List<&2, Content>, +id: String) -> Maybe<&2, Ops.Doc>:
  match cs:
    case Nil{}:
      None{}
    case Content{+i, Parsed.Ops{d}} <> rest:
      Bool.pick(Maybe<&2, Ops.Doc>, String.eq(i, id), Some{d}, opdoc.of(rest, id))
    case c <> rest:
      opdoc.of(rest, id)

def res.of(cs: List<&2, Content>, +id: String) -> Maybe<&2, Res.Doc>:
  match cs:
    case Nil{}:
      None{}
    case Content{+i, Parsed.Res{d}} <> rest:
      Bool.pick(Maybe<&2, Res.Doc>, String.eq(i, id), Some{d}, res.of(rest, id))
    case c <> rest:
      res.of(rest, id)

def is.forgets(f: Maybe<&2, String>, +target: String) -> Bool:
  match f:
    case None{}:
      False{}
    case Some{x}:
      String.eq(x, target)

# The documents standing in for `target`, in digest order, in each grammar.
def standing.ops(cs: List<&2, Content>, +target: String) -> List<&2, Ops.Doc>:
  match cs:
    case Nil{}:
      Nil{}
    case Content{i, Parsed.Ops{Ops.Doc{+f, r, os}}} <> rest:
      +more = standing.ops(rest, target)
      Bool.pick(List<&2, Ops.Doc>, is.forgets(f, target), Ops.Doc{f, r, os} <> more, more)
    case c <> rest:
      standing.ops(rest, target)

def standing.res(cs: List<&2, Content>, +target: String) -> List<&2, Res.Doc>:
  match cs:
    case Nil{}:
      Nil{}
    case Content{i, Parsed.Res{Res.Doc{+f, r, ps}}} <> rest:
      +more = standing.res(rest, target)
      Bool.pick(List<&2, Res.Doc>, is.forgets(f, target), Res.Doc{f, r, ps} <> more, more)
    case c <> rest:
      standing.res(rest, target)

def standing.payload(cs: List<&2, Content>, +target: String) -> Bool:
  match cs:
    case Nil{}:
      False{}
    case Content{i, Parsed.Forgot{+f}} <> rest:
      Bool.or(String.eq(f, target), standing.payload(rest, target))
    case c <> rest:
      standing.payload(rest, target)

def forgets.of(p: Parsed) -> Maybe<&2, String>:
  match p:
    case Parsed.Ops{Ops.Doc{f, r, os}}:
      f
    case Parsed.Res{Res.Doc{f, r, ps}}:
      f
    case Parsed.Forgot{f}:
      Some{f}
    case Parsed.Wrong{e}:
      None{}

# What each grammar's forgetting documents stand in for, in digest order.
def targets.ops(cs: List<&2, Content>) -> List<&2, String>:
  match cs:
    case Nil{}:
      Nil{}
    case Content{i, Parsed.Ops{Ops.Doc{Some{t}, r, os}}} <> rest:
      t <> targets.ops(rest)
    case c <> rest:
      targets.ops(rest)

def targets.res(cs: List<&2, Content>) -> List<&2, String>:
  match cs:
    case Nil{}:
      Nil{}
    case Content{i, Parsed.Res{Res.Doc{Some{t}, r, ps}}} <> rest:
      t <> targets.res(rest)
    case c <> rest:
      targets.res(rest)

def targets.payloads(cs: List<&2, Content>) -> List<&2, String>:
  match cs:
    case Nil{}:
      Nil{}
    case Content{i, Parsed.Forgot{t}} <> rest:
      t <> targets.payloads(rest)
    case c <> rest:
      targets.payloads(rest)

def payload.held(ps: List<&2, Stored>, +id: String) -> Bool:
  match ps:
    case Nil{}:
      False{}
    case Stored{+i, p} <> rest:
      Bool.or(String.eq(i, id), payload.held(rest, id))

# Whether this store holds a document or a payload under the digest —
# parsed, in either grammar that states operations.
def doc.held(cs: List<&2, Content>, +id: String) -> Bool:
  match cs:
    case Nil{}:
      False{}
    case Content{+i, Parsed.Ops{d}} <> rest:
      Bool.or(String.eq(i, id), doc.held(rest, id))
    case Content{+i, Parsed.Res{d}} <> rest:
      Bool.or(String.eq(i, id), doc.held(rest, id))
    case c <> rest:
      doc.held(rest, id)

def resurrected(+cs: List<&2, Content>, +ps: List<&2, Stored>, ts: List<&2, String>) -> List<&2, Finding>:
  match ts:
    case Nil{}:
      Nil{}
    case +t <> rest:
      +more = resurrected(cs, ps, rest)
      Bool.pick(List<&2, Finding>, Bool.or(doc.held(cs, t), payload.held(ps, t)),
        note(ab12(t) ++ " was forgotten and its bytes are here again, probably by sync; the redaction still holds, and `forget` run again destroys them again") <> more, more)

# Decision 0014's stand-ins
# -------------------------

def item.forget(stated: Ops.Item, kept: Ops.Item) -> Ops.Item:
  match stated kept:
    case Ops.Item{t1, n1, f1} Ops.Item{t2, +n2, +f2}:
      Bool.pick(Ops.Item, Bool.and(f1, Bool.not(f2)), Ops.Item{SNil{}, n2, True{}}, Ops.Item{t2, n2, f2})

def items.forget(stated: List<&2, Ops.Item>, kept: List<&2, Ops.Item>) -> List<&2, Ops.Item>:
  match stated kept:
    case s <> ss k <> ks:
      item.forget(s, k) <> items.forget(ss, ks)
    case _ ks:
      ks

def opdoc.forget(stated: List<&2, Ops.Op>, kept: List<&2, Ops.Op>) -> List<&2, Ops.Op>:
  match stated kept:
    case Ops.Op{v1, a1, is1} <> ss Ops.Op{v2, a2, is2} <> ks:
      Ops.Op{v2, a2, items.forget(is1, is2)} <> opdoc.forget(ss, ks)
    case _ ks:
      ks

def terms.same(a: List<&2, Ops.Item>, b: List<&2, Ops.Item>) -> Bool:
  match a b:
    case Ops.Item{t1, n1, f1} <> xs Ops.Item{t2, n2, f2} <> ys:
      Bool.and(Bool.not(Bool.xor(n1, n2)), terms.same(xs, ys))
    case Nil{} Nil{}:
      True{}
    case _ _:
      False{}

def opdoc.shape(a: List<&2, Ops.Op>, b: List<&2, Ops.Op>) -> Bool:
  match a b:
    case Ops.Op{v1, +a1, is1} <> xs Ops.Op{v2, +a2, is2} <> ys:
      Bool.and(Ops.verb_is(v1, v2), Bool.and(Nat.is_eq(a1, a2), Bool.and(terms.same(is1, is2), opdoc.shape(xs, ys))))
    case Nil{} Nil{}:
      True{}
    case _ _:
      False{}

def doc.ops(d: Ops.Doc) -> List<&2, Ops.Op>:
  match d:
    case Ops.Doc{f, r, os}:
      os

def stand_in.one(eff: Ops.Doc, +f: Ops.Doc) -> Ops.Doc:
  match eff:
    case Ops.Doc{+x, +r, +os}:
      Bool.pick(Ops.Doc, opdoc.shape(os, doc.ops(f)), Ops.Doc{x, r, opdoc.forget(doc.ops(f), os)}, Ops.Doc{x, r, os})

def stand_in.go(fs: List<&2, Ops.Doc>, eff: Ops.Doc) -> Ops.Doc:
  match fs:
    case Nil{}:
      eff
    case +f <> rest:
      stand_in.go(rest, stand_in.one(eff, f))

# `format::stand_in`: the document as a reader gets it — the one named, or
# where its bytes were destroyed the first standing in for it — with every
# item any stand-in of the same shape forgets forgotten.
def stand_in(base: Maybe<&2, Ops.Doc>, +fs: List<&2, Ops.Doc>) -> Maybe<&2, Ops.Doc>:
  match base fs:
    case Some{b} _:
      Some{stand_in.go(fs, b)}
    case None{} Nil{}:
      None{}
    case None{} f <> rest:
      Some{stand_in.go(f <> rest, f)}

def res.stand_in(base: Maybe<&2, Res.Doc>, fs: List<&2, Res.Doc>) -> Maybe<&2, Res.Doc>:
  match base fs:
    case Some{b} _:
      Some{b}
    case None{} Nil{}:
      None{}
    case None{} f <> rest:
      Some{f}

# What each revision names
# ------------------------

# The document a revision names for a file, as a reader gets it: operations
# to apply, or a resolution stating the file whole.
type Held is Data:
  Held.Ops{rev: String, file: String, doc: Ops.Doc}
  Held.Res{rev: String, file: String, doc: Res.Doc}

# What one step of the pass found, and what it holds.
type Step is Data:
  Step{findings: List<&2, Finding>, held: List<&2, Held>}

def step.then(a: Step, b: Step) -> Step:
  match a b:
    case Step{f1, h1} Step{f2, h2}:
      Step{List.append(&2, Finding, f1, f2), List.append(&2, Held, h1, h2)}

def pair.of(cut: Maybe<&2, T.Split>) -> List<&2, T.Split>:
  match cut:
    case None{}:
      Nil{}
    case Some{s}:
      [s]

# The `<file> <digest>` a revision's headers of one key state, in order.
def pairs(hs: List<&2, Rev.Header>, +key: String) -> List<&2, T.Split>:
  match hs:
    case Nil{}:
      Nil{}
    case Rev.Header{+k, +v} <> rest:
      +more = pairs(rest, key)
      Bool.pick(List<&2, T.Split>, String.eq(k, key), List.append(&2, T.Split, pair.of(T.split_once(v)), more), more)

def split.second(s: T.Split) -> String:
  match s:
    case T.Split{a, b}:
      b

def split.first(s: T.Split) -> String:
  match s:
    case T.Split{a, b}:
      a

def forgotten.note(+id: String, +named: String) -> Finding:
  note(ab12(id) ++ " names " ++ ab12(named) ++ ", whose bytes were destroyed; a forgetting document stands in for it")

def missing.payload(+id: String, +named: String) -> Finding:
  note(ab12(id) ++ " names the content " ++ ab12(named) ++ ", which is not here; it may not have arrived yet, or another writer may have overwritten it")

def missing.document(+id: String, +named: String) -> Finding:
  note(id ++ " names the operation document " ++ named ++ ", which this store does not hold yet")

def held.res(+id: String, +file: String, +named: String, absent: Bool, eff: Maybe<&2, Res.Doc>) -> Step:
  match eff:
    case None{}:
      Step{[missing.document(id, named)], Nil{}}
    case Some{d}:
      Step{Bool.pick(List<&2, Finding>, absent, [forgotten.note(id, named)], Nil{}), [Held.Res{id, file, d}]}

def held.ops(+id: String, +file: String, +named: String, absent: Bool, eff: Maybe<&2, Ops.Doc>) -> Step:
  match eff:
    case None{}:
      Step{[missing.document(id, named)], Nil{}}
    case Some{d}:
      Step{Bool.pick(List<&2, Finding>, absent, [forgotten.note(id, named)], Nil{}), [Held.Ops{id, file, d}]}

# An `edit`: a resolution where one is here or stands in, and otherwise
# operations, standing in or not.
def edit.step(+cs: List<&2, Content>, +id: String, +file: String, +named: String) -> Step:
  +r = res.of(cs, named)
  +rs = standing.res(cs, named)
  +o = opdoc.of(cs, named)
  Bool.pick(Step, Bool.or(Maybe.is_some(&2, Res.Doc, r), Bool.not(List.is_empty(&2, Res.Doc, rs))),
    held.res(id, file, named, Maybe.is_none(&2, Res.Doc, r), res.stand_in(r, rs)),
    held.ops(id, file, named, Maybe.is_none(&2, Ops.Doc, o), stand_in(o, standing.ops(cs, named))))

# A `bytes` header: its payload here, destroyed with a document saying so,
# or not here yet.
def bytes.step(+cs: List<&2, Content>, +ps: List<&2, Stored>, +id: String, +named: String) -> Step:
  Step{Bool.pick(List<&2, Finding>, payload.held(ps, named), Nil{},
    Bool.pick(List<&2, Finding>, standing.payload(cs, named), [forgotten.note(id, named)], [missing.payload(id, named)])), Nil{}}

# A `text` payload's lines, read where the store holds it: `None` for bytes
# that are not UTF-8.
type Lines is Data:
  Lines{id: String, text: Maybe<&2, String>}

def lines.of(ls: List<&2, Lines>, +id: String) -> Maybe<&2, Maybe<&2, String>>:
  match ls:
    case Nil{}:
      None{}
    case Lines{+i, +t} <> rest:
      Bool.pick(Maybe<&2, Maybe<&2, String>>, String.eq(i, id), Some{t}, lines.of(rest, id))

# `replay::creation`: a file stated whole replays as the document inserting
# its lines at 0 — nothing, for a file of no lines.
def creation.of(+items: List<&2, Ops.Item>) -> Maybe<&2, Ops.Doc>:
  Bool.pick(Maybe<&2, Ops.Doc>, List.is_empty(&2, Ops.Item, items), None{}, Some{Ops.Doc{None{}, None{}, [Ops.Op{Ops.Insert{}, 0n, items}]}})

def creation(+text: String) -> Maybe<&2, Ops.Doc>:
  creation.of(Ops.from_text(text))

def lines.held(+id: String, +file: String, eff: Maybe<&2, Ops.Doc>) -> List<&2, Held>:
  match eff:
    case None{}:
      Nil{}
    case Some{d}:
      [Held.Ops{id, file, d}]

def lines.read(+id: String, +file: String, +named: String, +os: List<&2, Ops.Doc>, t: Maybe<&2, String>) -> Step:
  match t:
    case None{}:
      Step{[error(ab12(id) ++ " names " ++ ab12(named) ++ " as text and it is not UTF-8, so no operation document could ever quote a line of it")], Nil{}}
    case Some{+text}:
      Step{Nil{}, lines.held(id, file, stand_in(creation(text), os))}

def lines.found(+id: String, +file: String, +named: String, +os: List<&2, Ops.Doc>, got: Maybe<&2, Maybe<&2, String>>) -> Step:
  match got:
    case Some{t}:
      lines.read(id, file, named, os, t)
    case None{}:
      Bool.pick(Step, List.is_empty(&2, Ops.Doc, os), Step{[missing.payload(id, named)], Nil{}},
        Step{[forgotten.note(id, named)], lines.held(id, file, stand_in(None{}, os))})

# A `text` header: the payload's lines as the file's creation, where the
# store holds it and it is text.
def lines.step(+cs: List<&2, Content>, +ps: List<&2, Stored>, +ls: List<&2, Lines>, +id: String, +file: String, +named: String) -> Step:
  lines.found(id, file, named, standing.ops(cs, named), Bool.pick(Maybe<&2, Maybe<&2, String>>, payload.held(ps, named), lines.of(ls, named), None{}))

def edits.steps(+cs: List<&2, Content>, +id: String, es: List<&2, T.Split>) -> Step:
  match es:
    case Nil{}:
      Step{Nil{}, Nil{}}
    case T.Split{+f, +d} <> rest:
      step.then(edit.step(cs, id, f, d), edits.steps(cs, id, rest))

def bytes.steps(+cs: List<&2, Content>, +ps: List<&2, Stored>, +id: String, es: List<&2, T.Split>) -> Step:
  match es:
    case Nil{}:
      Step{Nil{}, Nil{}}
    case T.Split{f, +d} <> rest:
      step.then(bytes.step(cs, ps, id, d), bytes.steps(cs, ps, id, rest))

def texts.steps(+cs: List<&2, Content>, +ps: List<&2, Stored>, +ls: List<&2, Lines>, +id: String, es: List<&2, T.Split>) -> Step:
  match es:
    case Nil{}:
      Step{Nil{}, Nil{}}
    case T.Split{+f, +d} <> rest:
      step.then(lines.step(cs, ps, ls, id, f, d), texts.steps(cs, ps, ls, id, rest))

def facts(f: Main.Full) -> List<&2, Rev.Header>:
  match f:
    case Main.Full{id, change, parents, supersedes, author, when, revised_by, revised, facts, message}:
      facts

# What each revision names: its `edit`s, then its `bytes`, then its `text`,
# each file in order.
def named.steps(+cs: List<&2, Content>, +ps: List<&2, Stored>, +ls: List<&2, Lines>, ds: List<&2, Main.Full>) -> Step:
  match ds:
    case Nil{}:
      Step{Nil{}, Nil{}}
    case +d <> rest:
      +id = Main.id_of(d)
      +hs = facts(d)
      step.then(step.then(step.then(edits.steps(cs, id, pairs(hs, "edit")), bytes.steps(cs, ps, id, pairs(hs, "bytes"))), texts.steps(cs, ps, ls, id, pairs(hs, "text"))),
        named.steps(cs, ps, ls, rest))

# Every digest a `text` or `bytes` header names.
def contents.named(ds: List<&2, Main.Full>) -> List<&2, String>:
  match ds:
    case Nil{}:
      Nil{}
    case +d <> rest:
      +hs = facts(d)
      List.append(&2, String, T.map(~T.Split, ~String, ~(s => split.second(s)), List.append(&2, T.Split, pairs(hs, "text"), pairs(hs, "bytes"))), contents.named(rest))

# A payload no revision names: nothing reads it.
def unnamed(+named: List<&2, String>, ps: List<&2, Stored>) -> List<&2, Finding>:
  match ps:
    case Nil{}:
      Nil{}
    case Stored{+i, +p} <> rest:
      +more = unnamed(named, rest)
      Bool.pick(List<&2, Finding>, Rev.member(named, i), more, note(p ++ " is not `.ops.txt` and no revision names it as content, so nothing reads it") <> more)

def stored.le(+a: Stored, +b: Stored) -> Bool:
  String.is_le(stored.id(a), stored.id(b))

# The payloads by digest, as a map keeps them: a digest stored twice is at
# the last path found.
def payloads.last(ps: List<&2, Stored>, +next: Maybe<&2, String>) -> List<&2, Stored>:
  match ps:
    case Nil{}:
      Nil{}
    case +s <> rest:
      +id = stored.id(s)
      +more = payloads.last(rest, Some{id})
      Bool.pick(List<&2, Stored>, Maybe.default(&2, Bool, Maybe.map(&2, String, Bool, n => String.eq(n, id), next), False{}), more, s <> more)

def payloads(fs: List<&2, OpFiled>) -> List<&2, Stored>:
  List.reverse(&2, Stored, payloads.last(List.sort(~Stored, ~(a => b => stored.le(b, a)), List.reverse(&2, Stored, payloads.go(fs))), None{}))

# Replaying a chain
# -----------------

# `State::apply`, and why not, in the Rust tool's words: every operation
# held to the parent it names — a delete to the items it quotes, a position
# to the parent's length — then the result built, held to having only its
# last line unterminated and to the digest the document states.
def at.item(items: List<&2, Ops.Item>, n: Nat) -> Ops.Item:
  Maybe.default(&2, Ops.Item, List.get(&2, Ops.Item, items, n), Ops.Item{SNil{}, True{}, False{}})

def item.agrees(+position: Nat, recorded: Ops.Item, found: Ops.Item) -> Maybe<&2, String>:
  match recorded found:
    case Ops.Item{+t1, +n1, f1} Ops.Item{+t2, n2, f2}:
      Bool.pick(Maybe<&2, String>, Bool.xor(n1, n2),
        Some{Bool.pick(String, n1, "the parent's item at position " ++ Nat.show(position) ++ " ends without a newline and this document deletes it as though it had one; add `\\ no newline` under that line",
          "`\\ no newline` says the item at position " ++ Nat.show(position) ++ " is the file's last and unterminated, and the parent's ends with a newline; delete the marker")},
        Bool.pick(Maybe<&2, String>, Bool.or(Bool.or(f1, f2), String.eq(t1, t2)), None{},
          Some{"the document deletes `" ++ t1 ++ "` at position " ++ Nat.show(position) ++ ", where the parent holds `" ++ t2 ++ "`; one of the two is corrupt, and the parent's digest says which"}))

def deleted.check(items: List<&2, Ops.Item>, +state: List<&2, Ops.Item>, +at: Nat) -> Maybe<&2, String>:
  match items:
    case Nil{}:
      None{}
    case +it <> rest:
      Maybe.or(&2, String, item.agrees(at, it, at.item(state, at)), deleted.check(rest, state, 1n+at))

def out.of(+position: Nat, +length: Nat) -> String:
  "this operation names position " ++ Nat.show(position) ++ " of a parent that has " ++ Nat.show(length) ++ " items; the document was written against a different state, so check that its revision's parents are the ones it was recorded from"

def op.check(+state: List<&2, Ops.Item>, +length: Nat, o: Ops.Op) -> Maybe<&2, String>:
  match o:
    case Ops.Op{Ops.Delete{}, +at, +items}:
      +end = Nat.add(at, List.length(&2, Ops.Item, items))
      Bool.pick(Maybe<&2, String>, Nat.is_gt(end, length), Some{out.of(end, length)}, deleted.check(items, state, at))
    case Ops.Op{Ops.Insert{}, +at, items}:
      Bool.pick(Maybe<&2, String>, Nat.is_gt(at, length), Some{out.of(at, length)}, None{})

def opdoc.check(+state: List<&2, Ops.Item>, +length: Nat, os: List<&2, Ops.Op>) -> Maybe<&2, String>:
  match os:
    case Nil{}:
      None{}
    case o <> rest:
      Maybe.or(&2, String, op.check(state, length, o), opdoc.check(state, length, rest))

def inserted.at(os: List<&2, Ops.Op>, +position: Nat) -> List<&2, Ops.Item>:
  match os:
    case Nil{}:
      Nil{}
    case Ops.Op{Ops.Insert{}, +at, +items} <> rest:
      +more = inserted.at(rest, position)
      Bool.pick(List<&2, Ops.Item>, Nat.is_eq(at, position), List.append(&2, Ops.Item, items, more), more)
    case o <> rest:
      inserted.at(rest, position)

def deleted.at(os: List<&2, Ops.Op>, +position: Nat) -> Bool:
  match os:
    case Nil{}:
      False{}
    case Ops.Op{Ops.Delete{}, +at, items} <> rest:
      Bool.or(Bool.and(Nat.is_ge(position, at), Nat.is_lt(position, Nat.add(at, List.length(&2, Ops.Item, items)))), deleted.at(rest, position))
    case o <> rest:
      deleted.at(rest, position)

def built(+os: List<&2, Ops.Op>, state: List<&2, Ops.Item>, +position: Nat) -> List<&2, Ops.Item>:
  match state:
    case Nil{}:
      inserted.at(os, position)
    case it <> rest:
      List.append(&2, Ops.Item, inserted.at(os, position), List.append(&2, Ops.Item, Bool.pick(List<&2, Ops.Item>, deleted.at(os, position), Nil{}, [it]), built(os, rest, 1n+position)))

def unterminated(items: List<&2, Ops.Item>, +n: Nat) -> Maybe<&2, Nat>:
  match items:
    case Nil{}:
      None{}
    case Ops.Item{t, term, f} <> Nil{}:
      None{}
    case Ops.Item{t, term, f} <> rest:
      +later = unterminated(rest, 1n+n)
      Bool.pick(Maybe<&2, Nat>, term, later, Some{n})

def result.check(r: Maybe<&2, String>, +items: List<&2, Ops.Item>) -> Result<&2, &2, String, List<&2, Ops.Item>>:
  match r:
    case None{}:
      Done{items}
    case Some{+stated}:
      +found = Ops.state_digest(items)
      Bool.pick(Result<&2, &2, String, List<&2, Ops.Item>>, Bool.or(Ops.any_forgotten(items), String.eq(stated, found)), Done{items},
        Fail{"this document says it produces " ++ stated ++ " and replaying it produces " ++ found ++ "; the document, its parent, or the replayer is wrong, and `shasum -a 256` on the replayed file is how to see which"})

def produced.check(r: Maybe<&2, String>, +items: List<&2, Ops.Item>, u: Maybe<&2, Nat>) -> Result<&2, &2, String, List<&2, Ops.Item>>:
  match u:
    case Some{n}:
      Fail{"only a file's last line may end without a newline, and item " ++ Nat.show(n) ++ " of the result does not end with one; delete that line and add it back with a terminator, in the revision that puts items after it"}
    case None{}:
      result.check(r, items)

def applied(+state: List<&2, Ops.Item>, r: Maybe<&2, String>, +os: List<&2, Ops.Op>, refused: Maybe<&2, String>) -> Result<&2, &2, String, List<&2, Ops.Item>>:
  match refused:
    case Some{e}:
      Fail{e}
    case None{}:
      +items = built(os, state, 0n)
      produced.check(r, items, unterminated(items, 0n))

def replay.apply(+state: List<&2, Ops.Item>, d: Ops.Doc) -> Result<&2, &2, String, List<&2, Ops.Item>>:
  match d:
    case Ops.Doc{f, r, +os}:
      applied(state, r, os, opdoc.check(state, List.length(&2, Ops.Item, state), os))

# Each head
# ---------

def parents.all(ds: List<&2, Main.Full>) -> List<&2, String>:
  match ds:
    case Nil{}:
      Nil{}
    case +d <> rest:
      List.append(&2, String, Main.parents_of(d), parents.all(rest))

# The revisions no revision names as a parent, in digest order.
def heads(+ds: List<&2, Main.Full>) -> List<&2, String>:
  Rev.without(Main.ids(ds), parents.all(ds))

# Whether a head's whole ancestry is here: every parent any of it names.
def all.held(+docs: List<&2, Main.Full>, ps: List<&2, String>) -> Bool:
  match ps:
    case Nil{}:
      True{}
    case +p <> rest:
      Bool.and(held(docs, p), all.held(docs, rest))

def complete(+docs: List<&2, Main.Full>, anc: List<&2, Main.Full>) -> Bool:
  match anc:
    case Nil{}:
      True{}
    case +a <> rest:
      Bool.and(all.held(docs, Main.parents_of(a)), complete(docs, rest))

# A head's ancestry as a chain, oldest first, or nothing where a revision on
# it has two parents or one is not here.
def chain.go(fuel: Nat, +docs: List<&2, Main.Full>, found: Maybe<&2, Main.Full>, acc: List<&2, Main.Full>) -> Maybe<&2, List<&2, Main.Full>>:
  match fuel found:
    case 0n _:
      None{}
    case _ None{}:
      None{}
    case 1n+k Some{Main.Full{i, c, parents, s, a, w, rb, rv, fs, m}}:
      match parents:
        case Nil{}:
          Some{Main.Full{i, c, Nil{}, s, a, w, rb, rv, fs, m} <> acc}
        case +p <> Nil{}:
          chain.go(k, docs, Main.find(docs, p), Main.Full{i, c, [p], s, a, w, rb, rv, fs, m} <> acc)
        case p <> q <> more:
          None{}

def chain(+docs: List<&2, Main.Full>, +head: String) -> Maybe<&2, List<&2, Main.Full>>:
  chain.go(1n+List.length(&2, Main.Full, docs), docs, Main.find(docs, head), Nil{})

def held.of(hs: List<&2, Held>, +rev: String, +file: String) -> Maybe<&2, Held>:
  match hs:
    case Nil{}:
      None{}
    case Held.Ops{+r, +f, d} <> rest:
      Bool.pick(Maybe<&2, Held>, Bool.and(String.eq(r, rev), String.eq(f, file)), Some{Held.Ops{r, f, d}}, held.of(rest, rev, file))
    case Held.Res{+r, +f, d} <> rest:
      Bool.pick(Maybe<&2, Held>, Bool.and(String.eq(r, rev), String.eq(f, file)), Some{Held.Res{r, f, d}}, held.of(rest, rev, file))

def held.is_ops(h: Maybe<&2, Held>) -> Bool:
  match h:
    case Some{Held.Ops{r, f, d}}:
      True{}
    case _:
      False{}

def files.named(+f: Main.Full) -> List<&2, String>:
  T.map(~T.Split, ~String, ~(s => split.first(s)), List.append(&2, T.Split, pairs(facts(f), "edit"), pairs(facts(f), "text")))

def all.ops(+hs: List<&2, Held>, +id: String, fs: List<&2, String>) -> Bool:
  match fs:
    case Nil{}:
      True{}
    case +f <> rest:
      Bool.and(held.is_ops(held.of(hs, id, f)), all.ops(hs, id, rest))

# Whether every document a revision names for a file is held as operations:
# a chain the arithmetic replays.
def held.ops.all(+hs: List<&2, Held>, ds: List<&2, Main.Full>) -> Bool:
  match ds:
    case Nil{}:
      True{}
    case +d <> rest:
      Bool.and(all.ops(hs, Main.id_of(d), files.named(d)), held.ops.all(hs, rest))

def disagrees(+head: String, +file: String, +because: String) -> Finding:
  error(head ++ ", file " ++ file ++ ": " ++ because)

def held.doc(h: Maybe<&2, Held>) -> Maybe<&2, Ops.Doc>:
  match h:
    case Some{Held.Ops{r, f, d}}:
      Some{d}
    case _:
      None{}

def replayed.step(r: Result<&2, &2, String, List<&2, Ops.Item>>, d: Maybe<&2, Ops.Doc>) -> Result<&2, &2, String, List<&2, Ops.Item>>:
  match r d:
    case Fail{e} _:
      Fail{e}
    case Done{s} None{}:
      Done{s}
    case Done{+s} Some{doc}:
      replay.apply(s, doc)

def replayed(+hs: List<&2, Held>, +file: String, chain: List<&2, Main.Full>, r: Result<&2, &2, String, List<&2, Ops.Item>>) -> Result<&2, &2, String, List<&2, Ops.Item>>:
  match chain:
    case Nil{}:
      r
    case +d <> rest:
      replayed(hs, file, rest, replayed.step(r, held.doc(held.of(hs, Main.id_of(d), file))))

def replayed.finding(+head: String, +file: String, r: Result<&2, &2, String, List<&2, Ops.Item>>) -> List<&2, Finding>:
  match r:
    case Fail{e}:
      [disagrees(head, file, e)]
    case Done{s}:
      Nil{}

# A chain replayed forward, one document applied to the state the one
# before it produced, for each file its history edits.
def chain.files(+hs: List<&2, Held>, +head: String, +chain: List<&2, Main.Full>, files: List<&2, String>) -> List<&2, Finding>:
  match files:
    case Nil{}:
      Nil{}
    case +f <> rest:
      List.append(&2, Finding, replayed.finding(head, f, replayed(hs, f, chain, Done{Nil{}})), chain.files(hs, head, chain, rest))

# Reading a file by the walk
# --------------------------

def said.for(ps: List<&2, T.Split>, +file: String) -> List<&2, String>:
  match ps:
    case Nil{}:
      Nil{}
    case T.Split{+f, +d} <> rest:
      +more = said.for(rest, file)
      Bool.pick(List<&2, String>, String.eq(f, file), d <> more, more)

def view.go(+rev: String, +file: String, anc: List<&2, Main.Full>) -> List<&2, String>:
  match anc:
    case Nil{}:
      Nil{}
    case +a <> rest:
      +more = view.go(rev, file, rest)
      Bool.pick(List<&2, String>, String.eq(Main.id_of(a), rev), more,
        List.append(&2, String, said.for(List.append(&2, T.Split, pairs(facts(a), "edit"), pairs(facts(a), "text")), file), more))

# What a resolution's author could see of the file: every document its past
# named for it.
def view(+docs: List<&2, Main.Full>, +rev: String, +file: String) -> List<&2, String>:
  view.go(rev, file, Main.ancestry(docs, rev))

def minted.count(+cs: List<&2, Content>, +ls: List<&2, Lines>, +d: String) -> Nat:
  +o = opdoc.of(cs, d)
  +r = res.of(cs, d)
  Bool.pick(Nat, Maybe.is_some(&2, Ops.Doc, o), List.length(&2, Ops.Item, Main.minted.inserts(Maybe.default(&2, List<&2, Ops.Op>, Maybe.map(&2, Ops.Doc, List<&2, Ops.Op>, x => doc.ops(x), o), Nil{}))),
    Bool.pick(Nat, Maybe.is_some(&2, Res.Doc, r), List.length(&2, Ops.Item, Maybe.default(&2, List<&2, Ops.Item>, Maybe.map(&2, Res.Doc, List<&2, Ops.Item>, x => Res.minted(x), r), Nil{})),
      List.length(&2, Ops.Item, Ops.from_text(Maybe.default(&2, String, Maybe.default(&2, Maybe<&2, String>, lines.of(ls, d), None{}), SNil{})))))

def unknown.reference(+rev: String, +d: String, +item: Nat) -> String:
  rev ++ " keeps item " ++ Nat.show(item) ++ " of " ++ d ++ ", which its author's view of the file does not hold; the resolution names a document outside this merge's past, or a run longer than that document has items"

# `MergeError::UnknownReference`: a `keep` naming a document its author's
# view never held, or more of one than it minted.
def keep.check(+cs: List<&2, Content>, +ls: List<&2, Lines>, +rev: String, +seen: List<&2, String>, ps: List<&2, Res.Piece>) -> Maybe<&2, String>:
  match ps:
    case Nil{}:
      None{}
    case Res.Piece.Keep{+d, +first, +count} <> rest:
      +holds = minted.count(cs, ls, d)
      Bool.pick(Maybe<&2, String>, Bool.not(Rev.member(seen, d)), Some{unknown.reference(rev, d, first)},
        Bool.pick(Maybe<&2, String>, Nat.is_gt(Nat.add(first, count), holds), Some{unknown.reference(rev, d, Nat.max(first, holds))},
          keep.check(cs, ls, rev, seen, rest)))
    case Res.Piece.Insert{items} <> rest:
      keep.check(cs, ls, rev, seen, rest)

def res.pieces(d: Res.Doc) -> List<&2, Res.Piece>:
  match d:
    case Res.Doc{f, r, ps}:
      ps

# `merge::quotes`, as `check` asks it
# -----------------------------------
#
# A file past a merge is read by walking every event of the head's
# ancestry, each stating what the store holds for the file — nothing where
# it holds nothing, since an absence is a finding of its own — in the order
# `merge.rs` takes: the lowest digest whose past is all placed. The first
# event whose document its author's view refuses stops the walk, and says
# why as `MergeError` does.

def quotes.stated(+digests: List<&2, String>, h: Maybe<&2, Held>) -> Maybe<&2, Merge.Statement>:
  match h:
    case None{}:
      None{}
    case Some{Held.Ops{r, f, d}}:
      Some{Merge.Edits{doc.ops(d)}}
    case Some{Held.Res{r, f, d}}:
      Main.walked.resolution(digests, d)

def quotes.revs(rs: List<&2, Main.Full>, +names: List<&2, String>, +digests: List<&2, String>, +ss: List<&2, Tree.Seen>, +hs: List<&2, Held>, +file: String) -> List<&2, Merge.Rev>:
  match rs:
    case Nil{}:
      Nil{}
    case +f <> rest:
      +id = Main.id_of(f)
      Merge.Rev{Main.indices(Tree.ancestors_of(ss, id), names), quotes.stated(digests, held.of(hs, id, file))} <> quotes.revs(rest, names, digests, ss, hs, file)

def all.in(xs: List<&2, Nat>, +ys: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case +x <> rest:
      Bool.and(Merge.has(ys, x), all.in(rest, ys))

# The lowest index not yet placed whose past is.
def ready(+g: List<&2, Merge.Rev>, +placed: List<&2, Nat>, ixs: List<&2, Nat>) -> List<&2, Nat>:
  match ixs:
    case Nil{}:
      Nil{}
    case +i <> rest:
      Bool.pick(List<&2, Nat>, Bool.and(Bool.not(Merge.has(placed, i)), all.in(Merge.past(g, i), placed)), [i], ready(g, placed, rest))

# `Graph::new`'s order: Kahn's, taking the lowest ready index each time.
# One placement a round, so as many rounds as events place them all.
def kahn(fuel: Nat, +g: List<&2, Merge.Rev>, +ixs: List<&2, Nat>, +placed: List<&2, Nat>) -> List<&2, Nat>:
  match fuel:
    case 0n:
      placed
    case 1n+p:
      kahn(p, g, ixs, List.append(&2, Nat, placed, ready(g, placed, ixs)))

# Whether an order places each event after every event it had seen: the
# order a walk of a history must take (`LAWS.check_walks_causally`).
def causal.go(o: List<&2, Nat>, +g: List<&2, Merge.Rev>, +before: List<&2, Nat>) -> Bool:
  match o:
    case Nil{}:
      True{}
    case +i <> rest:
      Bool.and(all.in(Merge.past(g, i), before), causal.go(rest, g, List.append(&2, Nat, before, [i])))

def causal(+g: List<&2, Merge.Rev>, o: List<&2, Nat>) -> Bool:
  causal.go(o, g, Nil{})

def out.of.range(+rev: String, +position: Nat, +length: Nat) -> String:
  rev ++ " names position " ++ Nat.show(position) ++ " of a file its author saw " ++ Nat.show(length) ++ " items of; the document was recorded against a different history"

def item.text(i: Ops.Item) -> String:
  match i:
    case Ops.Item{t, n, f}:
      t

def item.disagrees(+rev: String, +at: Nat, +it: Ops.Item, found: Maybe<&2, Ops.Item>) -> Maybe<&2, String>:
  match found:
    case None{}:
      None{}
    case Some{+f}:
      Bool.pick(Maybe<&2, String>, Ops.agrees(it, f), None{},
        Some{rev ++ " deletes `" ++ item.text(it) ++ "` at position " ++ Nat.show(at) ++ ", where its author's view held `" ++ item.text(f) ++ "`; one of the two is corrupt, and the digests say which"})

def deleted.disagrees(+rev: String, items: List<&2, Ops.Item>, +view: List<&2, Ops.Item>, +at: Nat) -> Maybe<&2, String>:
  match items:
    case Nil{}:
      None{}
    case it <> rest:
      Maybe.or(&2, String, item.disagrees(rev, at, it, List.get(&2, Ops.Item, view, at)), deleted.disagrees(rev, rest, view, 1n+at))

# `Tree::operations`: every position counted into the author's view, a
# delete's range before its items.
def op.refused(+rev: String, +view: List<&2, Ops.Item>, +length: Nat, o: Ops.Op) -> Maybe<&2, String>:
  match o:
    case Ops.Op{Ops.Delete{}, +at, +items}:
      +end = Nat.add(at, List.length(&2, Ops.Item, items))
      Bool.pick(Maybe<&2, String>, Nat.is_gt(end, length), Some{out.of.range(rev, end, length)}, deleted.disagrees(rev, items, view, at))
    case Ops.Op{Ops.Insert{}, +at, items}:
      Bool.pick(Maybe<&2, String>, Nat.is_gt(at, length), Some{out.of.range(rev, at, length)}, None{})

def ops.refused(+rev: String, +view: List<&2, Ops.Item>, os: List<&2, Ops.Op>) -> Maybe<&2, String>:
  match os:
    case Nil{}:
      None{}
    case o <> rest:
      Maybe.or(&2, String, op.refused(rev, view, List.length(&2, Ops.Item, view), o), ops.refused(rev, view, rest))

def keep.took(+rev: String, +d: String, +m: Nat, kept: List<&2, Merge.Name>, found: Maybe<&2, Merge.Name>) -> Result<&2, &2, String, List<&2, Merge.Name>>:
  match found:
    case None{}:
      Fail{unknown.reference(rev, d, m)}
    case Some{n}:
      Done{n <> kept}

def keep.one(+rev: String, +d: String, +authors: List<&2, Nat>, +view: List<&2, Merge.Node>, +m: Nat, r: Result<&2, &2, String, List<&2, Merge.Name>>) -> Result<&2, &2, String, List<&2, Merge.Name>>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{+kept}:
      keep.took(rev, d, m, kept, Merge.res.find(view, authors, m, kept))

def keep.run(ms: List<&2, Nat>, +rev: String, +d: String, +authors: List<&2, Nat>, +view: List<&2, Merge.Node>, r: Result<&2, &2, String, List<&2, Merge.Name>>) -> Result<&2, &2, String, List<&2, Merge.Name>>:
  match ms:
    case Nil{}:
      r
    case +m <> rest:
      keep.run(rest, rev, d, authors, view, keep.one(rev, d, authors, view, m, r))

def ordinals(count: Nat, +first: Nat) -> List<&2, Nat>:
  match count:
    case 0n:
      Nil{}
    case 1n+c:
      first <> ordinals(c, 1n+first)

# `Tree::resolution`: each `keep` takes the next element of the view
# standing under its name, and one with none left is the refusal.
def pieces.refused(ps: List<&2, Res.Piece>, +rev: String, +digests: List<&2, String>, +view: List<&2, Merge.Node>, r: Result<&2, &2, String, List<&2, Merge.Name>>) -> Result<&2, &2, String, List<&2, Merge.Name>>:
  match ps:
    case Nil{}:
      r
    case Res.Piece.Keep{+d, first, count} <> rest:
      pieces.refused(rest, rev, digests, view, keep.run(ordinals(count, first), rev, d, Main.authors_of(digests, d, 0n), view, r))
    case Res.Piece.Insert{items} <> rest:
      pieces.refused(rest, rev, digests, view, r)

def result.refusal(r: Result<&2, &2, String, List<&2, Merge.Name>>) -> Maybe<&2, String>:
  match r:
    case Fail{e}:
      Some{e}
    case Done{x}:
      None{}

def held.refused(+rev: String, +digests: List<&2, String>, +view: List<&2, Merge.Node>, h: Maybe<&2, Held>) -> Maybe<&2, String>:
  match h:
    case None{}:
      None{}
    case Some{Held.Ops{r, f, d}}:
      ops.refused(rev, Merge.file.of(view), doc.ops(d))
    case Some{Held.Res{r, f, d}}:
      result.refusal(pieces.refused(res.pieces(d), rev, digests, view, Done{Nil{}}))

def refusal(+g: List<&2, Merge.Rev>, +names: List<&2, String>, +digests: List<&2, String>, +hs: List<&2, Held>, +file: String, +t: List<&2, Merge.Node>, +e: Nat) -> String:
  +rev = Maybe.default(&2, String, List.get(&2, String, names, e), SNil{})
  Maybe.default(&2, String, held.refused(rev, digests, Merge.visible(Merge.restrict(t, Merge.past(g, e))), held.of(hs, rev, file)),
    "a revision behind it names a position or an item its author's view of the file does not hold; the document was recorded against a different history")

def quotes.stepped(+g: List<&2, Merge.Rev>, +names: List<&2, String>, +digests: List<&2, String>, +hs: List<&2, Held>, +file: String, +t: List<&2, Merge.Node>, +e: Nat, s: Maybe<&2, List<&2, Merge.Node>>) -> Result<&2, &2, String, List<&2, Merge.Node>>:
  match s:
    case None{}:
      Fail{refusal(g, names, digests, hs, file, t, e)}
    case Some{t2}:
      Done{t2}

def quotes.one(+g: List<&2, Merge.Rev>, +names: List<&2, String>, +digests: List<&2, String>, +hs: List<&2, Held>, +file: String, +e: Nat, r: Result<&2, &2, String, List<&2, Merge.Node>>) -> Result<&2, &2, String, List<&2, Merge.Node>>:
  match r:
    case Fail{m}:
      Fail{m}
    case Done{+t}:
      quotes.stepped(g, names, digests, hs, file, t, e, Merge.step(List.get(&2, Merge.Rev, g, e), t, e))

def quotes.go(o: List<&2, Nat>, +g: List<&2, Merge.Rev>, +names: List<&2, String>, +digests: List<&2, String>, +hs: List<&2, Held>, +file: String, r: Result<&2, &2, String, List<&2, Merge.Node>>) -> Result<&2, &2, String, List<&2, Merge.Node>>:
  match o:
    case Nil{}:
      r
    case +e <> rest:
      quotes.go(rest, g, names, digests, hs, file, quotes.one(g, names, digests, hs, file, e, r))

def quotes.found(+head: String, +file: String, r: Result<&2, &2, String, List<&2, Merge.Node>>) -> List<&2, Finding>:
  match r:
    case Fail{m}:
      [disagrees(head, file, m)]
    case Done{t}:
      Nil{}

def quotes.seen(+anc: List<&2, Main.Full>, +hs: List<&2, Held>, +head: String, +file: String, r: Result<&2, &2, Tree.Fault, List<&2, Tree.Seen>>) -> List<&2, Finding>:
  match r:
    case Fail{e}:
      Nil{}
    case Done{+ss}:
      +names = Main.ids(anc)
      +digests = Main.minted_digests(anc, file)
      +g = quotes.revs(anc, names, digests, ss, hs, file)
      +n = List.length(&2, Merge.Rev, g)
      quotes.found(head, file, quotes.go(kahn(n, g, Merge.upto(n), Nil{}), g, names, digests, hs, file, Done{Nil{}}))

def quotes.file(+docs: List<&2, Main.Full>, +hs: List<&2, Held>, +head: String, +file: String) -> List<&2, Finding>:
  +anc = Main.walked.ancestry(docs, head)
  quotes.seen(anc, hs, head, file, Tree.seen(List.length(&2, Main.Full, anc), Main.events_of(anc), Nil{}))

# A file past a merge, walked.
def walk.files(+docs: List<&2, Main.Full>, +cs: List<&2, Content>, +ls: List<&2, Lines>, +ds: List<&2, Store.Doc>, +hs: List<&2, Held>, +anc: List<&2, Main.Full>, +head: String, files: List<&2, String>) -> List<&2, Finding>:
  match files:
    case Nil{}:
      Nil{}
    case +f <> rest:
      List.append(&2, Finding, quotes.file(docs, hs, head, f), walk.files(docs, cs, ls, ds, hs, anc, head, rest))

def content.files(+docs: List<&2, Main.Full>, +cs: List<&2, Content>, +ls: List<&2, Lines>, +ds: List<&2, Store.Doc>, +hs: List<&2, Held>, +anc: List<&2, Main.Full>, +head: String, +files: List<&2, String>, +forgetting: Bool, c: Maybe<&2, List<&2, Main.Full>>) -> List<&2, Finding>:
  match c:
    case Some{+ch}:
      Bool.pick(List<&2, Finding>, Bool.and(Bool.not(forgetting), held.ops.all(hs, ch)), chain.files(hs, head, ch, files), walk.files(docs, cs, ls, ds, hs, anc, head, files))
    case None{}:
      walk.files(docs, cs, ls, ds, hs, anc, head, files)

def head.tree(+docs: List<&2, Main.Full>, +cs: List<&2, Content>, +ls: List<&2, Lines>, +ds: List<&2, Store.Doc>, +hs: List<&2, Held>, +anc: List<&2, Main.Full>, +head: String, +forgetting: Bool, t: Result<&2, &2, Main.Refused, Tree.Tree()>) -> List<&2, Finding>:
  match t:
    case Fail{Main.Refused{c, +msg}}:
      [error(msg)]
    case Done{x}:
      content.files(docs, cs, ls, ds, hs, anc, head, set.of(T.concat(String, T.map(~Main.Full, ~List<&2, String>, ~(a => files.named(a)), anc))), forgetting, chain(docs, head))

def head.findings(+docs: List<&2, Main.Full>, +cs: List<&2, Content>, +ls: List<&2, Lines>, +ds: List<&2, Store.Doc>, +hs: List<&2, Held>, +forgetting: Bool, +head: String) -> List<&2, Finding>:
  +anc = Main.ancestry(docs, head)
  Bool.pick(List<&2, Finding>, complete(docs, anc), head.tree(docs, cs, ls, ds, hs, anc, head, forgetting, Main.tree.r(docs, head)), Nil{})

def heads.findings(+docs: List<&2, Main.Full>, +cs: List<&2, Content>, +ls: List<&2, Lines>, +ds: List<&2, Store.Doc>, +hs: List<&2, Held>, +forgetting: Bool, heads: List<&2, String>) -> List<&2, Finding>:
  match heads:
    case Nil{}:
      Nil{}
    case +h <> rest:
      List.append(&2, Finding, head.findings(docs, cs, ls, ds, hs, forgetting, h), heads.findings(docs, cs, ls, ds, hs, forgetting, rest))

# A redaction still arriving
# --------------------------
#
# `still_quoted`: where the walk reads a file, each element's sites — the
# document that wrote it and each document whose `delete` quotes it — and
# the first of them to say the element was destroyed. Every other site
# that still holds its text undercuts that redaction, which is what a
# forgetting document that has not finished arriving looks like.

# A `delete`'s quote of one element: which element, which event, and
# whether the quote is the text or the marker standing for it.
type Quote is Data:
  Quote{target: Merge.Name, event: Nat, forgotten: Bool}

def uc.forgotten(i: Ops.Item) -> Bool:
  match i:
    case Ops.Item{t, n, f}:
      f

def uc.deletes(items: List<&2, Ops.Item>, +view: List<&2, Merge.Node>, +at: Nat, +e: Nat) -> List<&2, Quote>:
  match items:
    case Nil{}:
      Nil{}
    case +it <> rest:
      List.append(&2, Quote, Maybe.default(&2, List<&2, Quote>, Maybe.map(&2, Merge.Node, List<&2, Quote>, n => [Quote{Merge.Node.name(n), e, uc.forgotten(it)}], List.get(&2, Merge.Node, view, at)), Nil{}),
        uc.deletes(rest, view, 1n+at, e))

def uc.op(+view: List<&2, Merge.Node>, +e: Nat, o: Ops.Op) -> List<&2, Quote>:
  match o:
    case Ops.Op{Ops.Delete{}, +at, items}:
      uc.deletes(items, view, at, e)
    case Ops.Op{Ops.Insert{}, at, items}:
      Nil{}

def uc.ops(os: List<&2, Ops.Op>, +view: List<&2, Merge.Node>, +e: Nat) -> List<&2, Quote>:
  match os:
    case Nil{}:
      Nil{}
    case o <> rest:
      List.append(&2, Quote, uc.op(view, e, o), uc.ops(rest, view, e))

def uc.event(+t: List<&2, Merge.Node>, +e: Nat, ev: Maybe<&2, Merge.Rev>) -> List<&2, Quote>:
  match ev:
    case Some{Merge.Rev{+seen, Some{Merge.Edits{ops}}}}:
      uc.ops(ops, Merge.visible(Merge.restrict(t, seen)), e)
    case _:
      Nil{}

# The walk again, keeping every quote each `delete` made.
type QW is Data:
  QW{tree: List<&2, Merge.Node>, quotes: List<&2, Quote>}

def uc.step(+g: List<&2, Merge.Rev>, +e: Nat, st: QW) -> QW:
  match st:
    case QW{+t, +qs}:
      QW{Maybe.default(&2, List<&2, Merge.Node>, Merge.step(List.get(&2, Merge.Rev, g, e), t, e), t), List.append(&2, Quote, qs, uc.event(t, e, List.get(&2, Merge.Rev, g, e)))}

def uc.go(o: List<&2, Nat>, +g: List<&2, Merge.Rev>, st: QW) -> QW:
  match o:
    case Nil{}:
      st
    case +e <> rest:
      uc.go(rest, g, uc.step(g, e, st))

def uc.quote(qs: List<&2, Quote>, +name: Merge.Name, +e: Nat) -> Maybe<&2, Bool>:
  match qs:
    case Nil{}:
      None{}
    case Quote{+t, +ev, +f} <> rest:
      Bool.pick(Maybe<&2, Bool>, Bool.and(Merge.Name.eq(t, name), Nat.is_eq(ev, e)), Some{f}, uc.quote(rest, name, e))

# Where an element stands: the digest a document is named by for the file,
# and whether its text there is the marker.
def uc.site.at(+d: String, f: Maybe<&2, Bool>) -> List<&2, T.Split>:
  match f:
    case None{}:
      Nil{}
    case Some{+x}:
      Bool.pick(List<&2, T.Split>, String.is_empty(d), Nil{}, [T.Split{d, Bool.pick(String, x, "1", "0")}])

def uc.site(+digests: List<&2, String>, +e: Nat, f: Maybe<&2, Bool>) -> List<&2, T.Split>:
  uc.site.at(Maybe.default(&2, String, List.get(&2, String, digests, e), SNil{}), f)

def uc.deleters(+digests: List<&2, String>, +qs: List<&2, Quote>, +name: Merge.Name, es: List<&2, Nat>) -> List<&2, T.Split>:
  match es:
    case Nil{}:
      Nil{}
    case +e <> rest:
      List.append(&2, T.Split, uc.site(digests, e, uc.quote(qs, name, e)), uc.deleters(digests, qs, name, rest))

def uc.first(ss: List<&2, T.Split>) -> Maybe<&2, String>:
  match ss:
    case Nil{}:
      None{}
    case T.Split{+d, +f} <> rest:
      Bool.pick(Maybe<&2, String>, String.eq(f, "1"), Some{d}, uc.first(rest))

def uc.against(+forgets: String, ss: List<&2, T.Split>) -> List<&2, T.Split>:
  match ss:
    case Nil{}:
      Nil{}
    case T.Split{+d, +f} <> rest:
      +more = uc.against(forgets, rest)
      Bool.pick(List<&2, T.Split>, Bool.or(String.eq(f, "1"), String.eq(d, forgets)), more, T.Split{d, forgets} <> more)

def uc.sites(+ss: List<&2, T.Split>, m: Maybe<&2, String>) -> List<&2, T.Split>:
  match m:
    case None{}:
      Nil{}
    case Some{+forgets}:
      uc.against(forgets, ss)

def uc.node(+digests: List<&2, String>, +qs: List<&2, Quote>, n: Merge.Node) -> List<&2, T.Split>:
  match n:
    case Merge.Node{+nm, +it, pl, +d}:
      +ss = List.append(&2, T.Split, uc.site(digests, Merge.Node.author(Merge.Node{nm, it, pl, d}), Some{uc.forgotten(it)}),
        uc.deleters(digests, qs, nm, List.sort(~Nat, ~(a => b => Nat.is_le(a, b)), d)))
      uc.sites(ss, uc.first(ss))

def uc.nodes(+digests: List<&2, String>, +qs: List<&2, Quote>, ns: List<&2, Merge.Node>) -> List<&2, T.Split>:
  match ns:
    case Nil{}:
      Nil{}
    case n <> rest:
      List.append(&2, T.Split, uc.node(digests, qs, n), uc.nodes(digests, qs, rest))

def uc.walked(+digests: List<&2, String>, ok: Bool, st: QW) -> List<&2, T.Split>:
  match st:
    case QW{t, +qs}:
      Bool.pick(List<&2, T.Split>, ok, uc.nodes(digests, qs, t), Nil{})

def uc.seen(+anc: List<&2, Main.Full>, +hs: List<&2, Held>, +file: String, r: Result<&2, &2, Tree.Fault, List<&2, Tree.Seen>>) -> List<&2, T.Split>:
  match r:
    case Fail{e}:
      Nil{}
    case Done{+ss}:
      +names = Main.ids(anc)
      +digests = Main.minted_digests(anc, file)
      +g = quotes.revs(anc, names, digests, ss, hs, file)
      +n = List.length(&2, Merge.Rev, g)
      +o = kahn(n, g, Merge.upto(n), Nil{})
      uc.walked(digests, Result.is_done(&2, &2, String, List<&2, Merge.Node>, quotes.go(o, g, names, digests, hs, file, Done{Nil{}})), uc.go(o, g, QW{Nil{}, Nil{}}))

def uc.files(+docs: List<&2, Main.Full>, +hs: List<&2, Held>, +head: String, files: List<&2, String>) -> List<&2, T.Split>:
  match files:
    case Nil{}:
      Nil{}
    case +f <> rest:
      +anc = Main.walked.ancestry(docs, head)
      List.append(&2, T.Split, uc.seen(anc, hs, f, Tree.seen(List.length(&2, Main.Full, anc), Main.events_of(anc), Nil{})), uc.files(docs, hs, head, rest))

# The heads read by the walk: where a redaction is anywhere, or a chain
# does not hold operations all the way, as `content.files` decides.
def uc.head(+docs: List<&2, Main.Full>, +hs: List<&2, Held>, +forgetting: Bool, +head: String) -> List<&2, T.Split>:
  +anc = Main.ancestry(docs, head)
  +walked = Maybe.default(&2, Bool, Maybe.map(&2, List<&2, Main.Full>, Bool, ch => Bool.or(forgetting, Bool.not(held.ops.all(hs, ch))), chain(docs, head)), True{})
  Bool.pick(List<&2, T.Split>, Bool.and(Bool.and(complete(docs, anc), Result.is_done(&2, &2, Main.Refused, Tree.Tree(), Main.tree.r(docs, head))), walked),
    uc.files(docs, hs, head, set.of(T.concat(String, T.map(~Main.Full, ~List<&2, String>, ~(a => files.named(a)), anc)))), Nil{})

def uc.heads(+docs: List<&2, Main.Full>, +hs: List<&2, Held>, +forgetting: Bool, heads: List<&2, String>) -> List<&2, T.Split>:
  match heads:
    case Nil{}:
      Nil{}
    case +h <> rest:
      List.append(&2, T.Split, uc.head(docs, hs, forgetting, h), uc.heads(docs, hs, forgetting, rest))

def uc.said(ss: List<&2, T.Split>) -> List<&2, Finding>:
  match ss:
    case Nil{}:
      Nil{}
    case T.Split{+d, +f} <> rest:
      note(ab12(d) ++ " still quotes items " ++ ab12(f) ++ " says were destroyed; a redaction that has not finished arriving looks exactly like this") <> uc.said(rest)

def uc.key(s: T.Split) -> String:
  match s:
    case T.Split{d, f}:
      d ++ " " ++ f

def uc.keys(ss: List<&2, T.Split>) -> List<&2, String>:
  match ss:
    case Nil{}:
      Nil{}
    case s <> rest:
      uc.key(s) <> uc.keys(rest)

def uc.unkey(+s: String) -> T.Split:
  Maybe.default(&2, T.Split, T.split_once(s), T.Split{s, SNil{}})

def uc.unkeys(ks: List<&2, String>) -> List<&2, T.Split>:
  match ks:
    case Nil{}:
      Nil{}
    case k <> rest:
      uc.unkey(k) <> uc.unkeys(rest)

# Each undercut once, in digest order, as the Rust tool's set holds them.
def undercuts(+docs: List<&2, Main.Full>, +hs: List<&2, Held>, +forgetting: Bool, +heads: List<&2, String>) -> List<&2, Finding>:
  uc.said(uc.unkeys(set.of(uc.keys(uc.heads(docs, hs, forgetting, heads)))))

# Which heads can be produced
# ---------------------------

def standing.all(+cs: List<&2, Content>) -> List<&2, String>:
  List.append(&2, String, targets.ops(cs), List.append(&2, String, targets.res(cs), targets.payloads(cs)))

# Whether a digest is here for a reader: a document in either grammar that
# states operations, a payload, or something standing in for it — decision
# 0014 destroys the bytes and keeps the shape.
def digest.held(+cs: List<&2, Content>, +ps: List<&2, Stored>, +standing: List<&2, String>, +x: String) -> Bool:
  Bool.or(doc.held(cs, x), Bool.or(payload.held(ps, x), Rev.member(standing, x)))

def unheld(+cs: List<&2, Content>, +ps: List<&2, Stored>, +standing: List<&2, String>, xs: List<&2, String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case +x <> rest:
      +more = unheld(cs, ps, standing, rest)
      Bool.pick(List<&2, String>, digest.held(cs, ps, standing, x), more, x <> more)

def keeps.of(ps: List<&2, Res.Piece>) -> List<&2, String>:
  match ps:
    case Nil{}:
      Nil{}
    case Res.Piece.Keep{d, f, c} <> rest:
      d <> keeps.of(rest)
    case Res.Piece.Insert{items} <> rest:
      keeps.of(rest)

def first.res(rs: List<&2, Res.Doc>) -> Maybe<&2, Res.Doc>:
  match rs:
    case Nil{}:
      None{}
    case r <> rest:
      Some{r}

# A resolution is not self-contained: a `keep` of something absent is a
# hole in the file as a missing document is.
def edits.missing(+cs: List<&2, Content>, +ps: List<&2, Stored>, +standing: List<&2, String>, es: List<&2, String>) -> List<&2, String>:
  match es:
    case Nil{}:
      Nil{}
    case +named <> rest:
      +keeps = Maybe.default(&2, List<&2, String>, Maybe.map(&2, Res.Doc, List<&2, String>, r => keeps.of(res.pieces(r)), Maybe.or(&2, Res.Doc, res.of(cs, named), first.res(standing.res(cs, named)))), Nil{})
      List.append(&2, String, Bool.pick(List<&2, String>, digest.held(cs, ps, standing, named), unheld(cs, ps, standing, keeps), [named]), edits.missing(cs, ps, standing, rest))

def missing.from(+cs: List<&2, Content>, +ps: List<&2, Stored>, +standing: List<&2, String>, anc: List<&2, Main.Full>) -> List<&2, String>:
  match anc:
    case Nil{}:
      Nil{}
    case +a <> rest:
      +hs = facts(a)
      List.append(&2, String, edits.missing(cs, ps, standing, T.map(~T.Split, ~String, ~(s => split.second(s)), pairs(hs, "edit"))),
        List.append(&2, String, unheld(cs, ps, standing, T.map(~T.Split, ~String, ~(s => split.second(s)), List.append(&2, T.Split, pairs(hs, "text"), pairs(hs, "bytes")))),
          missing.from(cs, ps, standing, rest)))

def parents.unheld(+docs: List<&2, Main.Full>, anc: List<&2, Main.Full>) -> List<&2, String>:
  match anc:
    case Nil{}:
      Nil{}
    case +a <> rest:
      List.append(&2, String, Rev.without(Main.parents_of(a), Main.ids(docs)), parents.unheld(docs, rest))

def incomplete.of(+head: String, +missing: List<&2, String>) -> List<&2, Finding>:
  Bool.pick(List<&2, Finding>, List.is_empty(&2, String, missing), Nil{},
    [Finding{False{}, ab12(head) ++ " is a head this store cannot produce: its history names " ++ missing.said(missing) ++ ", which is not here", True{}}])

# A head whose history is not all here: every digest its ancestry names
# that nothing here answers.
def incomplete(+docs: List<&2, Main.Full>, +cs: List<&2, Content>, +ps: List<&2, Stored>, +standing: List<&2, String>, heads: List<&2, String>) -> List<&2, Finding>:
  match heads:
    case Nil{}:
      Nil{}
    case +h <> rest:
      +anc = Main.ancestry(docs, h)
      List.append(&2, Finding, incomplete.of(h, set.of(List.append(&2, String, parents.unheld(docs, anc), missing.from(cs, ps, standing, anc)))), incomplete(docs, cs, ps, standing, rest))

# `skipped/`
# ----------

# A rule of `skipped/` and the file stating it.
type Rule is Data:
  Rule{rule: Skip.Rule, file: String}

def rule.of(r: Rule) -> Skip.Rule:
  match r:
    case Rule{x, f}:
      x

# What one file of `skipped/` is: a rule, prose, or wrong — and where it is
# wrong because it still states the retired `skip-suffix`, the line that
# says the same thing.
def retired.go(ls: List<&2, String>) -> Maybe<&2, String>:
  match ls:
    case Nil{}:
      None{}
    case +l <> rest:
      +value = Naming.trim_space(String.drop(l, 12n))
      +more = retired.go(rest)
      Bool.pick(Maybe<&2, String>, Bool.or(String.is_empty(l), String.starts_with(l, "#")), more,
        Bool.pick(Maybe<&2, String>, Bool.and(String.starts_with(l, "skip-suffix "), Bool.not(String.is_empty(value))), Some{"skip-name *" ++ value}, more))

def retired(+text: String) -> Maybe<&2, String>:
  retired.go(Folder.lines.trimmed(String.split(text, '\n')))

def skipped.wrong(+path: String, +e: String, r: Maybe<&2, String>) -> Finding:
  match r:
    case Some{x}:
      error(path ++ " states `skip-suffix`, which is retired and no longer reads; `" ++ x ++ "` says the same thing, matched against a file's own name as the old key always was")
    case None{}:
      error(path ++ ": " ++ e ++ "; a rule that does not read would take a file somebody asked it to leave")

# What `skipped/` found: its findings so far, and the rules its files state.
type Stating is Data:
  Stating{findings: List<&2, Finding>, rules: List<&2, Rule>}

def stating.then(a: Stating, b: Stating) -> Stating:
  match a b:
    case Stating{f1, r1} Stating{f2, r2}:
      Stating{List.append(&2, Finding, f1, f2), List.append(&2, Rule, r1, r2)}

def skipped.one(+path: String, +text: String, st: Folder.Stated) -> Stating:
  match st:
    case Folder.Stated.One{sc}:
      Stating{Nil{}, [Rule{Skip.Rule{sc, Skip.private.line(Folder.lines.trimmed(String.split(text, '\n')))}, path}]}
    case Folder.Stated.None{}:
      Stating{Nil{}, Nil{}}
    case Folder.Stated.Wrong{e}:
      Stating{[skipped.wrong(path, e, retired(text))], Nil{}}

# A rule file whose bytes are not UTF-8 is `Unreadable`, and states nothing.
def skipped.read(+p: String, r: Result<&2, &2, String, String>) -> Stating:
  match r:
    case Fail{e}:
      Stating{[error(p ++ ": " ++ e)], Nil{}}
    case Done{+t}:
      skipped.one(p, t, Folder.rule_in(t))

def skipped.go(ps: List<&2, String>, k: Class) -> IO(Stating):
  match ps k:
    case Nil{} _:
      IO.pure(Stating, Stating{Nil{}, Nil{}})
    case p <> +rest Class.Platform{}:
      skipped.go(rest, class(rest, SNil{}))
    case +p <> +rest _:
      do IO<Stating>:
        r : Result<&2, &2, String, String> <- Store.read_utf8(p)
        more : Stating <- skipped.go(rest, class(rest, SNil{}))
        return stating.then(skipped.read(p, r), more)

def rule.show(r: Rule) -> String:
  match r:
    case Rule{x, f}:
      Skip.show(x)

def rule.file(r: Rule) -> String:
  match r:
    case Rule{x, f}:
      f

def files.stating(rs: List<&2, Rule>, +line: String) -> List<&2, String>:
  match rs:
    case Nil{}:
      Nil{}
    case +r <> rest:
      +more = files.stating(rest, line)
      Bool.pick(List<&2, String>, String.eq(rule.show(r), line), rule.file(r) <> more, more)

def twice.go(lines: List<&2, String>, +rs: List<&2, Rule>) -> List<&2, Finding>:
  match lines:
    case Nil{}:
      Nil{}
    case +l <> rest:
      +fs = files.stating(rs, l)
      +more = twice.go(rest, rs)
      Bool.pick(List<&2, Finding>, Nat.is_gt(List.length(&2, String, fs), 1n),
        note("`" ++ l ++ "` is stated twice, which means what stating it once means; either file may go:" ++ joined.go(fs)) <> more, more)

# One rule stated by two files, which means what stating it once means.
def twice(+rs: List<&2, Rule>) -> List<&2, Finding>:
  twice.go(set.of(T.map(~Rule, ~String, ~(r => rule.show(r)), rs)), rs)

def scope.value(+sc: Folder.Scope) -> String:
  Skip.value(sc) ++ Bool.pick(String, Skip.under(sc), "/", SNil{})

def shared.file(rs: List<&2, Rule>, +sc: Folder.Scope) -> Maybe<&2, String>:
  match rs:
    case Nil{}:
      None{}
    case Rule{Skip.Rule{+x, p}, +f} <> rest:
      Bool.pick(Maybe<&2, String>, Bool.and(Bool.not(p), Skip.scope.eq(x, sc)), Some{f}, shared.file(rest, sc))

def both.of(+value: String, +private: String, found: Maybe<&2, String>) -> List<&2, Finding>:
  match found:
    case None{}:
      Nil{}
    case Some{shared}:
      [error("`" ++ value ++ "` is covered privately by " ++ private ++ " and shared by " ++ shared ++ ": rules union, so both stand, so the shared one names the path in every copy and the private one accomplishes nothing; delete whichever of the two you did not mean")]

# Decision 0051's one way the travel axis fails: one scope stated on both
# sides of it.
def both(+all: List<&2, Rule>, rs: List<&2, Rule>) -> List<&2, Finding>:
  match rs:
    case Nil{}:
      Nil{}
    case Rule{Skip.Rule{+x, p}, +f} <> rest:
      List.append(&2, Finding, Bool.pick(List<&2, Finding>, p, both.of(scope.value(x), f, shared.file(all, x)), Nil{}), both(all, rest))

# A rule covering a path some head holds, said once for each rule.
type Covering is Data:
  Covering{said: List<&2, String>, findings: List<&2, Finding>}

def covering.rule(c: Covering, +path: String, r: Rule) -> Covering:
  match c r:
    case Covering{+said, +fs} Rule{Skip.Rule{+x, +p}, +f}:
      +line = Skip.show(Skip.Rule{x, p})
      Bool.pick(Covering, Bool.and(Folder.covers(x, path), Bool.not(Rev.member(said, line))),
        Covering{line <> said, List.append(&2, Finding, fs, [error(f ++ " states `" ++ line ++ "`, which covers `" ++ path ++ "` in this history; `record` refuses while it stands, and deleting that file is the fix — history holds what it holds")])},
        Covering{said, fs})

def covering.rules(rs: List<&2, Rule>, +path: String, c: Covering) -> Covering:
  match rs:
    case Nil{}:
      c
    case r <> rest:
      covering.rules(rest, path, covering.rule(c, path, r))

def covering.paths(ps: List<&2, String>, +rs: List<&2, Rule>, c: Covering) -> Covering:
  match ps:
    case Nil{}:
      c
    case +path <> rest:
      covering.paths(rest, rs, covering.rules(rs, path, c))

def entry.le(+a: Tree.Entry, +b: Tree.Entry) -> Bool:
  String.is_le(Tree.entry_file(a), Tree.entry_file(b))

# A tree's paths, in the order of the files that hold them.
def paths.in(t: Result<&2, &2, Main.Refused, Tree.Tree()>) -> List<&2, String>:
  match t:
    case Fail{e}:
      Nil{}
    case Done{+es}:
      T.map(~Tree.Entry, ~String, ~(e => Tree.entry_path(e)), List.sort(~Tree.Entry, ~(a => b => entry.le(a, b)), es))

def covering.heads(+docs: List<&2, Main.Full>, +rs: List<&2, Rule>, hs: List<&2, String>, c: Covering) -> Covering:
  match hs:
    case Nil{}:
      c
    case +h <> rest:
      covering.heads(docs, rs, rest, covering.paths(paths.in(Main.tree.r(docs, h)), rs, c))

def covering.findings(c: Covering) -> List<&2, Finding>:
  match c:
    case Covering{s, fs}:
      fs

# Decision 0045's directory, read through: what no loader says.
def skipped.findings(+docs: List<&2, Main.Full>, +stale: Bool, +stale_path: String, +opens: Bool, st: Stating) -> List<&2, Finding>:
  match st:
    case Stating{fs, +rs}:
      List.append(&2, Finding, Bool.pick(List<&2, Finding>, stale, [error(stale_path ++ " states nothing: rules are one to a file in `skipped/`, and leaving this here says history skips what it does not")], Nil{}),
        List.append(&2, Finding, fs, List.append(&2, Finding, twice(rs), List.append(&2, Finding, both(rs, rs),
          Bool.pick(List<&2, Finding>, opens, covering.findings(covering.heads(docs, rs, Rev.heads(Main.history(docs)), Covering{Nil{}, Nil{}})), Nil{})))))

# `names/`
# --------

def facts.files(hs: List<&2, Rev.Header>) -> List<&2, String>:
  match hs:
    case Nil{}:
      Nil{}
    case Rev.Header{+k, +v} <> rest:
      +more = facts.files(rest)
      Bool.pick(List<&2, String>, Bool.or(Bool.or(String.eq(k, "add"), String.eq(k, "move")), Bool.or(Bool.or(String.eq(k, "drop"), String.eq(k, "edit")), Bool.or(String.eq(k, "text"), String.eq(k, "bytes")))),
        T.word(v) <> more, more)

def change.of(f: Main.Full) -> String:
  match f:
    case Main.Full{id, change, parents, supersedes, author, when, revised_by, revised, facts, message}:
      change

# Whether a bookmark pointing here finds what it names: a change, a
# revision, or a file some revision says anything about (decision 0024).
def pointed.one(+d: Main.Full, t: Bm.Target) -> Bool:
  match t:
    case Bm.Target.Change{c}:
      String.eq(change.of(d), c)
    case Bm.Target.Revision{r}:
      String.eq(Main.id_of(d), r)
    case Bm.Target.File{f}:
      Rev.member(facts.files(facts(d)), f)

def pointed(ds: List<&2, Main.Full>, +t: Bm.Target) -> Bool:
  match ds:
    case Nil{}:
      False{}
    case +d <> rest:
      Bool.or(pointed.one(d, t), pointed(rest, t))


def bookmark.finding(+docs: List<&2, Main.Full>, +path: String, +name: String, r: Result<&2, &2, String, Bm.Stated>) -> List<&2, Finding>:
  match r:
    case Fail{e}:
      [error(path ++ ": " ++ e)]
    case Done{Bm.Stated{+t, p}}:
      Bool.pick(List<&2, Finding>, pointed(docs, t), Nil{}, [note("`" ++ name ++ "` points at `" ++ Bm.show_target(t) ++ "`, which is not here yet")])

def name.text(+docs: List<&2, Main.Full>, +path: String, +name: String, r: Result<&2, &2, String, String>) -> List<&2, Finding>:
  match r:
    case Fail{e}:
      [error(path ++ ": " ++ e)]
    case Done{text}:
      bookmark.finding(docs, path, name, Bm.parse(text))

def name.read(+docs: List<&2, Main.Full>, +path: String, n: Maybe<&2, String>) -> IO(List<&2, Finding>):
  match n:
    case None{}:
      IO.pure(List<&2, Finding>, [foreign(path)])
    case Some{+name}:
      do IO<List<&2, Finding>>:
        r : Result<&2, &2, String, String> <- Store.read_utf8(path)
        return name.text(docs, path, name, r)

# Each file of `names/`: a bookmark read, or a file nothing reads.
def names.go(+docs: List<&2, Main.Full>, +cut: Nat, ps: List<&2, String>, k: Class) -> IO(List<&2, Finding>):
  match ps k:
    case Nil{} _:
      IO.pure(List<&2, Finding>, Nil{})
    case p <> +rest Class.Platform{}:
      names.go(docs, cut, rest, class(rest, SNil{}))
    case +p <> +rest _:
      do IO<List<&2, Finding>>:
        here : List<&2, Finding> <- name.read(docs, p, Bm.name(String.drop(p, cut)))
        more : List<&2, Finding> <- names.go(docs, cut, rest, class(rest, SNil{}))
        return List.append(&2, Finding, here, more)

# Merges
# ------

def whole.files(ds: List<&2, Main.Full>) -> List<&2, String>:
  match ds:
    case Nil{}:
      Nil{}
    case +d <> rest:
      List.append(&2, String, T.map(~T.Split, ~String, ~(s => split.first(s)), pairs(facts(d), "bytes")), whole.files(rest))

# What one parent holds of a file: nothing said, a state, or no answer —
# which is a finding of its own elsewhere.
type Held2 is Data:
  Held2.Absent{}
  Held2.Known{items: List<&2, Ops.Item>}
  Held2.Unknown{}

def state.walked(r: Result<&2, &2, String, List<&2, Ops.Item>>) -> Held2:
  match r:
    case Done{items}:
      Held2.Known{items}
    case Fail{e}:
      Held2.Unknown{}

def state.of(+docs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +parent: String, +file: String, c: Maybe<&2, Result<&2, &2, String, Main.Rule>>) -> Held2:
  match c:
    case None{}:
      Held2.Absent{}
    case Some{Fail{e}}:
      Held2.Unknown{}
    case Some{Done{Main.Known{items}}}:
      Held2.Known{items}
    case Some{Done{Main.Unstated{}}}:
      state.walked(Main.walked(docs, ds, parent, file))

def states(+docs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +file: String, +cs: List<&2, Main.Contents>, ps: List<&2, String>) -> List<&2, Held2>:
  match ps:
    case Nil{}:
      Nil{}
    case +p <> rest:
      state.of(docs, ds, p, file, Main.content_of(cs, p)) <> states(docs, ds, file, cs, rest)

# Whether a parent's state differs from the one before it, where there is
# one. A match of its own rather than `Maybe.map` of a lambda: Bend's native
# build reads `Bool.or(found, Maybe.default(&2, Bool, Maybe.map(...), False{}))`
# as false where the JS build and the Rust tool read true.
def differ.from(last: Maybe<&2, List<&2, Ops.Item>>, items: List<&2, Ops.Item>) -> Bool:
  match last:
    case None{}:
      False{}
    case Some{l}:
      Bool.not(Main.items_eq(l, items))

# Whether the parents' states differ: where one has no answer, they do not
# — that is already a finding.
def differ.go(ss: List<&2, Held2>, last: Maybe<&2, List<&2, Ops.Item>>, found: Bool) -> Bool:
  match ss:
    case Nil{}:
      found
    case Held2.Absent{} <> rest:
      differ.go(rest, last, found)
    case Held2.Unknown{} <> rest:
      False{}
    case Held2.Known{+items} <> rest:
      differ.go(rest, Some{items}, Bool.or(found, differ.from(last, items)))

def edit.named(hs: List<&2, Rev.Header>, +file: String) -> Maybe<&2, String>:
  List.head(&2, String, said.for(pairs(hs, "edit"), file))

def resolves(+cs: List<&2, Content>, n: Maybe<&2, String>) -> Bool:
  match n:
    case None{}:
      False{}
    case Some{+named}:
      Bool.or(Maybe.is_some(&2, Res.Doc, res.of(cs, named)), Bool.not(List.is_empty(&2, Res.Doc, standing.res(cs, named))))

def resolution.of(+cs: List<&2, Content>, n: Maybe<&2, String>) -> List<&2, Res.Piece>:
  match n:
    case None{}:
      Nil{}
    case Some{+named}:
      Maybe.default(&2, List<&2, Res.Piece>, Maybe.map(&2, Res.Doc, List<&2, Res.Piece>, r => res.pieces(r), Maybe.or(&2, Res.Doc, res.of(cs, named), first.res(standing.res(cs, named)))), Nil{})

# Decision 0032's obligation, both ways: a merge states a resolution where
# its parents differ about a file, and nowhere else; and what it keeps is
# what its author could see.
def join.file(+docs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +cs: List<&2, Content>, +ls: List<&2, Lines>, +oldest: List<&2, Main.Full>, +m: Main.Full, +file: String) -> List<&2, Finding>:
  +id = Main.id_of(m)
  +named = edit.named(facts(m), file)
  +res = resolves(cs, named)
  +diff = differ.go(states(docs, ds, file, Main.contents.go(oldest, ds, file, Nil{}), Main.parents_of(m)), None{}, False{})
  List.append(&2, Finding,
    Bool.pick(List<&2, Finding>, Bool.and(Bool.not(diff), res), [error(id ++ " states a resolution for the file " ++ file ++ ", which both its parents leave exactly the same; a merge resolves where its parents differ, and where they agree the file is that agreed state")],
      Bool.pick(List<&2, Finding>, Bool.and(diff, Bool.not(res)), [note(id ++ " is a merge whose parents differ about the file " ++ file ++ " and which states no resolution; reading that file past this revision needs the merge algorithm rather than arithmetic")], Nil{})),
    Bool.pick(List<&2, Finding>, res, Maybe.default(&2, List<&2, Finding>, Maybe.map(&2, String, List<&2, Finding>, e => [disagrees(id, file, e)], keep.check(cs, ls, id, view(docs, id, file), resolution.of(cs, named))), Nil{}), Nil{}))

def join.files(+docs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +cs: List<&2, Content>, +ls: List<&2, Lines>, +oldest: List<&2, Main.Full>, +m: Main.Full, +whole: List<&2, String>, files: List<&2, String>) -> List<&2, Finding>:
  match files:
    case Nil{}:
      Nil{}
    case +f <> rest:
      +more = join.files(docs, ds, cs, ls, oldest, m, whole, rest)
      Bool.pick(List<&2, Finding>, Rev.member(whole, f), more, List.append(&2, Finding, join.file(docs, ds, cs, ls, oldest, m, f), more))

def files.in(t: Result<&2, &2, Main.Refused, Tree.Tree()>) -> List<&2, String>:
  match t:
    case Fail{e}:
      Nil{}
    case Done{+es}:
      T.map(~Tree.Entry, ~String, ~(e => Tree.entry_file(e)), List.sort(~Tree.Entry, ~(a => b => entry.le(a, b)), es))

def joins(+docs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +cs: List<&2, Content>, +ls: List<&2, Lines>, +oldest: List<&2, Main.Full>, +whole: List<&2, String>, ms: List<&2, Main.Full>) -> List<&2, Finding>:
  match ms:
    case Nil{}:
      Nil{}
    case +m <> rest:
      +more = joins(docs, ds, cs, ls, oldest, whole, rest)
      Bool.pick(List<&2, Finding>, Nat.is_ge(List.length(&2, String, Main.parents_of(m)), 2n),
        List.append(&2, Finding, join.files(docs, ds, cs, ls, oldest, m, whole, files.in(Main.tree.r(docs, Main.id_of(m)))), more), more)

def joined.any(ds: List<&2, Main.Full>) -> Bool:
  match ds:
    case Nil{}:
      False{}
    case +d <> rest:
      Bool.or(Nat.is_ge(List.length(&2, String, Main.parents_of(d)), 2n), joined.any(rest))

def wrong.any(cs: List<&2, Content>) -> Bool:
  match cs:
    case Nil{}:
      False{}
    case Content{i, Parsed.Wrong{e}} <> rest:
      True{}
    case c <> rest:
      wrong.any(rest)

def resolutions.findings(+docs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +cs: List<&2, Content>, +ls: List<&2, Lines>, opens: Bool) -> List<&2, Finding>:
  Bool.pick(List<&2, Finding>, Bool.and(Bool.and(opens, joined.any(docs)), Bool.not(wrong.any(cs))),
    joins(docs, ds, cs, ls, List.reverse(&2, Main.Full, Main.presentation(docs)), whole.files(docs), docs), Nil{})

# The pass
# --------

def filed.docs(fs: List<&2, OpFiled>) -> List<&2, Store.Doc>:
  match fs:
    case Nil{}:
      Nil{}
    case OpFiled.Doc{Read{+p, +i, +t}} <> rest:
      Store.Doc{p, i, String.length(t), t} <> filed.docs(rest)
    case OpFiled.Payload{p, s} <> rest:
      filed.docs(rest)

def stored.at(ps: List<&2, Stored>, +id: String) -> Maybe<&2, String>:
  match ps:
    case Nil{}:
      None{}
    case Stored{+i, +p} <> rest:
      Bool.pick(Maybe<&2, String>, String.eq(i, id), Some{p}, stored.at(rest, id))

# A `text` payload's lines: what the file was created with, where it is
# UTF-8, which decision 0017 makes a file of lines.
type Texts is Data:
  Texts{lines: List<&2, Lines>, docs: List<&2, Store.Doc>}

def texts.read(+id: String, +path: String, +bs: List<&2, U32>) -> Texts:
  +d = Store.doc_of(path, bs)
  Texts{[Lines{id, Bool.pick(Maybe<&2, String>, Folder.is_utf8(bs), Some{Store.text_of(d)}, None{})}], [d]}

def texts.then(a: Texts, b: Texts) -> Texts:
  match a b:
    case Texts{l1, d1} Texts{l2, d2}:
      Texts{List.append(&2, Lines, l1, l2), List.append(&2, Store.Doc, d1, d2)}

# The `text` payloads the pass reads as a file's lines, and where: each
# digest asked for, in order, that the store holds a payload under
# (`LAWS.check_reads_only_held_text`).
def texts.planned(+id: String, at: Maybe<&2, String>, more: List<&2, T.Split>) -> List<&2, T.Split>:
  match at:
    case None{}:
      more
    case Some{+path}:
      T.Split{id, path} <> more

def texts.plan(ids: List<&2, String>, +ps: List<&2, Stored>) -> List<&2, T.Split>:
  match ids:
    case Nil{}:
      Nil{}
    case +id <> rest:
      texts.planned(id, stored.at(ps, id), texts.plan(rest, ps))

def texts.at(plan: List<&2, T.Split>) -> IO(Texts):
  match plan:
    case Nil{}:
      IO.pure(Texts, Texts{Nil{}, Nil{}})
    case T.Split{+id, +path} <> rest:
      do IO<Texts>:
        bs : List<&2, U32> <- Utf8.read_file(path)
        more : Texts <- texts.at(rest)
        return texts.then(texts.read(id, path, bs), more)

def text.ids(ds: List<&2, Main.Full>) -> List<&2, String>:
  match ds:
    case Nil{}:
      Nil{}
    case +d <> rest:
      List.append(&2, String, T.map(~T.Split, ~String, ~(s => split.second(s)), pairs(facts(d), "text")), text.ids(rest))

def opened(r: Result<&1, &1, U32 & String, File>) -> IO(Bool):
  match r:
    case Fail{e}:
      IO.pure(Bool, False{})
    case Done{f}:
      do IO<Bool>:
        File.close(f)
        return True{}

def wrong.names(fs: List<&2, Finding>) -> Bool:
  List.any(~&2, ~Finding, ~(f => is_error(f)), fs)

def wrong.rules(st: Stating) -> Bool:
  match st:
    case Stating{fs, rs}:
      List.any(~&2, ~Finding, ~(f => is_error(f)), fs)

def texts.lines(t: Texts) -> List<&2, Lines>:
  match t:
    case Texts{l, d}:
      l

def texts.docs(t: Texts) -> List<&2, Store.Doc>:
  match t:
    case Texts{l, d}:
      d

def step.held(s: Step) -> List<&2, Held>:
  match s:
    case Step{f, h}:
      h

def step.findings(s: Step) -> List<&2, Finding>:
  match s:
    case Step{f, h}:
      f

# `Store::check`: every finding, in the order the pass finds them.
# What the pass read, everything it needs to say what it found: the header,
# and each directory walked and read.
type Gathered is Data:
  Gathered{root: String, header: Maybe<&2, String>, revisions: Walked, rfiled: List<&2, Filed>, operations: Walked, ofiled: List<&2, OpFiled>, texts: Texts, stale: Bool, skipped: Stating, names: Walked, named: List<&2, Finding>}

# What `check` finds in what it read, in the order the Rust tool reports it.
def found(g: Gathered) -> List<&2, Finding>:
  match g:
    case Gathered{+root, htext, +rw2, +rf2, +ow2, +of2, +tx2, +stale2, +st2, +nw2, +nf2}:
      +hf = header(htext)
      +docs = documents(rf2)
      +cs = contents(of2)
      +ps = payloads(of2)
      +ls = texts.lines(tx2)
      +ds = List.append(&2, Store.Doc, filed.docs(of2), texts.docs(tx2))
      +steps = named.steps(cs, ps, ls, docs)
      +hs = step.held(steps)
      +hd = heads(docs)
      +revs = revisions.findings(rf2)
      +opens = Bool.not(Bool.or(Bool.or(Bool.not(List.is_empty(&2, Finding, hf)), List.any(~&2, ~Finding, ~(f => is_error(f)), revs)), Bool.or(wrong.names(nf2), wrong.rules(st2))))
      List.concat(&2, Finding, [
        hf,
        unfollowed(walked.links(rw2)), revs, duplicates(stored.revisions(rf2)),
        missing_parents(docs, docs), stands(docs, docs),
        unfollowed(walked.links(ow2)), operations.findings(of2), duplicates(stored.operations(of2)),
        resurrected(cs, ps, List.append(&2, String, set.of(targets.ops(cs)), List.append(&2, String, set.of(targets.res(cs)), set.of(targets.payloads(cs))))),
        step.findings(steps), unnamed(contents.named(docs), ps),
        heads.findings(docs, cs, ls, ds, hs, Bool.not(List.is_empty(&2, String, targets.ops(cs))), hd),
        undercuts(docs, hs, Bool.not(List.is_empty(&2, String, targets.ops(cs))), hd),
        incomplete(docs, cs, ps, standing.all(cs), hd),
        skipped.findings(docs, stale2, root ++ "/skipped.txt", opens, st2),
        resolutions.findings(docs, ds, cs, ls, opens),
        unfollowed(walked.links(nw2)), nf2])

def pass(+root: String) -> IO(List<&2, Finding>):
  do IO<List<&2, Finding>>:
    h : Result<&1, &1, U32 & String, File> <- File.open(root ++ "/historica.txt", "r")
    htext : Maybe<&2, String> <- header.read(root, h)
    rw : Walked <- walk(root, "revisions")
    +rw2 : Walked = rw
    rf : List<&2, Filed> <- revisions.go(walked.files(rw2), class(walked.files(rw2), ".rev.txt"))
    +rf2 : List<&2, Filed> = rf
    +docs : List<&2, Main.Full> = documents(rf2)
    ow : Walked <- walk(root, "operations")
    +ow2 : Walked = ow
    of : List<&2, OpFiled> <- operations.go(walked.files(ow2), class(walked.files(ow2), ".ops.txt"))
    +of1 : List<&2, OpFiled> = of
    stats : List<&2, String> <- Store.stats(SNil{}, payload.paths(of1))
    +of2 : List<&2, OpFiled> = attach(of1, stats)
    +ps : List<&2, Stored> = payloads(of2)
    +tids : List<&2, String> = set.of(text.ids(docs))
    tx : Texts <- texts.at(texts.plan(tids, ps))
    stale : Result<&1, &1, U32 & String, File> <- File.open(root ++ "/skipped.txt", "r")
    stale2 : Bool <- opened(stale)
    sw : Walked <- walk(root, "skipped")
    +sw2 : Walked = sw
    st : Stating <- skipped.go(walked.files(sw2), class(walked.files(sw2), SNil{}))
    nw : Walked <- walk(root, "names")
    +nw2 : Walked = nw
    nf : List<&2, Finding> <- names.go(docs, 1n+String.length(root), walked.files(nw2), class(walked.files(nw2), SNil{}))
    return found(Gathered{root, htext, rw2, rf2, ow2, of2, tx, stale2, st, nw2, nf})

# Whether `check` passes a store, as `prune`, `receive` and `export` ask
# before destroying or copying anything (`Report::is_ok`): no error, whatever
# the notes say and whether or not every head can be produced.
def passes(+root: String) -> IO(Bool):
  do IO<Bool>:
    fs : List<&2, Finding> <- pass(root)
    return Bool.not(fails(fs, False{}))

# The command
# -----------

# `--complete` wherever it stands, and every other word a directory.
type Asked is Data:
  Asked{complete: Bool, words: List<&2, String>}

def asked.go(args: List<&2, String>, complete: Bool, +words: List<&2, String>) -> Asked:
  match args:
    case Nil{}:
      Asked{complete, words}
    case +w <> rest:
      +flag = String.eq(w, "--complete")
      asked.go(rest, Bool.or(complete, flag), Bool.pick(List<&2, String>, flag, words, List.append(&2, String, words, [w])))

# Every word but `--complete`, in order (`LAWS.check_reads_its_words`).
def words.other(ws: List<&2, String>) -> List<&2, String>:
  match ws:
    case Nil{}:
      Nil{}
    case +w <> rest:
      +more = words.other(rest)
      Bool.pick(List<&2, String>, String.eq(w, "--complete"), more, w <> more)

def asked(args: List<&2, String>) -> Asked:
  asked.go(args, False{}, Nil{})

# `named`: a directory given is the store itself — where it holds a
# `historica.txt`, or is called `history` — or the repository holding one.
def named.of(+given: String, header: Bool) -> String:
  Bool.pick(String, Bool.or(header, String.eq(Folder.last_component(Skip.trim_slashes(given)), "history")), given, Identity.joined(given, "history"))

def named.base(+path: String, r: Result<&1, &1, U32 & String, String>) -> IO(String):
  match r:
    case Fail{Tuple{c, msg}}:
      Main.die(String, 1, msg)
    case Done{+base}:
      +given = Identity.joined(base, path)
      do IO<String>:
        h : Result<&1, &1, U32 & String, File> <- File.open(Identity.joined(given, "historica.txt"), "r")
        header : Bool <- opened(h)
        return named.of(given, header)

def named(+path: String) -> IO(String):
  do IO<String>:
    b : Result<&1, &1, U32 & String, String> <- Store.base()
    named.base(path, b)

def root.of(ws: List<&2, String>) -> IO(String):
  match ws:
    case Nil{}:
      Store.root()
    case +w <> rest:
      named(w)

def extra.of(ws: List<&2, String>) -> IO(Unit):
  match ws:
    case a <> b <> rest:
      Main.die(Unit, 2, "`check` takes one directory, and `" ++ b ++ "` is a second")
    case _:
      IO.pure(Unit, Unit{})

def shown(+root: String, r: Result<&1, &1, U32 & String, String>) -> String:
  match r:
    case Done{real}:
      real
    case Fail{e}:
      root

def reported(+shown: String, +complete: Bool, +fs: List<&2, Finding>) -> IO(Unit):
  do IO<Unit>:
    IO.write(report(fs, shown, complete))
    Store.ended(Bool.pick(Nat, fails(fs, complete), 1n, 0n))

def check.asked(a: Asked) -> IO(Unit):
  match a:
    case Asked{+complete, +ws}:
      do IO<Unit>:
        root : String <- root.of(ws)
        +r : String = root
        extra.of(ws)
        fs : List<&2, Finding> <- pass(r)
        real : Result<&1, &1, U32 & String, String> <- Store.really(r)
        reported(shown(r, real), complete, sorted(fs))

# `check [<dir>] [--complete]`.
def check(args: List<&2, String>) -> IO(Unit):
  check.asked(asked(args))
