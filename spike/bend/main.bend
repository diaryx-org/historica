# historica, in Bend: the readable core of the format, over the store it finds.
#
# The reading commands `historica` has, in the shape it has them: the store is
# the `history` directory here or above, and a target is `head`, a change ID
# or a revision digest, either abbreviated to any unambiguous prefix.
#
#   bend main.bend -- log [<target>|<from>..<to>] [--limit <n>] [--author <text>]
#                         [--grep <text>] [--since <when>] [--until <when>]
#                         [--path <path>] [--fields]
#                                            the history, newest first
#   bend main.bend -- show <target> [<path>] one document as stored
#   bend main.bend -- files <target>         the file set at a revision
#   bend main.bend -- cat <target> <path>    one file's content at a revision
#   bend main.bend -- check                  every document, named by digest
#   bend main.bend -- names                  the bookmarks, and what they point at
#   bend main.bend -- replay <ops docs..>    the file a chain of documents makes
#   bend main.bend -- diff [<target>] [<path>] [--onto <target>] [--color <when>]
#                                            what a revision did, or the folder
#                                            against the head, rendered
#   bend main.bend -- blame [<target>] <path> [--lines <first>..<last>]
#                                            who wrote each line
#   bend main.bend -- opdiff <parent> <child> the operation document between two files
#
# Or compile it: `bend main.bend -o main.c`, then link the archive `ffi/`
# builds — `check.py` does both. What `bend main.bend` runs and what the
# binary runs are the same program over two adapters (`store.bend`).
#
# A target may also be a bookmark (`names/`), which wins over any other
# spelling, `head` included; a path may be `file:` and a file identifier or
# a file bookmark, or `path:` and a path. A merge's resolution — the file
# stated whole, by `keep` and `insert` — is read where an `edit` names one.

import Base
import ./text.bend as T
import ./ident.bend as Id
import ./ops.bend as Ops
import ./revision.bend as Rev
import ./store.bend as Store
import ./tree.bend as Tree
import ./utf8.bend as Utf8
import ./bookmark.bend as Bm
import ./resolution.bend as Res
import ./similar.bend as Sim
import ./folder.bend as Folder

# A refusal, said the way the Rust tool says it.
def die(-A: Type, code: U32, msg: String) -> IO(A):
  IO.die(A, code, "historica: " ++ msg)

# A revision the store holds: its digest and what its document says.
type Full is Data:
  Full{id: String, change: String, parents: List<&2, String>, supersedes: List<&2, String>,
       author: String, when: String, revised_by: Maybe<&2, String>, revised: Maybe<&2, String>,
       facts: List<&2, Rev.Header>, message: String}

def full(+id: String, parsed: Result<&2, &2, String, Rev.Rev>) -> Maybe<&2, Full>:
  match parsed:
    case Done{Rev.Rev{change, parents, supersedes, author, when, revised_by, revised, facts, message}}:
      Some{Full{id, change, parents, supersedes, author, when, revised_by, revised, facts, message}}
    case Fail{e}:
      None{}

def keep_full(b: Bool, f: Full, rest: List<&2, Full>) -> List<&2, Full>:
  match b:
    case True{}:
      f <> rest
    case False{}:
      rest

def push_full(f: Maybe<&2, Full>, rest: List<&2, Full>) -> List<&2, Full>:
  match f:
    case None{}:
      rest
    case Some{x}:
      x <> rest

# The revisions among a store's documents: what `revisions/` holds and the
# parser accepts. `check` is where the rest are reported.
def fulls(+root: String, ds: List<&2, Store.Doc>) -> List<&2, Full>:
  match ds:
    case Nil{}:
      Nil{}
    case Store.Doc{+path, +id, size, +text} <> rest:
      push_full(Bool.pick(Maybe<&2, Full>, Store.in_revisions(root, path), full(id, Rev.parse(text)), None{}), fulls(root, rest))

def id_of(f: Full) -> String:
  match f:
    case Full{id, change, parents, supersedes, author, when, revised_by, revised, facts, message}:
      id

def change_of(f: Full) -> String:
  match f:
    case Full{id, change, parents, supersedes, author, when, revised_by, revised, facts, message}:
      change

def parents_of(f: Full) -> List<&2, String>:
  match f:
    case Full{id, change, parents, supersedes, author, when, revised_by, revised, facts, message}:
      parents

def author_of(f: Full) -> String:
  match f:
    case Full{id, change, parents, supersedes, author, when, revised_by, revised, facts, message}:
      author

def message_of(f: Full) -> String:
  match f:
    case Full{id, change, parents, supersedes, author, when, revised_by, revised, facts, message}:
      message

def when_of(f: Full) -> String:
  match f:
    case Full{id, change, parents, supersedes, author, when, revised_by, revised, facts, message}:
      when

def facts_of(f: Full) -> List<&2, Rev.Header>:
  match f:
    case Full{id, change, parents, supersedes, author, when, revised_by, revised, facts, message}:
      facts

def revision_of(f: Full) -> Rev.Revision:
  match f:
    case Full{id, change, parents, supersedes, author, when, revised_by, revised, facts, message}:
      Rev.Revision{id, change, parents, supersedes, message}

def history.go(fs: List<&2, Full>, h: Rev.History()) -> Rev.History():
  match fs:
    case Nil{}:
      h
    case f <> rest:
      history.go(rest, Rev.insert(h, revision_of(f)))

def history(fs: List<&2, Full>) -> Rev.History():
  history.go(fs, Rev.empty())

def find(fs: List<&2, Full>, +id: String) -> Maybe<&2, Full>:
  match fs:
    case Nil{}:
      None{}
    case Full{+i, change, parents, supersedes, author, when, revised_by, revised, facts, message} <> rest:
      Bool.pick(Maybe<&2, Full>, String.eq(i, id), Some{Full{i, change, parents, supersedes, author, when, revised_by, revised, facts, message}}, find(rest, id))

def ids(fs: List<&2, Full>) -> List<&2, String>:
  T.map(~Full, ~String, ~(f => id_of(f)), fs)

def changes.push(+c: String, +rest: List<&2, String>) -> List<&2, String>:
  Rev.keep(Bool.not(Rev.member(rest, c)), c, rest)

# The distinct changes, each once.
def changes(fs: List<&2, Full>) -> List<&2, String>:
  match fs:
    case Nil{}:
      Nil{}
    case f <> rest:
      changes.push(change_of(f), changes(rest))

# Documents by digest, for the content a revision names.
def doc_by_id(ds: List<&2, Store.Doc>, +id: String) -> Maybe<&2, String>:
  match ds:
    case Nil{}:
      None{}
    case Store.Doc{path, +i, size, text} <> rest:
      Bool.pick(Maybe<&2, String>, String.starts_with(i, id), Some{text}, doc_by_id(rest, id))

# Bookmarks
# ---------

# Every bookmark the store holds, in name order, read before any target is:
# a bookmark file that does not parse refuses the command, as the Rust
# tool's store refuses to open, naming the file. A file under `names/` that
# is not a bookmark's is passed over.
type Named is Data:
  Named{name: String, path: String}

def named.of(+path: String, found: Maybe<&2, String>, rest: List<&2, Named>) -> List<&2, Named>:
  match found:
    case None{}:
      rest
    case Some{n}:
      Named{n, path} <> rest

def named(ps: List<&2, String>) -> List<&2, Named>:
  match ps:
    case Nil{}:
      Nil{}
    case +p <> rest:
      named.of(p, Bm.name(p), named(rest))

def named.name(n: Named) -> String:
  match n:
    case Named{name, path}:
      name

def named.le(+a: Named, +b: Named) -> Bool:
  String.is_le(named.name(a), named.name(b))

def bookmark.stated(+file: String, name: String, r: Result<&2, &2, String, Bm.Stated>) -> IO(Bm.Bookmark):
  match r:
    case Fail{e}:
      die(Bm.Bookmark, 1, file ++ ": " ++ e)
    case Done{Bm.Stated{t, p}}:
      IO.pure(Bm.Bookmark, Bm.Bookmark{name, t, p})

def bookmark.read(+file: String, name: String) -> IO(Bm.Bookmark):
  do IO<Bm.Bookmark>:
    text : String <- Store.read_text(file)
    bookmark.stated(file, name, Bm.parse(text))

def bookmarks.read(+root: String, ns: List<&2, Named>) -> IO(List<&2, Bm.Bookmark>):
  match ns:
    case Nil{}:
      IO.pure(List<&2, Bm.Bookmark>, Nil{})
    case Named{n, p} <> rest:
      do IO<List<&2, Bm.Bookmark>>:
        b : Bm.Bookmark <- bookmark.read(root ++ "/" ++ p, n)
        bs : List<&2, Bm.Bookmark> <- bookmarks.read(root, rest)
        return b <> bs

# What opening the store reads besides its documents: the bookmarks, then
# the rules of `skipped/` — each refusing the store, as the Rust tool's
# `Store::open` does, where a file is not what it should be.
def bookmarks(+root: String) -> IO(List<&2, Bm.Bookmark>):
  do IO<List<&2, Bm.Bookmark>>:
    ps : List<&2, String> <- Store.name_paths(root)
    bs : List<&2, Bm.Bookmark> <- bookmarks.read(root, List.sort(~Named, ~(a => b => named.le(a, b)), named(ps)))
    rules : List<&2, Folder.Scope> <- Folder.rules(root)
    return bs

# Whether a change's current revision is this one.
def resolved_to(state: Rev.ChangeState, +id: String) -> Bool:
  match state:
    case Rev.Resolved{r}:
      String.eq(r, id)
    case _:
      False{}

def names_at.one(+h: Rev.History(), +id: String, t: Bm.Target) -> Bool:
  match t:
    case Bm.Target.Revision{r}:
      String.eq(r, id)
    case Bm.Target.Change{c}:
      resolved_to(Rev.change_state(h, c), id)
    case Bm.Target.File{f}:
      False{}

# Every bookmark resolving to this revision, each after two spaces: a file
# bookmark names no revision, so it never marks one.
def names_at(bs: List<&2, Bm.Bookmark>, +h: Rev.History(), +id: String) -> String:
  match bs:
    case Nil{}:
      SNil{}
    case Bm.Bookmark{n, t, p} <> rest:
      Bool.pick(String, names_at.one(h, id, t), "  " ++ n, SNil{}) ++ names_at(rest, h, id)

# Targets
# -------

def all_chars(~f: Char -> Bool, s: String) -> Bool:
  T.all_chars(~f, s)

def is_hex(c: Char) -> Bool:
  T.is_hex(c)

def with_prefix(xs: List<&2, String>, +p: String) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case +x <> rest:
      Rev.keep(String.starts_with(x, p), x, with_prefix(rest, p))

def listed(xs: List<&2, String>) -> String:
  match xs:
    case Nil{}:
      SNil{}
    case x <> rest:
      "\n  " ++ x ++ listed(rest)

def one_of(found: List<&2, String>, +p: String, +none: String, +what: String) -> Result<&2, &2, String, String>:
  match found:
    case Nil{}:
      Fail{none ++ " `" ++ p ++ "`"}
    case only <> Nil{}:
      Done{only}
    case +several:
      Fail{"`" ++ p ++ "` could be " ++ Nat.show(List.length(&2, String, several)) ++ " " ++ what ++ ":" ++ listed(several)}

# The current revision of a change, or the reason there is not exactly one.
def current(state: Rev.ChangeState, +change: String, +named_by: String) -> Result<&2, &2, String, String>:
  match state:
    case Rev.Resolved{id}:
      Done{id}
    case Rev.UnknownChange{}:
      Fail{named_by ++ " names the change " ++ change ++ ", which no revision here claims"}
    case Rev.Abandoned{}:
      Fail{"every revision of " ++ change ++ " was superseded by revisions of other changes, so " ++ named_by ++ " has no current revision"}
    case Rev.Divergent{+rs}:
      Fail{change ++ " has " ++ Nat.show(List.length(&2, String, rs)) ++ " current revisions, none superseding the others; name one of them:" ++ listed(rs)}

def change_target(found: Result<&2, &2, String, String>, +h: Rev.History(), +spelling: String) -> Result<&2, &2, String, String>:
  match found:
    case Fail{e}:
      Fail{e}
    case Done{+change}:
      current(Rev.change_state(h, change), change, "`" ++ spelling ++ "`")

# The heads that are not superseded, or every head when all are.
def current_heads.of(heads: List<&2, String>, current: List<&2, String>) -> List<&2, String>:
  match current:
    case Nil{}:
      heads
    case +some:
      some

def current_heads(+h: Rev.History()) -> List<&2, String>:
  +heads = Rev.heads(h)
  current_heads.of(heads, Rev.without(heads, Rev.superseded(h)))

# Every head, said in enough detail to choose between them: the change, the
# author and moment, and the first line of the message. Heads are in digest
# order, as `Rev.heads` leaves them from the map.
def first_line.of(parts: List<&2, String>) -> String:
  match parts:
    case Nil{}:
      SNil{}
    case h <> t:
      h

def summary_line(+m: String) -> String:
  +first = first_line.of(String.split(m, '\n'))
  Bool.pick(String, String.is_empty(first), SNil{}, "\n      " ++ first)

def describe(+id: String, names: String, found: Maybe<&2, Full>) -> String:
  match found:
    case None{}:
      "\n  " ++ String.take(id, 12n) ++ names
    case Some{Full{i, change, parents, supersedes, author, when, revised_by, revised, facts, message}}:
      "\n  " ++ String.take(id, 12n) ++ "  " ++ change ++ names ++ "\n      " ++ author ++ "  " ++ when ++ summary_line(message)

def described(+fs: List<&2, Full>, +bs: List<&2, Bm.Bookmark>, heads: List<&2, String>) -> String:
  match heads:
    case Nil{}:
      SNil{}
    case +h <> rest:
      describe(h, names_at(bs, history(fs), h), find(fs, h)) ++ described(fs, bs, rest)

def head_target(+fs: List<&2, Full>, +bs: List<&2, Bm.Bookmark>, heads: List<&2, String>) -> Result<&2, &2, String, String>:
  match heads:
    case Nil{}:
      Fail{"this store holds no revisions yet"}
    case only <> Nil{}:
      Done{only}
    case +several:
      Fail{"this store has " ++ Nat.show(List.length(&2, String, several)) ++ " heads, so `head` names none of them; name one, or join them with `historica merge`:" ++ described(fs, bs, List.sort(~String, ~(a => b => String.is_le(a, b)), several))}

def resolve.spelled(+fs: List<&2, Full>, +bs: List<&2, Bm.Bookmark>, +spelling: String, is_head: Bool, hex: Bool, change: Bool) -> Result<&2, &2, String, String>:
  match is_head:
    case True{}:
      head_target(fs, bs, current_heads(history(fs)))
    case False{}:
      match hex:
        case True{}:
          one_of(with_prefix(ids(fs), spelling), spelling, "no revision here has a digest starting", "revisions")
        case False{}:
          match change:
            case True{}:
              change_target(one_of(with_prefix(changes(fs), spelling), spelling, "no change here has an ID starting", "changes"), history(fs), spelling)
            case False{}:
              Fail{"`" ++ spelling ++ "` is not a bookmark here, and it is spelled as neither a change ID (`k`–`z`) nor a digest (`0`–`9`, `a`–`f`)"}

# What a bookmark names, as a revision: a pin must be here, a change must
# have one current revision, and a file is not a revision at all.
def bookmarked(+fs: List<&2, Full>, +name: String, t: Bm.Target) -> Result<&2, &2, String, String>:
  match t:
    case Bm.Target.Revision{+id}:
      Bool.pick(Result<&2, &2, String, String>, Rev.member(ids(fs), id), Done{id}, Fail{"the bookmark `" ++ name ++ "` names the revision " ++ id ++ ", which this store does not hold yet"})
    case Bm.Target.Change{+c}:
      current(Rev.change_state(history(fs), c), c, "the bookmark `" ++ name ++ "`")
    case Bm.Target.File{f}:
      Fail{"the bookmark `" ++ name ++ "` names the file " ++ f ++ ", and a file is not a revision; a file is addressed at one, as `cat <target> file:" ++ name ++ "`"}

def resolve.named(+fs: List<&2, Full>, +bs: List<&2, Bm.Bookmark>, +s: String, found: Maybe<&2, Bm.Target>) -> Result<&2, &2, String, String>:
  match found:
    case Some{t}:
      bookmarked(fs, s, t)
    case None{}:
      resolve.spelled(fs, bs, s, String.eq(s, "head"), all_chars(~(c => is_hex(c)), s), all_chars(~(c => Id.is_letter(c)), s))

# The revision a target names. A bookmark wins over every other spelling,
# `head` included, because a name somebody chose beats a word the tool
# reserved; then `head`, a digest prefix, or a change prefix.
def resolve(+fs: List<&2, Full>, +bs: List<&2, Bm.Bookmark>, +spelling: String) -> Result<&2, &2, String, String>:
  match spelling:
    case SNil{}:
      Fail{"a target cannot be empty"}
    case +s:
      resolve.named(fs, bs, s, Bm.find(bs, s))

def resolved.found(+id: String, found: Maybe<&2, Full>) -> IO(Full):
  match found:
    case None{}:
      die(Full, 1, "this store does not hold the revision " ++ id)
    case Some{f}:
      IO.pure(Full, f)

def resolved.of(+fs: List<&2, Full>, r: Result<&2, &2, String, String>) -> IO(Full):
  match r:
    case Fail{e}:
      die(Full, 1, e)
    case Done{+id}:
      resolved.found(id, find(fs, id))

def resolved(+fs: List<&2, Full>, +bs: List<&2, Bm.Bookmark>, +spelling: String) -> IO(Full):
  resolved.of(fs, resolve(fs, bs, spelling))

# log
# ---

# Newest first, and a parent never above its child: of the revisions nothing
# unprinted stands on, the latest by `when`, then by digest.
# Every parent any of these revisions names.
def parents_named(fs: List<&2, Full>) -> List<&2, String>:
  match fs:
    case Nil{}:
      Nil{}
    case f <> rest:
      List.append(&2, String, parents_of(f), parents_named(rest))

def ready.keep(f: Full, rest: List<&2, Full>, r: Set() & Bool) -> List<&2, Full>:
  match r:
    case Tuple{s, True{}}:
      rest
    case Tuple{s, False{}}:
      f <> rest

def ready.go(fs: List<&2, Full>, +named: Set()) -> List<&2, Full>:
  match fs:
    case Nil{}:
      Nil{}
    case Full{+id, change, parents, supersedes, author, when, revised_by, revised, facts, message} <> rest:
      ready.keep(Full{id, change, parents, supersedes, author, when, revised_by, revised, facts, message}, ready.go(rest, named), Set.has(named, id))

# The revisions of `fs` that no revision in `all` names as a parent. The
# parents `all` names are a `Set` — a trie over the digest — asked once per
# revision, where asking every revision in turn was the count cubed over the
# whole presentation.
def ready(fs: List<&2, Full>, +all: List<&2, Full>) -> List<&2, Full>:
  ready.go(fs, Set.from_list(parents_named(all)))

def later(+a: Full, +b: Full) -> Bool:
  Bool.or(String.is_gt(when_of(a), when_of(b)), Bool.and(String.eq(when_of(a), when_of(b)), String.is_gt(id_of(a), id_of(b))))

def latest.go(fs: List<&2, Full>, +best: Full) -> Full:
  match fs:
    case Nil{}:
      best
    case +f <> rest:
      latest.go(rest, Bool.pick(Full, later(f, best), f, best))

def latest(fs: List<&2, Full>) -> Maybe<&2, Full>:
  match fs:
    case Nil{}:
      None{}
    case f <> rest:
      Some{latest.go(rest, f)}

def remove(fs: List<&2, Full>, +id: String) -> List<&2, Full>:
  match fs:
    case Nil{}:
      Nil{}
    case Full{+i, change, parents, supersedes, author, when, revised_by, revised, facts, message} <> rest:
      keep_full(Bool.not(String.eq(i, id)), Full{i, change, parents, supersedes, author, when, revised_by, revised, facts, message}, remove(rest, id))

# The walk, newest first, as Kahn's algorithm rather than a rescan: what was
# `ready(remaining, remaining)` at every step built a `Set` of every parent
# the unprinted revisions name and asked it once per revision, which is the
# revision count squared with a digest's length inside it — a hundred and
# twenty-four of `log`'s four hundred milliseconds on this archive. The same
# order comes out of one table: how many unprinted revisions name each digest
# as a parent, decremented as each revision is printed, so a revision joins
# the frontier the moment its last child has been. Only the frontier is
# searched for the latest, and only the revision just printed touches the
# table.

# The frontier, what has been printed, the count each digest is named by, and
# the revisions not yet reached, by digest.
type Walk is Data:
  Walk{ready: List<&2, Full>, printed: List<&2, Full>,
       counts: Map<&2, Nat>, waiting: Map<&2, Full>}

# One parent's count and the frontier, after the revision naming it went out.
type Drop is Data:
  Drop{counts: Map<&2, Nat>, waiting: Map<&2, Full>, ready: List<&2, Full>}

def counts.inc.of(+key: String, r: Map<&2, Nat> & Nat) -> Map<&2, Nat>:
  (m, n) = r
  Map.set(&2, Nat, m, key, 1n+n)

def counts.inc(m: Map<&2, Nat>, +key: String) -> Map<&2, Nat>:
  counts.inc.of(key, Map.get(Nat, 0n, m, key))

# How many revisions name each digest as a parent. A digest named twice by
# one revision counts twice, and is decremented twice when it goes out.
def counts.go(ps: List<&2, String>, m: Map<&2, Nat>) -> Map<&2, Nat>:
  match ps:
    case Nil{}:
      m
    case +p <> rest:
      counts.go(rest, counts.inc(m, p))

def counts(+fs: List<&2, Full>) -> Map<&2, Nat>:
  counts.go(parents_named(fs), Map.new(&2, Nat))

# The revisions that are not ready yet, by digest; a revision leaves this
# table exactly once, when the last revision naming it has been printed.
def waiting.go(fs: List<&2, Full>, m: Map<&2, Full>) -> Map<&2, Full>:
  match fs:
    case Nil{}:
      m
    case +f <> rest:
      waiting.go(rest, Map.set(&2, Full, m, id_of(f), f))

def waiting(fs: List<&2, Full>) -> Map<&2, Full>:
  waiting.go(fs, Map.new(&2, Full))

# A parent whose last child has gone out joins the frontier, unless this
# store holds no such revision — a missing parent is named and never printed.
def walk.arrive(counts: Map<&2, Nat>, rd: List<&2, Full>, r: Map<&2, Full> & Maybe<&2, Full>) -> Drop:
  (m, f) = r
  match f:
    case None{}:
      Drop{counts, m, rd}
    case Some{x}:
      Drop{counts, m, x <> rd}

def walk.zero(+key: String, counts: Map<&2, Nat>, waiting: Map<&2, Full>, rd: List<&2, Full>, n: Nat) -> Drop:
  match n:
    case 0n:
      walk.arrive(counts, rd, Map.pop(&2, Full, waiting, key))
    case 1n+k:
      Drop{counts, waiting, rd}

def walk.dec(+key: String, waiting: Map<&2, Full>, rd: List<&2, Full>, r: Map<&2, Nat> & Nat) -> Drop:
  (m, n) = r
  match n:
    case 0n:
      Drop{m, waiting, rd}
    case 1n++k:
      walk.zero(key, Map.set(&2, Nat, m, key, k), waiting, rd, k)

# Every parent of the revision just printed, counted down.
def walk.parents(ps: List<&2, String>, d: Drop) -> Drop:
  match ps:
    case Nil{}:
      d
    case +p <> rest:
      match d:
        case Drop{counts, waiting, rd}:
          walk.parents(rest, walk.dec(p, waiting, rd, Map.get(Nat, 0n, counts, p)))

def walk.went(printed: List<&2, Full>, d: Drop) -> Walk:
  match d:
    case Drop{counts, waiting, rd}:
      Walk{rd, printed, counts, waiting}

def walk.take(+f: Full, ready: List<&2, Full>, printed: List<&2, Full>, counts: Map<&2, Nat>, waiting: Map<&2, Full>) -> Walk:
  walk.went(f <> printed, walk.parents(parents_of(f), Drop{counts, waiting, remove(ready, id_of(f))}))

def walk.pick(+ready: List<&2, Full>, printed: List<&2, Full>, counts: Map<&2, Nat>, waiting: Map<&2, Full>, pick: Maybe<&2, Full>) -> Walk:
  match pick:
    case None{}:
      Walk{Nil{}, printed, counts, waiting}
    case Some{f}:
      walk.take(f, ready, printed, counts, waiting)

def presentation.step(w: Walk) -> Walk:
  match w:
    case Walk{+ready, printed, counts, waiting}:
      walk.pick(ready, printed, counts, waiting, latest(ready))

def presentation.go(fuel: Nat, w: Walk) -> Walk:
  match fuel:
    case 0n:
      w
    case 1n+n:
      presentation.go(n, presentation.step(w))

def presentation.printed(w: Walk) -> List<&2, Full>:
  match w:
    case Walk{ready, printed, counts, waiting}:
      printed

# What no frontier reached: a cycle cannot happen, and if one did, showing
# the rest in the order they were read beats dropping it.
def presentation.left.keep(f: Full, rest: List<&2, Full>, r: Set() & Bool) -> List<&2, Full>:
  match r:
    case Tuple{s, True{}}:
      rest
    case Tuple{s, False{}}:
      f <> rest

def presentation.left(fs: List<&2, Full>, +done: Set()) -> List<&2, Full>:
  match fs:
    case Nil{}:
      Nil{}
    case Full{+id, change, parents, supersedes, author, when, revised_by, revised, facts, message} <> rest:
      presentation.left.keep(Full{id, change, parents, supersedes, author, when, revised_by, revised, facts, message}, presentation.left(rest, done), Set.has(done, id))

def presentation.done(+fs: List<&2, Full>, +printed: List<&2, Full>) -> List<&2, Full>:
  List.append(&2, Full, List.reverse(&2, Full, printed),
    presentation.left(fs, Set.from_list(ids(printed))))

def presentation.of(+fs: List<&2, Full>, ready: List<&2, Full>) -> List<&2, Full>:
  presentation.done(fs, presentation.printed(presentation.go(1n+List.length(&2, Full, fs), Walk{ready, Nil{}, counts(fs), waiting(fs)})))

def presentation(+fs: List<&2, Full>) -> List<&2, Full>:
  presentation.of(fs, ready(fs, fs))

# Only the ancestry of one revision, when a target was named.
type Reach is Data:
  Reach{frontier: List<&2, String>, seen: List<&2, String>}

def ancestry.reach(id: String, rest: List<&2, String>, seen: List<&2, String>, parents: List<&2, String>, already: Bool) -> Reach:
  match already:
    case True{}:
      Reach{rest, seen}
    case False{}:
      Reach{List.append(&2, String, rest, parents), id <> seen}

def ancestry.next(+id: String, rest: List<&2, String>, +seen: List<&2, String>, found: Maybe<&2, Full>) -> Reach:
  match found:
    case None{}:
      Reach{rest, seen}
    case Some{f}:
      ancestry.reach(id, rest, seen, parents_of(f), Rev.member(seen, id))

def ancestry.step(+fs: List<&2, Full>, r: Reach) -> Reach:
  match r:
    case Reach{frontier, seen}:
      match frontier:
        case Nil{}:
          Reach{Nil{}, seen}
        case +id <> rest:
          ancestry.next(id, rest, seen, find(fs, id))

def ancestry.go(fuel: Nat, +fs: List<&2, Full>, r: Reach) -> Reach:
  match fuel:
    case 0n:
      r
    case 1n+n:
      ancestry.go(n, fs, ancestry.step(fs, r))

def ancestry.seen(r: Reach) -> List<&2, String>:
  match r:
    case Reach{frontier, seen}:
      seen

def among(fs: List<&2, Full>, +reached: List<&2, String>) -> List<&2, Full>:
  match fs:
    case Nil{}:
      Nil{}
    case +f <> rest:
      keep_full(Rev.member(reached, id_of(f)), f, among(rest, reached))

def reached.all(+fs: List<&2, Full>, starts: List<&2, String>) -> List<&2, String>:
  ancestry.seen(ancestry.go(Nat.mul(2n, 1n+List.length(&2, Full, fs)), fs, Reach{starts, Nil{}}))

def reached(+fs: List<&2, Full>, +id: String) -> List<&2, String>:
  reached.all(fs, [id])

def ancestry(+fs: List<&2, Full>, +id: String) -> List<&2, Full>:
  among(fs, reached(fs, id))

# The same revisions in the order the walk reached them, turned round: the
# walk goes out from the target, so what it reached last comes first and a
# chain comes out oldest first, which is the order `Tree.seen` takes in one
# pass. The store's own order is by file name, and a line of work named by
# its messages took `Tree.seen` a pass for nearly every revision in it.
type Pick is Data:
  Pick{left: Map<&2, Full>, picked: List<&2, Full>}

def pick.got(r: Map<&2, Full> & Maybe<&2, Full>, picked: List<&2, Full>) -> Pick:
  (m, f) = r
  match f:
    case None{}:
      Pick{m, picked}
    case Some{x}:
      Pick{m, x <> picked}

def pick.step(+id: String, p: Pick) -> Pick:
  match p:
    case Pick{m, picked}:
      pick.got(Map.pop(&2, Full, m, id), picked)

def picked(ids: List<&2, String>, p: Pick) -> List<&2, Full>:
  match ids:
    case Nil{}:
      match p:
        case Pick{m, fs}:
          List.reverse(&2, Full, fs)
    case +id <> rest:
      picked(rest, pick.step(id, p))

def ancestry.oldest(+fs: List<&2, Full>, +id: String) -> List<&2, Full>:
  picked(reached(fs, id), Pick{waiting(fs), Nil{}})

# An abbreviation is as long as it must be to be unique among these, and at
# least eight characters: what the store holds today decides it.
def shared(a: String, b: String) -> Nat:
  match a b:
    case SCon{x, xt} SCon{y, yt}:
      Bool.pick(Nat, Char.is_eq(x, y), 1n+shared(xt, yt), 0n)
    case _ _:
      0n

def longest_shared(+id: String, others: List<&2, String>) -> Nat:
  match others:
    case Nil{}:
      0n
    case +o <> rest:
      Nat.max(Bool.pick(Nat, String.eq(o, id), 0n, shared(id, o)), longest_shared(id, rest))

def abbreviate(+id: String, +among: List<&2, String>) -> String:
  String.take(id, Nat.max(8n, 1n+longest_shared(id, among)))

# Was this file added here? The added files are a set rather than a list,
# because a revision that adds a folder names every file in it twice — once
# to add it and once for the bytes it stored — and walking the added names
# for each of those is the whole listing squared. A `Set` is a trie over the
# name, which answers the same question by the name's own characters.
def was_added.of(r: Set() & Bool) -> Bool:
  (s, b) = r
  b

def was_added(+added: Set(), +file: String) -> Bool:
  was_added.of(Set.has(added, file))

# One fact, counted: under this key, and — where the key is one a revision
# states about a file it also added — not about such a file.
def count_facts.excl(+added: Set(), +v: String, exclude: Bool) -> Nat:
  match exclude:
    case False{}:
      1n
    case True{}:
      Bool.pick(Nat, was_added(added, T.word(v)), 0n, 1n)

def count_facts.one(+added: Set(), +exclude: Bool, +v: String, matched: Bool) -> Nat:
  match matched:
    case False{}:
      0n
    case True{}:
      count_facts.excl(added, v, exclude)

# What a revision says it did to the file set, counted.
def count_facts(facts: List<&2, Rev.Header>, +key: String, +added: Set(), +exclude: Bool) -> Nat:
  match facts:
    case Nil{}:
      0n
    case Rev.Header{+k, +v} <> rest:
      Nat.add(count_facts.one(added, exclude, v, String.eq(k, key)), count_facts(rest, key, added, exclude))

def fact.show(what: String, n: Nat, rest: List<&2, String>) -> List<&2, String>:
  match n:
    case 0n:
      rest
    case 1n+p:
      (what ++ " " ++ Nat.show(1n+p)) <> rest

def tree_facts(+facts: List<&2, Rev.Header>) -> String:
  +added : Set() = Set.from_list(Rev.files_of(facts, "add"))
  String.join(
    fact.show("added", count_facts(facts, "add", added, False{}),
    fact.show("moved", count_facts(facts, "move", added, False{}),
    fact.show("mode", count_facts(facts, "mode", added, True{}),
    fact.show("link", count_facts(facts, "link", added, True{}),
    fact.show("dropped", count_facts(facts, "drop", added, False{}),
    fact.show("edited", count_facts(facts, "edit", added, False{}),
    fact.show("stored", count_facts(facts, "bytes", added, True{}), Nil{}))))))), "  ")

def mark(b: Bool, m: String, rest: List<&2, String>) -> List<&2, String>:
  Rev.keep(b, m, rest)

def is_divergent(state: Rev.ChangeState) -> Bool:
  match state:
    case Rev.Divergent{rs}:
      True{}
    case _:
      False{}

def marks(+id: String, +change: String, parents: List<&2, String>, supersedes: List<&2, String>, +heads: List<&2, String>, +gone: List<&2, String>, +h: Rev.History()) -> String:
  +n_parents = List.length(&2, String, parents)
  +n_supersedes = List.length(&2, String, supersedes)
  +ms = mark(Rev.member(heads, id), "head",
    mark(Nat.is_gt(n_parents, 1n), "merge",
    mark(Rev.member(gone, id), "superseded",
    mark(Nat.is_gt(n_supersedes, 0n), "rewrites " ++ Nat.show(n_supersedes),
    mark(is_divergent(Rev.change_state(h, change)), "divergent", Nil{})))))
  Bool.pick(String, List.is_empty(&2, String, ms), SNil{}, "  (" ++ String.join(ms, ", ") ++ ")")

def revised_line(by: Maybe<&2, String>, at: Maybe<&2, String>) -> IO(Unit):
  match by at:
    case Some{b} Some{a}:
      IO.print("    revised by " ++ b ++ "  " ++ a)
    case _ _:
      IO.pure(Unit, Unit{})

def facts_line(+facts: String) -> IO(Unit):
  Bool.pick(IO(Unit), String.is_empty(facts), IO.pure(Unit, Unit{}), IO.print("    " ++ facts))

def message_lines(ls: List<&2, String>) -> IO(Unit):
  match ls:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case +l <> rest:
      do IO<Unit>:
        IO.print(Bool.pick(String, String.is_empty(l), SNil{}, "    " ++ l))
        message_lines(rest)

def line_texts(ls: List<&2, T.Line>) -> List<&2, String>:
  match ls:
    case Nil{}:
      Nil{}
    case T.Line{t, n} <> rest:
      t <> line_texts(rest)

# `lines` as Rust's `str::lines`: a final newline ends the last line rather
# than starting an empty one.
def message.print(+m: String) -> IO(Unit):
  Bool.pick(IO(Unit), String.is_empty(String.trim(m)), IO.print("    (no message)"), message_lines(line_texts(T.lines(m))))

def print_entry(f: Full, +all_ids: List<&2, String>, +all_changes: List<&2, String>, +heads: List<&2, String>, +gone: List<&2, String>, +h: Rev.History()) -> IO(Unit):
  match f:
    case Full{+id, +change, parents, supersedes, author, when, revised_by, revised, facts, message}:
      do IO<Unit>:
        IO.print(abbreviate(change, all_changes) ++ "  " ++ abbreviate(id, all_ids) ++ marks(id, change, parents, supersedes, heads, gone, h))
        IO.print("    " ++ author ++ "  " ++ when)
        revised_line(revised_by, revised)
        facts_line(tree_facts(facts))
        message.print(message)

def print_entries(fs: List<&2, Full>, +all_ids: List<&2, String>, +all_changes: List<&2, String>, +heads: List<&2, String>, +gone: List<&2, String>, +h: Rev.History(), first: Bool) -> IO(Unit):
  match fs:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case f <> rest:
      do IO<Unit>:
        Bool.pick(IO(Unit), first, IO.pure(Unit, Unit{}), IO.print(SNil{}))
        print_entry(f, all_ids, all_changes, heads, gone, h)
        print_entries(rest, all_ids, all_changes, heads, gone, h, False{})

def print_missing(ids: List<&2, String>) -> IO(Unit):
  match ids:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case id <> rest:
      do IO<Unit>:
        IO.print_err("missing parent " ++ String.take(id, 12n) ++ ": named, and not among these documents")
        print_missing(rest)

# A revision's file set, and one file in it
# ------------------------------------------

def rev_of(f: Full) -> Rev.Rev:
  match f:
    case Full{id, change, parents, supersedes, author, when, revised_by, revised, facts, message}:
      Rev.Rev{change, parents, supersedes, author, when, revised_by, revised, facts, message}

def events_of(fs: List<&2, Full>) -> List<&2, Tree.Ev>:
  match fs:
    case Nil{}:
      Nil{}
    case +f <> rest:
      Tree.Ev{id_of(f), rev_of(f)} <> events_of(rest)

def tree.of(+id: String, merged: Result<&2, &2, Tree.Fault, Tree.Merged>) -> IO(Tree.Tree()):
  match merged:
    case Fail{e}:
      die(Tree.Tree(), 1, id ++ ": " ++ Tree.fault_show(e))
    case Done{m}:
      IO.pure(Tree.Tree(), Tree.merged_tree(m))

def tree(+fs: List<&2, Full>, +id: String) -> IO(Tree.Tree()):
  tree.of(id, Tree.merge(events_of(ancestry.oldest(fs, id))))

def file_in.of(+id: String, +path: String, found: List<&2, String>) -> IO(String):
  match found:
    case Nil{}:
      die(String, 1, String.take(id, 12n) ++ " holds no file at " ++ path ++ "; `historica files " ++ String.take(id, 12n) ++ "` lists what it holds")
    case only <> Nil{}:
      IO.pure(String, only)
    case +several:
      die(String, 1, String.take(id, 12n) ++ " has " ++ Nat.show(List.length(&2, String, several)) ++ " files at " ++ path ++ ", so the path does not name one of them:" ++ String.concat(T.map(~String, ~String, ~(f => "\n  file:" ++ f), several)))

def file_named.listed(+t: Tree.Tree(), fs: List<&2, String>) -> String:
  match fs:
    case Nil{}:
      SNil{}
    case +f <> rest:
      "\n  file:" ++ f ++ "  " ++ Maybe.default(&2, String, Tree.path(t, f), SNil{}) ++ file_named.listed(t, rest)

# A `file:` spelling: a bookmark first, then an identifier's prefix among
# the files this revision holds, which are the ones `files` prints.
def file_named.matched(+id: String, +spelling: String, +t: Tree.Tree(), found: List<&2, String>) -> IO(String):
  match found:
    case Nil{}:
      die(String, 1, "no file at " ++ String.take(id, 12n) ++ " has an identifier starting `" ++ spelling ++ "`; `historica files " ++ String.take(id, 12n) ++ "` lists them")
    case only <> Nil{}:
      IO.pure(String, only)
    case +several:
      die(String, 1, "`" ++ spelling ++ "` could be " ++ Nat.show(List.length(&2, String, several)) ++ " files at " ++ String.take(id, 12n) ++ ":" ++ file_named.listed(t, several))

def file_named.prefix(+id: String, +spelling: String, +t: Tree.Tree(), letters: Bool) -> IO(String):
  match letters:
    case False{}:
      die(String, 1, "`" ++ spelling ++ "` is not a file bookmark here, and a file identifier is spelled in `k`–`z`")
    case True{}:
      file_named.matched(id, spelling, t, List.sort(~String, ~(a => b => String.is_le(a, b)), with_prefix(Tree.files(t), spelling)))

def file_named.held(+id: String, +spelling: String, +file: String, at: Maybe<&2, String>) -> IO(String):
  match at:
    case None{}:
      die(String, 1, "the bookmark `" ++ spelling ++ "` names the file " ++ file ++ ", which " ++ String.take(id, 12n) ++ " does not hold; `historica files " ++ String.take(id, 12n) ++ "` lists what it holds")
    case Some{p}:
      IO.pure(String, file)

def file_named.bookmark(+id: String, +spelling: String, +t: Tree.Tree(), target: Bm.Target) -> IO(String):
  match target:
    case Bm.Target.File{+f}:
      file_named.held(id, spelling, f, Tree.path(t, f))
    case +other:
      die(String, 1, "the bookmark `" ++ spelling ++ "` names a " ++ Bm.kind(other) ++ ", and this position names a file")

def file_named.found(+id: String, +spelling: String, +t: Tree.Tree(), found: Maybe<&2, Bm.Target>) -> IO(String):
  match found:
    case Some{target}:
      file_named.bookmark(id, spelling, t, target)
    case None{}:
      file_named.prefix(id, spelling, t, all_chars(~(c => Id.is_letter(c)), spelling))

def file_named(+id: String, +bs: List<&2, Bm.Bookmark>, spelling: String, +t: Tree.Tree()) -> IO(String):
  match spelling:
    case SNil{}:
      die(String, 2, "`file:` wants an identifier or a bookmark after it")
    case +s:
      file_named.found(id, s, t, Bm.find(bs, s))

def file_in.spelled(+id: String, +bs: List<&2, Bm.Bookmark>, +path: String, +t: Tree.Tree(), named: Maybe<&2, String>) -> IO(String):
  match named:
    case Some{n}:
      file_named(id, bs, n, t)
    case None{}:
      +p = Maybe.default(&2, String, T.strip_prefix(path, "path:"), path)
      file_in.of(id, p, Tree.at(t, p))

# The file one argument names at one revision: a path, `path:` and a path
# for a file whose own name begins `file:`, or `file:` and an identifier or
# a file bookmark — the one name a file keeps through a rename.
def file_in(+id: String, +bs: List<&2, Bm.Bookmark>, +path: String, +t: Tree.Tree()) -> IO(String):
  file_in.spelled(id, bs, path, t, T.strip_prefix(path, "file:"))

# What `log` was asked. Every flag is read before any target is resolved,
# and a word that is not a flag is the one target or range.
type Asked is Data:
  Asked{target: Maybe<&2, String>, path: Maybe<&2, String>, fields: Bool, limit: Maybe<&2, Nat>,
        author: Maybe<&2, String>, grep: Maybe<&2, String>, since: Maybe<&2, String>, until: Maybe<&2, String>}

# What a revision must satisfy to be listed: a filter takes entries out and
# changes nothing about the ones that stay. The limit counts what they left.
type Filter is Data:
  Filter{author: Maybe<&2, String>, grep: Maybe<&2, String>, since: Maybe<&2, String>, until: Maybe<&2, String>, file: Maybe<&2, String>}

# The arguments still to read, and what has been read of them.
type Parse is Data:
  Parse{rest: List<&2, String>, asked: Result<&2, &2, String, Asked>}

def asked.limit(a: Asked, n: Maybe<&2, Nat>) -> Asked:
  match a:
    case Asked{t, p, f, l, au, g, si, u}:
      Asked{t, p, f, n, au, g, si, u}

def asked.author(a: Asked, x: String) -> Asked:
  match a:
    case Asked{t, p, f, l, au, g, si, u}:
      Asked{t, p, f, l, Some{x}, g, si, u}

def asked.grep(a: Asked, x: String) -> Asked:
  match a:
    case Asked{t, p, f, l, au, g, si, u}:
      Asked{t, p, f, l, au, Some{x}, si, u}

def asked.since(a: Asked, x: String) -> Asked:
  match a:
    case Asked{t, p, f, l, au, g, si, u}:
      Asked{t, p, f, l, au, g, Some{x}, u}

def asked.until(a: Asked, x: String) -> Asked:
  match a:
    case Asked{t, p, f, l, au, g, si, u}:
      Asked{t, p, f, l, au, g, si, Some{x}}

def asked.path(a: Asked, x: String) -> Asked:
  match a:
    case Asked{t, p, f, l, au, g, si, u}:
      Asked{t, Some{x}, f, l, au, g, si, u}

def asked.fields(a: Asked) -> Asked:
  match a:
    case Asked{t, p, f, l, au, g, si, u}:
      Asked{t, p, True{}, l, au, g, si, u}

def asked.target(t: Maybe<&2, String>, p: Maybe<&2, String>, f: Bool, l: Maybe<&2, Nat>, au: Maybe<&2, String>, g: Maybe<&2, String>, si: Maybe<&2, String>, u: Maybe<&2, String>, +word: String) -> Result<&2, &2, String, Asked>:
  match t:
    case None{}:
      Done{Asked{Some{word}, p, f, l, au, g, si, u}}
    case Some{had}:
      Fail{"`log` takes one target or one range, and `" ++ word ++ "` is a second"}

def asked.named(a: Asked, +word: String) -> Result<&2, &2, String, Asked>:
  match a:
    case Asked{t, p, f, l, au, g, si, u}:
      asked.target(t, p, f, l, au, g, si, u, word)

def asked.word(a: Asked, +word: String, flag: Bool) -> Result<&2, &2, String, Asked>:
  match flag:
    case True{}:
      Fail{"`" ++ word ++ "` is not an argument `log` takes"}
    case False{}:
      asked.named(a, word)

# A count, as Rust reads a `usize`: an optional `+` and at least one digit.
# Past nine digits it is more entries than any store holds, and past a
# `usize` it is refused, as there.
def count.digits(+ds: String) -> Result<&2, &2, Unit, Maybe<&2, Nat>>:
  +n = String.length(ds)
  Bool.pick(Result<&2, &2, Unit, Maybe<&2, Nat>>, Bool.or(Nat.is_gt(n, 20n), Bool.and(Nat.is_eq(n, 20n), String.is_lt("18446744073709551615", ds))), Fail{Unit{}},
    Bool.pick(Result<&2, &2, Unit, Maybe<&2, Nat>>, Nat.is_gt(n, 9n), Done{None{}}, Done{Some{Maybe.default(&2, Nat, Nat.read(ds), 0n)}}))

def count.zeros(s: String) -> String:
  match s:
    case SCon{'0', SCon{c, t}}:
      count.zeros(SCon{c, t})
    case _:
      s

def count.of(+ds: String) -> Result<&2, &2, Unit, Maybe<&2, Nat>>:
  Bool.pick(Result<&2, &2, Unit, Maybe<&2, Nat>>, Bool.and(Bool.not(String.is_empty(ds)), all_chars(~(c => Char.is_digit(c)), ds)), count.digits(count.zeros(ds)), Fail{Unit{}})

def count(+v: String) -> Result<&2, &2, Unit, Maybe<&2, Nat>>:
  count.of(Maybe.default(&2, String, T.strip_prefix(v, "+"), v))

def asked.counted(a: Asked, +v: String, r: Result<&2, &2, Unit, Maybe<&2, Nat>>) -> Result<&2, &2, String, Asked>:
  match r:
    case Fail{u}:
      Fail{"`--limit` wants how many entries to stop after, and `" ++ v ++ "` is not a count"}
    case Done{n}:
      Done{asked.limit(a, n)}

# The wall clock a `--since` or `--until` bounds: a whole timestamp's date
# and time, in the author's own offset, or a date, which is that whole day.
def bound(+flag: String, +v: String, +time: String) -> Result<&2, &2, String, String>:
  Bool.pick(Result<&2, &2, String, String>, Rev.is_timestamp(v), Done{String.take(v, 19n)},
    Bool.pick(Result<&2, &2, String, String>, Rev.is_timestamp(v ++ "T00:00:00+00:00"), Done{v ++ "T" ++ time},
      Fail{"`" ++ flag ++ "` wants a date, as `YYYY-MM-DD`, or a whole time, as `YYYY-MM-DDThh:mm:ss±hh:mm`; `" ++ v ++ "` is neither"}))

def asked.bound(a: Asked, since: Bool, b: String) -> Asked:
  match since:
    case True{}:
      asked.since(a, b)
    case False{}:
      asked.until(a, b)

def asked.bounded(a: Asked, since: Bool, r: Result<&2, &2, String, String>) -> Result<&2, &2, String, Asked>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{b}:
      Done{asked.bound(a, since, b)}

def wants_value(flag: String) -> Parse:
  Parse{Nil{}, Fail{"`" ++ flag ++ "` wants a value"}}

# One argument, or a flag and its value.
def asked.step(args: List<&2, String>, a: Asked) -> Parse:
  match args:
    case "--limit" <> +v <> rest:
      Parse{rest, asked.counted(a, v, count(v))}
    case "--author" <> v <> rest:
      Parse{rest, Done{asked.author(a, v)}}
    case "--grep" <> v <> rest:
      Parse{rest, Done{asked.grep(a, v)}}
    case "--since" <> v <> rest:
      Parse{rest, asked.bounded(a, True{}, bound("--since", v, "00:00:00"))}
    case "--until" <> v <> rest:
      Parse{rest, asked.bounded(a, False{}, bound("--until", v, "23:59:59"))}
    case "--path" <> v <> rest:
      Parse{rest, Done{asked.path(a, v)}}
    case "--fields" <> rest:
      Parse{rest, Done{asked.fields(a)}}
    case "--limit" <> Nil{}:
      wants_value("--limit")
    case "--author" <> Nil{}:
      wants_value("--author")
    case "--grep" <> Nil{}:
      wants_value("--grep")
    case "--since" <> Nil{}:
      wants_value("--since")
    case "--until" <> Nil{}:
      wants_value("--until")
    case "--path" <> Nil{}:
      wants_value("--path")
    case +w <> rest:
      Parse{rest, asked.word(a, w, String.starts_with(w, "-"))}
    case Nil{}:
      Parse{Nil{}, Done{a}}

def asked.go(fuel: Nat, p: Parse) -> Result<&2, &2, String, Asked>:
  match fuel p:
    case _ Parse{rest, Fail{e}}:
      Fail{e}
    case _ Parse{Nil{}, r}:
      r
    case 0n Parse{rest, r}:
      r
    case 1n+f Parse{args, Done{a}}:
      asked.go(f, asked.step(args, a))

def asked(+args: List<&2, String>) -> Result<&2, &2, String, Asked>:
  asked.go(1n+List.length(&2, String, args), Parse{args, Done{Asked{None{}, None{}, False{}, None{}, None{}, None{}, None{}, None{}}}})

def asked.io(r: Result<&2, &2, String, Asked>) -> IO(Asked):
  match r:
    case Fail{e}:
      die(Asked, 2, e)
    case Done{a}:
      IO.pure(Asked, a)

# What a target argument covers: everything, one revision's ancestry, or
# what `to` has behind it and `from` does not.
type Span is Data:
  Span.All{}
  Span.From{id: String}
  Span.Between{from: String, to: String}

# The first `..` cuts a spelling no minted identifier could have, so the
# only thing it can collide with is a bookmark, which is looked up whole
# first.
def range.cut(s: String, before: String) -> Maybe<&2, T.Split>:
  match s:
    case SNil{}:
      None{}
    case SCon{'.', SCon{'.', rest}}:
      Some{T.Split{String.reverse(before), rest}}
    case SCon{c, rest}:
      range.cut(rest, SCon{c, before})

def span.between(+fs: List<&2, Full>, +bs: List<&2, Bm.Bookmark>, +from: String, +to: String) -> IO(Span):
  do IO<Span>:
    f : Full <- resolved(fs, bs, from)
    t : Full <- resolved(fs, bs, to)
    return Span.Between{id_of(f), id_of(t)}

def span.range(+fs: List<&2, Full>, +bs: List<&2, Bm.Bookmark>, +s: String, +from: String, +to: String) -> IO(Span):
  Bool.pick(IO(Span), String.starts_with(to, "."),
    die(Span, 2, "`" ++ s ++ "` is spelled with three dots, which git reads as the work either side of a fork; `<from>..<to>` is what `<to>` has and `<from>` does not, and there is no spelling for the other one"),
    Bool.pick(IO(Span), Bool.or(String.is_empty(from), String.is_empty(to)),
      die(Span, 2, "`" ++ s ++ "` " ++ Bool.pick(String, Bool.and(String.is_empty(from), String.is_empty(to)), "names neither end of a range", "names one end of a range and leaves the other blank") ++ "; both ends are said outright, as `<from>..<to>`, and the head is spelled `head`"),
      span.between(fs, bs, from, to)))

def span.one(+fs: List<&2, Full>, +bs: List<&2, Bm.Bookmark>, +s: String) -> IO(Span):
  do IO<Span>:
    f : Full <- resolved(fs, bs, s)
    return Span.From{id_of(f)}

def span.cut(+fs: List<&2, Full>, +bs: List<&2, Bm.Bookmark>, +s: String, bookmarked: Bool, cut: Maybe<&2, T.Split>) -> IO(Span):
  match bookmarked cut:
    case False{} Some{T.Split{from, to}}:
      span.range(fs, bs, s, from, to)
    case _ _:
      span.one(fs, bs, s)

def span(+fs: List<&2, Full>, +bs: List<&2, Bm.Bookmark>, target: Maybe<&2, String>) -> IO(Span):
  match target:
    case None{}:
      IO.pure(Span, Span.All{})
    case Some{+s}:
      span.cut(fs, bs, s, Maybe.is_some(&2, Bm.Target, Bm.find(bs, s)), range.cut(s, SNil{}))

def span.shown(+fs: List<&2, Full>, sp: Span) -> List<&2, Full>:
  match sp:
    case Span.All{}:
      fs
    case Span.From{+id}:
      ancestry(fs, id)
    case Span.Between{+from, +to}:
      among(fs, Rev.without(reached(fs, to), reached(fs, from)))

# The revision a `--path` is read at: the far end of what was named, or the
# head where nothing was — and where there are several heads, none.
def read_at.heads(+fs: List<&2, Full>, +bs: List<&2, Bm.Bookmark>, +path: String, heads: List<&2, String>) -> IO(String):
  match heads:
    case Nil{}:
      die(String, 1, "this store holds no revisions yet")
    case only <> Nil{}:
      IO.pure(String, only)
    case +several:
      die(String, 1, "this store has " ++ Nat.show(List.length(&2, String, several)) ++ " heads, so there is no one place to read `" ++ path ++ "` at; say which revision to read it at, as `historica log <target> --path " ++ path ++ "`:" ++ described(fs, bs, List.sort(~String, ~(a => b => String.is_le(a, b)), several)))

def read_at(+fs: List<&2, Full>, +bs: List<&2, Bm.Bookmark>, +path: String, sp: Span) -> IO(String):
  match sp:
    case Span.All{}:
      read_at.heads(fs, bs, path, current_heads(history(fs)))
    case Span.From{id}:
      IO.pure(String, id)
    case Span.Between{from, to}:
      IO.pure(String, to)

# The file a `--path` names, read once, at one revision: what the log then
# follows is the file, through the `move` that renamed it as readily as
# through the edits either side.
def followed(+fs: List<&2, Full>, +bs: List<&2, Bm.Bookmark>, +sp: Span, path: Maybe<&2, String>) -> IO(Maybe<&2, String>):
  match path:
    case None{}:
      IO.pure(Maybe<&2, String>, None{})
    case Some{+p}:
      do IO<Maybe<&2, String>>:
        at : String <- read_at(fs, bs, p, sp)
        +at2 : String = at
        t : Tree.Tree() <- tree(fs, at2)
        file : String <- file_in(at2, bs, p, t)
        return Some{file}

# Filtering
# ---------

def holds.opt(m: Maybe<&2, String>, +text: String) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{p}:
      String.contains(text, p)

def not_before(m: Maybe<&2, String>, +wall: String) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{b}:
      String.is_le(b, wall)

def not_after(m: Maybe<&2, String>, +wall: String) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{b}:
      String.is_le(wall, b)

def touch_keys(+k: String) -> Bool:
  match k:
    case "add":
      True{}
    case "move":
      True{}
    case "mode":
      True{}
    case "drop":
      True{}
    case "edit":
      True{}
    case "text":
      True{}
    case "bytes":
      True{}
    case "link":
      True{}
    case _:
      False{}

# Whether a revision states any fact about the file.
def touches(facts: List<&2, Rev.Header>, +file: String) -> Bool:
  match facts:
    case Nil{}:
      False{}
    case Rev.Header{+k, v} <> rest:
      Bool.or(Bool.and(touch_keys(k), String.eq(T.word(v), file)), touches(rest, file))

def touches.opt(m: Maybe<&2, String>, facts: List<&2, Rev.Header>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{+f}:
      touches(facts, f)

def keeps(+fl: Filter, +f: Full) -> Bool:
  match fl:
    case Filter{author, grep, since, until, file}:
      +wall = String.take(when_of(f), 19n)
      Bool.and(Bool.and(holds.opt(author, author_of(f)), holds.opt(grep, message_of(f))),
        Bool.and(Bool.and(not_before(since, wall), not_after(until, wall)), touches.opt(file, facts_of(f))))

def some(m: Maybe<&2, String>) -> Bool:
  Maybe.is_some(&2, String, m)

def selects(fl: Filter) -> Bool:
  match fl:
    case Filter{author, grep, since, until, file}:
      Bool.or(Bool.or(some(author), some(grep)), Bool.or(Bool.or(some(since), some(until)), some(file)))

def kept(+fl: Filter, fs: List<&2, Full>) -> List<&2, Full>:
  match fs:
    case Nil{}:
      Nil{}
    case +f <> rest:
      keep_full(keeps(fl, f), f, kept(fl, rest))

def limited(fs: List<&2, Full>, limit: Maybe<&2, Nat>) -> List<&2, Full>:
  match limit:
    case None{}:
      fs
    case Some{n}:
      List.take(&2, Full, fs, n)

# `--fields`
# ----------

# One line per revision, the digest and change spelled whole, and of the
# marks only what the graph found — the document says `merge` and
# `rewrites` outright. Never an empty field: `-` where there is nothing.
def found(+id: String, +change: String, +heads: List<&2, String>, +gone: List<&2, String>, +h: Rev.History()) -> String:
  +ms = mark(Rev.member(heads, id), "head",
    mark(Rev.member(gone, id), "superseded",
    mark(is_divergent(Rev.change_state(h, change)), "divergent", Nil{})))
  Bool.pick(String, List.is_empty(&2, String, ms), "-", String.join(ms, ","))

def fields_line(f: Full, +heads: List<&2, String>, +gone: List<&2, String>, +h: Rev.History()) -> String:
  match f:
    case Full{+id, +change, parents, supersedes, author, when, revised_by, revised, facts, message}:
      id ++ " " ++ change ++ " " ++ when ++ " " ++ found(id, change, heads, gone, h) ++ String.concat(T.map(~String, ~String, ~(p => " " ++ p), parents))

def print_fields(fs: List<&2, Full>, +heads: List<&2, String>, +gone: List<&2, String>, +h: Rev.History()) -> IO(Unit):
  match fs:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case f <> rest:
      do IO<Unit>:
        IO.print(fields_line(f, heads, gone, h))
        print_fields(rest, heads, gone, h)

# Printing
# --------

def log.fields(+h: Rev.History(), listed: List<&2, Full>) -> IO(Unit):
  do IO<Unit>:
    IO.print("historica-log-1")
    print_fields(listed, Rev.heads(h), Rev.superseded(h), h)

def log.entries(+fs: List<&2, Full>, +h: Rev.History(), +listed: List<&2, Full>, +selects: Bool) -> IO(Unit):
  Bool.pick(IO(Unit), Bool.and(List.is_empty(&2, Full, listed), selects), IO.print("no revision here matches all of those"),
    print_entries(listed, ids(fs), changes(fs), Rev.heads(h), Rev.superseded(h), h, True{}))

def log.listed(+fs: List<&2, Full>, +listed: List<&2, Full>, fields: Bool, +selects: Bool) -> IO(Unit):
  match fields:
    case True{}:
      log.fields(history(fs), listed)
    case False{}:
      log.entries(fs, history(fs), listed, selects)

def spelled(+fs: List<&2, Full>, +bs: List<&2, Bm.Bookmark>, +id: String) -> String:
  String.take(id, 12n) ++ names_at(bs, history(fs), id)

# An empty span is an answer rather than a fault: a range that is empty says
# the work asked about is already behind the revision it was held up against.
def log.empty(+fs: List<&2, Full>, +bs: List<&2, Bm.Bookmark>, sp: Span) -> IO(Unit):
  match sp:
    case Span.Between{+from, +to}:
      IO.print(spelled(fs, bs, to) ++ " holds nothing " ++ spelled(fs, bs, from) ++ " does not")
    case _:
      IO.print("no revisions here yet")

def log.shown(+fs: List<&2, Full>, +bs: List<&2, Bm.Bookmark>, +sp: Span, +shown: List<&2, Full>, +fl: Filter, +fields: Bool, limit: Maybe<&2, Nat>) -> IO(Unit):
  Bool.pick(IO(Unit), Bool.and(List.is_empty(&2, Full, shown), Bool.not(fields)), log.empty(fs, bs, sp),
    log.listed(fs, limited(kept(fl, presentation(shown)), limit), fields, selects(fl)))

def log.of(+fs: List<&2, Full>, +bs: List<&2, Bm.Bookmark>, a: Asked) -> IO(Unit):
  match a:
    case Asked{target, path, fields, limit, author, grep, since, until}:
      do IO<Unit>:
        sp : Span <- span(fs, bs, target)
        +sp2 : Span = sp
        file : Maybe<&2, String> <- followed(fs, bs, sp2, path)
        log.shown(fs, bs, sp2, span.shown(fs, sp2), Filter{author, grep, since, until, file}, fields, limit)

def log(+args: List<&2, String>) -> IO(Unit):
  do IO<Unit>:
    root : String <- Store.root()
    +r : String = root
    rs : List<&2, Store.Doc> <- Store.revisions(r)
    bs : List<&2, Bm.Bookmark> <- bookmarks(r)
    a : Asked <- asked.io(asked(args))
    log.of(fulls(r, rs), bs, a)

# check
# -----

# What a file in a store is, told by where it is and what it is called: a
# revision, an operation document, or a payload, which has no grammar and
# only a digest.
def check_rev(+id: String, parsed: Result<&2, &2, String, Rev.Rev>) -> String:
  match parsed:
    case Fail{e}:
      "refused  " ++ String.take(id, 12n) ++ "  " ++ e
    case Done{r}:
      "revision " ++ String.take(id, 12n) ++ "  change " ++ String.take(Rev.change_of(Rev.of_doc(id, r)), 8n)

def result_note(r: Maybe<&2, String>) -> String:
  match r:
    case None{}:
      SNil{}
    case Some{d}:
      ", producing " ++ String.take(d, 12n)

def check_ops.of(+id: String, parsed: Result<&2, &2, String, Ops.Doc>) -> String:
  match parsed:
    case Fail{e}:
      "refused  " ++ String.take(id, 12n) ++ "  " ++ e
    case Done{Ops.Doc{forgets, result, ops}}:
      "edit     " ++ String.take(id, 12n) ++ "  " ++ Nat.show(List.length(&2, Ops.Op, ops)) ++ " operations" ++ result_note(result)

def check_doc.of(+d: Store.Doc, is_rev: Bool) -> String:
  match is_rev:
    case True{}:
      check_rev(Store.id_of(d), Rev.parse(Store.text_of(d)))
    case False{}:
      check_ops.of(Store.id_of(d), Ops.parse(Store.text_of(d)))

# A payload has no grammar: what `check` says about one is the digest of its
# bytes and how many there are, which is what `Store.digests` answers. Its
# bytes are the only thing in a store no reader here parses, and the only
# thing a store holds fifty megabytes of.
def check_payload.of(+stat: String, cut: Maybe<&2, T.Split>) -> String:
  match cut:
    case Some{T.Split{d, n}}:
      "payload  " ++ String.take(d, 12n) ++ "  " ++ n ++ " bytes"
    case None{}:
      "refused  " ++ String.take(stat, 12n) ++ "  the host would not read it"

def check_payload(+stat: String) -> String:
  check_payload.of(stat, T.split_once(stat))

# What a file in a store is, told by where it is and what it is called,
# before anything is opened: a revision, an operation document, or a payload.
# The first two are read and hashed here; the third is not read at all.
type Filed is Data:
  Filed{path: String, doc: Bool, rev: Bool, stat: String}

# What each listed path is, before anything is opened.
def filed.of(+path: String, +rev: Bool) -> Filed:
  Filed{path, Bool.or(rev, String.ends_with(path, ".ops.txt")), rev, SNil{}}

def filed(ls: List<&2, String>) -> List<&2, Filed>:
  match ls:
    case Nil{}:
      Nil{}
    case +l <> rest:
      filed.of(l, String.starts_with(l, "revisions/")) <> filed(rest)

# The payload digests, attached where they belong: they were asked for in the
# listing's own order, so one is taken at each payload and none elsewhere.
def attach(fs: List<&2, Filed>, stats: List<&2, String>) -> List<&2, Filed>:
  match fs:
    case Nil{}:
      Nil{}
    case Filed{+path, doc, rev, stat} <> rest:
      match doc:
        case True{}:
          Filed{path, True{}, rev, stat} <> attach(rest, stats)
        case False{}:
          match stats:
            case Nil{}:
              Filed{path, False{}, rev, stat} <> attach(rest, Nil{})
            case s <> more:
              Filed{path, False{}, rev, s} <> attach(rest, more)

def is_payload(+l: String) -> Bool:
  Bool.not(Bool.or(String.starts_with(l, "revisions/"), String.ends_with(l, ".ops.txt")))

def payloads(ls: List<&2, String>) -> List<&2, String>:
  match ls:
    case Nil{}:
      Nil{}
    case +l <> rest:
      Rev.keep(is_payload(l), l, payloads(rest))

# A revision is reported and then kept: the graph `check` closes with is the
# same documents, and reading and hashing the whole of `revisions/` a second
# time to ask which parents are missing is a second pass over the store for
# an answer the first pass already holds.
def check_filed.doc(+path: String, +rev: Bool, +d: Store.Doc) -> IO(List<&2, Store.Doc>):
  do IO<List<&2, Store.Doc>>:
    IO.print(check_doc.of(d, rev) ++ "  " ++ path)
    return Bool.pick(List<&2, Store.Doc>, rev, d <> Nil{}, Nil{})

def check_filed(+root: String, f: Filed) -> IO(List<&2, Store.Doc>):
  match f:
    case Filed{+path, doc, rev, +stat}:
      match doc:
        case True{}:
          do IO<List<&2, Store.Doc>>:
            d : Store.Doc <- Store.read_doc(root ++ "/" ++ path)
            check_filed.doc(path, rev, d)
        case False{}:
          do IO<List<&2, Store.Doc>>:
            IO.print(check_payload(stat) ++ "  " ++ path)
            return Nil{}

def check_files(+root: String, fs: List<&2, Filed>) -> IO(List<&2, Store.Doc>):
  match fs:
    case Nil{}:
      IO.pure(List<&2, Store.Doc>, Nil{})
    case f <> rest:
      do IO<List<&2, Store.Doc>>:
        here : List<&2, Store.Doc> <- check_filed(root, f)
        later : List<&2, Store.Doc> <- check_files(root, rest)
        return List.append(&2, Store.Doc, here, later)

def check() -> IO(Unit):
  do IO<Unit>:
    root : String <- Store.root()
    +r : String = root
    ls : List<&2, String> <- Store.listing(r)
    +ls2 : List<&2, String> = ls
    stats : List<&2, String> <- Store.stats(r, payloads(ls2))
    rs : List<&2, Store.Doc> <- check_files(r, attach(filed(ls2), stats))
    print_missing(Rev.missing_parents(history(fulls(r, rs))))

# The file set at a revision
# --------------------------

# `tree.bend` over everything the revision reaches, which is what the
# store does: decision 0008's rules decide what concurrent branches left,
# and a chain walks the same path with nothing contested.
def pad(+s: String, width: Nat) -> String:
  s ++ String.repeat(" ", Nat.sub(width, String.length(s)))

# The column is as wide as the longest path in bytes, and a path is padded
# out to it in characters: the Rust tool's `path.len()` measures the one and
# `{path:width$}` fills the other, so a path with a character outside ASCII
# in the store widens every line, and this prints the same bytes.
def widest(es: Tree.Tree()) -> Nat:
  match es:
    case Nil{}:
      0n
    case +e <> rest:
      Nat.max(List.length(&2, U32, Utf8.encode(Tree.entry_path(e))), widest(rest))

def by_path(+a: Tree.Entry, +b: Tree.Entry) -> Bool:
  String.is_le(Tree.entry_path(a) ++ "  " ++ Tree.entry_file(a), Tree.entry_path(b) ++ "  " ++ Tree.entry_file(b))

def print_files(es: Tree.Tree(), +width: Nat) -> IO(Unit):
  match es:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case +e <> rest:
      do IO<Unit>:
        IO.print(pad(Tree.entry_path(e), width) ++ "  " ++ Tree.entry_file(e))
        print_files(rest, width)

def files.of(+es: Tree.Tree()) -> IO(Unit):
  match es:
    case Nil{}:
      IO.print("no files here")
    case +some:
      print_files(List.sort(~Tree.Entry, ~(a => b => by_path(a, b)), some), widest(some))

def files(+target: String) -> IO(Unit):
  do IO<Unit>:
    root : String <- Store.root()
    +r : String = root
    rs : List<&2, Store.Doc> <- Store.revisions(r)
    +fs : List<&2, Full> = fulls(r, rs)
    bs : List<&2, Bm.Bookmark> <- bookmarks(r)
    f : Full <- resolved(fs, bs, target)
    t : Tree.Tree() <- tree(fs, id_of(f))
    files.of(t)

# names
# -----

# Where each bookmark points now. A file bookmark records no revision, so
# what it resolves to is where that file sits in what the current heads
# say together — the question a person made the bookmark to stop asking.
def names.here(merged: Result<&2, &2, Tree.Fault, Tree.Merged>) -> Maybe<&2, Tree.Tree()>:
  match merged:
    case Fail{e}:
      None{}
    case Done{m}:
      Some{Tree.merged_tree(m)}

def names.change(state: Rev.ChangeState, +all_ids: List<&2, String>) -> String:
  match state:
    case Rev.Resolved{+id}:
      abbreviate(id, all_ids)
    case Rev.UnknownChange{}:
      "(no revision here claims it)"
    case Rev.Abandoned{}:
      "(abandoned: every revision was superseded)"
    case Rev.Divergent{rs}:
      "(" ++ Nat.show(List.length(&2, String, rs)) ++ " current revisions; divergent)"

def names.file(here: Maybe<&2, Tree.Tree()>, +f: String) -> String:
  match here:
    case None{}:
      "(no file here has it)"
    case Some{t}:
      Maybe.default(&2, String, Tree.path(t, f), "(no file here has it)")

def names.resolution(+h: Rev.History(), +all_ids: List<&2, String>, +here: Maybe<&2, Tree.Tree()>, t: Bm.Target) -> String:
  match t:
    case Bm.Target.Revision{+id}:
      Bool.pick(String, Rev.member(all_ids, id), abbreviate(id, all_ids), "(not here yet)")
    case Bm.Target.Change{c}:
      names.change(Rev.change_state(h, c), all_ids)
    case Bm.Target.File{f}:
      names.file(here, f)

def names.widest(bs: List<&2, Bm.Bookmark>) -> Nat:
  match bs:
    case Nil{}:
      0n
    case b <> rest:
      Nat.max(List.length(&2, U32, Utf8.encode(Bm.name_of(b))), names.widest(rest))

def names.lines(bs: List<&2, Bm.Bookmark>, +h: Rev.History(), +all_ids: List<&2, String>, +here: Maybe<&2, Tree.Tree()>, +width: Nat) -> IO(Unit):
  match bs:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case +b <> rest:
      do IO<Unit>:
        IO.print(pad(Bm.name_of(b), width) ++ "  " ++ Bm.show(b) ++ "  ->  " ++ names.resolution(h, all_ids, here, Bm.target_of(b)))
        names.lines(rest, h, all_ids, here, width)

def names.of(+fs: List<&2, Full>, bs: List<&2, Bm.Bookmark>) -> IO(Unit):
  match bs:
    case Nil{}:
      IO.print("no bookmarks here yet")
    case +some:
      +h = history(fs)
      names.lines(some, h, ids(fs), names.here(Tree.merge(events_of(picked(reached.all(fs, current_heads(h)), Pick{waiting(fs), Nil{}})))), names.widest(some))

def names() -> IO(Unit):
  do IO<Unit>:
    root : String <- Store.root()
    +r : String = root
    rs : List<&2, Store.Doc> <- Store.revisions(r)
    bs : List<&2, Bm.Bookmark> <- bookmarks(r)
    names.of(fulls(r, rs), bs)

# One file's content
# ------------------

# What a revision says one file holds: `text` and `bytes` name a payload,
# `edit` an operation document over the parent's state, and nothing means
# the parent's state stands.
type Said is Data:
  Whole{digest: String}
  Edited{digest: String}
  Nothing{}

def said.kind(d: String, ours: Bool, is_edit: Bool, is_whole: Bool) -> Said:
  match ours:
    case False{}:
      Nothing{}
    case True{}:
      match is_edit:
        case True{}:
          Edited{d}
        case False{}:
          Bool.pick(Said, is_whole, Whole{d}, Nothing{})

def said.or(here: Said, later: Said) -> Said:
  match here:
    case Nothing{}:
      later
    case +some:
      some

def said.cut(+key: String, +file: String, cut: Maybe<&2, T.Split>) -> Said:
  match cut:
    case Some{T.Split{f, d}}:
      said.kind(d, String.eq(f, file), String.eq(key, "edit"), Bool.or(String.eq(key, "text"), String.eq(key, "bytes")))
    case None{}:
      Nothing{}

def said(facts: List<&2, Rev.Header>, +file: String) -> Said:
  match facts:
    case Nil{}:
      Nothing{}
    case Rev.Header{+k, +v} <> rest:
      said.or(said.cut(k, file, T.split_once(v)), said(rest, file))

# The documents a revision names for one file, which is all of `operations/`
# a reading command has any business opening. Collected before the content is
# built, so that the pure walk below has what it needs and the store is asked
# once for the whole chain rather than once a revision.
def said_digests(s: Said) -> List<&2, String>:
  match s:
    case Whole{d}:
      [d]
    case Edited{d}:
      [d]
    case Nothing{}:
      Nil{}

def wanted(fs: List<&2, Full>, +file: String) -> List<&2, String>:
  match fs:
    case Nil{}:
      Nil{}
    case f <> rest:
      List.append(&2, String, said_digests(said(facts_of(f), file)), wanted(rest, file))

def held(+id: String, +digest: String, doc: Maybe<&2, String>) -> Result<&2, &2, String, String>:
  match doc:
    case None{}:
      Fail{String.take(id, 12n) ++ " names the content document " ++ digest ++ ", which this store does not hold yet"}
    case Some{text}:
      Done{text}

# The file's content at every revision that holds it, oldest first as the
# trees are. A revision that says nothing inherits the first parent's that
# holds the file; a merge that resolved the file says so with an `edit`
# naming a resolution, which is the file whatever the parents hold.
type Contents is Data:
  Contents{content: Result<&2, &2, String, List<&2, Ops.Item>>, id: String}

def content_of(cs: List<&2, Contents>, +id: String) -> Maybe<&2, Result<&2, &2, String, List<&2, Ops.Item>>>:
  match cs:
    case Nil{}:
      None{}
    case Contents{c, +i} <> rest:
      Bool.pick(Maybe<&2, Result<&2, &2, String, List<&2, Ops.Item>>>, String.eq(i, id), Some{c}, content_of(rest, id))

def contents.parents(+cs: List<&2, Contents>, ps: List<&2, String>) -> Maybe<&2, Result<&2, &2, String, List<&2, Ops.Item>>>:
  match ps:
    case Nil{}:
      None{}
    case p <> rest:
      Maybe.or(&2, Result<&2, &2, String, List<&2, Ops.Item>>, content_of(cs, p), contents.parents(cs, rest))

def edited(state: Maybe<&2, Result<&2, &2, String, List<&2, Ops.Item>>>, doc: Result<&2, &2, String, String>, +file: String) -> Result<&2, &2, String, List<&2, Ops.Item>>:
  match state:
    case None{}:
      Fail{"an edit of " ++ file ++ " where no parent holds it"}
    case Some{r}:
      do Result<&2, &2, String, List<&2, Ops.Item>>:
        items : List<&2, Ops.Item> <- r
        text : String <- doc
        parsed : Ops.Doc <- Ops.parse(text)
        Ops.apply(items, parsed)

# Resolutions
# -----------

# The items one document mints, in its own order: a resolution's inserts,
# an operation document's inserts, or the lines of a payload, which is the
# document that inserts every line at 0.
def minted.inserts(ops: List<&2, Ops.Op>) -> List<&2, Ops.Item>:
  match ops:
    case Nil{}:
      Nil{}
    case Ops.Op{Ops.Insert{}, at, items} <> rest:
      List.append(&2, Ops.Item, items, minted.inserts(rest))
    case Ops.Op{Ops.Delete{}, at, items} <> rest:
      minted.inserts(rest)

def minted.ops(+text: String, parsed: Result<&2, &2, String, Ops.Doc>) -> List<&2, Ops.Item>:
  match parsed:
    case Done{Ops.Doc{forgets, result, ops}}:
      minted.inserts(ops)
    case Fail{e}:
      Ops.from_text(text)

def minted.resolution(parsed: Result<&2, &2, String, Res.Doc>) -> List<&2, Ops.Item>:
  match parsed:
    case Done{d}:
      Res.minted(d)
    case Fail{e}:
      Nil{}

def minted.by(+text: String, resolution: Bool) -> List<&2, Ops.Item>:
  match resolution:
    case True{}:
      minted.resolution(Res.parse(text))
    case False{}:
      minted.ops(text, Ops.parse(text))

def minted(+text: String) -> List<&2, Ops.Item>:
  minted.by(text, Res.is_resolution(text))

def kept.run(+d: String, +first: Nat, +count: Nat, +items: List<&2, Ops.Item>) -> Result<&2, &2, String, List<&2, Ops.Item>>:
  +holds = List.length(&2, Ops.Item, items)
  Bool.pick(Result<&2, &2, String, List<&2, Ops.Item>>, Nat.is_gt(Nat.add(first, count), holds),
    Fail{"this resolution keeps up to item " ++ Nat.show(Nat.add(first, count)) ++ " of " ++ d ++ ", which mints " ++ Nat.show(holds) ++ "; count the `+` lines of that document to see what the run should say"},
    Done{List.take(&2, Ops.Item, List.drop(&2, Ops.Item, items, first), count)})

def kept.found(+d: String, +first: Nat, +count: Nat, doc: Maybe<&2, String>) -> Result<&2, &2, String, List<&2, Ops.Item>>:
  match doc:
    case None{}:
      Fail{"this resolution keeps items of " ++ d ++ ", which nothing here holds; a resolution names the documents its lines come from, and that one has not arrived"}
    case Some{text}:
      kept.run(d, first, count, minted(text))

def assemble.piece(+ds: List<&2, Store.Doc>, p: Res.Piece) -> Result<&2, &2, String, List<&2, Ops.Item>>:
  match p:
    case Res.Piece.Keep{+d, first, count}:
      kept.found(d, first, count, doc_by_id(ds, d))
    case Res.Piece.Insert{items}:
      Done{items}

def assemble.pieces(+ds: List<&2, Store.Doc>, ps: List<&2, Res.Piece>) -> Result<&2, &2, String, List<&2, Ops.Item>>:
  match ps:
    case Nil{}:
      Done{Nil{}}
    case p <> rest:
      do Result<&2, &2, String, List<&2, Ops.Item>>:
        here : List<&2, Ops.Item> <- assemble.piece(ds, p)
        later : List<&2, Ops.Item> <- assemble.pieces(ds, rest)
        return List.append(&2, Ops.Item, here, later)

# The first item but the last that ends without a newline, if any.
def unterminated_at(items: List<&2, Ops.Item>, +i: Nat) -> Maybe<&2, Nat>:
  match items:
    case Nil{}:
      None{}
    case it <> Nil{}:
      None{}
    case Ops.Item{t, True{}, f} <> rest:
      unterminated_at(rest, 1n+i)
    case Ops.Item{t, False{}, f} <> rest:
      Some{i}

def assembled.shape(at: Maybe<&2, Nat>) -> Result<&2, &2, String, Unit>:
  match at:
    case None{}:
      Done{Unit{}}
    case Some{i}:
      Fail{"only a file's last line may end without a newline, and item " ++ Nat.show(i) ++ " of the result does not end with one; delete that line and add it back with a terminator, in the revision that puts items after it"}

# Decision 0031: a hand-assembled resolution is verified by `shasum` like
# everything else, until forgetting has put bytes in it nobody hashed.
def assembled.result(result: Maybe<&2, String>, +items: List<&2, Ops.Item>) -> Result<&2, &2, String, Unit>:
  match result:
    case None{}:
      Done{Unit{}}
    case Some{+stated}:
      +found = Ops.state_digest(items)
      Bool.pick(Result<&2, &2, String, Unit>, Bool.or(Ops.any_forgotten(items), String.eq(stated, found)), Done{Unit{}},
        Fail{"this document says it produces " ++ stated ++ " and replaying it produces " ++ found ++ "; the document, its parent, or the replayer is wrong, and `shasum -a 256` on the replayed file is how to see which"})

def assemble(+ds: List<&2, Store.Doc>, d: Res.Doc) -> Result<&2, &2, String, List<&2, Ops.Item>>:
  match d:
    case Res.Doc{forgets, result, pieces}:
      do Result<&2, &2, String, List<&2, Ops.Item>>:
        +items : List<&2, Ops.Item> <- assemble.pieces(ds, pieces)
        assembled.shape(unterminated_at(items, 0n))
        assembled.result(result, items)
        return items

def resolved.said(+id: String, +file: String, r: Result<&2, &2, String, List<&2, Ops.Item>>) -> Result<&2, &2, String, List<&2, Ops.Item>>:
  match r:
    case Fail{e}:
      Fail{id ++ ", file " ++ file ++ ": " ++ e}
    case Done{items}:
      Done{items}

# Where the document with this digest was read from.
def path_by_id(ds: List<&2, Store.Doc>, +id: String) -> String:
  match ds:
    case Nil{}:
      id
    case Store.Doc{path, +i, size, text} <> rest:
      Bool.pick(String, String.eq(i, id), path, path_by_id(rest, id))

def resolved.doc(+ds: List<&2, Store.Doc>, +id: String, +file: String, +digest: String, parsed: Result<&2, &2, String, Res.Doc>) -> Result<&2, &2, String, List<&2, Ops.Item>>:
  match parsed:
    case Fail{e}:
      Fail{"what the revisions did could not be read: " ++ path_by_id(ds, digest) ++ ": " ++ e}
    case Done{d}:
      resolved.said(id, file, assemble(ds, d))

# What an `edit` names is a resolution or an operation document, and which
# is said by the document's own bytes.
def edited.by(+ds: List<&2, Store.Doc>, +id: String, +file: String, +digest: String, inherited: Maybe<&2, Result<&2, &2, String, List<&2, Ops.Item>>>, +text: String, resolution: Bool) -> Result<&2, &2, String, List<&2, Ops.Item>>:
  match resolution:
    case True{}:
      resolved.doc(ds, id, file, digest, Res.parse(text))
    case False{}:
      edited(inherited, Done{text}, file)

def edited.doc(+ds: List<&2, Store.Doc>, +id: String, +file: String, +digest: String, inherited: Maybe<&2, Result<&2, &2, String, List<&2, Ops.Item>>>, doc: Result<&2, &2, String, String>) -> Result<&2, &2, String, List<&2, Ops.Item>>:
  match doc:
    case Fail{e}:
      Fail{e}
    case Done{+text}:
      edited.by(ds, id, file, digest, inherited, text, Res.is_resolution(text))

# The documents the resolutions among these keep items of, which a reader
# fetches after the documents the revisions name and before it assembles.
def kept_digests.of(+text: String, resolution: Bool) -> List<&2, String>:
  match resolution:
    case True{}:
      Res.keeps(Res.parse(text))
    case False{}:
      Nil{}

def kept_digests(ds: List<&2, Store.Doc>) -> List<&2, String>:
  match ds:
    case Nil{}:
      Nil{}
    case Store.Doc{path, id, size, +text} <> rest:
      List.append(&2, String, kept_digests.of(text, Res.is_resolution(text)), kept_digests(rest))

def contents.said(+ds: List<&2, Store.Doc>, +id: String, +file: String, inherited: Maybe<&2, Result<&2, &2, String, List<&2, Ops.Item>>>, s: Said) -> Maybe<&2, Result<&2, &2, String, List<&2, Ops.Item>>>:
  match s:
    case Whole{+d}:
      Some{Result.map(&2, &2, String, String, List<&2, Ops.Item>, t => Ops.from_text(t), held(id, d, doc_by_id(ds, d)))}
    case Edited{+d}:
      Some{edited.doc(ds, id, file, d, inherited, held(id, d, doc_by_id(ds, d)))}
    case Nothing{}:
      inherited

def contents.push(+id: String, c: Maybe<&2, Result<&2, &2, String, List<&2, Ops.Item>>>, cs: List<&2, Contents>) -> List<&2, Contents>:
  match c:
    case None{}:
      cs
    case Some{r}:
      Contents{r, id} <> cs

def contents.go(oldest_first: List<&2, Full>, +ds: List<&2, Store.Doc>, +file: String, +cs: List<&2, Contents>) -> List<&2, Contents>:
  match oldest_first:
    case Nil{}:
      cs
    case Full{+id, change, parents, supersedes, author, when, revised_by, revised, facts, message} <> rest:
      contents.go(rest, ds, file, contents.push(id, contents.said(ds, id, file, contents.parents(cs, parents), said(facts, file)), cs))

def content.found(+file: String, found: Maybe<&2, Result<&2, &2, String, List<&2, Ops.Item>>>) -> Result<&2, &2, String, List<&2, Ops.Item>>:
  match found:
    case None{}:
      Fail{"no revision behind here says what " ++ file ++ " holds"}
    case Some{r}:
      r

def content.in(oldest_first: List<&2, Full>, +ds: List<&2, Store.Doc>, +id: String, +file: String) -> Result<&2, &2, String, List<&2, Ops.Item>>:
  content.found(file, content_of(contents.go(oldest_first, ds, file, Nil{}), id))

def content(+fs: List<&2, Full>, +ds: List<&2, Store.Doc>, +id: String, +file: String) -> Result<&2, &2, String, List<&2, Ops.Item>>:
  content.found(file, content_of(contents.go(List.reverse(&2, Full, presentation(fs)), ds, file, Nil{}), id))

# Decision 0040: a link has no bytes, and printing the target where the
# content goes would be a rendering standing in for a file; the reader is
def directory_of.join(first: String, rest: String) -> String:
  match rest:
    case SNil{}:
      first
    case SCon{c, t}:
      first ++ "/" ++ SCon{c, t}

# Every part but the last, joined; nothing for a path at the root.
def directory_of.rest(rest: List<&2, String>, first: String) -> String:
  match rest:
    case Nil{}:
      ""
    case second <> more:
      directory_of.join(first, directory_of.rest(more, second))

# told where it points, relative to where the link sits.
def directory_of.of(parts: List<&2, String>) -> String:
  match parts:
    case Nil{}:
      ""
    case first <> rest:
      directory_of.rest(rest, first)

def directory_of(+path: String) -> String:
  directory_of.of(String.split(path, '/'))

def relative.go(from: List<&2, String>, to: List<&2, String>) -> List<&2, String>:
  match from to:
    case +f <> +fs +t <> +ts:
      Bool.pick(List<&2, String>, String.eq(f, t), relative.go(fs, ts), List.append(&2, String, List.replicate(String, 1n+List.length(&2, String, fs), ".."), t <> ts))
    case Nil{} _:
      to
    case _ Nil{}:
      List.replicate(String, List.length(&2, String, from), "..")

def relative.of(parts: List<&2, String>) -> String:
  match parts:
    case Nil{}:
      "."
    case +some:
      String.join(some, "/")

def relative_path(+from: String, to: String) -> String:
  relative.of(relative.go(Bool.pick(List<&2, String>, String.is_empty(from), Nil{}, String.split(from, '/')), String.split(to, '/')))

def materialise.of(+at: String, found: Maybe<&2, String>, otherwise: String) -> String:
  match found:
    case None{}:
      otherwise
    case Some{to}:
      relative_path(directory_of(at), to)

def materialise(+t: Tree.Tree(), +at: String, target: Tree.Target) -> String:
  match target:
    case Tree.Verbatim{spelling}:
      spelling
    case Tree.Reference{+named}:
      materialise.of(at, Tree.path(t, named), "file:" ++ named)

def not_a_link(+t: Tree.Tree(), +path: String, +file: String, target: Maybe<&2, Tree.Target>) -> IO(Unit):
  match target:
    case None{}:
      IO.pure(Unit, Unit{})
    case Some{g}:
      die(Unit, 1, "`" ++ path ++ "` is a link to `" ++ materialise(t, Maybe.default(&2, String, Tree.path(t, file), path), g) ++ "`, so there is nothing to print; what it holds is where it points")

def cat.print(r: Result<&2, &2, String, List<&2, Ops.Item>>) -> IO(Unit):
  match r:
    case Fail{e}:
      die(Unit, 1, e)
    case Done{items}:
      IO.write(Ops.text(items))

def cat(+target: String, +path: String) -> IO(Unit):
  do IO<Unit>:
    root : String <- Store.root()
    +r : String = root
    rs : List<&2, Store.Doc> <- Store.revisions(r)
    +fs : List<&2, Full> = fulls(r, rs)
    bs : List<&2, Bm.Bookmark> <- bookmarks(r)
    +bs2 : List<&2, Bm.Bookmark> = bs
    f : Full <- resolved(fs, bs2, target)
    +id : String = id_of(f)
    t : Tree.Tree() <- tree(fs, id)
    +t2 : Tree.Tree() = t
    +path2 : String = path
    file : String <- file_in(id, bs2, path2, t2)
    +file2 : String = file
    not_a_link(t2, path2, file2, Tree.entry_target_of(Tree.lookup(t2, file2)))
    ds : List<&2, Store.Doc> <- Store.fetch(r, wanted(fs, file2))
    +ds2 : List<&2, Store.Doc> = ds
    more : List<&2, Store.Doc> <- Store.fetch(r, kept_digests(ds2))
    cat.print(content(fs, List.append(&2, Store.Doc, ds2, more), id, file2))

# show
# ----

def show.doc(+id: String, +digest: String, doc: Maybe<&2, String>) -> IO(Unit):
  match doc:
    case None{}:
      die(Unit, 1, String.take(id, 12n) ++ " names the content document " ++ digest ++ ", which this store does not hold yet")
    case Some{text}:
      IO.write(text)

def show.said(+id: String, +file: String, +ds: List<&2, Store.Doc>, s: Said) -> IO(Unit):
  match s:
    case Nothing{}:
      die(Unit, 1, String.take(id, 12n) ++ " did nothing to " ++ file)
    case Whole{+d}:
      show.doc(id, d, doc_by_id(ds, d))
    case Edited{+d}:
      show.doc(id, d, doc_by_id(ds, d))

def show.of(+fs: List<&2, Full>, +bs: List<&2, Bm.Bookmark>, +root: String, +f: Full, path: Maybe<&2, String>) -> IO(Unit):
  match path:
    case None{}:
      do IO<Unit>:
        ds : List<&2, Store.Doc> <- Store.fetch(root, [id_of(f)])
        show.doc(id_of(f), id_of(f), doc_by_id(ds, id_of(f)))
    case Some{+p}:
      do IO<Unit>:
        t : Tree.Tree() <- tree(fs, id_of(f))
        file : String <- file_in(id_of(f), bs, p, t)
        +file2 : String = file
        +s : Said = said(facts_of(f), file2)
        ds : List<&2, Store.Doc> <- Store.fetch(root, said_digests(s))
        show.said(id_of(f), file2, ds, s)

def show(+target: String, path: Maybe<&2, String>) -> IO(Unit):
  do IO<Unit>:
    root : String <- Store.root()
    +r : String = root
    rs : List<&2, Store.Doc> <- Store.revisions(r)
    +fs : List<&2, Full> = fulls(r, rs)
    bs : List<&2, Bm.Bookmark> <- bookmarks(r)
    +bs2 : List<&2, Bm.Bookmark> = bs
    f : Full <- resolved(fs, bs2, target)
    show.of(fs, bs2, r, f, path)

# What changed
# ------------

# A comparison laid over the parent: every line the parent held, in order,
# as a context line or a removal, and each run that arrived where the
# document puts it — removals first where a run was replaced. The positions
# are the document's, counted into the parent, so this is arithmetic rather
# than a second diff; `diff` renders it and `blame` reads its origins off it.
type Laid is Data:
  Laid{sign: String, item: Ops.Item}

def laid.sign(l: Laid) -> String:
  match l:
    case Laid{sign, item}:
      sign

def laid.all(+sign: String, items: List<&2, Ops.Item>, acc: List<&2, Laid>) -> List<&2, Laid>:
  match items:
    case Nil{}:
      acc
    case it <> rest:
      laid.all(sign, rest, Laid{sign, it} <> acc)

# The parent's items still to lay, where they start, the operations still
# to consult, and the lines laid so far, newest first.
type Lay is Data:
  Lay{items: List<&2, Ops.Item>, at: Nat, ops: List<&2, Ops.Op>, acc: List<&2, Laid>}

def lay.arrived(+at: Nat, here: Bool, op: Ops.Op, rest: List<&2, Ops.Op>, acc: List<&2, Laid>) -> Lay:
  match here op:
    case True{} Ops.Op{v, p, items}:
      Lay{Nil{}, at, rest, laid.all("+", items, acc)}
    case False{} _:
      Lay{Nil{}, at, op <> rest, acc}

def lay.arrivals(+at: Nat, ops: List<&2, Ops.Op>, acc: List<&2, Laid>) -> Lay:
  match ops:
    case Ops.Op{Ops.Insert{}, +p, items} <> rest:
      lay.arrived(at, Nat.is_eq(p, at), Ops.Op{Ops.Insert{}, p, items}, rest, acc)
    case +other:
      Lay{Nil{}, at, other, acc}

def lay.context(items: List<&2, Ops.Item>, +at: Nat, l: Lay) -> Lay:
  match items l:
    case it <> rest Lay{none, a, ops, acc}:
      Lay{rest, 1n+at, ops, Laid{" ", it} <> acc}
    case Nil{} Lay{none, a, ops, acc}:
      Lay{Nil{}, at, ops, acc}

def lay.removed(+n: Nat, items: List<&2, Ops.Item>, +at: Nat, l: Lay) -> Lay:
  match l:
    case Lay{none, a, ops, acc}:
      Lay{List.drop(&2, Ops.Item, items, n), Nat.add(at, n), ops, acc}

def lay.delete(+items: List<&2, Ops.Item>, +at: Nat, +n: Nat, rest: List<&2, Ops.Op>, acc: List<&2, Laid>) -> Lay:
  lay.removed(n, items, at, lay.arrivals(at, rest, laid.all("-", List.take(&2, Ops.Item, items, n), acc)))

def lay.tail(ops: List<&2, Ops.Op>) -> List<&2, Ops.Op>:
  match ops:
    case Nil{}:
      Nil{}
    case op <> rest:
      rest

def lay.at(items: List<&2, Ops.Item>, +at: Nat, ops: List<&2, Ops.Op>, acc: List<&2, Laid>, deleting: Maybe<&2, Nat>) -> Lay:
  match deleting:
    case Some{n}:
      lay.delete(items, at, n, lay.tail(ops), acc)
    case None{}:
      lay.context(items, at, lay.arrivals(at, ops, acc))

def lay.deleting(+at: Nat, ops: List<&2, Ops.Op>) -> Maybe<&2, Nat>:
  match ops:
    case Ops.Op{Ops.Delete{}, +p, +gone} <> rest:
      Bool.pick(Maybe<&2, Nat>, Nat.is_eq(p, at), Some{List.length(&2, Ops.Item, gone)}, None{})
    case _:
      None{}

def lay.step(l: Lay) -> Lay:
  match l:
    case Lay{items, +at, +ops, acc}:
      lay.at(items, at, ops, acc, lay.deleting(at, ops))

def lay.go(fuel: Nat, l: Lay) -> List<&2, Laid>:
  match fuel l:
    case _ Lay{Nil{}, at, Nil{}, acc}:
      List.reverse(&2, Laid, acc)
    case 0n Lay{items, at, ops, acc}:
      List.reverse(&2, Laid, acc)
    case 1n+f Lay{items, at, ops, acc}:
      lay.go(f, lay.step(Lay{items, at, ops, acc}))

def laid(+before: List<&2, Ops.Item>, doc: Ops.Doc) -> List<&2, Laid>:
  match doc:
    case Ops.Doc{forgets, result, +ops}:
      lay.go(Nat.add(1n+List.length(&2, Ops.Item, before), Nat.mul(2n, List.length(&2, Ops.Op, ops))), Lay{before, 0n, ops, Nil{}})

# Hunks
# -----

# A line of the rendering and the colour it is drawn in where there is
# colour: bold for a fact about a file, cyan for a hunk's header, red and
# green for what left and arrived, nothing for context. Off, every line is
# the bytes it would be anyway, which is what `historica diff | patch` sees.
type Painted is Data:
  Painted{code: String, text: String}

def plain(text: String) -> Painted:
  Painted{SNil{}, text}

def meta(text: String) -> Painted:
  Painted{"\u{1b}[1m", text}

def sign_code(+sign: String) -> String:
  Bool.pick(String, String.eq(sign, "-"), "\u{1b}[31m", Bool.pick(String, String.eq(sign, "+"), "\u{1b}[32m", SNil{}))

# A laid line with its line number on each side, counting from one.
type Numbered is Data:
  Numbered{laid: Laid, before: Nat, after: Nat}

def numbered(ls: List<&2, Laid>, +b: Nat, +a: Nat) -> List<&2, Numbered>:
  match ls:
    case Nil{}:
      Nil{}
    case Laid{+sign, it} <> rest:
      Numbered{Laid{sign, it}, b, a} <> numbered(rest, Bool.pick(Nat, String.eq(sign, "+"), b, 1n+b), Bool.pick(Nat, String.eq(sign, "-"), a, 1n+a))

def numbered.sign(n: Numbered) -> String:
  match n:
    case Numbered{l, b, a}:
      laid.sign(l)

# A run of lines to print, `end` exclusive.
type Span2 is Data:
  Span2{start: Nat, end: Nat}

# Three lines of context around each change, and two runs whose context
# would print a line twice are one.
def spans.add(+start: Nat, +end: Nat, acc: List<&2, Span2>) -> List<&2, Span2>:
  match acc:
    case Span2{+s, +e} <> +rest:
      Bool.pick(List<&2, Span2>, Nat.is_ge(e, start), Span2{s, Nat.max(end, e)} <> rest, Span2{start, end} <> Span2{s, e} <> rest)
    case Nil{}:
      [Span2{start, end}]

def spans.at(+i: Nat, +len: Nat, changed: Bool, acc: List<&2, Span2>) -> List<&2, Span2>:
  match changed:
    case True{}:
      spans.add(Nat.sub(i, 3n), Nat.min(Nat.add(i, 4n), len), acc)
    case False{}:
      acc

def spans(ns: List<&2, Numbered>, +i: Nat, +len: Nat, acc: List<&2, Span2>) -> List<&2, Span2>:
  match ns:
    case Nil{}:
      List.reverse(&2, Span2, acc)
    case n <> rest:
      spans(rest, 1n+i, len, spans.at(i, len, Bool.not(String.eq(numbered.sign(n), " ")), acc))

def hunk.count(ns: List<&2, Numbered>, +skip: String) -> Nat:
  match ns:
    case Nil{}:
      0n
    case n <> rest:
      Nat.add(Bool.pick(Nat, String.eq(numbered.sign(n), skip), 0n, 1n), hunk.count(rest, skip))

def hunk.first(ns: List<&2, Numbered>, before: Bool) -> Nat:
  match ns:
    case Nil{}:
      0n
    case Numbered{l, b, a} <> rest:
      Bool.pick(Nat, before, b, a)

def hunk.side(+count: Nat, first: Nat) -> Nat:
  Bool.pick(Nat, Nat.is_eq(count, 0n), 0n, first)

# One line of a comparison, and the marker after one that ends without a
# newline.
def laid.text(+sign: String, it: Ops.Item) -> List<&2, Painted>:
  match it:
    case Ops.Item{t, True{}, f}:
      [Painted{sign_code(sign), sign ++ Ops.shown(Ops.Item{t, True{}, f})}]
    case Ops.Item{t, False{}, f}:
      [Painted{sign_code(sign), sign ++ Ops.shown(Ops.Item{t, False{}, f})}, Painted{sign_code(sign), "\\ no newline at end of file"}]

def hunk.lines(ns: List<&2, Numbered>) -> List<&2, Painted>:
  match ns:
    case Nil{}:
      Nil{}
    case Numbered{Laid{sign, it}, b, a} <> rest:
      List.append(&2, Painted, laid.text(sign, it), hunk.lines(rest))

def hunk(+ns: List<&2, Numbered>, sp: Span2) -> List<&2, Painted>:
  match sp:
    case Span2{+start, end}:
      +slice = List.take(&2, Numbered, List.drop(&2, Numbered, ns, start), Nat.sub(end, start))
      +bc = hunk.count(slice, "+")
      +ac = hunk.count(slice, "-")
      Painted{"\u{1b}[36m", "@@ -" ++ Nat.show(hunk.side(bc, hunk.first(slice, True{}))) ++ "," ++ Nat.show(bc) ++ " +" ++ Nat.show(hunk.side(ac, hunk.first(slice, False{}))) ++ "," ++ Nat.show(ac) ++ " @@"} <> hunk.lines(slice)

def hunks.of(+ns: List<&2, Numbered>, sps: List<&2, Span2>) -> List<&2, Painted>:
  match sps:
    case Nil{}:
      Nil{}
    case sp <> rest:
      List.append(&2, Painted, hunk(ns, sp), hunks.of(ns, rest))

def hunks(+ls: List<&2, Laid>) -> List<&2, Painted>:
  +ns = numbered(ls, 1n, 1n)
  hunks.of(ns, spans(ns, 0n, List.length(&2, Numbered, ns), Nil{}))

# diff
# ----

# What one side holds of a file: its lines, or the digest of a file of
# bytes and how many there are, where the store holds them.
type Side is Data:
  Side.Lines{items: List<&2, Ops.Item>}
  Side.Whole{digest: String, size: Maybe<&2, Nat>}

def side.digest(s: Maybe<&2, Side>) -> String:
  match s:
    case None{}:
      SNil{}
    case Some{Side.Lines{items}}:
      Ops.state_digest(items)
    case Some{Side.Whole{d, n}}:
      d

# A link's target as a person reads it at that revision: the path a `file:`
# target resolves to there, and the identity beside it.
def shown.target(+t: Tree.Tree(), +at: String, target: Tree.Target) -> String:
  match target:
    case Tree.Reference{+file}:
      materialise(t, at, Tree.Reference{file}) ++ " (file:" ++ String.take(file, 8n) ++ ")"
    case Tree.Verbatim{spelling}:
      spelling

def shown(+t: Tree.Tree(), e: Maybe<&2, Tree.Entry>) -> Maybe<&2, String>:
  match e:
    case None{}:
      None{}
    case Some{Tree.Entry{f, +p, k, y, g, m}}:
      Maybe.map(&2, Tree.Target, String, x => shown.target(t, p, x), g)

# Where a link pointed on each side, where they differ; `None` on a side
# that holds no link at all.
type Retarget is Data:
  Retarget{was: Maybe<&2, String>, now: Maybe<&2, String>}

# One file as the two sides hold it.
type Compared is Data:
  Compared{from: Maybe<&2, String>, to: Maybe<&2, String>, before: Maybe<&2, Side>, after: Maybe<&2, Side>,
       modes: Maybe<&2, T.Split>, targets: Maybe<&2, Retarget>}

def maybe_eq(a: Maybe<&2, String>, b: Maybe<&2, String>) -> Bool:
  match a b:
    case None{} None{}:
      True{}
    case Some{x} Some{y}:
      String.eq(x, y)
    case _ _:
      False{}

def side.present(s: Maybe<&2, Side>) -> Bool:
  match s:
    case None{}:
      False{}
    case Some{x}:
      True{}

def pair.differs(p: Compared) -> Bool:
  match p:
    case Compared{from, to, +before, +after, modes, targets}:
      Bool.or(Bool.or(Bool.not(maybe_eq(from, to)), Bool.or(Maybe.is_some(&2, T.Split, modes), Maybe.is_some(&2, Retarget, targets))),
        Bool.or(Bool.xor(side.present(before), side.present(after)), Bool.not(String.eq(side.digest(before), side.digest(after)))))

def entry.path(e: Maybe<&2, Tree.Entry>) -> Maybe<&2, String>:
  Maybe.map(&2, Tree.Entry, String, x => Tree.entry_path(x), e)

def modes(was: Maybe<&2, Tree.Entry>, now: Maybe<&2, Tree.Entry>) -> Maybe<&2, T.Split>:
  match was now:
    case Some{Tree.Entry{f, p, Tree.Link{}, y, g, m}} _:
      None{}
    case Some{Tree.Entry{f, p, k, y, g, +m}} Some{Tree.Entry{f2, p2, k2, y2, g2, +m2}}:
      Bool.pick(Maybe<&2, T.Split>, Tree.mode_eq(m, m2), None{}, Some{T.Split{Tree.mode_show(m), Tree.mode_show(m2)}})
    case _ _:
      None{}

def retargeting(was: Maybe<&2, String>, now: Maybe<&2, String>) -> Maybe<&2, Retarget>:
  match was now:
    case None{} None{}:
      None{}
    case Some{+a} Some{+b}:
      Bool.pick(Maybe<&2, Retarget>, String.eq(a, b), None{}, Some{Retarget{Some{a}, Some{b}}})
    case x y:
      Some{Retarget{x, y}}

# Rendering
# ---------

def spelled.side(s: Maybe<&2, String>) -> String:
  match s:
    case None{}:
      SNil{}
    case Some{x}:
      " " ++ x

def binary.side(s: Maybe<&2, Side>) -> String:
  match s:
    case None{}:
      SNil{}
    case Some{Side.Whole{d, None{}}}:
      " " ++ String.take(d, 12n)
    case Some{Side.Whole{d, Some{n}}}:
      " " ++ String.take(d, 12n) ++ " " ++ Nat.show(n) ++ " bytes"
    case Some{Side.Lines{+items}}:
      " " ++ String.take(Ops.state_digest(items), 12n) ++ " " ++ Nat.show(List.length(&2, U32, Utf8.encode(Ops.text(items)))) ++ " bytes"

def side.lines(s: Maybe<&2, Side>) -> Maybe<&2, List<&2, Ops.Item>>:
  match s:
    case None{}:
      Some{Nil{}}
    case Some{Side.Lines{items}}:
      Some{items}
    case Some{Side.Whole{d, n}}:
      None{}

def render.facts(from: Maybe<&2, String>, to: Maybe<&2, String>) -> List<&2, Painted>:
  match from to:
    case None{} Some{p}:
      [meta("new file " ++ p)]
    case Some{p} None{}:
      [meta("deleted file " ++ p)]
    case Some{+a} Some{+b}:
      Bool.pick(List<&2, Painted>, String.eq(a, b), Nil{}, [meta("rename from " ++ a), meta("rename to " ++ b)])
    case _ _:
      Nil{}

def render.mode(+path: String, m: Maybe<&2, T.Split>) -> List<&2, Painted>:
  match m:
    case None{}:
      Nil{}
    case Some{T.Split{was, now}}:
      [meta("mode " ++ path ++ " " ++ was ++ " -> " ++ now)]

def render.link(+path: String, t: Maybe<&2, Retarget>) -> List<&2, Painted>:
  match t:
    case None{}:
      Nil{}
    case Some{Retarget{was, now}}:
      [meta("link " ++ path ++ spelled.side(was) ++ " ->" ++ spelled.side(now))]

def render.hunks(+left: String, +right: String, +before: List<&2, Ops.Item>, d: Maybe<&2, Ops.Doc>) -> List<&2, Painted>:
  match d:
    case None{}:
      Nil{}
    case Some{doc}:
      meta("--- " ++ left) <> meta("+++ " ++ right) <> hunks(laid(before, doc))

# The same decomposition `record` would write down, rendered: `similar`'s
# Histogram diff, which `Sim` ports.
def render.content(+left: String, +right: String, before: Maybe<&2, List<&2, Ops.Item>>, after: Maybe<&2, List<&2, Ops.Item>>, +whole: String) -> List<&2, Painted>:
  match before after:
    case Some{+b} Some{a}:
      render.hunks(left, right, b, Sim.diff(b, a))
    case _ _:
      [meta("--- " ++ left), meta("+++ " ++ right), meta("binary files differ:" ++ whole)]

def render(p: Compared) -> List<&2, Painted>:
  match p:
    case Compared{+from, +to, +before, +after, modes, targets}:
      +path = Maybe.default(&2, String, Maybe.or(&2, String, to, from), "?")
      List.append(&2, Painted, render.facts(from, to), List.append(&2, Painted, render.mode(path, modes), List.append(&2, Painted, render.link(path, targets),
        render.content(Maybe.default(&2, String, Maybe.map(&2, String, String, x => "a/" ++ x, from), "/dev/null"), Maybe.default(&2, String, Maybe.map(&2, String, String, x => "b/" ++ x, to), "/dev/null"),
          side.lines(before), side.lines(after), binary.side(before) ++ " ->" ++ binary.side(after)))))

def print_lines(ls: List<&2, String>) -> IO(Unit):
  match ls:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case l <> rest:
      do IO<Unit>:
        IO.print(l)
        print_lines(rest)

def diff.rendered(ps: List<&2, Compared>) -> List<&2, Painted>:
  match ps:
    case Nil{}:
      Nil{}
    case p <> rest:
      List.append(&2, Painted, render(p), diff.rendered(rest))

def painted(+paint: Bool, p: Painted) -> String:
  match p:
    case Painted{+code, +text}:
      Bool.pick(String, Bool.and(paint, Bool.not(String.is_empty(code))), code ++ text ++ "\u{1b}[0m", text)

def print_painted(+paint: Bool, ls: List<&2, Painted>) -> IO(Unit):
  match ls:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case l <> rest:
      do IO<Unit>:
        IO.print(painted(paint, l))
        print_painted(paint, rest)

def print_pairs(+paint: Bool, ps: List<&2, Compared>) -> IO(Unit):
  match ps:
    case Nil{}:
      IO.print("nothing differs")
    case +some:
      print_painted(paint, diff.rendered(some))

# The command
# -----------

# What `diff` was asked: `--onto`, `--color`, and the rest in order.
type DiffAsked is Data:
  DiffAsked{onto: Maybe<&2, String>, color: String, rest: List<&2, String>}

type DParse is Data:
  DParse{args: List<&2, String>, asked: Result<&2, &2, String, DiffAsked>}

def dasked.onto(a: DiffAsked, v: String) -> DiffAsked:
  match a:
    case DiffAsked{o, c, r}:
      DiffAsked{Some{v}, c, r}

def dasked.word(a: DiffAsked, w: String) -> DiffAsked:
  match a:
    case DiffAsked{o, c, r}:
      DiffAsked{o, c, w <> r}

def dasked.set_color(a: DiffAsked, v: String) -> DiffAsked:
  match a:
    case DiffAsked{o, c, r}:
      DiffAsked{o, v, r}

def color_ok(+v: String) -> Bool:
  Bool.or(String.eq(v, "auto"), Bool.or(String.eq(v, "always"), String.eq(v, "never")))

def dasked.color(a: DiffAsked, +v: String, ok: Bool) -> Result<&2, &2, String, DiffAsked>:
  match ok:
    case True{}:
      Done{dasked.set_color(a, v)}
    case False{}:
      Fail{"`" ++ v ++ "` is not a `--color` setting; it is `auto`, which decorates a terminal and nothing else, `always`, or `never`"}

def dasked.other(a: DiffAsked, +w: String, spelled: Maybe<&2, String>) -> Result<&2, &2, String, DiffAsked>:
  match spelled:
    case Some{+v}:
      dasked.color(a, v, color_ok(v))
    case None{}:
      Done{dasked.word(a, w)}

def dasked.step(args: List<&2, String>, a: DiffAsked) -> DParse:
  match args:
    case "--onto" <> v <> rest:
      DParse{rest, Done{dasked.onto(a, v)}}
    case "--onto" <> Nil{}:
      DParse{Nil{}, Fail{"`--onto` wants a value"}}
    case "--color" <> +v <> rest:
      DParse{rest, dasked.color(a, v, color_ok(v))}
    case "--color" <> Nil{}:
      DParse{Nil{}, Fail{"`--color` wants `auto`, `always`, or `never`"}}
    case +w <> rest:
      DParse{rest, dasked.other(a, w, T.strip_prefix(w, "--color="))}
    case Nil{}:
      DParse{Nil{}, Done{a}}

def dasked.go(fuel: Nat, p: DParse) -> Result<&2, &2, String, DiffAsked>:
  match fuel p:
    case _ DParse{rest, Fail{e}}:
      Fail{e}
    case _ DParse{Nil{}, r}:
      r
    case 0n DParse{rest, r}:
      r
    case 1n+f DParse{args, Done{a}}:
      dasked.go(f, dasked.step(args, a))

def dasked.io(r: Result<&2, &2, String, DiffAsked>) -> IO(DiffAsked):
  match r:
    case Fail{e}:
      die(DiffAsked, 2, e)
    case Done{a}:
      IO.pure(DiffAsked, a)

# Whether a spelling could name a target at all: `head`, a bookmark, or a
# spelling in either alphabet. What nothing else could name is a path.
def could_be_target(+bs: List<&2, Bm.Bookmark>, +s: String) -> Bool:
  Bool.and(Bool.not(String.is_empty(s)), Bool.or(Bool.or(String.eq(s, "head"), Maybe.is_some(&2, Bm.Target, Bm.find(bs, s))),
    Bool.or(all_chars(~(c => is_hex(c)), s), all_chars(~(c => Id.is_letter(c)), s))))

# What that revision did is a comparison with its parent; a merge has more
# than one, and which a reader means is theirs to say.
def sole_parent.named(+id: String, ps: List<&2, String>) -> String:
  match ps:
    case Nil{}:
      SNil{}
    case p <> rest:
      "\n  historica diff " ++ String.take(id, 12n) ++ " --onto " ++ String.take(p, 12n) ++ sole_parent.named(id, rest)

def sole_parent.of(+id: String, ps: List<&2, String>) -> IO(Maybe<&2, String>):
  match ps:
    case Nil{}:
      IO.pure(Maybe<&2, String>, None{})
    case p <> Nil{}:
      IO.pure(Maybe<&2, String>, Some{p})
    case +several:
      die(Maybe<&2, String>, 1, String.take(id, 12n) ++ " is a merge, so what it did depends on which side you are asking about; name one with --onto:" ++ sole_parent.named(id, several))

def diff.left(+fs: List<&2, Full>, +bs: List<&2, Bm.Bookmark>, +right: Full, onto: Maybe<&2, String>) -> IO(Maybe<&2, String>):
  match onto:
    case Some{t}:
      do IO<Maybe<&2, String>>:
        f : Full <- resolved(fs, bs, t)
        return Some{id_of(f)}
    case None{}:
      sole_parent.of(id_of(right), parents_of(right))

# The one file a comparison is limited to: an identifier, which both sides
# share through any rename, or a path, which either side may hold.
type Limit is Data:
  Limit.None{}
  Limit.File{file: String}
  Limit.Path{path: String}

def limit.wants(l: Limit, +file: String, was: Maybe<&2, String>, now: Maybe<&2, String>) -> Bool:
  match l:
    case Limit.None{}:
      True{}
    case Limit.File{+f}:
      String.eq(f, file)
    case Limit.Path{+p}:
      Bool.or(maybe_eq(was, Some{p}), maybe_eq(now, Some{p}))

def diff.limit.file(+fs: List<&2, Full>, +bs: List<&2, Bm.Bookmark>, +right: String, +sp: String) -> IO(Limit):
  do IO<Limit>:
    t : Tree.Tree() <- tree(fs, right)
    f : String <- file_in(right, bs, sp, t)
    return Limit.File{f}

def diff.limit(+fs: List<&2, Full>, +bs: List<&2, Bm.Bookmark>, +right: String, only: Maybe<&2, String>) -> IO(Limit):
  match only:
    case None{}:
      IO.pure(Limit, Limit.None{})
    case Some{+sp}:
      Bool.pick(IO(Limit), String.starts_with(sp, "file:"), diff.limit.file(fs, bs, right, sp), IO.pure(Limit, Limit.Path{Maybe.default(&2, String, T.strip_prefix(sp, "path:"), sp)}))

# Which revisions stated each file's content, on one side: its ancestry's
# `text`, `bytes` and `edit` lines, newest first. Two sides whose lists for
# a file agree hold the same content for it — the same documents over the
# same graph — so only a file whose lists differ, or that one side lacks, is
# read at all; the rest are equal without being replayed.
def stating.put(+id: String, +file: String, r: Map<&2, List<&2, String>> & List<&2, String>) -> Map<&2, List<&2, String>>:
  (m, had) = r
  Map.set(&2, List<&2, String>, m, file, id <> had)

def stating.key(+k: String) -> Bool:
  Bool.or(String.eq(k, "text"), Bool.or(String.eq(k, "bytes"), String.eq(k, "edit")))

def stating.fact(+id: String, m: Map<&2, List<&2, String>>, +file: String, content: Bool) -> Map<&2, List<&2, String>>:
  match content:
    case True{}:
      stating.put(id, file, Map.get(List<&2, String>, Nil{}, m, file))
    case False{}:
      m

def stating.facts(+id: String, facts: List<&2, Rev.Header>, m: Map<&2, List<&2, String>>) -> Map<&2, List<&2, String>>:
  match facts:
    case Nil{}:
      m
    case Rev.Header{+k, +v} <> rest:
      stating.facts(id, rest, stating.fact(id, m, T.word(v), stating.key(k)))

def stating(fs: List<&2, Full>, m: Map<&2, List<&2, String>>) -> Map<&2, List<&2, String>>:
  match fs:
    case Nil{}:
      m
    case +f <> rest:
      stating(rest, stating.facts(id_of(f), facts_of(f), m))

def same_list(xs: List<&2, String>, ys: List<&2, String>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case x <> xr y <> yr:
      Bool.and(String.eq(x, y), same_list(xr, yr))
    case _ _:
      False{}

def stated.lists(r: Map<&2, List<&2, String>> & List<&2, String>) -> List<&2, String>:
  (m, xs) = r
  xs

# Both sides, and what reading content on them needs.
type Sides is Data:
  Sides{before: Tree.Tree(), after: Tree.Tree(), older: List<&2, Full>, newer: List<&2, Full>, docs: List<&2, Store.Doc>,
        left: String, right: String, was_stated: Map<&2, List<&2, String>>, now_stated: Map<&2, List<&2, String>>}

def side.read(+oldest: List<&2, Full>, +ds: List<&2, Store.Doc>, +at: String, +file: String, needed: Bool) -> Result<&2, &2, String, Maybe<&2, Side>>:
  match needed:
    case True{}:
      Result.map(&2, &2, String, List<&2, Ops.Item>, Maybe<&2, Side>, items => Some{Side.Lines{items}}, content.in(oldest, ds, at, file))
    case False{}:
      Done{Some{Side.Lines{Nil{}}}}

# What one side holds of a file: nothing for a link, whose target is said
# instead, the digest for a file of bytes, and the lines — where this
# comparison could find them changed, and otherwise a stand-in both sides
# share, since a file the revision said nothing about is what its parent
# held.
def side(+oldest: List<&2, Full>, +ds: List<&2, Store.Doc>, +at: String, +file: String, needed: Bool, e: Maybe<&2, Tree.Entry>) -> Result<&2, &2, String, Maybe<&2, Side>>:
  match e:
    case None{}:
      Done{None{}}
    case Some{Tree.Entry{f, p, Tree.Link{}, y, g, m}}:
      Done{None{}}
    case Some{Tree.Entry{f, p, Tree.Whole{}, y, g, m}}:
      Done{Some{Side.Whole{Maybe.default(&2, String, y, SNil{}), None{}}}}
    case Some{Tree.Entry{f, p, Tree.Lines{}, y, g, m}}:
      side.read(oldest, ds, at, file, needed)

def compare.built(+c: Compared) -> Maybe<&2, Compared>:
  Bool.pick(Maybe<&2, Compared>, pair.differs(c), Some{c}, None{})

# A file is read where one side lacks it or the two were stated by
# different revisions.
def compare.needed(+ws: Map<&2, List<&2, String>>, +ns: Map<&2, List<&2, String>>, +file: String, +was: Maybe<&2, Tree.Entry>, +now: Maybe<&2, Tree.Entry>) -> Bool:
  Bool.or(Bool.xor(Maybe.is_some(&2, Tree.Entry, was), Maybe.is_some(&2, Tree.Entry, now)),
    Bool.not(same_list(stated.lists(Map.get(List<&2, String>, Nil{}, ws, file)), stated.lists(Map.get(List<&2, String>, Nil{}, ns, file)))))

def compare.sides(+sd: Sides, +file: String, +was: Maybe<&2, Tree.Entry>, +now: Maybe<&2, Tree.Entry>) -> Result<&2, &2, String, Maybe<&2, Compared>>:
  match sd:
    case Sides{+before, +after, +older, +newer, +ds, +left, +right, +ws, +ns}:
      +needed = compare.needed(ws, ns, file, was, now)
      do Result<&2, &2, String, Maybe<&2, Compared>>:
        b : Maybe<&2, Side> <- side(older, ds, left, file, needed, was)
        a : Maybe<&2, Side> <- side(newer, ds, right, file, needed, now)
        return compare.built(Compared{entry.path(was), entry.path(now), b, a, modes(was, now), retargeting(shown(before, was), shown(after, now))})

def compare.wanted(+sd: Sides, +file: String, +was: Maybe<&2, Tree.Entry>, +now: Maybe<&2, Tree.Entry>, wants: Bool) -> Result<&2, &2, String, Maybe<&2, Compared>>:
  match wants:
    case True{}:
      compare.sides(sd, file, was, now)
    case False{}:
      Done{None{}}

def sides.before(sd: Sides) -> Tree.Tree():
  match sd:
    case Sides{before, after, older, newer, ds, left, right, ws, ns}:
      before

def sides.after(sd: Sides) -> Tree.Tree():
  match sd:
    case Sides{before, after, older, newer, ds, left, right, ws, ns}:
      after

# One file on both sides, found by walking the two trees together: each is
# in identifier order, so the pairing is one pass rather than a lookup in
# each for every file.
type Both is Data:
  Both{file: String, was: Maybe<&2, Tree.Entry>, now: Maybe<&2, Tree.Entry>}

def both.cmp(xs: List<&2, Tree.Entry>, ys: List<&2, Tree.Entry>) -> Cmp:
  match xs ys:
    case x <> xr y <> yr:
      String.order(Tree.entry_file(x), Tree.entry_file(y))
    case Nil{} _:
      GT{}
    case _ Nil{}:
      LT{}

def both.go(fuel: Nat, xs: List<&2, Tree.Entry>, ys: List<&2, Tree.Entry>, c: Cmp) -> List<&2, Both>:
  match fuel xs ys c:
    case 0n _ _ _:
      Nil{}
    case _ Nil{} Nil{} _:
      Nil{}
    case 1n+f +x <> +xr +y <> +yr EQ{}:
      Both{Tree.entry_file(x), Some{x}, Some{y}} <> both.go(f, xr, yr, both.cmp(xr, yr))
    case 1n+f +x <> +xr +ys2 LT{}:
      Both{Tree.entry_file(x), Some{x}, None{}} <> both.go(f, xr, ys2, both.cmp(xr, ys2))
    case 1n+f +xs2 +y <> +yr _:
      Both{Tree.entry_file(y), None{}, Some{y}} <> both.go(f, xs2, yr, both.cmp(xs2, yr))
    case 1n+f +x <> +xr Nil{} _:
      Both{Tree.entry_file(x), Some{x}, None{}} <> both.go(f, xr, Nil{}, both.cmp(xr, Nil{}))

def by_file(+a: Tree.Entry, +b: Tree.Entry) -> Bool:
  String.is_le(Tree.entry_file(a), Tree.entry_file(b))

def both(xs: List<&2, Tree.Entry>, ys: List<&2, Tree.Entry>) -> List<&2, Both>:
  +xs2 = List.sort(~Tree.Entry, ~(a => b => by_file(a, b)), xs)
  +ys2 = List.sort(~Tree.Entry, ~(a => b => by_file(a, b)), ys)
  both.go(1n+Nat.add(List.length(&2, Tree.Entry, xs2), List.length(&2, Tree.Entry, ys2)), xs2, ys2, both.cmp(xs2, ys2))

def compare.one(+sd: Sides, +l: Limit, b: Both) -> Result<&2, &2, String, Maybe<&2, Compared>>:
  match b:
    case Both{+file, +was, +now}:
      compare.wanted(sd, file, was, now, limit.wants(l, file, entry.path(was), entry.path(now)))

def compare.push(m: Maybe<&2, Compared>, rest: List<&2, Compared>) -> List<&2, Compared>:
  match m:
    case None{}:
      rest
    case Some{c}:
      c <> rest

def compare(+sd: Sides, +l: Limit, files: List<&2, Both>) -> Result<&2, &2, String, List<&2, Compared>>:
  match files:
    case Nil{}:
      Done{Nil{}}
    case f <> rest:
      do Result<&2, &2, String, List<&2, Compared>>:
        here : Maybe<&2, Compared> <- compare.one(sd, l, f)
        later : List<&2, Compared> <- compare(sd, l, rest)
        return compare.push(here, later)

# Each identifier once, in order.
def distinct.keep(+a: String, rest: List<&2, String>, same: Bool) -> List<&2, String>:
  match same:
    case True{}:
      rest
    case False{}:
      a <> rest

def distinct(xs: List<&2, String>) -> List<&2, String>:
  match xs:
    case +a <> +b <> rest:
      distinct.keep(a, distinct(b <> rest), String.eq(a, b))
    case other:
      other

def both.files(bs: List<&2, Both>) -> List<&2, String>:
  match bs:
    case Nil{}:
      Nil{}
    case Both{f, w, n} <> rest:
      f <> both.files(rest)

# The documents every file this comparison reads needs, fetched at once.
# Matched rather than picked: `Bool.pick` is strict, and would walk the
# history for every file in the tree to throw most of it away.
def compare.wanted_one(+fs: List<&2, Full>, +f: String, needed: Bool) -> List<&2, String>:
  match needed:
    case True{}:
      wanted(fs, f)
    case False{}:
      Nil{}

def compare.wanted_docs(+fs: List<&2, Full>, +ws: Map<&2, List<&2, String>>, +ns: Map<&2, List<&2, String>>, files: List<&2, Both>) -> List<&2, String>:
  match files:
    case Nil{}:
      Nil{}
    case Both{+f, +was, +now} <> rest:
      List.append(&2, String, compare.wanted_one(fs, f, compare.needed(ws, ns, f, was, now)), compare.wanted_docs(fs, ws, ns, rest))

# How many bytes each payload is, asked of the host and believed only where
# the digest it reports is the one asked for.
def sizes.keep(+d: String, +p: String, rest: List<&2, T.Split>, missing: Bool) -> List<&2, T.Split>:
  match missing:
    case True{}:
      rest
    case False{}:
      T.Split{d, p} <> rest

def sizes.of(+root: String, digests: List<&2, String>, located: List<&2, String>) -> List<&2, T.Split>:
  match digests located:
    case +d <> rest +p <> more:
      sizes.keep(d, p, sizes.of(root, rest, more), String.eq(p, "-"))
    case _ _:
      Nil{}

def sizes.believed(+d: String, +st: String, rest: List<&2, T.Split>, same: Bool) -> List<&2, T.Split>:
  match same:
    case True{}:
      T.Split{d, String.drop(st, 65n)} <> rest
    case False{}:
      rest

def sizes.read(found: List<&2, T.Split>, stats: List<&2, String>) -> List<&2, T.Split>:
  match found stats:
    case T.Split{+d, p} <> rest +st <> more:
      sizes.believed(d, st, sizes.read(rest, more), String.eq(T.word(st), d))
    case _ _:
      Nil{}

def size_of(ss: List<&2, T.Split>, +d: String) -> Maybe<&2, Nat>:
  match ss:
    case Nil{}:
      None{}
    case T.Split{+x, n} <> rest:
      Bool.pick(Maybe<&2, Nat>, String.eq(x, d), Nat.read(n), size_of(rest, d))

# A side the folder holds was sized when it was listed.
def side.sized(+ss: List<&2, T.Split>, s: Maybe<&2, Side>) -> Maybe<&2, Side>:
  match s:
    case Some{Side.Whole{+d, None{}}}:
      Some{Side.Whole{d, size_of(ss, d)}}
    case other:
      other

def sized(+ss: List<&2, T.Split>, cs: List<&2, Compared>) -> List<&2, Compared>:
  match cs:
    case Nil{}:
      Nil{}
    case Compared{f, t, b, a, m, g} <> rest:
      Compared{f, t, side.sized(ss, b), side.sized(ss, a), m, g} <> sized(ss, rest)

def side.payload(s: Maybe<&2, Side>) -> List<&2, String>:
  match s:
    case Some{Side.Whole{d, n}}:
      [d]
    case _:
      Nil{}

def payloads_of(cs: List<&2, Compared>) -> List<&2, String>:
  match cs:
    case Nil{}:
      Nil{}
    case Compared{f, t, b, a, m, g} <> rest:
      List.append(&2, String, side.payload(b), List.append(&2, String, side.payload(a), payloads_of(rest)))

def split_rests(xs: List<&2, T.Split>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case T.Split{a, b} <> rest:
      b <> split_rests(rest)

def diff.sized(+root: String, +paint: Bool, cs: List<&2, Compared>) -> IO(Unit):
  do IO<Unit>:
    +cs2 : List<&2, Compared> = cs
    +ds : List<&2, String> = distinct(List.sort(~String, ~(a => b => String.is_le(a, b)), payloads_of(cs2)))
    at : List<&2, String> <- Store.located(root, ds)
    +found : List<&2, T.Split> = sizes.of(root, ds, at)
    stats : List<&2, String> <- Store.stats(root, split_rests(found))
    print_pairs(paint, sized(sizes.read(found, stats), cs2))

def diff.compared(+root: String, +paint: Bool, r: Result<&2, &2, String, List<&2, Compared>>) -> IO(Unit):
  match r:
    case Fail{e}:
      die(Unit, 1, e)
    case Done{cs}:
      diff.sized(root, paint, cs)

def oldest_of(+fs: List<&2, Full>, at: Maybe<&2, String>) -> List<&2, Full>:
  match at:
    case None{}:
      Nil{}
    case Some{+id}:
      List.reverse(&2, Full, presentation(ancestry(fs, id)))

def tree.maybe(+fs: List<&2, Full>, at: Maybe<&2, String>) -> IO(Tree.Tree()):
  match at:
    case None{}:
      IO.pure(Tree.Tree(), Nil{})
    case Some{+id}:
      tree(fs, id)

def diff.revisions(+root: String, +fs: List<&2, Full>, +bs: List<&2, Bm.Bookmark>, +right: Full, +paint: Bool, only: Maybe<&2, String>, left: Maybe<&2, String>) -> IO(Unit):
  do IO<Unit>:
    +l : Maybe<&2, String> = left
    +r : String = id_of(right)
    lim : Limit <- diff.limit(fs, bs, r, only)
    before : Tree.Tree() <- tree.maybe(fs, l)
    after : Tree.Tree() <- tree(fs, r)
    +b2 : Tree.Tree() = before
    +a2 : Tree.Tree() = after
    +pairs : List<&2, Both> = both(b2, a2)
    +older : List<&2, Full> = oldest_of(fs, l)
    +newer : List<&2, Full> = oldest_of(fs, Some{r})
    +ws : Map<&2, List<&2, String>> = stating(older, Map.new(&2, List<&2, String>))
    +ns : Map<&2, List<&2, String>> = stating(newer, Map.new(&2, List<&2, String>))
    ds : List<&2, Store.Doc> <- Store.fetch(root, compare.wanted_docs(fs, ws, ns, pairs))
    +ds2 : List<&2, Store.Doc> = ds
    more : List<&2, Store.Doc> <- Store.fetch(root, kept_digests(ds2))
    diff.compared(root, paint, compare(Sides{b2, a2, older, newer, List.append(&2, Store.Doc, ds2, more), Maybe.default(&2, String, l, SNil{}), r, ws, ns}, lim, pairs))

# The folder
# ----------

# The folder the working copy is: the directory holding the store.
def repository(+root: String) -> String:
  String.take(root, Nat.sub(String.length(root), 8n))

# The position the folder is compared with, where nothing else is named:
# none in an empty store, and refused where a person has to choose.
def the_head(+fs: List<&2, Full>, +bs: List<&2, Bm.Bookmark>, heads: List<&2, String>) -> IO(Maybe<&2, String>):
  match heads:
    case Nil{}:
      IO.pure(Maybe<&2, String>, None{})
    case only <> Nil{}:
      IO.pure(Maybe<&2, String>, Some{only})
    case +several:
      die(Maybe<&2, String>, 1, "this store has " ++ Nat.show(List.length(&2, String, several)) ++ " heads, so nothing here is `the` latest; name one with --onto, or join them with `historica merge`:" ++ described(fs, bs, List.sort(~String, ~(a => b => String.is_le(a, b)), several)))

# The first-parent line back from a revision, newest first. A file's content
# at a revision is what the nearest revision on that line to state it
# stated: every revision passed on the way says nothing about the file, and
# inherits its first parent's — which holds the file, since a revision
# further along stated it.
def first_parent(+fs: List<&2, Full>, ps: List<&2, String>) -> Maybe<&2, Full>:
  match ps:
    case Nil{}:
      None{}
    case p <> rest:
      find(fs, p)

def chain.go(fuel: Nat, +fs: List<&2, Full>, at: Maybe<&2, Full>, acc: List<&2, Full>) -> List<&2, Full>:
  match fuel at:
    case 0n _:
      List.reverse(&2, Full, acc)
    case 1n+q None{}:
      List.reverse(&2, Full, acc)
    case 1n+q Some{+f}:
      chain.go(q, fs, first_parent(fs, parents_of(f)), f <> acc)

def chain(+fs: List<&2, Full>, at: Maybe<&2, String>) -> List<&2, Full>:
  match at:
    case None{}:
      Nil{}
    case Some{+id}:
      chain.go(1n+List.length(&2, Full, fs), fs, find(fs, id), Nil{})

# For each file, the nearest statement of its content on that line: the key
# (`text`, `bytes` or `edit`) and the document it names.
def origin.had(+m: Map<&2, T.Split>, +file: String, +k: String, +d: String, had: T.Split) -> Map<&2, T.Split>:
  match had:
    case T.Split{+hk, hd}:
      Bool.pick(Map<&2, T.Split>, String.is_empty(hk), Map.set(&2, T.Split, m, file, T.Split{k, d}), m)

def origin.put(+file: String, +k: String, +d: String, r: Map<&2, T.Split> & T.Split) -> Map<&2, T.Split>:
  (m, had) = r
  origin.had(m, file, k, d, had)

def origin.fact(m: Map<&2, T.Split>, +k: String, cut: Maybe<&2, T.Split>) -> Map<&2, T.Split>:
  match cut:
    case None{}:
      m
    case Some{T.Split{+file, +d}}:
      origin.put(file, k, d, Map.get(T.Split, T.Split{SNil{}, SNil{}}, m, file))

def origin.fact.if(m: Map<&2, T.Split>, +k: String, +v: String, content: Bool) -> Map<&2, T.Split>:
  match content:
    case True{}:
      origin.fact(m, k, T.split_once(v))
    case False{}:
      m

def origin.facts(facts: List<&2, Rev.Header>, m: Map<&2, T.Split>) -> Map<&2, T.Split>:
  match facts:
    case Nil{}:
      m
    case Rev.Header{+k, +v} <> rest:
      origin.facts(rest, origin.fact.if(m, k, v, stating.key(k)))

def origins.map(line: List<&2, Full>, m: Map<&2, T.Split>) -> Map<&2, T.Split>:
  match line:
    case Nil{}:
      m
    case f <> rest:
      origins.map(rest, origin.facts(facts_of(f), m))

def origin.of(+file: String, r: Map<&2, T.Split> & T.Split) -> T.Split:
  (m, had) = r
  had

def origin(+os: Map<&2, T.Split>, +file: String) -> T.Split:
  origin.of(file, Map.get(T.Split, T.Split{SNil{}, SNil{}}, os, file))

# The digest of a file of lines as its nearest statement leaves it: the
# payload a `text` names, or the `result` an `edit`'s document states in its
# header. Unknown otherwise, which is answered by replaying.
def first_blank(ls: List<&2, String>) -> Bool:
  match ls:
    case Nil{}:
      True{}
    case l <> rest:
      String.is_empty(l)

def result.go(ls: List<&2, String>, done: Bool) -> Maybe<&2, String>:
  match ls done:
    case _ True{}:
      None{}
    case Nil{} False{}:
      None{}
    case +l <> +rest False{}:
      Bool.pick(Maybe<&2, String>, String.starts_with(l, "result "), Some{String.drop(l, 7n)}, result.go(rest, first_blank(rest)))

def result.doc(doc: Maybe<&2, String>) -> Maybe<&2, String>:
  match doc:
    case None{}:
      None{}
    case Some{text}:
      result.go(String.split(text, '\n'), False{})

def stated_digest(+ds: List<&2, Store.Doc>, o: T.Split) -> Maybe<&2, String>:
  match o:
    case T.Split{"text", d}:
      Some{d}
    case T.Split{"edit", +d}:
      result.doc(doc_by_id(ds, d))
    case _:
      None{}

# One path, as the position and the folder hold it.
type Here is Data:
  Here{path: String, entry: Maybe<&2, Tree.Entry>, found: Maybe<&2, Folder.Found>}

def here.cmp(xs: List<&2, Tree.Entry>, ys: List<&2, Folder.Found>) -> Cmp:
  match xs ys:
    case x <> xr y <> yr:
      String.order(Tree.entry_path(x), Folder.found.path(y))
    case Nil{} _:
      GT{}
    case _ Nil{}:
      LT{}

def here.go(fuel: Nat, xs: List<&2, Tree.Entry>, ys: List<&2, Folder.Found>, c: Cmp) -> List<&2, Here>:
  match fuel xs ys c:
    case 0n _ _ _:
      Nil{}
    case _ Nil{} Nil{} _:
      Nil{}
    case 1n+f +x <> +xr +y <> +yr EQ{}:
      Here{Tree.entry_path(x), Some{x}, Some{y}} <> here.go(f, xr, yr, here.cmp(xr, yr))
    case 1n+f +x <> +xr +ys2 LT{}:
      Here{Tree.entry_path(x), Some{x}, None{}} <> here.go(f, xr, ys2, here.cmp(xr, ys2))
    case 1n+f +xs2 +y <> +yr _:
      Here{Folder.found.path(y), None{}, Some{y}} <> here.go(f, xs2, yr, here.cmp(xs2, yr))
    case 1n+f +x <> +xr Nil{} _:
      Here{Tree.entry_path(x), Some{x}, None{}} <> here.go(f, xr, Nil{}, here.cmp(xr, Nil{}))

def here.wanted(+l: Limit, h: Here) -> Bool:
  match h:
    case Here{+path, entry, found}:
      limit.wants(l, Maybe.default(&2, String, Maybe.map(&2, Tree.Entry, String, e => Tree.entry_file(e), entry), SNil{}), Some{path}, Some{path})

def heres.limited(+l: Limit, hs: List<&2, Here>) -> List<&2, Here>:
  match hs:
    case Nil{}:
      Nil{}
    case +h <> rest:
      +later = heres.limited(l, rest)
      Bool.pick(List<&2, Here>, here.wanted(l, h), h <> later, later)

# Every path either side holds, in path order, and only the one a limit
# names where there is one.
def heres(t: Tree.Tree(), found: List<&2, Folder.Found>, +l: Limit) -> List<&2, Here>:
  +xs = List.sort(~Tree.Entry, ~(a => b => by_path(a, b)), t)
  +ys = found
  heres.limited(l, here.go(1n+Nat.add(List.length(&2, Tree.Entry, xs), List.length(&2, Folder.Found, ys)), xs, ys, here.cmp(xs, ys)))

def here.lines(h: Here) -> Bool:
  match h:
    case Here{p, Some{Tree.Entry{f, q, Tree.Lines{}, y, g, m}}, found}:
      True{}
    case _:
      False{}

def here.regular(h: Here) -> Bool:
  match h:
    case Here{p, e, Some{Folder.Found.File{q, r, n}}}:
      True{}
    case _:
      False{}

def here.file(h: Here) -> String:
  match h:
    case Here{p, Some{e}, found}:
      Tree.entry_file(e)
    case Here{p, None{}, found}:
      SNil{}

def here.path(h: Here) -> String:
  match h:
    case Here{p, e, found}:
      p

# The `edit` documents whose results say whether a file of lines changed.
def edit_of.split(o: T.Split) -> List<&2, String>:
  match o:
    case T.Split{"edit", d}:
      [d]
    case _:
      Nil{}

def edit_of(+os: Map<&2, T.Split>, +h: Here, needs: Bool) -> List<&2, String>:
  match needs:
    case False{}:
      Nil{}
    case True{}:
      edit_of.split(origin(os, here.file(h)))

def edits_of(+os: Map<&2, T.Split>, hs: List<&2, Here>) -> List<&2, String>:
  match hs:
    case Nil{}:
      Nil{}
    case +h <> rest:
      List.append(&2, String, edit_of(os, h, Bool.and(here.lines(h), here.regular(h))), edits_of(os, rest))

def regular_paths(hs: List<&2, Here>) -> List<&2, String>:
  match hs:
    case Nil{}:
      Nil{}
    case +h <> rest:
      Rev.keep(here.regular(h), here.path(h), regular_paths(rest))

def stats.map(paths: List<&2, String>, stats: List<&2, String>, m: Map<&2, String>) -> Map<&2, String>:
  match paths stats:
    case p <> rest s <> more:
      stats.map(rest, more, Map.set(&2, String, m, p, s))
    case _ _:
      m

def stat_of(+file: String, r: Map<&2, String> & String) -> String:
  (m, s) = r
  s

# What a path needs before it can be compared: its folder digest, whether
# the position's content has to be replayed, and whether the folder's file
# has to be read.
type Planned is Data:
  Planned{here: Here, digest: String, replay: Bool, read: Bool}

def plan.of(+h: Here, +digest: String, +lines: Bool, +regular: Bool, +same: Bool) -> Planned:
  Planned{h, digest, Bool.and(lines, Bool.not(Bool.and(regular, same))), Bool.and(regular, Bool.or(String.is_empty(here.file(h)), Bool.and(lines, Bool.not(same))))}

def plan(+dg: Map<&2, String>, +os: Map<&2, T.Split>, +eds: List<&2, Store.Doc>, h: Here) -> Planned:
  +h2 = h
  +digest = T.word(stat_of(here.path(h2), Map.get(String, SNil{}, dg, here.path(h2))))
  plan.of(h2, digest, here.lines(h2), here.regular(h2),
    maybe_eq(stated_digest(eds, origin(os, here.file(h2))), Some{digest}))

def plans(+dg: Map<&2, String>, +os: Map<&2, T.Split>, +eds: List<&2, Store.Doc>, hs: List<&2, Here>) -> List<&2, Planned>:
  match hs:
    case Nil{}:
      Nil{}
    case h <> rest:
      plan(dg, os, eds, h) <> plans(dg, os, eds, rest)

def planned.replayed(ps: List<&2, Planned>) -> List<&2, String>:
  match ps:
    case Nil{}:
      Nil{}
    case Planned{+h, d, +replay, r} <> rest:
      Rev.keep(replay, here.file(h), planned.replayed(rest))

def planned.read(ps: List<&2, Planned>) -> List<&2, String>:
  match ps:
    case Nil{}:
      Nil{}
    case Planned{+h, d, p, +read} <> rest:
      Rev.keep(read, here.path(h), planned.read(rest))

def wanted_all(+fs: List<&2, Full>, files: List<&2, String>) -> List<&2, String>:
  match files:
    case Nil{}:
      Nil{}
    case f <> rest:
      List.append(&2, String, wanted(fs, f), wanted_all(fs, rest))

# The folder's files that have to be read, by path.
def read_all(+repo: String, paths: List<&2, String>, m: Map<&2, List<&2, U32>>) -> IO(Map<&2, List<&2, U32>>):
  match paths:
    case Nil{}:
      IO.pure(Map<&2, List<&2, U32>>, m)
    case +p <> rest:
      do IO<Map<&2, List<&2, U32>>>:
        bs : List<&2, U32> <- Utf8.read_file(repo ++ "/" ++ p)
        read_all(repo, rest, Map.set(&2, List<&2, U32>, m, p, bs))

def bytes_of(+path: String, r: Map<&2, List<&2, U32>> & List<&2, U32>) -> List<&2, U32>:
  (m, bs) = r
  bs

# What the position holds of a path: nothing for a link, whose target is
# said instead; the payload of a file of bytes; the lines, where they were
# replayed, and otherwise a stand-in the folder's side shares.
def wc.before(e: Maybe<&2, Tree.Entry>, +content: Result<&2, &2, String, List<&2, Ops.Item>>) -> Result<&2, &2, String, Maybe<&2, Side>>:
  match e:
    case None{}:
      Done{None{}}
    case Some{Tree.Entry{f, p, Tree.Link{}, y, g, m}}:
      Done{None{}}
    case Some{Tree.Entry{f, p, Tree.Whole{}, y, g, m}}:
      Done{Some{Side.Whole{Maybe.default(&2, String, y, SNil{}), None{}}}}
    case Some{Tree.Entry{f, p, Tree.Lines{}, y, g, m}}:
      Result.map(&2, &2, String, List<&2, Ops.Item>, Maybe<&2, Side>, items => Some{Side.Lines{items}}, content)

# A file recorded as lines has to be text still, and a file nobody has
# recorded is whatever the recorder would call it (decision 0017).
def wc.lines(+path: String, +bs: List<&2, U32>, text: Bool) -> Result<&2, &2, String, Maybe<&2, Side>>:
  match text:
    case True{}:
      Done{Some{Side.Lines{Ops.from_text(Utf8.decode(bs))}}}
    case False{}:
      Fail{"`" ++ path ++ "` was recorded as lines and is no longer UTF-8 text; a file's kind is fixed when it is added, so this is a `drop` and an `add` rather than an edit"}

def wc.sniffed(+bs: List<&2, U32>, +digest: String, +size: Nat, text: Bool) -> Result<&2, &2, String, Maybe<&2, Side>>:
  match text:
    case True{}:
      Done{Some{Side.Lines{Ops.from_text(Utf8.decode(bs))}}}
    case False{}:
      Done{Some{Side.Whole{digest, Some{size}}}}

def wc.regular(+path: String, e: Maybe<&2, Tree.Entry>, +bs: List<&2, U32>, +digest: String, +size: Nat, read: Bool) -> Result<&2, &2, String, Maybe<&2, Side>>:
  match e:
    case None{}:
      wc.sniffed(bs, digest, size, Folder.is_text(bs))
    case Some{Tree.Entry{f, p, Tree.Lines{}, y, g, m}}:
      match read:
        case True{}:
          wc.lines(path, bs, Folder.is_utf8(bs))
        case False{}:
          Done{Some{Side.Lines{Nil{}}}}
    case Some{other}:
      Done{Some{Side.Whole{digest, Some{size}}}}

# What the folder holds of a path: nothing where it holds no file or a link,
# and otherwise the file.
def wc.after(+path: String, e: Maybe<&2, Tree.Entry>, found: Maybe<&2, Folder.Found>, +bs: List<&2, U32>, +digest: String, read: Bool) -> Result<&2, &2, String, Maybe<&2, Side>>:
  match found:
    case Some{Folder.Found.File{p, r, size}}:
      wc.regular(path, e, bs, digest, size, read)
    case _:
      Done{None{}}

def wc.mode(e: Maybe<&2, Tree.Entry>, found: Maybe<&2, Folder.Found>) -> Maybe<&2, T.Split>:
  match e found:
    case Some{Tree.Entry{f, p, Tree.Link{}, y, g, m}} _:
      None{}
    case Some{Tree.Entry{f, p, k, y, g, +m}} Some{Folder.Found.File{q, +runs, n}}:
      +now = Bool.pick(Tree.Mode, runs, Tree.Executable{}, Tree.Plain{})
      Bool.pick(Maybe<&2, T.Split>, Tree.mode_eq(m, now), None{}, Some{T.Split{Tree.mode_show(m), Tree.mode_show(now)}})
    case _ _:
      None{}

def wc.target(found: Maybe<&2, Folder.Found>) -> Maybe<&2, String>:
  match found:
    case Some{Folder.Found.Link{p, target}}:
      Some{target}
    case _:
      None{}

def wc.content(+older: List<&2, Full>, +ds: List<&2, Store.Doc>, +left: String, +file: String, replay: Bool) -> Result<&2, &2, String, List<&2, Ops.Item>>:
  match replay:
    case True{}:
      content.in(older, ds, left, file)
    case False{}:
      Done{Nil{}}

# One path compared: the folder has no identifiers, so a file that moved
# there is a loss and an arrival, as `status` says it is.
def wc.compare.one(+t: Tree.Tree(), +older: List<&2, Full>, +ds: List<&2, Store.Doc>, +left: String, +reads: Map<&2, List<&2, U32>>, p: Planned) -> Result<&2, &2, String, Maybe<&2, Compared>>:
  match p:
    case Planned{Here{+path, +e, +found}, +digest, replay, read}:
      +file = Maybe.default(&2, String, Maybe.map(&2, Tree.Entry, String, x => Tree.entry_file(x), e), SNil{})
      do Result<&2, &2, String, Maybe<&2, Compared>>:
        b : Maybe<&2, Side> <- wc.before(e, wc.content(older, ds, left, file, replay))
        a : Maybe<&2, Side> <- wc.after(path, e, found, bytes_of(path, Map.get(List<&2, U32>, Nil{}, reads, path)), digest, read)
        return compare.built(Compared{entry.path(e), Maybe.map(&2, Folder.Found, String, x => Folder.found.path(x), found), b, a, wc.mode(e, found), retargeting(shown(t, e), wc.target(found))})

def wc.compare(+t: Tree.Tree(), +older: List<&2, Full>, +ds: List<&2, Store.Doc>, +left: String, +reads: Map<&2, List<&2, U32>>, ps: List<&2, Planned>) -> Result<&2, &2, String, List<&2, Compared>>:
  match ps:
    case Nil{}:
      Done{Nil{}}
    case p <> rest:
      do Result<&2, &2, String, List<&2, Compared>>:
        here : Maybe<&2, Compared> <- wc.compare.one(t, older, ds, left, reads, p)
        later : List<&2, Compared> <- wc.compare(t, older, ds, left, reads, rest)
        return compare.push(here, later)

def wc.left(+fs: List<&2, Full>, +bs: List<&2, Bm.Bookmark>, onto: Maybe<&2, String>) -> IO(Maybe<&2, String>):
  match onto:
    case Some{t}:
      do IO<Maybe<&2, String>>:
        f : Full <- resolved(fs, bs, t)
        return Some{id_of(f)}
    case None{}:
      the_head(fs, bs, current_heads(history(fs)))

def wc.limit.file(+fs: List<&2, Full>, +bs: List<&2, Bm.Bookmark>, +sp: String, left: Maybe<&2, String>) -> IO(Limit):
  match left:
    case None{}:
      die(Limit, 1, "there is no revision here to name a file against")
    case Some{id}:
      diff.limit.file(fs, bs, id, sp)

def wc.limit(+fs: List<&2, Full>, +bs: List<&2, Bm.Bookmark>, +left: Maybe<&2, String>, only: Maybe<&2, String>) -> IO(Limit):
  match only:
    case None{}:
      IO.pure(Limit, Limit.None{})
    case Some{+sp}:
      Bool.pick(IO(Limit), String.starts_with(sp, "file:"), wc.limit.file(fs, bs, sp, left), IO.pure(Limit, Limit.Path{Maybe.default(&2, String, T.strip_prefix(sp, "path:"), sp)}))

# `diff` with no target: the folder against the position — the head, or
# what `--onto` names. A file of lines is replayed only where the folder's
# digest is not the one its nearest statement leaves, and the folder's file
# read only where the two differ or the position does not hold it.
def diff.folder(+root: String, +fs: List<&2, Full>, +bs: List<&2, Bm.Bookmark>, +onto: Maybe<&2, String>, +paint: Bool, only: Maybe<&2, String>) -> IO(Unit):
  do IO<Unit>:
    rules : List<&2, Folder.Scope> <- Folder.rules(root)
    left : Maybe<&2, String> <- wc.left(fs, bs, onto)
    +l : Maybe<&2, String> = left
    lim : Limit <- wc.limit(fs, bs, l, only)
    +repo : String = repository(root)
    found : List<&2, Folder.Found> <- Folder.walk(repo, rules)
    t : Tree.Tree() <- tree.maybe(fs, l)
    +t2 : Tree.Tree() = t
    +hs : List<&2, Here> = heres(t2, found, lim)
    +os : Map<&2, T.Split> = origins.map(chain(fs, l), Map.new(&2, T.Split))
    eds : List<&2, Store.Doc> <- Store.fetch(root, distinct(List.sort(~String, ~(a => b => String.is_le(a, b)), edits_of(os, hs))))
    +paths : List<&2, String> = regular_paths(hs)
    stats : List<&2, String> <- Store.stats(repo, paths)
    +ps : List<&2, Planned> = plans(stats.map(paths, stats, Map.new(&2, String)), os, eds, hs)
    ds : List<&2, Store.Doc> <- Store.fetch(root, wanted_all(fs, planned.replayed(ps)))
    +ds2 : List<&2, Store.Doc> = ds
    more : List<&2, Store.Doc> <- Store.fetch(root, kept_digests(ds2))
    reads : Map<&2, List<&2, U32>> <- read_all(repo, planned.read(ps), Map.new(&2, List<&2, U32>))
    diff.compared(root, paint, wc.compare(t2, oldest_of(fs, l), List.append(&2, Store.Doc, ds2, more), Maybe.default(&2, String, l, SNil{}), reads, ps))

def diff.named(+root: String, +fs: List<&2, Full>, +bs: List<&2, Bm.Bookmark>, +onto: Maybe<&2, String>, +paint: Bool, named: Maybe<&2, String>, only: Maybe<&2, String>) -> IO(Unit):
  match named:
    case None{}:
      diff.folder(root, fs, bs, onto, paint, only)
    case Some{t}:
      do IO<Unit>:
        f : Full <- resolved(fs, bs, t)
        +f2 : Full = f
        left : Maybe<&2, String> <- diff.left(fs, bs, f2, onto)
        diff.revisions(root, fs, bs, f2, paint, only, left)

def diff.split(+root: String, +fs: List<&2, Full>, +bs: List<&2, Bm.Bookmark>, +onto: Maybe<&2, String>, +paint: Bool, rest: List<&2, String>) -> IO(Unit):
  match rest:
    case Nil{}:
      diff.named(root, fs, bs, onto, paint, None{}, None{})
    case +first <> Nil{}:
      Bool.pick(IO(Unit), could_be_target(bs, first), diff.named(root, fs, bs, onto, paint, Some{first}, None{}), diff.named(root, fs, bs, onto, paint, None{}, Some{first}))
    case first <> second <> Nil{}:
      diff.named(root, fs, bs, onto, paint, Some{first}, Some{second})
    case first <> second <> third <> more:
      die(Unit, 2, "`diff` takes a target and a path, and `" ++ third ++ "` is a third argument")

# `auto` colours a terminal and nothing else, and this port cannot ask
# whether it is writing to one, so it colours only where told to.
def diff.of(+root: String, +fs: List<&2, Full>, +bs: List<&2, Bm.Bookmark>, a: DiffAsked) -> IO(Unit):
  match a:
    case DiffAsked{onto, color, rest}:
      diff.split(root, fs, bs, onto, String.eq(color, "always"), List.reverse(&2, String, rest))

def diff(+args: List<&2, String>) -> IO(Unit):
  do IO<Unit>:
    root : String <- Store.root()
    +r : String = root
    rs : List<&2, Store.Doc> <- Store.revisions(r)
    bs : List<&2, Bm.Bookmark> <- bookmarks(r)
    a : DiffAsked <- dasked.io(dasked.go(1n+List.length(&2, String, args), DParse{args, Done{DiffAsked{None{}, "auto", Nil{}}}}))
    diff.of(r, fulls(r, rs), bs, a)

# blame
# -----

# One line and the revision that wrote it: `None` for a line only the folder
# holds.
type Row is Data:
  Row{by: Maybe<&2, String>, item: Ops.Item}

# A line's origin through an edit: what stood keeps its author, what arrived
# is this revision's, and what left is gone.
def overlay(ls: List<&2, Laid>, origins: List<&2, Row>, +by: Maybe<&2, String>) -> List<&2, Row>:
  match ls origins:
    case Laid{"+", it} <> rest _:
      Row{by, it} <> overlay(rest, origins, by)
    case Laid{"-", it} <> rest o <> more:
      overlay(rest, more, by)
    case Laid{s, it} <> rest Row{b, i} <> more:
      Row{b, it} <> overlay(rest, more, by)
    case _ _:
      Nil{}

def rows.items(rs: List<&2, Row>) -> List<&2, Ops.Item>:
  match rs:
    case Nil{}:
      Nil{}
    case Row{b, it} <> rest:
      it <> rows.items(rest)

def rows.by(+by: Maybe<&2, String>, items: List<&2, Ops.Item>) -> List<&2, Row>:
  match items:
    case Nil{}:
      Nil{}
    case it <> rest:
      Row{by, it} <> rows.by(by, rest)

# The revision whose document minted the items a `keep` names: the one that
# stated that document for some file.
def minter.says(+d: String, facts: List<&2, Rev.Header>) -> Bool:
  match facts:
    case Nil{}:
      False{}
    case Rev.Header{k, +v} <> rest:
      Bool.or(String.ends_with(v, " " ++ d), minter.says(d, rest))

def minter(fs: List<&2, Full>, +d: String) -> Maybe<&2, String>:
  match fs:
    case Nil{}:
      None{}
    case +f <> rest:
      Bool.pick(Maybe<&2, String>, minter.says(d, facts_of(f)), Some{id_of(f)}, minter(rest, d))

def origins.piece(+oldest: List<&2, Full>, +ds: List<&2, Store.Doc>, +id: String, p: Res.Piece) -> List<&2, Row>:
  match p:
    case Res.Piece.Keep{+d, first, count}:
      rows.by(minter(oldest, d), List.take(&2, Ops.Item, List.drop(&2, Ops.Item, minted(Maybe.default(&2, String, doc_by_id(ds, d), SNil{})), first), count))
    case Res.Piece.Insert{items}:
      rows.by(Some{id}, items)

def origins.pieces(+oldest: List<&2, Full>, +ds: List<&2, Store.Doc>, +id: String, ps: List<&2, Res.Piece>) -> List<&2, Row>:
  match ps:
    case Nil{}:
      Nil{}
    case p <> rest:
      List.append(&2, Row, origins.piece(oldest, ds, id, p), origins.pieces(oldest, ds, id, rest))

def origins.resolved(+oldest: List<&2, Full>, +ds: List<&2, Store.Doc>, +id: String, parsed: Result<&2, &2, String, Res.Doc>) -> Maybe<&2, List<&2, Row>>:
  match parsed:
    case Fail{e}:
      None{}
    case Done{Res.Doc{f, r, ps}}:
      Some{origins.pieces(oldest, ds, id, ps)}

def origins.edited(+id: String, before: Maybe<&2, List<&2, Row>>, parsed: Result<&2, &2, String, Ops.Doc>) -> Maybe<&2, List<&2, Row>>:
  match before parsed:
    case Some{+rs} Done{doc}:
      Some{overlay(laid(rows.items(rs), doc), rs, Some{id})}
    case _ _:
      None{}

def origins.text(+oldest: List<&2, Full>, +ds: List<&2, Store.Doc>, +id: String, before: Maybe<&2, List<&2, Row>>, +text: String, resolution: Bool) -> Maybe<&2, List<&2, Row>>:
  match resolution:
    case True{}:
      origins.resolved(oldest, ds, id, Res.parse(text))
    case False{}:
      origins.edited(id, before, Ops.parse(text))

def origins.doc(+oldest: List<&2, Full>, +ds: List<&2, Store.Doc>, +id: String, before: Maybe<&2, List<&2, Row>>, doc: Maybe<&2, String>) -> Maybe<&2, List<&2, Row>>:
  match doc:
    case None{}:
      None{}
    case Some{+text}:
      origins.text(oldest, ds, id, before, text, Res.is_resolution(text))

def origins.said(+oldest: List<&2, Full>, +ds: List<&2, Store.Doc>, +id: String, inherited: Maybe<&2, List<&2, Row>>, s: Said) -> Maybe<&2, List<&2, Row>>:
  match s:
    case Whole{+d}:
      Maybe.map(&2, String, List<&2, Row>, t => rows.by(Some{id}, Ops.from_text(t)), doc_by_id(ds, d))
    case Edited{+d}:
      origins.doc(oldest, ds, id, inherited, doc_by_id(ds, d))
    case Nothing{}:
      inherited

# Who wrote each line of the file at every revision that holds it, walked
# as `content` walks, oldest first; `content` is what says whether the file
# is readable at all, and this only who wrote what it reads.
type Origins is Data:
  Origins{rows: List<&2, Row>, id: String}

def origins_of(os: List<&2, Origins>, +id: String) -> Maybe<&2, List<&2, Row>>:
  match os:
    case Nil{}:
      None{}
    case Origins{rs, +i} <> rest:
      Bool.pick(Maybe<&2, List<&2, Row>>, String.eq(i, id), Some{rs}, origins_of(rest, id))

def origins.parents(+os: List<&2, Origins>, ps: List<&2, String>) -> Maybe<&2, List<&2, Row>>:
  match ps:
    case Nil{}:
      None{}
    case p <> rest:
      Maybe.or(&2, List<&2, Row>, origins_of(os, p), origins.parents(os, rest))

def origins.push(+id: String, o: Maybe<&2, List<&2, Row>>, os: List<&2, Origins>) -> List<&2, Origins>:
  match o:
    case None{}:
      os
    case Some{rs}:
      Origins{rs, id} <> os

def origins.go(+all: List<&2, Full>, oldest_first: List<&2, Full>, +ds: List<&2, Store.Doc>, +file: String, +os: List<&2, Origins>) -> List<&2, Origins>:
  match oldest_first:
    case Nil{}:
      os
    case Full{+id, change, parents, supersedes, author, when, revised_by, revised, facts, message} <> rest:
      origins.go(all, rest, ds, file, origins.push(id, origins.said(all, ds, id, origins.parents(os, parents), said(facts, file)), os))

def origins(+oldest: List<&2, Full>, +ds: List<&2, Store.Doc>, +id: String, +file: String) -> List<&2, Row>:
  Maybe.default(&2, List<&2, Row>, origins_of(origins.go(oldest, oldest, ds, file, Nil{}), id), Nil{})

# Printing
# --------

# The name in an author line, without the address: what comes before the
# first ` <`, trimmed.
def author_name.at(s: String, +i: Nat, space: Bool) -> Maybe<&2, Nat>:
  match s:
    case SNil{}:
      None{}
    case SCon{+c, rest}:
      Bool.pick(Maybe<&2, Nat>, Bool.and(space, Char.is_eq(c, '<')), Some{Nat.sub(i, 1n)}, author_name.at(rest, 1n+i, Char.is_eq(c, ' ')))

def author_name.of(+a: String, at: Maybe<&2, Nat>) -> String:
  match at:
    case None{}:
      String.trim(a)
    case Some{n}:
      String.trim(String.take(a, n))

def author_name(+a: String) -> String:
  author_name.of(a, author_name.at(a, 0n, False{}))

type Columns is Data:
  Columns{change: String, who: String, day: String}

def columns.of(+all_changes: List<&2, String>, +by: String, found: Maybe<&2, Full>) -> Columns:
  match found:
    case None{}:
      Columns{String.take(by, 8n), SNil{}, SNil{}}
    case Some{+f}:
      Columns{abbreviate(change_of(f), all_changes), author_name(author_of(f)), String.take(when_of(f), 10n)}

def columns(+fs: List<&2, Full>, +all_changes: List<&2, String>, by: Maybe<&2, String>) -> Columns:
  match by:
    case None{}:
      Columns{"-", "(the folder)", "-"}
    case Some{+b}:
      columns.of(all_changes, b, find(fs, b))

type Shown is Data:
  Shown{n: Nat, cols: Columns, item: Ops.Item}

def shown.rows(+fs: List<&2, Full>, +all_changes: List<&2, String>, rs: List<&2, Row>, +n: Nat) -> List<&2, Shown>:
  match rs:
    case Nil{}:
      Nil{}
    case Row{by, it} <> rest:
      Shown{n, columns(fs, all_changes, by), it} <> shown.rows(fs, all_changes, rest, 1n+n)

def widest.col(ss: List<&2, Shown>, +which: Nat) -> Nat:
  match ss:
    case Nil{}:
      0n
    case Shown{n, Columns{c, w, d}, it} <> rest:
      Nat.max(String.length(Bool.pick(String, Nat.is_eq(which, 0n), c, Bool.pick(String, Nat.is_eq(which, 1n), w, d))), widest.col(rest, which))

def last_number(ss: List<&2, Shown>) -> Nat:
  match ss:
    case Nil{}:
      0n
    case Shown{n, c, it} <> Nil{}:
      String.length(Nat.show(n))
    case s <> rest:
      last_number(rest)

def pad_left(+s: String, width: Nat) -> String:
  String.repeat(" ", Nat.sub(width, String.length(s))) ++ s

def blame.lines(ss: List<&2, Shown>, +cw: Nat, +ww: Nat, +dw: Nat, +nw: Nat) -> IO(Unit):
  match ss:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case Shown{n, Columns{c, w, d}, Ops.Item{t, +term, forgot}} <> rest:
      do IO<Unit>:
        IO.print(pad_left(c, cw) ++ "  " ++ pad(w, ww) ++ "  " ++ pad(d, dw) ++ "  " ++ pad_left(Nat.show(n), nw) ++ "  " ++ Ops.shown(Ops.Item{t, term, forgot}))
        Bool.pick(IO(Unit), term, IO.pure(Unit, Unit{}), IO.print("\\ no newline at end of file"))
        blame.lines(rest, cw, ww, dw, nw)

def blame.print(+ss: List<&2, Shown>) -> IO(Unit):
  blame.lines(ss, widest.col(ss, 0n), widest.col(ss, 1n), widest.col(ss, 2n), last_number(ss))

# The span asked for, counting from one: `<first>..<last>`, or one line.
type Wanted is Data:
  Wanted{first: Nat, last: Nat}

def lines.nat(+s: String) -> Maybe<&2, Nat>:
  Bool.pick(Maybe<&2, Nat>, Bool.and(Bool.not(String.is_empty(s)), all_chars(~(c => Char.is_digit(c)), s)), Nat.read(s), None{})

def lines.one(+s: String) -> Maybe<&2, Nat>:
  lines.nat(Maybe.default(&2, String, T.strip_prefix(s, "+"), s))

def lines.pair(a: Maybe<&2, Nat>, b: Maybe<&2, Nat>) -> Result<&2, &2, String, Wanted>:
  match a b:
    case Some{x} Some{y}:
      Done{Wanted{x, y}}
    case _ _:
      Fail{"a span is `<first>..<last>`, or one line number"}

def lines.single(a: Maybe<&2, Nat>) -> Result<&2, &2, String, Wanted>:
  match a:
    case Some{+x}:
      Done{Wanted{x, x}}
    case None{}:
      Fail{"a span is `<first>..<last>`, or one line number"}

def lines.cut(+s: String, cut: Maybe<&2, T.Split>) -> Result<&2, &2, String, Wanted>:
  match cut:
    case Some{T.Split{+a, +b}}:
      lines.pair(lines.one(a), lines.one(b))
    case None{}:
      lines.single(lines.one(s))

def lines.checked(r: Result<&2, &2, String, Wanted>) -> Result<&2, &2, String, Wanted>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{Wanted{+a, +b}}:
      Bool.pick(Result<&2, &2, String, Wanted>, Bool.or(Nat.is_eq(a, 0n), Nat.is_gt(a, b)), Fail{"a span runs from a first line to a last one, counting from 1"}, Done{Wanted{a, b}})

def lines.of(+s: String) -> Result<&2, &2, String, Wanted>:
  lines.checked(lines.cut(s, range.cut(s, SNil{})))

# Arguments
# ---------

type BlameAsked is Data:
  BlameAsked{lines: Maybe<&2, String>, rest: List<&2, String>}

type BParse is Data:
  BParse{args: List<&2, String>, asked: Result<&2, &2, String, BlameAsked>}

def basked.lines(a: BlameAsked, v: String) -> BlameAsked:
  match a:
    case BlameAsked{l, r}:
      BlameAsked{Some{v}, r}

def basked.push(a: BlameAsked, w: String) -> BlameAsked:
  match a:
    case BlameAsked{l, r}:
      BlameAsked{l, w <> r}

def basked.word(a: BlameAsked, +w: String, flag: Bool) -> Result<&2, &2, String, BlameAsked>:
  match flag:
    case True{}:
      Fail{"`" ++ w ++ "` is not an argument `blame` takes"}
    case False{}:
      Done{basked.push(a, w)}

def basked.step(args: List<&2, String>, a: BlameAsked) -> BParse:
  match args:
    case "--lines" <> v <> rest:
      BParse{rest, Done{basked.lines(a, v)}}
    case "--lines" <> Nil{}:
      BParse{Nil{}, Fail{"`--lines` wants a span, as `<first>..<last>`"}}
    case +w <> rest:
      BParse{rest, basked.word(a, w, String.starts_with(w, "-"))}
    case Nil{}:
      BParse{Nil{}, Done{a}}

def basked.go(fuel: Nat, p: BParse) -> Result<&2, &2, String, BlameAsked>:
  match fuel p:
    case _ BParse{rest, Fail{e}}:
      Fail{e}
    case _ BParse{Nil{}, r}:
      r
    case 0n BParse{rest, r}:
      r
    case 1n+f BParse{args, Done{a}}:
      basked.go(f, basked.step(args, a))

def basked.io(r: Result<&2, &2, String, BlameAsked>) -> IO(BlameAsked):
  match r:
    case Fail{e}:
      die(BlameAsked, 2, e)
    case Done{a}:
      IO.pure(BlameAsked, a)

def usage.io(-A: Data, r: Result<&2, &2, String, A>) -> IO(A):
  match r:
    case Fail{e}:
      die(A, 2, e)
    case Done{a}:
      IO.pure(A, a)

# The rows asked for, or where a span begins past the end.
def blame.limited(+fs: List<&2, Full>, +all_changes: List<&2, String>, +rs: List<&2, Row>, asked_span: Maybe<&2, Wanted>) -> IO(Unit):
  match asked_span:
    case None{}:
      blame.print(shown.rows(fs, all_changes, rs, 1n))
    case Some{Wanted{+first, last}}:
      +len = List.length(&2, Row, rs)
      Bool.pick(IO(Unit), Nat.is_gt(first, len), die(Unit, 1, "that span begins past the end: the file has " ++ Nat.show(len) ++ " lines"),
        blame.print(shown.rows(fs, all_changes, List.take(&2, Row, List.drop(&2, Row, rs, Nat.sub(first, 1n)), Nat.sub(Nat.min(last, len), Nat.sub(first, 1n))), first)))

# A file of bytes has no lines, and a link holds where it points.
def lines_only(+path: String, k: Maybe<&2, Tree.FileKind>) -> IO(Unit):
  match k:
    case Some{Tree.Whole{}}:
      die(Unit, 1, path ++ " is a file of bytes: decision 0017 gives it no lines, and there is nothing to attribute line by line")
    case Some{Tree.Link{}}:
      die(Unit, 1, path ++ " is a link: what it holds is where it points, which the revision that stated it is the whole of the answer for")
    case _:
      IO.pure(Unit, Unit{})

def blame.readable(r: Result<&2, &2, String, List<&2, Ops.Item>>) -> IO(List<&2, Ops.Item>):
  match r:
    case Fail{e}:
      die(List<&2, Ops.Item>, 1, e)
    case Done{items}:
      IO.pure(List<&2, Ops.Item>, items)

# Who wrote each line of the file as a revision left it.
def blame.recorded(+root: String, +fs: List<&2, Full>, +bs: List<&2, Bm.Bookmark>, +target: String, +spelling: String, asked_span: Maybe<&2, Wanted>) -> IO(Unit):
  do IO<Unit>:
    f : Full <- resolved(fs, bs, target)
    +id : String = id_of(f)
    t : Tree.Tree() <- tree(fs, id)
    +t2 : Tree.Tree() = t
    file : String <- file_in(id, bs, spelling, t2)
    +file2 : String = file
    lines_only(Maybe.default(&2, String, Tree.path(t2, file2), spelling), Tree.kind(t2, file2))
    ds : List<&2, Store.Doc> <- Store.fetch(root, wanted(fs, file2))
    +ds2 : List<&2, Store.Doc> = ds
    more : List<&2, Store.Doc> <- Store.fetch(root, kept_digests(ds2))
    +all : List<&2, Store.Doc> = List.append(&2, Store.Doc, ds2, more)
    +oldest : List<&2, Full> = List.reverse(&2, Full, presentation(ancestry(fs, id)))
    items : List<&2, Ops.Item> <- blame.readable(content.in(oldest, all, id, file2))
    blame.limited(fs, changes(fs), origins(oldest, all, id, file2), asked_span)

def blame.wanted(lines: Maybe<&2, String>) -> IO(Maybe<&2, Wanted>):
  match lines:
    case None{}:
      IO.pure(Maybe<&2, Wanted>, None{})
    case Some{+l}:
      do IO<Maybe<&2, Wanted>>:
        w : Wanted <- usage.io(Wanted, lines.of(l))
        return Some{w}

# One file as the folder holds it: which file the argument names, and where
# the folder keeps it. A `file:` spelling names an identifier, which the
# folder does not have, so it is resolved against the position and the path
# comes back from the tree.
type Held is Data:
  Held{file: Maybe<&2, String>, path: String}

def wcf.at(+f: String, p: Maybe<&2, String>) -> IO(Held):
  match p:
    case None{}:
      die(Held, 1, "the position holds no path for that file")
    case Some{path}:
      IO.pure(Held, Held{Some{f}, path})

def wcf.file(+bs: List<&2, Bm.Bookmark>, +t: Tree.Tree(), +sp: String, left: Maybe<&2, String>) -> IO(Held):
  match left:
    case None{}:
      die(Held, 1, "there are no revisions here to name a file against")
    case Some{+id}:
      do IO<Held>:
        f : String <- file_in(id, bs, sp, t)
        +f2 : String = f
        wcf.at(f2, Tree.path(t, f2))

def wcf.several(+bs: List<&2, Bm.Bookmark>, +t: Tree.Tree(), +path: String, left: Maybe<&2, String>) -> IO(Held):
  match left:
    case None{}:
      die(Held, 1, "this store holds no position")
    case Some{+id}:
      do IO<Held>:
        f : String <- file_in(id, bs, path, t)
        return Held{Some{f}, path}

def wcf.path(+bs: List<&2, Bm.Bookmark>, +t: Tree.Tree(), +path: String, +left: Maybe<&2, String>, at: List<&2, String>) -> IO(Held):
  match at:
    case Nil{}:
      IO.pure(Held, Held{None{}, path})
    case only <> Nil{}:
      IO.pure(Held, Held{Some{only}, path})
    case _:
      wcf.several(bs, t, path, left)

def wcf.held(+bs: List<&2, Bm.Bookmark>, +t: Tree.Tree(), +sp: String, +left: Maybe<&2, String>) -> IO(Held):
  +p = Maybe.default(&2, String, T.strip_prefix(sp, "path:"), sp)
  Bool.pick(IO(Held), String.starts_with(sp, "file:"), wcf.file(bs, t, sp, left), wcf.path(bs, t, p, left, Tree.at(t, p)))

def found_at(fs: List<&2, Folder.Found>, +path: String) -> Maybe<&2, Folder.Found>:
  match fs:
    case Nil{}:
      None{}
    case +f <> rest:
      Bool.pick(Maybe<&2, Folder.Found>, String.eq(Folder.found.path(f), path), Some{f}, found_at(rest, path))

def wcf.found(+path: String, f: Maybe<&2, Folder.Found>) -> IO(Folder.Found):
  match f:
    case None{}:
      die(Folder.Found, 1, "the folder holds no " ++ path ++ "; `historica blame <target> " ++ path ++ "` reads it as a revision left it")
    case Some{x}:
      IO.pure(Folder.Found, x)

# A link holds where it points, asked before anything is read through it.
def wcf.link(+path: String, f: Folder.Found) -> IO(Unit):
  match f:
    case Folder.Found.Link{p, t}:
      lines_only(path, Some{Tree.Link{}})
    case Folder.Found.File{p, r, n}:
      IO.pure(Unit, Unit{})

# A file the position holds keeps the kind it was added with; one it does
# not is whatever the recorder would call it.
def wcf.kind(+path: String, k: Maybe<&2, Tree.FileKind>, +bs: List<&2, U32>) -> IO(Unit):
  match k:
    case Some{kind}:
      lines_only(path, Some{kind})
    case None{}:
      Bool.pick(IO(Unit), Folder.is_text(bs), IO.pure(Unit, Unit{}), lines_only(path, Some{Tree.Whole{}}))

def wcf.kind_of(+t: Tree.Tree(), f: Maybe<&2, String>) -> Maybe<&2, Tree.FileKind>:
  match f:
    case None{}:
      None{}
    case Some{+file}:
      Tree.kind(t, file)

# The lines history holds keep the revision that wrote them; the rest are
# the folder's own and belong to nobody yet — which is which comes from the
# same decomposition `record` would write down.
def wc.overlay.of(+rows: List<&2, Row>, d: Maybe<&2, Ops.Doc>) -> List<&2, Row>:
  match d:
    case None{}:
      rows
    case Some{doc}:
      overlay(laid(rows.items(rows), doc), rows, None{})

def wc.overlay(+rows: List<&2, Row>, after: List<&2, Ops.Item>) -> List<&2, Row>:
  wc.overlay.of(rows, Sim.diff(rows.items(rows), after))

def wcf.origins(+root: String, +fs: List<&2, Full>, +left: Maybe<&2, String>, file: Maybe<&2, String>) -> IO(List<&2, Row>):
  match left file:
    case Some{+id} Some{+f}:
      do IO<List<&2, Row>>:
        ds : List<&2, Store.Doc> <- Store.fetch(root, wanted(fs, f))
        +ds2 : List<&2, Store.Doc> = ds
        more : List<&2, Store.Doc> <- Store.fetch(root, kept_digests(ds2))
        +all : List<&2, Store.Doc> = List.append(&2, Store.Doc, ds2, more)
        +oldest : List<&2, Full> = List.reverse(&2, Full, presentation(ancestry(fs, id)))
        items : List<&2, Ops.Item> <- blame.readable(content.in(oldest, all, id, f))
        return origins(oldest, all, id, f)
    case _ _:
      IO.pure(List<&2, Row>, Nil{})

def blame.held(+root: String, +fs: List<&2, Full>, +repo: String, +t: Tree.Tree(), +l: Maybe<&2, String>, found: List<&2, Folder.Found>, h: Held, asked_span: Maybe<&2, Wanted>) -> IO(Unit):
  match h:
    case Held{+file, +path}:
      do IO<Unit>:
        f : Folder.Found <- wcf.found(path, found_at(found, path))
        wcf.link(path, f)
        +k : Maybe<&2, Tree.FileKind> = wcf.kind_of(t, file)
        lines_only(path, k)
        bs : List<&2, U32> <- Utf8.read_file(repo ++ "/" ++ path)
        +bs2 : List<&2, U32> = bs
        wcf.kind(path, k, bs2)
        rows : List<&2, Row> <- wcf.origins(root, fs, l, file)
        blame.limited(fs, changes(fs), wc.overlay(rows, Ops.from_text(Folder.lossy(bs2))), asked_span)

# `blame <path>`: the file as the folder holds it, attributed as far as the
# store can.
def blame.folder(+root: String, +fs: List<&2, Full>, +bs: List<&2, Bm.Bookmark>, +sp: String, asked_span: Maybe<&2, Wanted>) -> IO(Unit):
  do IO<Unit>:
    rules : List<&2, Folder.Scope> <- Folder.rules(root)
    +repo : String = repository(root)
    found : List<&2, Folder.Found> <- Folder.walk(repo, rules)
    left : Maybe<&2, String> <- the_head(fs, bs, current_heads(history(fs)))
    +l : Maybe<&2, String> = left
    t : Tree.Tree() <- tree.maybe(fs, l)
    +t2 : Tree.Tree() = t
    h : Held <- wcf.held(bs, t2, sp, l)
    blame.held(root, fs, repo, t2, l, found, h, asked_span)

def blame.side(+root: String, +fs: List<&2, Full>, +bs: List<&2, Bm.Bookmark>, named: Maybe<&2, String>, +sp: String, asked_span: Maybe<&2, Wanted>) -> IO(Unit):
  match named:
    case Some{+t}:
      blame.recorded(root, fs, bs, t, sp, asked_span)
    case None{}:
      blame.folder(root, fs, bs, sp, asked_span)

def blame.named(+root: String, +fs: List<&2, Full>, +bs: List<&2, Bm.Bookmark>, named: Maybe<&2, String>, only: Maybe<&2, String>, lines: Maybe<&2, String>) -> IO(Unit):
  match only:
    case None{}:
      die(Unit, 2, "`blame` wants a path: it answers who wrote each line of one file")
    case Some{+sp}:
      do IO<Unit>:
        asked_span : Maybe<&2, Wanted> <- blame.wanted(lines)
        blame.side(root, fs, bs, named, sp, asked_span)

def blame.split(+root: String, +fs: List<&2, Full>, +bs: List<&2, Bm.Bookmark>, +lines: Maybe<&2, String>, rest: List<&2, String>) -> IO(Unit):
  match rest:
    case Nil{}:
      blame.named(root, fs, bs, None{}, None{}, lines)
    case +first <> Nil{}:
      Bool.pick(IO(Unit), could_be_target(bs, first), blame.named(root, fs, bs, Some{first}, None{}, lines), blame.named(root, fs, bs, None{}, Some{first}, lines))
    case first <> second <> Nil{}:
      blame.named(root, fs, bs, Some{first}, Some{second}, lines)
    case first <> second <> third <> more:
      die(Unit, 2, "`blame` takes a target and a path, and `" ++ third ++ "` is a third argument")

def blame.of(+root: String, +fs: List<&2, Full>, +bs: List<&2, Bm.Bookmark>, a: BlameAsked) -> IO(Unit):
  match a:
    case BlameAsked{lines, rest}:
      blame.split(root, fs, bs, lines, List.reverse(&2, String, rest))

def blame(+args: List<&2, String>) -> IO(Unit):
  do IO<Unit>:
    root : String <- Store.root()
    +r : String = root
    rs : List<&2, Store.Doc> <- Store.revisions(r)
    bs : List<&2, Bm.Bookmark> <- bookmarks(r)
    a : BlameAsked <- basked.io(basked.go(1n+List.length(&2, String, args), BParse{args, Done{BlameAsked{None{}, Nil{}}}}))
    blame.of(r, fulls(r, rs), bs, a)

# replay
# ------

def replay.step(state: Result<&2, &2, String, List<&2, Ops.Item>>, parsed: Result<&2, &2, String, Ops.Doc>) -> Result<&2, &2, String, List<&2, Ops.Item>>:
  do Result<&2, &2, String, List<&2, Ops.Item>>:
    items : List<&2, Ops.Item> <- state
    doc : Ops.Doc <- parsed
    Ops.apply(items, doc)

# A document that is not an operation document is a payload: the file
# created whole, which decision 0017 makes the same as an insert at 0.
def replay.doc(state: Result<&2, &2, String, List<&2, Ops.Item>>, text: String, is_ops: Bool) -> Result<&2, &2, String, List<&2, Ops.Item>>:
  match is_ops:
    case True{}:
      replay.step(state, Ops.parse(text))
    case False{}:
      Done{Ops.from_text(text)}

def replay.go(ds: List<&2, Store.Doc>, state: Result<&2, &2, String, List<&2, Ops.Item>>) -> Result<&2, &2, String, List<&2, Ops.Item>>:
  match ds:
    case Nil{}:
      state
    case Store.Doc{path, id, size, text} <> rest:
      replay.go(rest, replay.doc(state, text, String.ends_with(path, ".ops.txt")))

def replay(paths: List<&2, String>) -> IO(Unit):
  do IO<Unit>:
    ds : List<&2, Store.Doc> <- Store.read_docs(paths)
    cat.print(replay.go(ds, Done{Nil{}}))

# diff
# ----

def opdiff.print(d: Maybe<&2, Ops.Doc>) -> IO(Unit):
  match d:
    case None{}:
      IO.print("the two files agree")
    case Some{doc}:
      IO.write(Ops.write(doc))

def opdiff(parent: String, child: String) -> IO(Unit):
  do IO<Unit>:
    p : Store.Doc <- Store.read_doc(parent)
    c : Store.Doc <- Store.read_doc(child)
    opdiff.print(Ops.diff(Ops.from_text(Store.text_of(p)), Ops.from_text(Store.text_of(c))))

# main
# ----

def usage() -> IO(Unit):
  die(Unit, 2, "usage: log [<target>|<from>..<to>] [--limit <n>] [--author <text>] [--grep <text>] [--since <when>] [--until <when>] [--path <path>] [--fields] | show <target> [<path>] | files <target> | cat <target> <path> | check | names | diff [<target>] [<path>] [--onto <target>] [--color <when>] | blame [<target>] <path> [--lines <first>..<last>] | replay <ops docs..> | opdiff <parent> <child>")

def dispatch(args: List<&2, String>) -> IO(Unit):
  match args:
    case "log" <> args:
      log(args)
    case "show" <> t <> Nil{}:
      show(t, None{})
    case "show" <> t <> p <> Nil{}:
      show(t, Some{p})
    case "files" <> t <> Nil{}:
      files(t)
    case "cat" <> t <> p <> Nil{}:
      cat(t, p)
    case "check" <> Nil{}:
      check()
    case "names" <> Nil{}:
      names()
    case "names" <> extra <> rest:
      die(Unit, 2, "`names` takes no arguments, and `" ++ extra ++ "` is one")
    case "replay" <> paths:
      replay(paths)
    case "diff" <> args:
      diff(args)
    case "blame" <> args:
      blame(args)
    case "opdiff" <> parent <> child <> Nil{}:
      opdiff(parent, child)
    case _:
      usage()

def reusable(xs: List<&1, String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case h <> t:
      h <> reusable(t)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    dispatch(reusable(args))
