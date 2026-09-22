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
#   bend main.bend -- diff <parent> <child>  the operation document between two files
#
# Or compile it: `bend main.bend -o main.c`, then link the archive `ffi/`
# builds — `check.py` does both. What `bend main.bend` runs and what the
# binary runs are the same program over two adapters (`store.bend`).
#
# A target may also be a bookmark (`names/`), which wins over any other
# spelling, `head` included; a path may be `file:` and a file identifier or
# a file bookmark, or `path:` and a path. Not here: a merge's `keep`
# resolution, which `cat` refuses rather than guesses at.

import Base
import ./text.bend as T
import ./ident.bend as Id
import ./ops.bend as Ops
import ./revision.bend as Rev
import ./store.bend as Store
import ./tree.bend as Tree
import ./utf8.bend as Utf8
import ./bookmark.bend as Bm

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

def bookmarks(+root: String) -> IO(List<&2, Bm.Bookmark>):
  do IO<List<&2, Bm.Bookmark>>:
    ps : List<&2, String> <- Store.name_paths(root)
    bookmarks.read(root, List.sort(~Named, ~(a => b => named.le(a, b)), named(ps)))

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
# holds the file; a merge that resolved the file says so with an `edit`,
# whose `keep` grammar this spike does not read, so it is refused there.
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

def contents.said(+ds: List<&2, Store.Doc>, +id: String, +file: String, inherited: Maybe<&2, Result<&2, &2, String, List<&2, Ops.Item>>>, s: Said) -> Maybe<&2, Result<&2, &2, String, List<&2, Ops.Item>>>:
  match s:
    case Whole{+d}:
      Some{Result.map(&2, &2, String, String, List<&2, Ops.Item>, t => Ops.from_text(t), held(id, d, doc_by_id(ds, d)))}
    case Edited{+d}:
      Some{edited(inherited, held(id, d, doc_by_id(ds, d)), file)}
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
    cat.print(content(fs, ds, id, file2))

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

def diff.print(d: Maybe<&2, Ops.Doc>) -> IO(Unit):
  match d:
    case None{}:
      IO.print("the two files agree")
    case Some{doc}:
      IO.write(Ops.write(doc))

def diff(parent: String, child: String) -> IO(Unit):
  do IO<Unit>:
    p : Store.Doc <- Store.read_doc(parent)
    c : Store.Doc <- Store.read_doc(child)
    diff.print(Ops.diff(Ops.from_text(Store.text_of(p)), Ops.from_text(Store.text_of(c))))

# main
# ----

def usage() -> IO(Unit):
  die(Unit, 2, "usage: log [<target>|<from>..<to>] [--limit <n>] [--author <text>] [--grep <text>] [--since <when>] [--until <when>] [--path <path>] [--fields] | show <target> [<path>] | files <target> | cat <target> <path> | check | names | replay <ops docs..> | diff <parent> <child>")

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
    case "diff" <> parent <> child <> Nil{}:
      diff(parent, child)
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
