# The commands `main.bend` dispatches to, over the store each finds: every
# one here is a def taking its arguments and answering `IO(Unit)`, and every
# conclusion it reaches is a pure def beside it that a law can name.
#
# `main.bend` is the entry point and nothing else — the command line read,
# and the word before the arguments looked up. The commands a later port
# adds live in modules of their own that import this one, so that each can
# be read, and proven about, apart from the rest.

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
import ./merge.bend as Merge
import ./similar.bend as Sim
import ./folder.bend as Folder
import ./unicode.bend as Uni
import ./survey.bend as Sv
import ./notes.bend as Notes
import ./naming.bend as Naming
import ./sha256.bend as Sha
import ./identity.bend as Identity
import ./editor.bend as Editor

# A usage error, exit 2, is a command line that was wrong, and the Rust tool
# says its usage after the message, a blank line between.
def usage.after(code: U32) -> String:
  Bool.pick(String, U32.is_eq(code, 2), "\n\n" ++ Notes.USAGE(), SNil{})

# A refusal, said the way the Rust tool says it.
def die(-A: Type, +code: U32, msg: String) -> IO(A):
  IO.die(A, code, "historica: " ++ msg ++ usage.after(code))

# A refusal decided without IO, and the IO that says it.
type Refused is Data:
  Refused{code: U32, msg: String}

def refused.io(-A: Data, r: Result<&2, &2, Refused, A>) -> IO(A):
  match r:
    case Fail{Refused{code, msg}}:
      die(A, code, msg)
    case Done{x}:
      IO.pure(A, x)

# Lines a command decided on, printed.
def print_lines(ls: List<&2, String>) -> IO(Unit):
  match ls:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case l <> rest:
      do IO<Unit>:
        IO.print(l)
        print_lines(rest)

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

# A revision opening accepts and its whole reading refuses is in the
# graph, as the Rust tool's store holds it (decision 0061), carrying why
# where its facts would be: every command that asks what it did is refused
# in the whole reading's words, naming the file (`unread`). `fulls` keeps
# only what reads whole (`LAWS.revisions_read_are_their_documents`); the
# commands open the store with `opened.fulls`, which is that and these.
def full.unread(+id: String, +why: String, r: Maybe<&2, Rev.Rev>) -> Maybe<&2, Full>:
  match r:
    case None{}:
      None{}
    case Some{Rev.Rev{change, parents, supersedes, author, when, revised_by, revised, facts, message}}:
      Some{Full{id, change, parents, supersedes, author, when, revised_by, revised, [Rev.Header{SNil{}, why}], message}}

def full.opened(+id: String, +path: String, +text: String, parsed: Result<&2, &2, String, Rev.Rev>) -> Maybe<&2, Full>:
  match parsed:
    case Done{r}:
      full(id, Done{r})
    case Fail{e}:
      full.unread(id, path ++ ": " ++ e, Rev.opening.read(text))

def opened.fulls(+root: String, ds: List<&2, Store.Doc>) -> List<&2, Full>:
  match ds:
    case Nil{}:
      Nil{}
    case Store.Doc{+path, +id, size, +text} <> rest:
      push_full(Bool.pick(Maybe<&2, Full>, Store.in_revisions(root, path), full.opened(id, path, text, Rev.parse(text)), None{}), opened.fulls(root, rest))

def unread.facts(hs: List<&2, Rev.Header>) -> Maybe<&2, String>:
  match hs:
    case Rev.Header{+k, +v} <> Nil{}:
      Bool.pick(Maybe<&2, String>, String.is_empty(k), Some{v}, None{})
    case _:
      None{}

# Why a revision's document does not read whole, where it does not.
def unread(f: Full) -> Maybe<&2, String>:
  match f:
    case Full{id, change, parents, supersedes, author, when, revised_by, revised, facts, message}:
      unread.facts(facts)

def unread.first(fs: List<&2, Full>) -> Maybe<&2, String>:
  match fs:
    case Nil{}:
      None{}
    case f <> rest:
      Maybe.or(&2, String, unread(f), unread.first(rest))

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

def bookmark.text(+file: String, name: String, r: Result<&2, &2, String, String>) -> IO(Bm.Bookmark):
  match r:
    case Fail{e}:
      die(Bm.Bookmark, 1, file ++ ": " ++ e)
    case Done{text}:
      bookmark.stated(file, name, Bm.parse(text))

def bookmark.read(+file: String, name: String) -> IO(Bm.Bookmark):
  do IO<Bm.Bookmark>:
    r : Result<&2, &2, String, String> <- Store.read_utf8(file)
    bookmark.text(file, name, r)

def bookmarks.read(+root: String, ns: List<&2, Named>) -> IO(List<&2, Bm.Bookmark>):
  match ns:
    case Nil{}:
      IO.pure(List<&2, Bm.Bookmark>, Nil{})
    case Named{n, p} <> rest:
      do IO<List<&2, Bm.Bookmark>>:
        b : Bm.Bookmark <- bookmark.read(root ++ "/" ++ p, n)
        bs : List<&2, Bm.Bookmark> <- bookmarks.read(root, rest)
        return b <> bs

# The bookmarks under `names/`, in name order.
def bookmarks.order(ps: List<&2, String>) -> List<&2, Named>:
  List.sort(~Named, ~(a => b => named.le(a, b)), named(ps))

# What opening the store reads besides its documents: the bookmarks, then
# the rules of `skipped/` — each refusing the store, as the Rust tool's
# `Store::open` does, where a file is not what it should be.
def bookmarks(+root: String) -> IO(List<&2, Bm.Bookmark>):
  do IO<List<&2, Bm.Bookmark>>:
    ps : List<&2, String> <- Store.name_paths(root)
    bs : List<&2, Bm.Bookmark> <- bookmarks.read(root, bookmarks.order(ps))
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

# A head whose document does not read whole is listed by what opening read
# of it: its digest and its change.
def describe(+id: String, names: String, found: Maybe<&2, Full>) -> String:
  match found:
    case None{}:
      "\n  " ++ String.take(id, 12n) ++ names
    case Some{Full{i, +change, parents, supersedes, author, when, revised_by, revised, +facts, message}}:
      "\n  " ++ String.take(id, 12n) ++ "  " ++ change ++ names ++ Bool.pick(String, Maybe.is_some(&2, String, unread.facts(facts)), SNil{}, "\n      " ++ author ++ "  " ++ when ++ summary_line(message))

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

def resolved.found.r(+id: String, found: Maybe<&2, Full>) -> Result<&2, &2, Refused, Full>:
  match found:
    case None{}:
      Fail{Refused{1, "this store does not hold the revision " ++ id}}
    case Some{f}:
      Done{f}

def resolved.of.r(+fs: List<&2, Full>, r: Result<&2, &2, String, String>) -> Result<&2, &2, Refused, Full>:
  match r:
    case Fail{e}:
      Fail{Refused{1, e}}
    case Done{+id}:
      resolved.found.r(id, find(fs, id))

def resolved.r(+fs: List<&2, Full>, +bs: List<&2, Bm.Bookmark>, +spelling: String) -> Result<&2, &2, Refused, Full>:
  resolved.of.r(fs, resolve(fs, bs, spelling))

def resolved(+fs: List<&2, Full>, +bs: List<&2, Bm.Bookmark>, +spelling: String) -> IO(Full):
  refused.io(Full, resolved.r(fs, bs, spelling))

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

def marks.list(+id: String, +change: String, parents: List<&2, String>, supersedes: List<&2, String>, +heads: List<&2, String>, +gone: List<&2, String>, +h: Rev.History()) -> List<&2, String>:
  +n_parents = List.length(&2, String, parents)
  +n_supersedes = List.length(&2, String, supersedes)
  mark(Rev.member(heads, id), "head",
    mark(Nat.is_gt(n_parents, 1n), "merge",
    mark(Rev.member(gone, id), "superseded",
    mark(Nat.is_gt(n_supersedes, 0n), "rewrites " ++ Nat.show(n_supersedes),
    mark(is_divergent(Rev.change_state(h, change)), "divergent", Nil{})))))

# Marks as they sit after a digest, or nothing where there are none.
def parenthesised(+ms: List<&2, String>) -> String:
  Bool.pick(String, List.is_empty(&2, String, ms), SNil{}, "  (" ++ String.join(ms, ", ") ++ ")")

def marks(+id: String, +change: String, parents: List<&2, String>, supersedes: List<&2, String>, +heads: List<&2, String>, +gone: List<&2, String>, +h: Rev.History()) -> String:
  parenthesised(marks.list(id, change, parents, supersedes, heads, gone, h))

def revised_line(by: Maybe<&2, String>, at: Maybe<&2, String>) -> List<&2, String>:
  match by at:
    case Some{b} Some{a}:
      ["    revised by " ++ b ++ "  " ++ a]
    case _ _:
      Nil{}

def facts_line(+facts: String) -> List<&2, String>:
  Bool.pick(List<&2, String>, String.is_empty(facts), Nil{}, ["    " ++ facts])

def message_lines(ls: List<&2, String>) -> List<&2, String>:
  match ls:
    case Nil{}:
      Nil{}
    case +l <> rest:
      Bool.pick(String, String.is_empty(l), SNil{}, "    " ++ l) <> message_lines(rest)

def line_texts(ls: List<&2, T.Line>) -> List<&2, String>:
  match ls:
    case Nil{}:
      Nil{}
    case T.Line{t, n} <> rest:
      t <> line_texts(rest)

# `lines` as Rust's `str::lines`: a final newline ends the last line rather
# than starting an empty one.
def message.said(+m: String) -> List<&2, String>:
  Bool.pick(List<&2, String>, String.is_empty(String.trim(m)), ["    (no message)"], message_lines(line_texts(T.lines(m))))

# One revision as `log` shows it: its change and digest abbreviated, with
# its marks; who and when; who revised it last, if anyone; what it did to
# the file set, if anything; and its message, indented.
def entry.lines(f: Full, +all_ids: List<&2, String>, +all_changes: List<&2, String>, +heads: List<&2, String>, +gone: List<&2, String>, +h: Rev.History()) -> List<&2, String>:
  match f:
    case Full{+id, +change, parents, supersedes, author, when, revised_by, revised, facts, message}:
      (abbreviate(change, all_changes) ++ "  " ++ abbreviate(id, all_ids) ++ marks(id, change, parents, supersedes, heads, gone, h)) <> ("    " ++ author ++ "  " ++ when) <>
        List.append(&2, String, revised_line(revised_by, revised), List.append(&2, String, facts_line(tree_facts(facts)), message.said(message)))

# The entries, a blank line between each and the next.
def entries.lines(fs: List<&2, Full>, +all_ids: List<&2, String>, +all_changes: List<&2, String>, +heads: List<&2, String>, +gone: List<&2, String>, +h: Rev.History(), first: Bool) -> List<&2, String>:
  match fs:
    case Nil{}:
      Nil{}
    case f <> rest:
      List.append(&2, String, Bool.pick(List<&2, String>, first, Nil{}, [SNil{}]), List.append(&2, String, entry.lines(f, all_ids, all_changes, heads, gone, h), entries.lines(rest, all_ids, all_changes, heads, gone, h, False{})))

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

def tree.of.r(+id: String, merged: Result<&2, &2, Tree.Fault, Tree.Merged>) -> Result<&2, &2, Refused, Tree.Tree()>:
  match merged:
    case Fail{e}:
      Fail{Refused{1, id ++ ": " ++ Tree.fault_show(e)}}
    case Done{m}:
      Done{Tree.merged_tree(m)}

def tree.r(+fs: List<&2, Full>, +id: String) -> Result<&2, &2, Refused, Tree.Tree()>:
  tree.of.r(id, Tree.merge(events_of(ancestry.oldest(fs, id))))

# Where a command asks what the revisions behind `ids` did: the first of
# them, by digest, whose document does not read whole stops it
# (`MaterialiseError::UnreadableOperations`).
def by_id(+fs: List<&2, Full>) -> List<&2, Full>:
  List.sort(~Full, ~(a => b => String.is_le(id_of(a), id_of(b))), fs)

def unread.io(+prefix: String, m: Maybe<&2, String>) -> IO(Unit):
  match m:
    case None{}:
      IO.pure(Unit, Unit{})
    case Some{e}:
      die(Unit, 1, prefix ++ e)

def ancestries(+fs: List<&2, Full>, ids: List<&2, String>) -> List<&2, Full>:
  match ids:
    case Nil{}:
      Nil{}
    case +i <> rest:
      List.append(&2, Full, ancestry(fs, i), ancestries(fs, rest))

def readable(+fs: List<&2, Full>, +ids: List<&2, String>) -> IO(Unit):
  unread.io("what the revisions did could not be read: ", unread.first(by_id(ancestries(fs, ids))))

def tree(+fs: List<&2, Full>, +id: String) -> IO(Tree.Tree()):
  do IO<Tree.Tree()>:
    readable(fs, [id])
    refused.io(Tree.Tree(), tree.r(fs, id))

def file_in.of.r(+id: String, +path: String, found: List<&2, String>) -> Result<&2, &2, Refused, String>:
  match found:
    case Nil{}:
      Fail{Refused{1, String.take(id, 12n) ++ " holds no file at " ++ path ++ "; `historica files " ++ String.take(id, 12n) ++ "` lists what it holds"}}
    case only <> Nil{}:
      Done{only}
    case +several:
      Fail{Refused{1, String.take(id, 12n) ++ " has " ++ Nat.show(List.length(&2, String, several)) ++ " files at " ++ path ++ ", so the path does not name one of them:" ++ String.concat(T.map(~String, ~String, ~(f => "\n  file:" ++ f), several))}}

def file_named.listed(+t: Tree.Tree(), fs: List<&2, String>) -> String:
  match fs:
    case Nil{}:
      SNil{}
    case +f <> rest:
      "\n  file:" ++ f ++ "  " ++ Maybe.default(&2, String, Tree.path(t, f), SNil{}) ++ file_named.listed(t, rest)

# A `file:` spelling: a bookmark first, then an identifier's prefix among
# the files this revision holds, which are the ones `files` prints.
def file_named.matched.r(+id: String, +spelling: String, +t: Tree.Tree(), found: List<&2, String>) -> Result<&2, &2, Refused, String>:
  match found:
    case Nil{}:
      Fail{Refused{1, "no file at " ++ String.take(id, 12n) ++ " has an identifier starting `" ++ spelling ++ "`; `historica files " ++ String.take(id, 12n) ++ "` lists them"}}
    case only <> Nil{}:
      Done{only}
    case +several:
      Fail{Refused{1, "`" ++ spelling ++ "` could be " ++ Nat.show(List.length(&2, String, several)) ++ " files at " ++ String.take(id, 12n) ++ ":" ++ file_named.listed(t, List.sort(~String, ~(a => b => String.is_le(a, b)), several))}}

def file_named.prefix.r(+id: String, +spelling: String, +t: Tree.Tree(), letters: Bool) -> Result<&2, &2, Refused, String>:
  match letters:
    case False{}:
      Fail{Refused{1, "`" ++ spelling ++ "` is not a file bookmark here, and a file identifier is spelled in `k`–`z`"}}
    case True{}:
      file_named.matched.r(id, spelling, t, with_prefix(Tree.files(t), spelling))

def file_named.held.r(+id: String, +spelling: String, +file: String, at: Maybe<&2, String>) -> Result<&2, &2, Refused, String>:
  match at:
    case None{}:
      Fail{Refused{1, "the bookmark `" ++ spelling ++ "` names the file " ++ file ++ ", which " ++ String.take(id, 12n) ++ " does not hold; `historica files " ++ String.take(id, 12n) ++ "` lists what it holds"}}
    case Some{p}:
      Done{file}

def file_named.bookmark.r(+id: String, +spelling: String, +t: Tree.Tree(), target: Bm.Target) -> Result<&2, &2, Refused, String>:
  match target:
    case Bm.Target.File{+f}:
      file_named.held.r(id, spelling, f, Tree.path(t, f))
    case +other:
      Fail{Refused{1, "the bookmark `" ++ spelling ++ "` names a " ++ Bm.kind(other) ++ ", and this position names a file"}}

def file_named.found.r(+id: String, +spelling: String, +t: Tree.Tree(), found: Maybe<&2, Bm.Target>) -> Result<&2, &2, Refused, String>:
  match found:
    case Some{target}:
      file_named.bookmark.r(id, spelling, t, target)
    case None{}:
      file_named.prefix.r(id, spelling, t, all_chars(~(c => Id.is_letter(c)), spelling))

def file_named.r(+id: String, +bs: List<&2, Bm.Bookmark>, spelling: String, +t: Tree.Tree()) -> Result<&2, &2, Refused, String>:
  match spelling:
    case SNil{}:
      Fail{Refused{2, "`file:` wants an identifier or a bookmark after it"}}
    case +s:
      file_named.found.r(id, s, t, Bm.find(bs, s))

def file_in.spelled.r(+id: String, +bs: List<&2, Bm.Bookmark>, +path: String, +t: Tree.Tree(), named: Maybe<&2, String>) -> Result<&2, &2, Refused, String>:
  match named:
    case Some{n}:
      file_named.r(id, bs, n, t)
    case None{}:
      +p = Maybe.default(&2, String, T.strip_prefix(path, "path:"), path)
      file_in.of.r(id, p, Tree.at(t, p))

# The file one argument names at one revision: a path, `path:` and a path
# for a file whose own name begins `file:`, or `file:` and an identifier or
# a file bookmark — the one name a file keeps through a rename.
def file_in.r(+id: String, +bs: List<&2, Bm.Bookmark>, +path: String, +t: Tree.Tree()) -> Result<&2, &2, Refused, String>:
  file_in.spelled.r(id, bs, path, t, T.strip_prefix(path, "file:"))

def file_in(+id: String, +bs: List<&2, Bm.Bookmark>, +path: String, +t: Tree.Tree()) -> IO(String):
  refused.io(String, file_in.r(id, bs, path, t))

# What `log` was asked. Every flag is read before any target is resolved,
# and a word that is not a flag is the one target or range.
type Asked is Data:
  Asked{target: Maybe<&2, String>, path: Maybe<&2, String>, fields: Bool, limit: Maybe<&2, Nat>,
        author: Maybe<&2, String>, grep: Maybe<&2, String>, since: Maybe<&2, String>, until: Maybe<&2, String>}

# What a revision must satisfy to be listed: a filter takes entries out and
# changes nothing about the ones that stay. The limit counts what they left.
type Filter is Data:
  Filter{author: Maybe<&2, String>, grep: Maybe<&2, String>, since: Maybe<&2, String>, until: Maybe<&2, String>, file: Maybe<&2, String>}

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

# The wall clock a `--since` or `--until` bounds: a whole timestamp's date
# and time, in the author's own offset, or a date, which is that whole day.
def bound(+flag: String, +v: String, +time: String) -> Result<&2, &2, String, String>:
  Bool.pick(Result<&2, &2, String, String>, Rev.is_timestamp(v), Done{String.take(v, 19n)},
    Bool.pick(Result<&2, &2, String, String>, Rev.is_timestamp(v ++ "T00:00:00+00:00"), Done{v ++ "T" ++ time},
      Fail{"`" ++ flag ++ "` wants a date, as `YYYY-MM-DD`, or a whole time, as `YYYY-MM-DDThh:mm:ss±hh:mm`; `" ++ v ++ "` is neither"}))

# A word of `log`'s arguments: a flag that takes the word after it as its
# value, `--fields`, some other flag, or a word.
type LFlag is Data:
  LFlag.Limit{}
  LFlag.Author{}
  LFlag.Grep{}
  LFlag.Since{}
  LFlag.Until{}
  LFlag.Path{}
  LFlag.Fields{}
  LFlag.Other{}
  LFlag.Word{}

def log.flag(+w: String) -> LFlag:
  Bool.pick(LFlag, String.eq(w, "--limit"), LFlag.Limit{}, Bool.pick(LFlag, String.eq(w, "--author"), LFlag.Author{},
    Bool.pick(LFlag, String.eq(w, "--grep"), LFlag.Grep{}, Bool.pick(LFlag, String.eq(w, "--since"), LFlag.Since{},
      Bool.pick(LFlag, String.eq(w, "--until"), LFlag.Until{}, Bool.pick(LFlag, String.eq(w, "--path"), LFlag.Path{},
        Bool.pick(LFlag, String.eq(w, "--fields"), LFlag.Fields{}, Bool.pick(LFlag, String.starts_with(w, "-"), LFlag.Other{}, LFlag.Word{}))))))))

def flag.name(f: LFlag) -> String:
  match f:
    case LFlag.Limit{}:
      "--limit"
    case LFlag.Author{}:
      "--author"
    case LFlag.Grep{}:
      "--grep"
    case LFlag.Since{}:
      "--since"
    case LFlag.Until{}:
      "--until"
    case LFlag.Path{}:
      "--path"
    case _:
      SNil{}

# What the arguments said, as they said it: the words, each flag's last
# value, and whether `--fields` was among them.
type LRaw is Data:
  LRaw{words: List<&2, String>, path: Maybe<&2, String>, fields: Bool, limit: Maybe<&2, String>,
       author: Maybe<&2, String>, grep: Maybe<&2, String>, since: Maybe<&2, String>, until: Maybe<&2, String>}

def raw.set(r: LRaw, f: LFlag, v: String) -> LRaw:
  match r:
    case LRaw{ws, p, fi, l, au, g, si, u}:
      match f:
        case LFlag.Limit{}:
          LRaw{ws, p, fi, Some{v}, au, g, si, u}
        case LFlag.Author{}:
          LRaw{ws, p, fi, l, Some{v}, g, si, u}
        case LFlag.Grep{}:
          LRaw{ws, p, fi, l, au, Some{v}, si, u}
        case LFlag.Since{}:
          LRaw{ws, p, fi, l, au, g, Some{v}, u}
        case LFlag.Until{}:
          LRaw{ws, p, fi, l, au, g, si, Some{v}}
        case LFlag.Path{}:
          LRaw{ws, Some{v}, fi, l, au, g, si, u}
        case LFlag.Fields{}:
          LRaw{ws, p, fi, l, au, g, si, u}
        case LFlag.Other{}:
          LRaw{ws, p, fi, l, au, g, si, u}
        case LFlag.Word{}:
          LRaw{ws, p, fi, l, au, g, si, u}

def raw.fields(r: LRaw) -> LRaw:
  match r:
    case LRaw{ws, p, fi, l, au, g, si, u}:
      LRaw{ws, p, True{}, l, au, g, si, u}

def raw.word(r: LRaw, +w: String) -> Result<&2, &2, String, LRaw>:
  match r:
    case LRaw{ws, p, fi, l, au, g, si, u}:
      match ws:
        case Nil{}:
          Done{LRaw{[w], p, fi, l, au, g, si, u}}
        case +had:
          Fail{"`log` takes one target or one range, and `" ++ w ++ "` is a second"}

# A value is checked as it is read, so the first that is wrong is the one
# refused.
def value.counted(+v: String, r: Result<&2, &2, Unit, Maybe<&2, Nat>>) -> Result<&2, &2, String, Maybe<&2, Nat>>:
  match r:
    case Fail{u}:
      Fail{"`--limit` wants how many entries to stop after, and `" ++ v ++ "` is not a count"}
    case Done{n}:
      Done{n}

def value.check(f: LFlag, +v: String) -> Result<&2, &2, String, Unit>:
  match f:
    case LFlag.Limit{}:
      Result.map(&2, &2, String, Maybe<&2, Nat>, Unit, n => Unit{}, value.counted(v, count(v)))
    case LFlag.Since{}:
      Result.map(&2, &2, String, String, Unit, b => Unit{}, bound("--since", v, "00:00:00"))
    case LFlag.Until{}:
      Result.map(&2, &2, String, String, Unit, b => Unit{}, bound("--until", v, "23:59:59"))
    case _:
      Done{Unit{}}

# Whether a flag takes the word after it.
def flag.want(f: LFlag) -> Maybe<&2, LFlag>:
  match f:
    case LFlag.Fields{}:
      None{}
    case LFlag.Other{}:
      None{}
    case LFlag.Word{}:
      None{}
    case +other:
      Some{other}

# The arguments read in one pass: what has been read, and the flag whose
# value this word is, if any.
type LRead is Data:
  LRead{raw: Result<&2, &2, String, LRaw>, want: Maybe<&2, LFlag>}

def raw.valued(r: LRaw, f: LFlag, +v: String, c: Result<&2, &2, String, Unit>) -> Result<&2, &2, String, LRaw>:
  match c:
    case Fail{e}:
      Fail{e}
    case Done{u}:
      Done{raw.set(r, f, v)}

def raw.flagged(r: LRaw, +w: String, f: LFlag) -> LRead:
  match f:
    case LFlag.Fields{}:
      LRead{Done{raw.fields(r)}, None{}}
    case LFlag.Other{}:
      LRead{Fail{"`" ++ w ++ "` is not an argument `log` takes"}, None{}}
    case LFlag.Word{}:
      LRead{raw.word(r, w), None{}}
    case +other:
      LRead{Done{r}, Some{other}}

def raw.eat(st: LRead, +w: String) -> LRead:
  match st:
    case LRead{Fail{e}, want}:
      LRead{Fail{e}, want}
    case LRead{Done{r}, None{}}:
      raw.flagged(r, w, log.flag(w))
    case LRead{Done{r}, Some{+f}}:
      LRead{raw.valued(r, f, w, value.check(f, w)), None{}}

def raw.run(args: List<&2, String>, st: LRead) -> LRead:
  match args:
    case Nil{}:
      st
    case w <> rest:
      raw.run(rest, raw.eat(st, w))

def raw.end(st: LRead) -> Result<&2, &2, String, LRaw>:
  match st:
    case LRead{Fail{e}, want}:
      Fail{e}
    case LRead{Done{r}, None{}}:
      Done{r}
    case LRead{Done{r}, Some{f}}:
      Fail{"`" ++ flag.name(f) ++ "` wants a value"}

# What was asked, from what the arguments said: the one target, and each
# value read as what it names.
def limit.of(m: Maybe<&2, String>) -> Result<&2, &2, String, Maybe<&2, Nat>>:
  match m:
    case None{}:
      Done{None{}}
    case Some{+v}:
      value.counted(v, count(v))

def bound.of(+flag: String, m: Maybe<&2, String>, +time: String) -> Result<&2, &2, String, Maybe<&2, String>>:
  match m:
    case None{}:
      Done{None{}}
    case Some{+v}:
      Result.map(&2, &2, String, String, Maybe<&2, String>, b => Some{b}, bound(flag, v, time))

def target.of(ws: List<&2, String>) -> Maybe<&2, String>:
  match ws:
    case Nil{}:
      None{}
    case w <> rest:
      Some{w}

def asked.of(r: LRaw) -> Result<&2, &2, String, Asked>:
  match r:
    case LRaw{ws, p, fi, l, au, g, si, u}:
      do Result<&2, &2, String, Asked>:
        n : Maybe<&2, Nat> <- limit.of(l)
        s : Maybe<&2, String> <- bound.of("--since", si, "00:00:00")
        v : Maybe<&2, String> <- bound.of("--until", u, "23:59:59")
        return Asked{target.of(ws), p, fi, n, au, g, s, v}

def asked(+args: List<&2, String>) -> Result<&2, &2, String, Asked>:
  do Result<&2, &2, String, Asked>:
    r : LRaw <- raw.end(raw.run(args, LRead{Done{LRaw{Nil{}, None{}, False{}, None{}, None{}, None{}, None{}, None{}}}, None{}}))
    asked.of(r)

# What `log`'s arguments say, read plainly: the word after a flag that
# takes a value is that flag's value, the last counting; `--fields` is asked
# for if it is there; every other word is the target. `LAWS.log_reads_its_words`
# holds `asked` to it.
def flag.word(f: LFlag, +w: String, ws: List<&2, String>) -> List<&2, String>:
  match f:
    case LFlag.Word{}:
      w <> ws
    case _:
      ws

def flag.same(g: LFlag, f: LFlag) -> Bool:
  match g f:
    case LFlag.Limit{} LFlag.Limit{}:
      True{}
    case LFlag.Author{} LFlag.Author{}:
      True{}
    case LFlag.Grep{} LFlag.Grep{}:
      True{}
    case LFlag.Since{} LFlag.Since{}:
      True{}
    case LFlag.Until{} LFlag.Until{}:
      True{}
    case LFlag.Path{} LFlag.Path{}:
      True{}
    case LFlag.Fields{} LFlag.Fields{}:
      True{}
    case LFlag.Other{} LFlag.Other{}:
      True{}
    case LFlag.Word{} LFlag.Word{}:
      True{}
    case _ _:
      False{}

def flag.pick(g: LFlag, f: LFlag, +w: String, last: Maybe<&2, String>) -> Maybe<&2, String>:
  Bool.pick(Maybe<&2, String>, flag.same(g, f), Some{w}, last)

def flag.fields(f: LFlag, had: Bool) -> Bool:
  match f:
    case LFlag.Fields{}:
      True{}
    case _:
      had

def largs.words(args: List<&2, String>, want: Maybe<&2, LFlag>) -> List<&2, String>:
  match args:
    case Nil{}:
      Nil{}
    case +w <> +rest:
      match want:
        case Some{g}:
          largs.words(rest, None{})
        case None{}:
          flag.word(log.flag(w), w, largs.words(rest, flag.want(log.flag(w))))

def largs.last(args: List<&2, String>, want: Maybe<&2, LFlag>, +f: LFlag, last: Maybe<&2, String>) -> Maybe<&2, String>:
  match args:
    case Nil{}:
      last
    case +w <> +rest:
      match want:
        case Some{g}:
          largs.last(rest, None{}, f, flag.pick(g, f, w, last))
        case None{}:
          largs.last(rest, flag.want(log.flag(w)), f, last)

def largs.fields(args: List<&2, String>, want: Maybe<&2, LFlag>, had: Bool) -> Bool:
  match args:
    case Nil{}:
      had
    case +w <> +rest:
      match want:
        case Some{g}:
          largs.fields(rest, None{}, had)
        case None{}:
          largs.fields(rest, flag.want(log.flag(w)), flag.fields(log.flag(w), had))

def largs.raw(+args: List<&2, String>) -> LRaw:
  LRaw{largs.words(args, None{}), largs.last(args, None{}, LFlag.Path{}, None{}), largs.fields(args, None{}, False{}),
    largs.last(args, None{}, LFlag.Limit{}, None{}), largs.last(args, None{}, LFlag.Author{}, None{}), largs.last(args, None{}, LFlag.Grep{}, None{}),
    largs.last(args, None{}, LFlag.Since{}, None{}), largs.last(args, None{}, LFlag.Until{}, None{})}

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
def dots_first(s: String) -> Bool:
  match s:
    case SCon{a, SCon{b, t}}:
      Bool.and(Char.is_eq(a, '.'), Char.is_eq(b, '.'))
    case _:
      False{}

def range.cut.go(s: String, before: String, hit: Bool) -> Maybe<&2, T.Split>:
  match s hit:
    case SNil{} _:
      None{}
    case SCon{c, t} True{}:
      Some{T.Split{String.reverse(before), String.drop(t, 1n)}}
    case SCon{c, +t} False{}:
      range.cut.go(t, SCon{c, before}, dots_first(t))

def range.cut(+s: String, before: String) -> Maybe<&2, T.Split>:
  range.cut.go(s, before, dots_first(s))

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

# Where `LAWS.log_lists_its_span` looks: a revision of the store a span
# names — any, with no target; one the target reaches; or, of `a..b`, one
# `b` reaches and `a` does not.
def span.has(+fs: List<&2, Full>, sp: Span, +id: String) -> Bool:
  match sp:
    case Span.All{}:
      Rev.member(ids(fs), id)
    case Span.From{+a}:
      Bool.and(Rev.member(ids(fs), id), Rev.member(reached(fs, a), id))
    case Span.Between{+from, +to}:
      Bool.and(Rev.member(ids(fs), id), Bool.and(Rev.member(reached(fs, to), id), Bool.not(Rev.member(reached(fs, from), id))))

def span.all_in(+fs: List<&2, Full>, +sp: Span, xs: List<&2, Full>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case +x <> rest:
      Bool.and(span.has(fs, sp, id_of(x)), span.all_in(fs, sp, rest))

# The revision a `--path` is read at: the far end of what was named, or the
# head where nothing was — and where there are several heads, none.
def read_at.heads.r(+fs: List<&2, Full>, +bs: List<&2, Bm.Bookmark>, +path: String, heads: List<&2, String>) -> Result<&2, &2, Refused, String>:
  match heads:
    case Nil{}:
      Fail{Refused{1, "this store holds no revisions yet"}}
    case only <> Nil{}:
      Done{only}
    case +several:
      Fail{Refused{1, "this store has " ++ Nat.show(List.length(&2, String, several)) ++ " heads, so there is no one place to read `" ++ path ++ "` at; say which revision to read it at, as `historica log <target> --path " ++ path ++ "`:" ++ described(fs, bs, List.sort(~String, ~(a => b => String.is_le(a, b)), several))}}

def read_at.r(+fs: List<&2, Full>, +bs: List<&2, Bm.Bookmark>, +path: String, sp: Span) -> Result<&2, &2, Refused, String>:
  match sp:
    case Span.All{}:
      read_at.heads.r(fs, bs, path, current_heads(history(fs)))
    case Span.From{id}:
      Done{id}
    case Span.Between{from, to}:
      Done{to}

# The file a `--path` names, read once, at one revision: what the log then
# follows is the file, through the `move` that renamed it as readily as
# through the edits either side.
def followed.at.r(+fs: List<&2, Full>, +bs: List<&2, Bm.Bookmark>, +p: String, +at: String) -> Result<&2, &2, Refused, Maybe<&2, String>>:
  Result.map(&2, &2, Refused, String, Maybe<&2, String>, file => Some{file}, Result.bind(&2, &2, Refused, Tree.Tree(), String, tree.r(fs, at), t => file_in.r(at, bs, p, t)))

def followed.r(+fs: List<&2, Full>, +bs: List<&2, Bm.Bookmark>, +sp: Span, path: Maybe<&2, String>) -> Result<&2, &2, Refused, Maybe<&2, String>>:
  match path:
    case None{}:
      Done{None{}}
    case Some{+p}:
      Result.bind(&2, &2, Refused, String, Maybe<&2, String>, read_at.r(fs, bs, p, sp), at => followed.at.r(fs, bs, p, at))

def followed(+fs: List<&2, Full>, +bs: List<&2, Bm.Bookmark>, +sp: Span, path: Maybe<&2, String>) -> IO(Maybe<&2, String>):
  refused.io(Maybe<&2, String>, followed.r(fs, bs, sp, path))

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

# What every listed revision satisfies: each filter asked of it
# (`LAWS.log_lists_what_it_asks`).
def all_kept(+fl: Filter, fs: List<&2, Full>) -> Bool:
  match fs:
    case Nil{}:
      True{}
    case +f <> rest:
      Bool.and(keeps(fl, f), all_kept(fl, rest))

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

def fields.lines(fs: List<&2, Full>, +heads: List<&2, String>, +gone: List<&2, String>, +h: Rev.History()) -> List<&2, String>:
  match fs:
    case Nil{}:
      Nil{}
    case f <> rest:
      fields_line(f, heads, gone, h) <> fields.lines(rest, heads, gone, h)

# Printing
# --------

def log.listed.lines(+fs: List<&2, Full>, +listed: List<&2, Full>, fields: Bool, +selects: Bool) -> List<&2, String>:
  match fields:
    case True{}:
      +h = history(fs)
      "historica-log-1" <> fields.lines(listed, Rev.heads(h), Rev.superseded(h), h)
    case False{}:
      +h = history(fs)
      Bool.pick(List<&2, String>, Bool.and(List.is_empty(&2, Full, listed), selects), ["no revision here matches all of those"],
        entries.lines(listed, ids(fs), changes(fs), Rev.heads(h), Rev.superseded(h), h, True{}))

def spelled(+fs: List<&2, Full>, +bs: List<&2, Bm.Bookmark>, +id: String) -> String:
  String.take(id, 12n) ++ names_at(bs, history(fs), id)

# An empty span is an answer rather than a fault: a range that is empty says
# the work asked about is already behind the revision it was held up against.
def log.empty(+fs: List<&2, Full>, +bs: List<&2, Bm.Bookmark>, sp: Span) -> String:
  match sp:
    case Span.Between{+from, +to}:
      spelled(fs, bs, to) ++ " holds nothing " ++ spelled(fs, bs, from) ++ " does not"
    case _:
      "no revisions here yet"

# What `log` prints of what the span shows: the revisions every filter
# admits, in the order the walk presents them, as far as the limit.
def log.shown.lines(+fs: List<&2, Full>, +bs: List<&2, Bm.Bookmark>, +sp: Span, +shown: List<&2, Full>, +fl: Filter, +fields: Bool, limit: Maybe<&2, Nat>) -> List<&2, String>:
  Bool.pick(List<&2, String>, Bool.and(List.is_empty(&2, Full, shown), Bool.not(fields)), [log.empty(fs, bs, sp)],
    log.listed.lines(fs, limited(kept(fl, presentation(shown)), limit), fields, selects(fl)))

# What `LAWS.log_fields_lists_what_it_keeps` reads in `--fields`: the
# header, and a line for each revision listed, in order, beginning with its
# digest and a space.
def log.fields.each(ls: List<&2, String>, fs: List<&2, Full>) -> Bool:
  match ls fs:
    case Nil{} Nil{}:
      True{}
    case l <> lr f <> fr:
      Bool.and(String.starts_with(l, id_of(f) ++ " "), log.fields.each(lr, fr))
    case _ _:
      False{}

def log.fields.ok(ls: List<&2, String>, fs: List<&2, Full>) -> Bool:
  match ls:
    case Nil{}:
      False{}
    case l <> rest:
      Bool.and(String.eq(l, "historica-log-1"), log.fields.each(rest, fs))

def log.of(+fs: List<&2, Full>, +bs: List<&2, Bm.Bookmark>, a: Asked) -> IO(Unit):
  match a:
    case Asked{target, path, fields, limit, author, grep, since, until}:
      do IO<Unit>:
        sp : Span <- span(fs, bs, target)
        +sp2 : Span = sp
        file : Maybe<&2, String> <- followed(fs, bs, sp2, path)
        unread.io(SNil{}, unread.first(by_id(span.shown(fs, sp2))))
        print_lines(log.shown.lines(fs, bs, sp2, span.shown(fs, sp2), Filter{author, grep, since, until, file}, fields, limit))

def log(+args: List<&2, String>) -> IO(Unit):
  do IO<Unit>:
    root : String <- Store.root()
    +r : String = root
    rs : List<&2, Store.Doc> <- Store.revisions(r)
    bs : List<&2, Bm.Bookmark> <- bookmarks(r)
    a : Asked <- asked.io(asked(args))
    log.of(opened.fulls(r, rs), bs, a)

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

# In path order, and a path's files in identifier order, as the Rust tool
# lists them: one line each, the path padded to the widest.
def files.key(+e: Tree.Entry) -> String:
  Tree.entry_path(e) ++ "  " ++ Tree.entry_file(e)

def files.listed(+es: Tree.Tree()) -> Tree.Tree():
  List.sort(~Tree.Entry, ~(a => b => String.is_le(files.key(a), files.key(b))), es)

def files.lines(es: Tree.Tree(), +width: Nat) -> List<&2, String>:
  match es:
    case Nil{}:
      Nil{}
    case +e <> rest:
      (pad(Tree.entry_path(e), width) ++ "  " ++ Tree.entry_file(e)) <> files.lines(rest, width)

def files.said(+es: Tree.Tree()) -> List<&2, String>:
  match es:
    case Nil{}:
      ["no files here"]
    case +some:
      files.lines(files.listed(some), widest(some))

# What each line of `files` ends with, as `LAWS.files_lists_in_path_order`
# reads it: the file identifier of each entry listed.
def files.ends(+es: Tree.Tree()) -> List<&2, String>:
  match es:
    case Nil{}:
      ["no files here"]
    case +some:
      T.map(~Tree.Entry, ~String, ~(e => Tree.entry_file(e)), files.listed(some))

def files.of(+es: Tree.Tree()) -> IO(Unit):
  print_lines(files.said(es))

def files(+target: String) -> IO(Unit):
  do IO<Unit>:
    root : String <- Store.root()
    +r : String = root
    rs : List<&2, Store.Doc> <- Store.revisions(r)
    +fs : List<&2, Full> = opened.fulls(r, rs)
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

def names.lines(bs: List<&2, Bm.Bookmark>, +h: Rev.History(), +all_ids: List<&2, String>, +here: Maybe<&2, Tree.Tree()>, +width: Nat) -> List<&2, String>:
  match bs:
    case Nil{}:
      Nil{}
    case +b <> rest:
      (pad(Bm.name_of(b), width) ++ "  " ++ Bm.show(b) ++ "  ->  " ++ names.resolution(h, all_ids, here, Bm.target_of(b))) <> names.lines(rest, h, all_ids, here, width)

def names.said(+fs: List<&2, Full>, bs: List<&2, Bm.Bookmark>) -> List<&2, String>:
  match bs:
    case Nil{}:
      ["no bookmarks here yet"]
    case +some:
      +h = history(fs)
      names.lines(some, h, ids(fs), names.here(Tree.merge(events_of(picked(reached.all(fs, current_heads(h)), Pick{waiting(fs), Nil{}})))), names.widest(some))

# What `LAWS.names_lists_each_bookmark` and `LAWS.names_resolves_to_held`
# read in it: a line for each bookmark, in the order they were read, each
# beginning with its name; and a revision pin or a change said as an
# abbreviation of a revision the store holds, or in parentheses why there
# is none.
def names.begin(ls: List<&2, String>, bs: List<&2, Bm.Bookmark>) -> Bool:
  match ls bs:
    case Nil{} Nil{}:
      True{}
    case l <> lr b <> br:
      Bool.and(String.starts_with(l, Bm.name_of(b)), names.begin(lr, br))
    case _ _:
      False{}

def names.begun(bs: List<&2, Bm.Bookmark>, ls: List<&2, String>) -> Bool:
  match bs:
    case Nil{}:
      True{}
    case +some:
      names.begin(ls, some)

def names.prefix(held: List<&2, String>, +s: String) -> Bool:
  match held:
    case Nil{}:
      False{}
    case +i <> rest:
      Bool.or(String.starts_with(i, s), names.prefix(rest, s))

def names.held(+fs: List<&2, Full>, t: Bm.Target, +s: String) -> Bool:
  match t:
    case Bm.Target.File{f}:
      True{}
    case _:
      Bool.or(String.starts_with(s, "("), names.prefix(ids(fs), s))

def names.of(+fs: List<&2, Full>, bs: List<&2, Bm.Bookmark>) -> IO(Unit):
  print_lines(names.said(fs, bs))

def names() -> IO(Unit):
  do IO<Unit>:
    root : String <- Store.root()
    +r : String = root
    rs : List<&2, Store.Doc> <- Store.revisions(r)
    bs : List<&2, Bm.Bookmark> <- bookmarks(r)
    names.of(opened.fulls(r, rs), bs)

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

# The document an `edit` names, found by its digest.
def doc_found(ds: List<&2, Store.Doc>, +id: String) -> Maybe<&2, Store.Doc>:
  match ds:
    case Nil{}:
      None{}
    case Store.Doc{+path, +i, +size, +text} <> rest:
      Bool.pick(Maybe<&2, Store.Doc>, String.starts_with(i, id), Some{Store.Doc{path, i, size, text}}, doc_found(rest, id))

def failed.ops(r: Result<&2, &2, String, Ops.Doc>) -> Maybe<&2, String>:
  match r:
    case Fail{e}:
      Some{e}
    case Done{d}:
      None{}

def failed.res(r: Result<&2, &2, String, Res.Doc>) -> Maybe<&2, String>:
  match r:
    case Fail{e}:
      Some{e}
    case Done{d}:
      None{}

# Why a document an `edit` names does not read, in its own grammar, naming
# the file as the Rust tool's `StoreError::Unparsable` does.
def unparsable(+path: String, +text: String) -> Maybe<&2, String>:
  Maybe.map(&2, String, String, e => path ++ ": " ++ e, Bool.pick(Maybe<&2, String>, Res.is_resolution(text), failed.res(Res.parse(text)), failed.ops(Ops.parse(text))))

def unparsed.first(ds: List<&2, Store.Doc>) -> Maybe<&2, String>:
  match ds:
    case Nil{}:
      None{}
    case Store.Doc{+path, i, size, +text} <> rest:
      Maybe.or(&2, String, unparsable(path, text), unparsed.first(rest))

def unparsable.found(found: Maybe<&2, Store.Doc>) -> Maybe<&2, String>:
  match found:
    case None{}:
      None{}
    case Some{Store.Doc{+path, i, size, +text}}:
      unparsable(path, text)

def unparsed.named(+ds: List<&2, Store.Doc>, digests: List<&2, String>) -> Maybe<&2, String>:
  match digests:
    case Nil{}:
      None{}
    case +d <> rest:
      Maybe.or(&2, String, unparsable.found(doc_found(ds, d)), unparsed.named(ds, rest))

# The documents the nearest statements name, read as the Rust tool reads
# them for their `result`, file by file in path order: one that does not
# parse stops the command.
def readable.docs(+ds: List<&2, Store.Doc>, digests: List<&2, String>) -> IO(Unit):
  unread.io("what the revisions did could not be read: ", unparsed.named(ds, digests))

# The document an `edit` names, held and readable: one that does not parse
# stops the reading of what the revisions did, the first time something
# asks what it says (`MaterialiseError::UnreadableOperations`).
def held.read(+id: String, +digest: String, found: Maybe<&2, Store.Doc>) -> Result<&2, &2, String, String>:
  match found:
    case None{}:
      held(id, digest, None{})
    case Some{Store.Doc{+path, i, size, +text}}:
      Maybe.default(&2, Result<&2, &2, String, String>, Maybe.map(&2, String, Result<&2, &2, String, String>, e => Fail{"what the revisions did could not be read: " ++ e}, unparsable(path, text)), Done{text})

# The file's content at every revision that holds it, oldest first as the
# trees are, by decision 0032's rule. A revision that says nothing holds
# what its parents agree it holds; an `edit` naming an operation document
# applies it to that; an `edit` naming a resolution is the file whatever
# the parents hold. A revision whose parents disagree and which states no
# resolution is where the rule stops (`Unstated`), and so is every edit
# over one: there the merge walk reads the file instead (`walked`).
type Rule is Data:
  Known{items: List<&2, Ops.Item>}
  Unstated{}

type Contents is Data:
  Contents{content: Result<&2, &2, String, Rule>, id: String}

def content_of(cs: List<&2, Contents>, +id: String) -> Maybe<&2, Result<&2, &2, String, Rule>>:
  match cs:
    case Nil{}:
      None{}
    case Contents{c, +i} <> rest:
      Bool.pick(Maybe<&2, Result<&2, &2, String, Rule>>, String.eq(i, id), Some{c}, content_of(rest, id))

# Two states are one when their items are, forgotten or not.
def item_eq(a: Ops.Item, b: Ops.Item) -> Bool:
  match a b:
    case Ops.Item{t1, n1, f1} Ops.Item{t2, n2, f2}:
      Bool.and(String.eq(t1, t2), Bool.and(Bool.not(Bool.xor(n1, n2)), Bool.not(Bool.xor(f1, f2))))

def items_eq(a: List<&2, Ops.Item>, b: List<&2, Ops.Item>) -> Bool:
  match a b:
    case x <> xs y <> ys:
      Bool.and(item_eq(x, y), items_eq(xs, ys))
    case Nil{} Nil{}:
      True{}
    case _ _:
      False{}

def agree.rule(a: Rule, b: Rule) -> Rule:
  match a b:
    case Known{+x} Known{+y}:
      Bool.pick(Rule, items_eq(x, y), Known{x}, Unstated{})
    case _ _:
      Unstated{}

def agree.some(r: Result<&2, &2, String, Rule>, next: Maybe<&2, Result<&2, &2, String, Rule>>) -> Result<&2, &2, String, Rule>:
  match next:
    case None{}:
      r
    case Some{s}:
      do Result<&2, &2, String, Rule>:
        a : Rule <- r
        b : Rule <- s
        return agree.rule(a, b)

# A parent that never mentioned the file has no say; the first failure
# among the rest is the answer.
def agree(acc: Maybe<&2, Result<&2, &2, String, Rule>>, next: Maybe<&2, Result<&2, &2, String, Rule>>) -> Maybe<&2, Result<&2, &2, String, Rule>>:
  match acc:
    case None{}:
      next
    case Some{r}:
      Some{agree.some(r, next)}

def contents.parents(+cs: List<&2, Contents>, ps: List<&2, String>, acc: Maybe<&2, Result<&2, &2, String, Rule>>) -> Maybe<&2, Result<&2, &2, String, Rule>>:
  match ps:
    case Nil{}:
      acc
    case p <> rest:
      contents.parents(cs, rest, agree(acc, content_of(cs, p)))

def edited.over(h: Rule, doc: Result<&2, &2, String, String>) -> Result<&2, &2, String, Rule>:
  match h:
    case Unstated{}:
      Done{Unstated{}}
    case Known{items}:
      do Result<&2, &2, String, Rule>:
        text : String <- doc
        parsed : Ops.Doc <- Ops.parse(text)
        after : List<&2, Ops.Item> <- Ops.apply(items, parsed)
        return Known{after}

def edited(state: Maybe<&2, Result<&2, &2, String, Rule>>, doc: Result<&2, &2, String, String>, +file: String) -> Result<&2, &2, String, Rule>:
  match state:
    case None{}:
      Fail{"an edit of " ++ file ++ " where no parent holds it"}
    case Some{r}:
      do Result<&2, &2, String, Rule>:
        h : Rule <- r
        edited.over(h, doc)

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
def edited.by(+ds: List<&2, Store.Doc>, +id: String, +file: String, +digest: String, inherited: Maybe<&2, Result<&2, &2, String, Rule>>, +text: String, resolution: Bool) -> Result<&2, &2, String, Rule>:
  match resolution:
    case True{}:
      Result.map(&2, &2, String, List<&2, Ops.Item>, Rule, items => Known{items}, resolved.doc(ds, id, file, digest, Res.parse(text)))
    case False{}:
      edited(inherited, Done{text}, file)

def edited.doc(+ds: List<&2, Store.Doc>, +id: String, +file: String, +digest: String, inherited: Maybe<&2, Result<&2, &2, String, Rule>>, doc: Result<&2, &2, String, String>) -> Result<&2, &2, String, Rule>:
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

def contents.said(+ds: List<&2, Store.Doc>, +id: String, +file: String, inherited: Maybe<&2, Result<&2, &2, String, Rule>>, s: Said) -> Maybe<&2, Result<&2, &2, String, Rule>>:
  match s:
    case Whole{+d}:
      Some{Result.map(&2, &2, String, String, Rule, t => Known{Ops.from_text(t)}, held(id, d, doc_by_id(ds, d)))}
    case Edited{+d}:
      Some{edited.doc(ds, id, file, d, inherited, held.read(id, d, doc_found(ds, d)))}
    case Nothing{}:
      inherited

def contents.push(+id: String, c: Maybe<&2, Result<&2, &2, String, Rule>>, cs: List<&2, Contents>) -> List<&2, Contents>:
  match c:
    case None{}:
      cs
    case Some{r}:
      Contents{r, id} <> cs

# A file added with no content stated is a file of no lines: decision 0017
# states a new file's lines outright, and there are none to state.
def contents.added(added: Bool, inherited: Maybe<&2, Result<&2, &2, String, Rule>>) -> Maybe<&2, Result<&2, &2, String, Rule>>:
  match added:
    case True{}:
      Some{Done{Known{Nil{}}}}
    case False{}:
      inherited

def contents.go(oldest_first: List<&2, Full>, +ds: List<&2, Store.Doc>, +file: String, +cs: List<&2, Contents>) -> List<&2, Contents>:
  match oldest_first:
    case Nil{}:
      cs
    case Full{+id, change, parents, supersedes, author, when, revised_by, revised, +facts, message} <> rest:
      contents.go(rest, ds, file, contents.push(id, contents.said(ds, id, file, contents.added(Rev.member(Rev.files_of(facts, "add"), file), contents.parents(cs, parents, None{})), said(facts, file)), cs))

# The merge walk
# --------------
#
# Where decision 0032's rule stops, the file is what `merge.bend`'s walk
# reads — the walk `LAWS.merge_converges`, `view_keeps_invariant` and
# `merge_intent` are about. Its graph is the target's ancestry in digest
# order, each revision with its ancestors as indices into it; its order is
# by the number of ancestors, which is causal because a revision has
# strictly more than any of its ancestors, and which causal order does not
# matter, since every one merges to one file.

# Whether a revision states a `text` payload for this file: what `merge.rs`
# reads as a creation, where a file of bytes is nothing to walk.
def is_text.cut(+file: String, cut: Maybe<&2, T.Split>) -> Bool:
  match cut:
    case Some{T.Split{f, d}}:
      String.eq(f, file)
    case None{}:
      False{}

def is_text(facts: List<&2, Rev.Header>, +file: String) -> Bool:
  match facts:
    case Nil{}:
      False{}
    case Rev.Header{+k, +v} <> rest:
      Bool.or(Bool.and(String.eq(k, "text"), is_text.cut(file, T.split_once(v))), is_text(rest, file))

def index_of(names: List<&2, String>, +x: String, +n: Nat) -> Nat:
  match names:
    case Nil{}:
      n
    case i <> rest:
      Bool.pick(Nat, String.eq(i, x), n, index_of(rest, x, 1n+n))

def indices(xs: List<&2, String>, +names: List<&2, String>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> rest:
      index_of(names, x, 0n) <> indices(rest, names)

def walked.ops(d: Ops.Doc) -> Maybe<&2, Merge.Statement>:
  match d:
    case Ops.Doc{forgets, result, ops}:
      Some{Merge.Edits{ops}}

# The document each event stated about the file, by digest, where it
# minted elements a `keep` can name: an `edit`, or a `text` payload.
def minted_digest(text: Bool, s: Said) -> String:
  match s:
    case Nothing{}:
      ""
    case Whole{d}:
      Bool.pick(String, text, d, "")
    case Edited{d}:
      d

def minted_digests.of(f: Full, +file: String) -> String:
  match f:
    case Full{id, change, parents, supersedes, author, when, revised_by, revised, +facts, message}:
      minted_digest(is_text(facts, file), said(facts, file))

def minted_digests(rs: List<&2, Full>, +file: String) -> List<&2, String>:
  match rs:
    case Nil{}:
      Nil{}
    case f <> rest:
      minted_digests.of(f, file) <> minted_digests(rest, file)

# The events that stated the document with this digest: whose elements a
# `keep` of it names. Two revisions may state one document, byte for byte.
def authors_of.put(+n: Nat, rest: List<&2, Nat>, hit: Bool) -> List<&2, Nat>:
  match hit:
    case True{}:
      n <> rest
    case False{}:
      rest

def authors_of(ds: List<&2, String>, +d: String, +n: Nat) -> List<&2, Nat>:
  match ds:
    case Nil{}:
      Nil{}
    case x <> rest:
      authors_of.put(n, authors_of(rest, d, 1n+n), String.eq(x, d))

def walked.part(+digests: List<&2, String>, p: Res.Piece) -> Merge.Part:
  match p:
    case Res.Piece.Keep{d, first, count}:
      Merge.Kept{authors_of(digests, d, 0n), first, count}
    case Res.Piece.Insert{items}:
      Merge.Own{items}

def walked.parts(+digests: List<&2, String>, ps: List<&2, Res.Piece>) -> List<&2, Merge.Part>:
  match ps:
    case Nil{}:
      Nil{}
    case p <> rest:
      walked.part(digests, p) <> walked.parts(digests, rest)

def walked.resolution(+digests: List<&2, String>, d: Res.Doc) -> Maybe<&2, Merge.Statement>:
  match d:
    case Res.Doc{forgets, result, pieces}:
      Some{Merge.Resolves{walked.parts(digests, pieces)}}

def walked.by(+digests: List<&2, String>, +text: String, resolution: Bool) -> Result<&2, &2, String, Maybe<&2, Merge.Statement>>:
  match resolution:
    case True{}:
      Result.map(&2, &2, String, Res.Doc, Maybe<&2, Merge.Statement>, d => walked.resolution(digests, d), Res.parse(text))
    case False{}:
      Result.map(&2, &2, String, Ops.Doc, Maybe<&2, Merge.Statement>, d => walked.ops(d), Ops.parse(text))

def walked.edited(+digests: List<&2, String>, doc: Result<&2, &2, String, String>) -> Result<&2, &2, String, Maybe<&2, Merge.Statement>>:
  match doc:
    case Fail{e}:
      Fail{e}
    case Done{+text}:
      walked.by(digests, text, Res.is_resolution(text))

# A payload is the document that inserts every line of it at 0.
def walked.whole(text: Bool, doc: Result<&2, &2, String, String>) -> Result<&2, &2, String, Maybe<&2, Merge.Statement>>:
  match text:
    case False{}:
      Done{None{}}
    case True{}:
      Result.map(&2, &2, String, String, Maybe<&2, Merge.Statement>, t => Some{Merge.Edits{[Ops.Op{Ops.Insert{}, 0n, Ops.from_text(t)}]}}, doc)

def walked.said(+ds: List<&2, Store.Doc>, +digests: List<&2, String>, +id: String, text: Bool, s: Said) -> Result<&2, &2, String, Maybe<&2, Merge.Statement>>:
  match s:
    case Nothing{}:
      Done{None{}}
    case Whole{+d}:
      walked.whole(text, held(id, d, doc_by_id(ds, d)))
    case Edited{+d}:
      walked.edited(digests, held.read(id, d, doc_found(ds, d)))

def walked.rev(+names: List<&2, String>, +digests: List<&2, String>, +ss: List<&2, Tree.Seen>, +ds: List<&2, Store.Doc>, +file: String, f: Full) -> Result<&2, &2, String, Merge.Rev>:
  match f:
    case Full{+id, change, parents, supersedes, author, when, revised_by, revised, +facts, message}:
      Result.map(&2, &2, String, Maybe<&2, Merge.Statement>, Merge.Rev, st => Merge.Rev{indices(Tree.ancestors_of(ss, id), names), st}, walked.said(ds, digests, id, is_text(facts, file), said(facts, file)))

def walked.revs(rs: List<&2, Full>, +names: List<&2, String>, +digests: List<&2, String>, +ss: List<&2, Tree.Seen>, +ds: List<&2, Store.Doc>, +file: String) -> Result<&2, &2, String, List<&2, Merge.Rev>>:
  match rs:
    case Nil{}:
      Done{Nil{}}
    case f <> rest:
      do Result<&2, &2, String, List<&2, Merge.Rev>>:
        here : Merge.Rev <- walked.rev(names, digests, ss, ds, file, f)
        more : List<&2, Merge.Rev> <- walked.revs(rest, names, digests, ss, ds, file)
        return here <> more

# Each event beside how many it had seen, so that sorting by that count is
# a causal order.
type Rank is Data:
  Rank{depth: Nat, at: Nat}

def ranks(+g: List<&2, Merge.Rev>, ixs: List<&2, Nat>) -> List<&2, Rank>:
  match ixs:
    case Nil{}:
      Nil{}
    case +i <> rest:
      Rank{List.length(&2, Nat, Merge.past(g, i)), i} <> ranks(g, rest)

def rank_at(rs: List<&2, Rank>) -> List<&2, Nat>:
  match rs:
    case Nil{}:
      Nil{}
    case Rank{d, at} <> rest:
      at <> rank_at(rest)

def depth_of(r: Rank) -> Nat:
  match r:
    case Rank{d, at}:
      d

# An insertion sort by depth, stable: `x` goes before the first rank at
# least as deep, and every rank it passes has a greater index, so the ranks
# come out by depth and then by index.
def rank.put.pick(+x: Rank, y: Rank, ys: List<&2, Rank>, later: List<&2, Rank>, le: Bool) -> List<&2, Rank>:
  match le:
    case True{}:
      x <> y <> ys
    case False{}:
      y <> later

def rank.put(+x: Rank, ys: List<&2, Rank>) -> List<&2, Rank>:
  match ys:
    case Nil{}:
      [x]
    case +y <> +rest:
      rank.put.pick(x, y, rest, rank.put(x, rest), Nat.is_le(depth_of(x), depth_of(y)))

def rank.sort(rs: List<&2, Rank>) -> List<&2, Rank>:
  match rs:
    case Nil{}:
      Nil{}
    case x <> rest:
      rank.put(x, rank.sort(rest))

def walked.order(+g: List<&2, Merge.Rev>) -> List<&2, Nat>:
  rank_at(rank.sort(ranks(g, Merge.upto(List.length(&2, Merge.Rev, g)))))

# What makes that order causal: every event had seen more events than any
# event it had seen. A graph whose pasts are closed under what each had
# seen, and never hold the event itself, has it.
def shallower(+g: List<&2, Merge.Rev>, js: List<&2, Nat>, +d: Nat) -> Bool:
  match js:
    case Nil{}:
      True{}
    case j <> rest:
      Bool.and(Nat.is_lt(List.length(&2, Nat, Merge.past(g, j)), d), shallower(g, rest, d))

def deepens.all(+g: List<&2, Merge.Rev>, ixs: List<&2, Nat>) -> Bool:
  match ixs:
    case Nil{}:
      True{}
    case +i <> rest:
      Bool.and(shallower(g, Merge.past(g, i), List.length(&2, Nat, Merge.past(g, i))), deepens.all(g, rest))

def deepens(+g: List<&2, Merge.Rev>) -> Bool:
  deepens.all(g, Merge.upto(List.length(&2, Merge.Rev, g)))

# The walked tree, beside the revisions its authors are indices into.
type Walked is Data:
  Walked{names: List<&2, String>, tree: List<&2, Merge.Node>}

def walked.tree(+head: String, +file: String, names: List<&2, String>, m: Maybe<&2, List<&2, Merge.Node>>) -> Result<&2, &2, String, Walked>:
  match m:
    case None{}:
      Fail{head ++ ", file " ++ file ++ ": a revision behind it names a position or an item its author's view of the file does not hold; the document was recorded against a different history"}
    case Some{t}:
      Done{Walked{names, t}}

# The walk, once the order it takes is known to be causal: every revision
# of an ancestry had seen more than any it had seen, which is what makes
# `walked.order` causal (`LAWS.walked_order_causal`). A store's ancestry
# always does; one that did not would not be a history.
def walked.causal(+head: String, +file: String, names: List<&2, String>, +g: List<&2, Merge.Rev>, ok: Bool) -> Result<&2, &2, String, Walked>:
  match ok:
    case True{}:
      walked.tree(head, file, names, Merge.walk(walked.order(g), g, Some{Nil{}}))
    case False{}:
      Fail{head ++ ", file " ++ file ++ ": a revision behind it had seen no more revisions than one it had seen, so the ancestry is not a history"}

def walked.seen(+rs: List<&2, Full>, +ds: List<&2, Store.Doc>, +head: String, +file: String, r: Result<&2, &2, Tree.Fault, List<&2, Tree.Seen>>) -> Result<&2, &2, String, Walked>:
  match r:
    case Fail{e}:
      Fail{head ++ ": " ++ Tree.fault_show(e)}
    case Done{+ss}:
      do Result<&2, &2, String, Walked>:
        +g : List<&2, Merge.Rev> <- walked.revs(rs, ids(rs), minted_digests(rs, file), ss, ds, file)
        walked.causal(head, file, ids(rs), g, deepens(g))

def walked.sorted(+rs: List<&2, Full>, +ds: List<&2, Store.Doc>, +head: String, +file: String) -> Result<&2, &2, String, Walked>:
  walked.seen(rs, ds, head, file, Tree.seen(List.length(&2, Full, rs), events_of(rs), Nil{}))

# The target's ancestry in digest order: the graph's events, whose indices
# its authors are.
def walked.ancestry(+fs: List<&2, Full>, +head: String) -> List<&2, Full>:
  List.sort(~Full, ~(a => b => String.is_le(id_of(a), id_of(b))), ancestry(fs, head))

def walked.of(+fs: List<&2, Full>, +ds: List<&2, Store.Doc>, +head: String, +file: String) -> Result<&2, &2, String, Walked>:
  walked.sorted(walked.ancestry(fs, head), ds, head, file)

def walked.file(w: Walked) -> List<&2, Ops.Item>:
  match w:
    case Walked{names, t}:
      Merge.file(t)

# The file, as `Merge.merged` reads a walk: `Merge.file` of its tree.
def walked(+fs: List<&2, Full>, +ds: List<&2, Store.Doc>, +head: String, +file: String) -> Result<&2, &2, String, List<&2, Ops.Item>>:
  Result.map(&2, &2, String, Walked, List<&2, Ops.Item>, w => walked.file(w), walked.of(fs, ds, head, file))

def content.rule(+fs: List<&2, Full>, +ds: List<&2, Store.Doc>, +id: String, +file: String, h: Rule) -> Result<&2, &2, String, List<&2, Ops.Item>>:
  match h:
    case Known{items}:
      Done{items}
    case Unstated{}:
      walked(fs, ds, id, file)

def content.found(+fs: List<&2, Full>, +ds: List<&2, Store.Doc>, +id: String, +file: String, found: Maybe<&2, Result<&2, &2, String, Rule>>) -> Result<&2, &2, String, List<&2, Ops.Item>>:
  match found:
    case None{}:
      Fail{"no revision behind here says what " ++ file ++ " holds"}
    case Some{r}:
      do Result<&2, &2, String, List<&2, Ops.Item>>:
        h : Rule <- r
        content.rule(fs, ds, id, file, h)

def content.in(+oldest_first: List<&2, Full>, +ds: List<&2, Store.Doc>, +id: String, +file: String) -> Result<&2, &2, String, List<&2, Ops.Item>>:
  content.found(oldest_first, ds, id, file, content_of(contents.go(oldest_first, ds, file, Nil{}), id))

def content(+fs: List<&2, Full>, +ds: List<&2, Store.Doc>, +id: String, +file: String) -> Result<&2, &2, String, List<&2, Ops.Item>>:
  content.found(fs, ds, id, file, content_of(contents.go(List.reverse(&2, Full, presentation(fs)), ds, file, Nil{}), id))

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

# The revision and the file a command reads.
type Picked is Data:
  Picked{id: String, file: String}

def not_a_link.r(+t: Tree.Tree(), +path: String, +file: String, target: Maybe<&2, Tree.Target>) -> Result<&2, &2, Refused, Unit>:
  match target:
    case None{}:
      Done{Unit{}}
    case Some{g}:
      Fail{Refused{1, "`" ++ path ++ "` is a link to `" ++ materialise(t, Maybe.default(&2, String, Tree.path(t, file), path), g) ++ "`, so there is nothing to print; what it holds is where it points"}}

# The revision and the file `cat <target> <path>` prints.
def cat.picked.file(+t: Tree.Tree(), +path: String, +id: String, +file: String) -> Result<&2, &2, Refused, Picked>:
  do Result<&2, &2, Refused, Picked>:
    not_a_link.r(t, path, file, Tree.entry_target_of(Tree.lookup(t, file)))
    return Picked{id, file}

def cat.picked.tree(+bs: List<&2, Bm.Bookmark>, +path: String, +id: String, +t: Tree.Tree()) -> Result<&2, &2, Refused, Picked>:
  do Result<&2, &2, Refused, Picked>:
    file : String <- file_in.r(id, bs, path, t)
    cat.picked.file(t, path, id, file)

def cat.picked.full(+fs: List<&2, Full>, +bs: List<&2, Bm.Bookmark>, +path: String, +id: String) -> Result<&2, &2, Refused, Picked>:
  do Result<&2, &2, Refused, Picked>:
    t : Tree.Tree() <- tree.r(fs, id)
    cat.picked.tree(bs, path, id, t)

def cat.picked.r(+fs: List<&2, Full>, +bs: List<&2, Bm.Bookmark>, +target: String, +path: String) -> Result<&2, &2, Refused, Picked>:
  do Result<&2, &2, Refused, Picked>:
    f : Full <- resolved.r(fs, bs, target)
    cat.picked.full(fs, bs, path, id_of(f))

def cat.print(r: Result<&2, &2, String, List<&2, Ops.Item>>) -> IO(Unit):
  match r:
    case Fail{e}:
      die(Unit, 1, e)
    case Done{items}:
      IO.write(Ops.text(items))

# What `cat <target> <path>` reads is a revision the store holds, and a
# file its tree holds that is not a link. `LAWS.cat_reads_a_held_file` holds
# `cat.picked.r` to it.
def tree.cat_ok(r: Result<&2, &2, Refused, Tree.Tree()>, +file: String) -> Bool:
  match r:
    case Fail{e}:
      False{}
    case Done{+t}:
      Bool.and(Tree.holds(t, file), Maybe.is_none(&2, Tree.Target, Tree.entry_target_of(Tree.lookup(t, file))))

def cat.ok(+fs: List<&2, Full>, p: Picked) -> Bool:
  match p:
    case Picked{+id, +file}:
      Bool.and(Rev.member(ids(fs), id), tree.cat_ok(tree.r(fs, id), file))

def cat.fetched(+r: String, +fs: List<&2, Full>, p: Picked) -> IO(Unit):
  match p:
    case Picked{+id, +file}:
      do IO<Unit>:
        ds : List<&2, Store.Doc> <- Store.fetch(r, wanted(fs, file))
        +ds2 : List<&2, Store.Doc> = ds
        more : List<&2, Store.Doc> <- Store.fetch(r, kept_digests(ds2))
        cat.print(content(fs, List.append(&2, Store.Doc, ds2, more), id, file))

def cat(+target: String, +path: String) -> IO(Unit):
  do IO<Unit>:
    root : String <- Store.root()
    +r : String = root
    rs : List<&2, Store.Doc> <- Store.revisions(r)
    +fs : List<&2, Full> = opened.fulls(r, rs)
    bs : List<&2, Bm.Bookmark> <- bookmarks(r)
    +bs2 : List<&2, Bm.Bookmark> = bs
    f : Full <- resolved(fs, bs2, target)
    readable(fs, [id_of(f)])
    p : Picked <- refused.io(Picked, cat.picked.r(fs, bs2, target, path))
    cat.fetched(r, fs, p)

# show
# ----

def show.doc.r(+id: String, +digest: String, doc: Maybe<&2, String>) -> Result<&2, &2, Refused, String>:
  match doc:
    case None{}:
      Fail{Refused{1, String.take(id, 12n) ++ " names the content document " ++ digest ++ ", which this store does not hold yet"}}
    case Some{text}:
      Done{text}

def unparsable.of(ds: List<&2, Store.Doc>, +d: String) -> Maybe<&2, String>:
  unparsable.found(doc_found(ds, d))

# `show` prints a document it has read, so one that does not parse is
# refused, naming the file.
def show.read(bad: Maybe<&2, String>, r: Result<&2, &2, Refused, String>) -> Result<&2, &2, Refused, String>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{+text}:
      Maybe.default(&2, Result<&2, &2, Refused, String>, Maybe.map(&2, String, Result<&2, &2, Refused, String>, e => Fail{Refused{1, e}}, bad), Done{text})

def show.said.r(+id: String, +file: String, +ds: List<&2, Store.Doc>, s: Said) -> Result<&2, &2, Refused, String>:
  match s:
    case Nothing{}:
      Fail{Refused{1, String.take(id, 12n) ++ " did nothing to " ++ file}}
    case Whole{+d}:
      show.doc.r(id, d, doc_by_id(ds, d))
    case Edited{+d}:
      show.read(unparsable.of(ds, d), show.doc.r(id, d, doc_by_id(ds, d)))

# The file `show <target> <path>` names at the target.
def show.file.r(+fs: List<&2, Full>, +bs: List<&2, Bm.Bookmark>, +id: String, +p: String) -> Result<&2, &2, Refused, String>:
  do Result<&2, &2, Refused, String>:
    t : Tree.Tree() <- tree.r(fs, id)
    file_in.r(id, bs, p, t)

# What `show` prints is a document the store holds under the digest named:
# the revision's own, or the one it states for the file. `LAWS.show_prints_a_held_document`
# holds `show.doc.r` and `show.said.r` to it.
def doc.holds(ds: List<&2, Store.Doc>, +d: String, +text: String) -> Bool:
  match ds:
    case Nil{}:
      False{}
    case Store.Doc{p, +i, n, +t} <> rest:
      Bool.or(Bool.and(String.starts_with(i, d), String.eq(t, text)), doc.holds(rest, d, text))

def said.digest(s: Said) -> String:
  match s:
    case Whole{d}:
      d
    case Edited{d}:
      d
    case Nothing{}:
      SNil{}

def show.write(r: Result<&2, &2, Refused, String>) -> IO(Unit):
  do IO<Unit>:
    text : String <- refused.io(String, r)
    IO.write(text)

# An `edit` names an operation document, and a payload that happens to have
# its digest is not one.
def ops.only(ds: List<&2, Store.Doc>) -> List<&2, Store.Doc>:
  match ds:
    case Nil{}:
      Nil{}
    case Store.Doc{+path, +i, +size, +text} <> rest:
      +more = ops.only(rest)
      Bool.pick(List<&2, Store.Doc>, String.ends_with(path, ".ops.txt"), Store.Doc{path, i, size, text} <> more, more)

def show.docs(s: Said, +ds: List<&2, Store.Doc>) -> List<&2, Store.Doc>:
  match s:
    case Edited{d}:
      ops.only(ds)
    case _:
      ds

# A revision that said nothing about the file asked after is said so in the
# words the person used for it.
def show.nothing(+id: String, +p: String, s: Said) -> IO(Unit):
  match s:
    case Nothing{}:
      die(Unit, 1, String.take(id, 12n) ++ " said nothing about " ++ p ++ "; `show " ++ String.take(id, 12n) ++ "` lists what it did")
    case _:
      IO.pure(Unit, Unit{})

def show.of(+fs: List<&2, Full>, +bs: List<&2, Bm.Bookmark>, +root: String, +f: Full, path: Maybe<&2, String>) -> IO(Unit):
  match path:
    case None{}:
      do IO<Unit>:
        unread.io(SNil{}, unread(f))
        ds : List<&2, Store.Doc> <- Store.fetch(root, [id_of(f)])
        show.write(show.doc.r(id_of(f), id_of(f), doc_by_id(ds, id_of(f))))
    case Some{+p}:
      do IO<Unit>:
        unread.io(SNil{}, unread(f))
        readable(fs, [id_of(f)])
        file : String <- refused.io(String, show.file.r(fs, bs, id_of(f), p))
        +file2 : String = file
        +s : Said = said(facts_of(f), file2)
        show.nothing(id_of(f), p, s)
        ds : List<&2, Store.Doc> <- Store.fetch(root, said_digests(s))
        show.write(show.said.r(id_of(f), file2, show.docs(s, ds), s))

def show(+target: String, path: Maybe<&2, String>) -> IO(Unit):
  do IO<Unit>:
    root : String <- Store.root()
    +r : String = root
    rs : List<&2, Store.Doc> <- Store.revisions(r)
    +fs : List<&2, Full> = opened.fulls(r, rs)
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

def laid.all(+sign: String, items: List<&2, Ops.Item>) -> List<&2, Laid>:
  match items:
    case Nil{}:
      Nil{}
    case it <> rest:
      Laid{sign, it} <> laid.all(sign, rest)

# The document's operations walked over the parent as the cursor walks them
# (`cursor_spec.bend`): the parent's lines before each operation are
# context, an insert's items arrive, and a delete's run of the parent
# leaves. The parent's lines are laid in order and each once, whatever the
# document says (`LAWS.laid_keeps_parent`), and where the cursor reads the
# child, the lines that stay and arrive are the child (`LAWS.laid_reads_child`).
def laid.walk(ops: List<&2, Ops.Op>, +pos: Nat, +state: List<&2, Ops.Item>) -> List<&2, Laid>:
  match ops:
    case Nil{}:
      laid.all(" ", state)
    case Ops.Op{Ops.Insert{}, +at, items} <> rest:
      List.append(&2, Laid, laid.all(" ", List.take(&2, Ops.Item, state, Nat.sub(at, pos))),
        List.append(&2, Laid, laid.all("+", items),
          laid.walk(rest, Nat.max(pos, at), List.drop(&2, Ops.Item, state, Nat.sub(at, pos)))))
    case Ops.Op{Ops.Delete{}, +at, +items} <> rest:
      List.append(&2, Laid, laid.all(" ", List.take(&2, Ops.Item, state, Nat.sub(at, pos))),
        List.append(&2, Laid, laid.all("-", List.take(&2, Ops.Item, List.drop(&2, Ops.Item, state, Nat.sub(at, pos)), List.length(&2, Ops.Item, items))),
          laid.walk(rest, Nat.add(at, List.length(&2, Ops.Item, items)), List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, state, Nat.sub(at, pos)), List.length(&2, Ops.Item, items)))))

def laid(+before: List<&2, Ops.Item>, doc: Ops.Doc) -> List<&2, Laid>:
  match doc:
    case Ops.Doc{forgets, result, ops}:
      laid.walk(ops, 0n, before)

# Each side of what is laid: the parent's lines, context and removals; the
# lines that stay and arrive.
def laid.side(other: Bool, it: Ops.Item, rest: List<&2, Ops.Item>) -> List<&2, Ops.Item>:
  match other:
    case True{}:
      rest
    case False{}:
      it <> rest

def laid.old(ls: List<&2, Laid>) -> List<&2, Ops.Item>:
  match ls:
    case Nil{}:
      Nil{}
    case Laid{+sign, it} <> rest:
      laid.side(String.eq(sign, "+"), it, laid.old(rest))

def laid.new(ls: List<&2, Laid>) -> List<&2, Ops.Item>:
  match ls:
    case Nil{}:
      Nil{}
    case Laid{+sign, it} <> rest:
      laid.side(String.eq(sign, "-"), it, laid.new(rest))

# Hunks
# -----

# A line of the rendering and the colour it is drawn in where there is
# colour: bold for a fact about a file, cyan for a hunk's header, red and
# green for what left and arrived, nothing for context. Its text is kept as
# runs (`Piece`, under Emphasis below), one for most lines, so that a line
# replaced one for one can have the runs that differ marked inside its
# colour. Off, every line is its runs read as they are, the bytes it would
# be anyway, which is what `historica diff | patch` sees.
type Painted is Data:
  Painted{code: String, runs: List<&2, Piece>}

def painted.line(+code: String, text: String) -> Painted:
  Painted{code, [Piece{text, False{}}]}

def meta(text: String) -> Painted:
  painted.line("\u{1b}[1m", text)

def sign_code(+sign: String) -> String:
  Bool.pick(String, String.eq(sign, "-"), "\u{1b}[31m", Bool.pick(String, String.eq(sign, "+"), "\u{1b}[32m", SNil{}))

# A laid line with its line number on each side, counting from one.
type Numbered is Data:
  Numbered{laid: Laid, before: Nat, after: Nat}

def numbered.sign(n: Numbered) -> String:
  match n:
    case Numbered{l, b, a}:
      laid.sign(l)

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

# A hunk: the line it begins at on each side and how many of its lines that
# side holds, and the lines. A side holding none of them begins at the line
# before, which a hunk's context makes the start of the file.
type Hunk is Data:
  Hunk{old: Nat, olds: Nat, new: Nat, news: Nat, lines: List<&2, Numbered>}

def hunk.of(+ns: List<&2, Numbered>) -> Hunk:
  +bc = hunk.count(ns, "+")
  +ac = hunk.count(ns, "-")
  Hunk{hunk.side(bc, hunk.first(ns, True{})), bc, hunk.side(ac, hunk.first(ns, False{})), ac, ns}

# Three lines of context around each change: a line is shown where a change
# is within three lines of it, before or after, and each run of shown lines
# is a hunk — so two changes whose context would print a line twice share
# one. `owed` is how many lines after the last change are still its context.
def laid.changed(+sign: String) -> Bool:
  Bool.not(String.eq(sign, " "))

def changed.near(ls: List<&2, Laid>, k: Nat) -> Bool:
  match ls:
    case Nil{}:
      False{}
    case Laid{+sign, it} <> rest:
      match k:
        case 0n:
          False{}
        case 1n+j:
          Bool.or(laid.changed(sign), changed.near(rest, j))

def hunks.owed(changed: Bool, owed: Nat) -> Nat:
  match changed:
    case True{}:
      3n
    case False{}:
      Nat.sub(owed, 1n)

def hunks.showing(changed: Bool, owed: Nat, near: Bool) -> Bool:
  Bool.or(changed, Bool.or(Nat.is_gt(owed, 0n), near))

# The shown lines from here up to the first that is not, and the hunks after
# it.
type Cut is Data:
  Cut{lines: List<&2, Numbered>, after: List<&2, Hunk>}

def hunks.close(ns: List<&2, Numbered>, hs: List<&2, Hunk>) -> List<&2, Hunk>:
  match ns:
    case Nil{}:
      hs
    case n <> rest:
      hunk.of(n <> rest) <> hs

def cut.step(n: Numbered, shown: Bool, c: Cut) -> Cut:
  match shown:
    case True{}:
      match c:
        case Cut{ns, hs}:
          Cut{n <> ns, hs}
    case False{}:
      match c:
        case Cut{ns, hs}:
          Cut{Nil{}, hunks.close(ns, hs)}

# Each line numbered on each side, counting from one.
def hunks.walk(ls: List<&2, Laid>, +b: Nat, +a: Nat, +owed: Nat) -> Cut:
  match ls:
    case Nil{}:
      Cut{Nil{}, Nil{}}
    case Laid{+sign, it} <> +rest:
      cut.step(Numbered{Laid{sign, it}, b, a}, hunks.showing(laid.changed(sign), owed, changed.near(rest, 3n)),
        hunks.walk(rest, Bool.pick(Nat, String.eq(sign, "+"), b, 1n+b), Bool.pick(Nat, String.eq(sign, "-"), a, 1n+a), hunks.owed(laid.changed(sign), owed)))

def cut.close(c: Cut) -> List<&2, Hunk>:
  match c:
    case Cut{ns, hs}:
      hunks.close(ns, hs)

def hunks.made(ls: List<&2, Laid>) -> List<&2, Hunk>:
  cut.close(hunks.walk(ls, 1n, 1n, 0n))

# One line of a comparison, and the marker after one that ends without a
# newline.
def laid.text(+sign: String, it: Ops.Item) -> List<&2, Painted>:
  match it:
    case Ops.Item{t, True{}, f}:
      [painted.line(sign_code(sign), sign ++ Ops.shown(Ops.Item{t, True{}, f}))]
    case Ops.Item{t, False{}, f}:
      [painted.line(sign_code(sign), sign ++ Ops.shown(Ops.Item{t, False{}, f})), painted.line(sign_code(sign), "\\ no newline at end of file")]

# Emphasis
# --------

# Where two lines replaced one for one differ, drawn in inverse video inside
# the line's own colour — only when there is colour, since emphasis has no
# plain-text spelling that would not change the bytes. A line is cut into
# words: a run of letters and digits is one, and every other character is
# one on its own. The words are compared with `similar`'s Myers, as the
# Rust tool compares them, and a pair that shares no word but whitespace, or
# more than 1024 words on a side, is left plain.
type Words is Data:
  Words{run: String, acc: List<&2, String>}

def words.flush(+run: String, +acc: List<&2, String>) -> List<&2, String>:
  Bool.pick(List<&2, String>, String.is_empty(run), acc, String.reverse(run) <> acc)

def words.char(w: Words, +c: Char, lettered: Bool) -> Words:
  match w:
    case Words{+run, +acc}:
      match lettered:
        case True{}:
          Words{SCon{c, run}, acc}
        case False{}:
          Words{SNil{}, SCon{c, SNil{}} <> words.flush(run, acc)}

def words.go(s: String, w: Words) -> Words:
  match s:
    case SNil{}:
      w
    case SCon{+c, t}:
      words.go(t, words.char(w, c, Uni.is_alnum(c)))

def words.done(w: Words) -> List<&2, String>:
  match w:
    case Words{run, acc}:
      List.reverse(&2, String, words.flush(run, acc))

def words(s: String) -> List<&2, String>:
  words.done(words.go(s, Words{SNil{}, Nil{}}))

# The operations, grouped as the `Replace` hook groups them: a shared run,
# or everything between two shared runs.
type Chunk is Data:
  Chunk.Keep{len: Nat}
  Chunk.Change{lost: Nat, gained: Nat}

def chunks.close(+lost: Nat, +gained: Nat, +acc: List<&2, Chunk>) -> List<&2, Chunk>:
  Bool.pick(List<&2, Chunk>, Nat.is_eq(Nat.add(lost, gained), 0n), acc, Chunk.Change{lost, gained} <> acc)

def chunks.go(ops: List<&2, Sim.Op>, +lost: Nat, +gained: Nat, acc: List<&2, Chunk>) -> List<&2, Chunk>:
  match ops:
    case Nil{}:
      List.reverse(&2, Chunk, chunks.close(lost, gained, acc))
    case Sim.Same{o, n, len} <> rest:
      chunks.go(rest, 0n, 0n, Chunk.Keep{U32.to_nat(len)} <> chunks.close(lost, gained, acc))
    case Sim.Lose{o, len, n} <> rest:
      chunks.go(rest, Nat.add(lost, U32.to_nat(len)), gained, acc)
    case Sim.Gain{o, n, len} <> rest:
      chunks.go(rest, lost, Nat.add(gained, U32.to_nat(len)), acc)

# A word that is not whitespace: what `!word.trim().is_empty()` asks of one.
def word.solid(w: String) -> Bool:
  match w:
    case SCon{c, SNil{}}:
      Bool.not(Folder.is_ws(c))
    case _:
      True{}

def shared.go(cs: List<&2, Chunk>, ws: List<&2, String>) -> Bool:
  match cs:
    case Nil{}:
      False{}
    case Chunk.Keep{+n} <> rest:
      +ws2 = ws
      Bool.or(List.any(~&2, ~String, ~word.solid, List.take(&2, String, ws2, n)), shared.go(rest, List.drop(&2, String, ws2, n)))
    case Chunk.Change{l, g} <> rest:
      shared.go(rest, List.drop(&2, String, ws, l))

def changed(cs: List<&2, Chunk>) -> Bool:
  match cs:
    case Nil{}:
      False{}
    case Chunk.Keep{n} <> rest:
      changed(rest)
    case Chunk.Change{l, g} <> rest:
      True{}

def joined.all(ws: List<&2, String>) -> String:
  match ws:
    case Nil{}:
      SNil{}
    case w <> rest:
      w ++ joined.all(rest)

# A run of a marked line: its text, and whether it is drawn in inverse
# video. The runs of a line are the line (`LAWS.emphasis_keeps_was`).
type Piece is Data:
  Piece{text: String, strong: Bool}

def piece.show(p: Piece) -> String:
  match p:
    case Piece{+t, True{}}:
      Bool.pick(String, String.is_empty(t), SNil{}, "\u{1b}[7m" ++ t ++ "\u{1b}[27m")
    case Piece{t, False{}}:
      t

def pieces.show(ps: List<&2, Piece>) -> String:
  match ps:
    case Nil{}:
      SNil{}
    case p <> rest:
      piece.show(p) ++ pieces.show(rest)

def pieces.text(ps: List<&2, Piece>) -> String:
  match ps:
    case Nil{}:
      SNil{}
    case Piece{t, s} <> rest:
      t ++ pieces.text(rest)

# One side's line with its differing runs marked: the old side's losses, or
# the new side's gains.
def marked.go(cs: List<&2, Chunk>, ws: List<&2, String>, +old: Bool) -> List<&2, Piece>:
  match cs:
    case Nil{}:
      [Piece{joined.all(ws), False{}}]
    case Chunk.Keep{+n} <> rest:
      +ws2 = ws
      Piece{joined.all(List.take(&2, String, ws2, n)), False{}} <> marked.go(rest, List.drop(&2, String, ws2, n), old)
    case Chunk.Change{+l, +g} <> rest:
      +ws2 = ws
      +n = Bool.pick(Nat, old, l, g)
      Piece{joined.all(List.take(&2, String, ws2, n)), True{}} <> marked.go(rest, List.drop(&2, String, ws2, n), old)

type Marked is Data:
  Marked{was: List<&2, Piece>, now: List<&2, Piece>}

def apart.chunks(+old: List<&2, String>, +new: List<&2, String>, +cs: List<&2, Chunk>) -> Maybe<&2, Marked>:
  Bool.pick(Maybe<&2, Marked>, Bool.and(shared.go(cs, old), changed(cs)), Some{Marked{marked.go(cs, old, True{}), marked.go(cs, new, False{})}}, None{})

def apart.of(+old: List<&2, String>, +new: List<&2, String>, short: Bool) -> Maybe<&2, Marked>:
  match short:
    case False{}:
      None{}
    case True{}:
      apart.chunks(old, new, chunks.go(Sim.myers.words(old, new), 0n, 0n, Nil{}))

def apart(was: String, now: String) -> Maybe<&2, Marked>:
  +old = words(was)
  +new = words(now)
  apart.of(old, new, Bool.and(Nat.is_le(List.length(&2, String, old), 1024n), Nat.is_le(List.length(&2, String, new), 1024n)))

# Pairing: a run of removals followed by as many arrivals is replaced one
# for one, and pairs up without anybody guessing which line became which;
# an unequal run has no such pairing and is left plain.
def head_is(ns: List<&2, Numbered>, +sign: String) -> Bool:
  match ns:
    case Nil{}:
      False{}
    case n <> rest:
      String.eq(numbered.sign(n), sign)

# A run of lines with one mark, and the lines after it. `hit` is whether
# the first has the mark.
type Run is Data:
  Run{lines: List<&2, Numbered>, rest: List<&2, Numbered>}

def run.cons(n: Numbered, r: Run) -> Run:
  match r:
    case Run{ns, rest}:
      Run{n <> ns, rest}

def run.split(ns: List<&2, Numbered>, +sign: String, hit: Bool) -> Run:
  match ns:
    case Nil{}:
      Run{Nil{}, Nil{}}
    case n <> +rest:
      match hit:
        case False{}:
          Run{Nil{}, n <> rest}
        case True{}:
          run.cons(n, run.split(rest, sign, head_is(rest, sign)))

def numbered.shown(n: Numbered) -> String:
  match n:
    case Numbered{Laid{s, it}, b, a}:
      Ops.shown(it)

# A line's mark: its runs, where it has them.
def mark.was(m: Maybe<&2, Marked>) -> Maybe<&2, List<&2, Piece>>:
  match m:
    case Some{Marked{w, n}}:
      Some{w}
    case None{}:
      None{}

def mark.now(m: Maybe<&2, Marked>) -> Maybe<&2, List<&2, Piece>>:
  match m:
    case Some{Marked{w, n}}:
      Some{n}
    case None{}:
      None{}

# Each removal with the arrival at the same place in its run.
def pairs(rem: List<&2, Numbered>, arr: List<&2, Numbered>) -> List<&2, Maybe<&2, Marked>>:
  match rem arr:
    case r <> rs a <> more:
      apart(numbered.shown(r), numbered.shown(a)) <> pairs(rs, more)
    case _ _:
      Nil{}

def marks.was(ps: List<&2, Maybe<&2, Marked>>) -> List<&2, Maybe<&2, List<&2, Piece>>>:
  match ps:
    case Nil{}:
      Nil{}
    case p <> rest:
      mark.was(p) <> marks.was(rest)

def marks.now(ps: List<&2, Maybe<&2, Marked>>) -> List<&2, Maybe<&2, List<&2, Piece>>>:
  match ps:
    case Nil{}:
      Nil{}
    case p <> rest:
      mark.now(p) <> marks.now(rest)

def marks.none(ns: List<&2, Numbered>) -> List<&2, Maybe<&2, List<&2, Piece>>>:
  match ns:
    case Nil{}:
      Nil{}
    case n <> rest:
      None{} <> marks.none(rest)

# The marks of a stretch of lines, and the lines after it.
type Chunked is Data:
  Chunked{marks: List<&2, Maybe<&2, List<&2, Piece>>>, after: List<&2, Numbered>}

def chunked.marks(c: Chunked) -> List<&2, Maybe<&2, List<&2, Piece>>>:
  match c:
    case Chunked{ms, a}:
      ms

def chunked.after(c: Chunked) -> List<&2, Numbered>:
  match c:
    case Chunked{ms, a}:
      a

def emph.pair(paired: Bool, +rem: List<&2, Numbered>, +arr: List<&2, Numbered>, rest: List<&2, Numbered>) -> Chunked:
  match paired:
    case True{}:
      +ps = pairs(rem, arr)
      Chunked{List.append(&2, Maybe<&2, List<&2, Piece>>, marks.was(ps), marks.now(ps)), rest}
    case False{}:
      Chunked{marks.none(List.append(&2, Numbered, rem, arr)), rest}

def emph.arrivals(+rem: List<&2, Numbered>, r: Run) -> Chunked:
  match r:
    case Run{+arr, rest}:
      emph.pair(Bool.and(Nat.is_gt(List.length(&2, Numbered, rem), 0n), Nat.is_eq(List.length(&2, Numbered, rem), List.length(&2, Numbered, arr))), rem, arr, rest)

def emph.removals(r: Run) -> Chunked:
  match r:
    case Run{rem, +after}:
      emph.arrivals(rem, run.split(after, "+", head_is(after, "+")))

# A run of removals and the arrivals after it, or one line that is neither.
def emph.step(changed: Bool, n: Numbered, +rest: List<&2, Numbered>) -> Chunked:
  match changed:
    case True{}:
      +all = {n <> rest : List<&2, Numbered>}
      emph.removals(run.split(all, "-", head_is(all, "-")))
    case False{}:
      Chunked{[None{}], rest}

def emph.go(fuel: Nat, ns: List<&2, Numbered>) -> List<&2, Maybe<&2, List<&2, Piece>>>:
  match fuel ns:
    case 0n _:
      Nil{}
    case 1n+q Nil{}:
      Nil{}
    case 1n+q +n <> +rest:
      +c = emph.step(laid.changed(numbered.sign(n)), n, rest)
      List.append(&2, Maybe<&2, List<&2, Piece>>, chunked.marks(c), emph.go(q, chunked.after(c)))

# Each line's marked runs where it has them; nothing to compute without
# colour.
def emph(+ns: List<&2, Numbered>, paint: Bool) -> List<&2, Maybe<&2, List<&2, Piece>>>:
  match paint:
    case True{}:
      emph.go(1n+List.length(&2, Numbered, ns), ns)
    case False{}:
      Nil{}

# A mark is its own line's: the runs it draws read as that line, and only a
# removal or an arrival has one (`LAWS.emphasis_marks_its_own_line`).
def mark.fits(+n: Numbered, m: Maybe<&2, List<&2, Piece>>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{ps}:
      Bool.and(String.eq(pieces.text(ps), numbered.shown(n)), laid.changed(numbered.sign(n)))

def marks.fit(ns: List<&2, Numbered>, ms: List<&2, Maybe<&2, List<&2, Piece>>>) -> Bool:
  match ns ms:
    case n <> nr m <> mr:
      Bool.and(mark.fits(n, m), marks.fit(nr, mr))
    case _ _:
      True{}

def laid.marked.of(+sign: String, it: Ops.Item, ps: List<&2, Piece>) -> List<&2, Painted>:
  match it:
    case Ops.Item{x, True{}, f}:
      [Painted{sign_code(sign), Piece{sign, False{}} <> ps}]
    case Ops.Item{x, False{}, f}:
      [Painted{sign_code(sign), Piece{sign, False{}} <> ps}, painted.line(sign_code(sign), "\\ no newline at end of file")]

def laid.marked(+sign: String, it: Ops.Item, m: Maybe<&2, List<&2, Piece>>) -> List<&2, Painted>:
  match m:
    case None{}:
      laid.text(sign, it)
    case Some{ps}:
      laid.marked.of(sign, it, ps)

def hunk.lines(ns: List<&2, Numbered>, marks: List<&2, Maybe<&2, List<&2, Piece>>>) -> List<&2, Painted>:
  match ns marks:
    case Nil{} _:
      Nil{}
    case Numbered{Laid{sign, it}, b, a} <> rest m <> ms:
      List.append(&2, Painted, laid.marked(sign, it, m), hunk.lines(rest, ms))
    case Numbered{Laid{sign, it}, b, a} <> rest Nil{}:
      List.append(&2, Painted, laid.text(sign, it), hunk.lines(rest, Nil{}))

def hunk.header(o: Nat, oc: Nat, n: Nat, nc: Nat) -> Painted:
  painted.line("\u{1b}[36m", "@@ -" ++ Nat.show(o) ++ "," ++ Nat.show(oc) ++ " +" ++ Nat.show(n) ++ "," ++ Nat.show(nc) ++ " @@")

def hunk.shown(+paint: Bool, h: Hunk) -> List<&2, Painted>:
  match h:
    case Hunk{o, oc, n, nc, +ns}:
      hunk.header(o, oc, n, nc) <> hunk.lines(ns, emph(ns, paint))

def hunks.shown(+paint: Bool, hs: List<&2, Hunk>) -> List<&2, Painted>:
  match hs:
    case Nil{}:
      Nil{}
    case h <> rest:
      List.append(&2, Painted, hunk.shown(paint, h), hunks.shown(paint, rest))

def hunks(+paint: Bool, ls: List<&2, Laid>) -> List<&2, Painted>:
  hunks.shown(paint, hunks.made(ls))

# What `patch` makes of them
# --------------------------

# The hunks, read back as `patch` reads a unified diff, without fuzz: each
# is found at the line its header names on each side, the parent's lines
# before it copied; its context and removals are read off the parent as it
# stands there and its context and arrivals written, and the header's
# counts are how many lines each side holds; whatever follows the last hunk
# is copied. A hunk anywhere but its own line, a line that is not the
# parent's, or a count that is wrong is refused. `LAWS.diff_hunks_apply`
# says what diff prints this way takes the parent to the child.
type Skipped is Data:
  Skipped{copied: List<&2, Ops.Item>, rest: List<&2, Ops.Item>}

type Patched is Data:
  Patched{rest: List<&2, Ops.Item>, out: List<&2, Ops.Item>, took: Nat, gave: Nat}

# The line a hunk's side begins at: the line after, where it holds none.
def patch.from(+first: Nat, +count: Nat) -> Nat:
  Bool.pick(Nat, Nat.is_eq(count, 0n), 1n+first, first)

def patch.end(here: Bool, both: Bool) -> Result<&2, &2, String, Skipped>:
  match here both:
    case True{} True{}:
      Done{Skipped{Nil{}, Nil{}}}
    case _ _:
      Fail{"a hunk is not where its header says"}

def patch.here(here: Bool, both: Bool, p: Ops.Item, ps: List<&2, Ops.Item>, r: Result<&2, &2, String, Skipped>) -> Result<&2, &2, String, Skipped>:
  match here:
    case True{}:
      match both:
        case True{}:
          Done{Skipped{Nil{}, p <> ps}}
        case False{}:
          Fail{"a hunk is not where its header says"}
    case False{}:
      match r:
        case Done{Skipped{c, rest}}:
          Done{Skipped{p <> c, rest}}
        case Fail{e}:
          Fail{e}

# Copying the parent up to the line a hunk begins at on each side, `at` and
# `nat` numbering the next line of the parent and of what is written.
def patch.skip(parent: List<&2, Ops.Item>, +at: Nat, +nat: Nat, +so: Nat, +sn: Nat) -> Result<&2, &2, String, Skipped>:
  match parent:
    case Nil{}:
      patch.end(Nat.is_eq(so, at), Nat.is_eq(sn, nat))
    case +p <> +ps:
      patch.here(Nat.is_eq(so, at), Nat.is_eq(sn, nat), p, ps, patch.skip(ps, 1n+at, 1n+nat, so, sn))

def patch.same(eq: Bool, keep: Bool, it: Ops.Item, ps: List<&2, Ops.Item>, out: List<&2, Ops.Item>, +took: Nat, +gave: Nat) -> Result<&2, &2, String, Patched>:
  match eq:
    case False{}:
      Fail{"a line of a hunk is not the parent's"}
    case True{}:
      match keep:
        case True{}:
          Done{Patched{ps, List.append(&2, Ops.Item, out, [it]), 1n+took, 1n+gave}}
        case False{}:
          Done{Patched{ps, out, 1n+took, gave}}

def patch.read(+it: Ops.Item, keep: Bool, st: Patched) -> Result<&2, &2, String, Patched>:
  match st:
    case Patched{parent, out, took, gave}:
      match parent:
        case Nil{}:
          Fail{"a hunk reads past the parent"}
        case p <> ps:
          patch.same(item_eq(p, it), keep, it, ps, out, took, gave)

def patch.sign(plus: Bool, minus: Bool, space: Bool, +it: Ops.Item, st: Patched) -> Result<&2, &2, String, Patched>:
  match plus:
    case True{}:
      match st:
        case Patched{parent, out, took, gave}:
          Done{Patched{parent, List.append(&2, Ops.Item, out, [it]), took, 1n+gave}}
    case False{}:
      match minus:
        case True{}:
          patch.read(it, False{}, st)
        case False{}:
          match space:
            case True{}:
              patch.read(it, True{}, st)
            case False{}:
              Fail{"a line of a hunk is marked neither ' ', '-' nor '+'"}

def patch.line(n: Numbered, st: Patched) -> Result<&2, &2, String, Patched>:
  match n:
    case Numbered{Laid{+sign, it}, b, a}:
      patch.sign(String.eq(sign, "+"), String.eq(sign, "-"), String.eq(sign, " "), it, st)

def patch.line.then(n: Numbered, r: Result<&2, &2, String, Patched>) -> Result<&2, &2, String, Patched>:
  match r:
    case Done{st}:
      patch.line(n, st)
    case Fail{e}:
      Fail{e}

def patch.lines(ns: List<&2, Numbered>, r: Result<&2, &2, String, Patched>) -> Result<&2, &2, String, Patched>:
  match ns:
    case Nil{}:
      r
    case n <> rest:
      patch.lines(rest, patch.line.then(n, r))

# Where the reading stands between hunks: what is left of the parent, what
# is written, and the numbers of the next line of each.
type Patching is Data:
  Patching{parent: List<&2, Ops.Item>, out: List<&2, Ops.Item>, at: Nat, nat: Nat}

def patch.check(ok: Bool, st: Patching) -> Result<&2, &2, String, Patching>:
  match ok:
    case True{}:
      Done{st}
    case False{}:
      Fail{"a hunk's header miscounts its lines"}

def patch.done(p: Result<&2, &2, String, Patched>, +olds: Nat, +news: Nat, +out: List<&2, Ops.Item>, +at: Nat, +nat: Nat) -> Result<&2, &2, String, Patching>:
  match p:
    case Done{Patched{rest, o, +took, +gave}}:
      patch.check(Bool.and(Nat.is_eq(took, olds), Nat.is_eq(gave, news)), Patching{rest, List.append(&2, Ops.Item, out, o), at, nat})
    case Fail{e}:
      Fail{e}

def patch.hunk(s: Result<&2, &2, String, Skipped>, ls: List<&2, Numbered>, +out: List<&2, Ops.Item>, +olds: Nat, +news: Nat, +so: Nat, +sn: Nat) -> Result<&2, &2, String, Patching>:
  match s:
    case Done{Skipped{copied, rest}}:
      patch.done(patch.lines(ls, Done{Patched{rest, Nil{}, 0n, 0n}}), olds, news, List.append(&2, Ops.Item, out, copied), Nat.add(so, olds), Nat.add(sn, news))
    case Fail{e}:
      Fail{e}

def patch.step(h: Hunk, st: Patching) -> Result<&2, &2, String, Patching>:
  match h:
    case Hunk{+o, +oc, +n, +nc, ls}:
      match st:
        case Patching{parent, out, +at, +nat}:
          patch.hunk(patch.skip(parent, at, nat, patch.from(o, oc), patch.from(n, nc)), ls, out, oc, nc, patch.from(o, oc), patch.from(n, nc))

def patch.then(h: Hunk, r: Result<&2, &2, String, Patching>) -> Result<&2, &2, String, Patching>:
  match r:
    case Done{st}:
      patch.step(h, st)
    case Fail{e}:
      Fail{e}

def patch.go(hs: List<&2, Hunk>, r: Result<&2, &2, String, Patching>) -> Result<&2, &2, String, List<&2, Ops.Item>>:
  match hs:
    case Nil{}:
      match r:
        case Done{Patching{parent, out, at, nat}}:
          Done{List.append(&2, Ops.Item, out, parent)}
        case Fail{e}:
          Fail{e}
    case h <> more:
      patch.go(more, patch.then(h, r))

def patch(parent: List<&2, Ops.Item>, hs: List<&2, Hunk>) -> Result<&2, &2, String, List<&2, Ops.Item>>:
  patch.go(hs, Done{Patching{parent, Nil{}, 1n, 1n}})

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

def render.hunks(+paint: Bool, +left: String, +right: String, +before: List<&2, Ops.Item>, d: Maybe<&2, Ops.Doc>) -> List<&2, Painted>:
  match d:
    case None{}:
      Nil{}
    case Some{doc}:
      meta("--- " ++ left) <> meta("+++ " ++ right) <> hunks(paint, laid(before, doc))

# The same decomposition `record` would write down, rendered: `similar`'s
# Histogram diff, which `Sim` ports.
def render.content(+paint: Bool, +left: String, +right: String, before: Maybe<&2, List<&2, Ops.Item>>, after: Maybe<&2, List<&2, Ops.Item>>, +whole: String) -> List<&2, Painted>:
  match before after:
    case Some{+b} Some{a}:
      render.hunks(paint, left, right, b, Sim.diff(b, a))
    case _ _:
      [meta("--- " ++ left), meta("+++ " ++ right), meta("binary files differ:" ++ whole)]

def render(+paint: Bool, p: Compared) -> List<&2, Painted>:
  match p:
    case Compared{+from, +to, +before, +after, modes, targets}:
      +path = Maybe.default(&2, String, Maybe.or(&2, String, to, from), "?")
      List.append(&2, Painted, render.facts(from, to), List.append(&2, Painted, render.mode(path, modes), List.append(&2, Painted, render.link(path, targets),
        render.content(paint, Maybe.default(&2, String, Maybe.map(&2, String, String, x => "a/" ++ x, from), "/dev/null"), Maybe.default(&2, String, Maybe.map(&2, String, String, x => "b/" ++ x, to), "/dev/null"),
          side.lines(before), side.lines(after), binary.side(before) ++ " ->" ++ binary.side(after)))))

def diff.rendered(+paint: Bool, ps: List<&2, Compared>) -> List<&2, Painted>:
  match ps:
    case Nil{}:
      Nil{}
    case p <> rest:
      List.append(&2, Painted, render(paint, p), diff.rendered(paint, rest))

# A line as printed: with colour, its runs drawn with the marks they have
# and the whole in its colour; without, its runs as they are.
def painted(+paint: Bool, p: Painted) -> String:
  match paint:
    case True{}:
      match p:
        case Painted{+code, runs}:
          +text = pieces.show(runs)
          Bool.pick(String, String.is_empty(code), text, code ++ text ++ "\u{1b}[0m")
    case False{}:
      match p:
        case Painted{code, runs}:
          pieces.text(runs)

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
      print_painted(paint, diff.rendered(paint, some))

# The command
# -----------

# What `diff` was asked: `--onto`, `--color`, and the rest in order.
type DiffAsked is Data:
  DiffAsked{onto: Maybe<&2, String>, color: String, rest: List<&2, String>}

def dasked.onto(a: DiffAsked, v: String) -> DiffAsked:
  match a:
    case DiffAsked{o, c, r}:
      DiffAsked{Some{v}, c, r}

def dasked.word(a: DiffAsked, w: String) -> DiffAsked:
  match a:
    case DiffAsked{o, c, r}:
      DiffAsked{o, c, List.append(&2, String, r, [w])}

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

# What the word before asked of this one: nothing, or to be the value of
# `--onto` or of `--color`.
type DWant is Data:
  DWant.No{}
  DWant.Onto{}
  DWant.Color{}

# The arguments read in one pass: what has been read, and what the word
# before asked of this one.
type DRead is Data:
  DRead{asked: Result<&2, &2, String, DiffAsked>, want: DWant}

def dasked.plain(a: DiffAsked, +w: String, onto: Bool, color: Bool) -> DRead:
  match onto:
    case True{}:
      DRead{Done{a}, DWant.Onto{}}
    case False{}:
      match color:
        case True{}:
          DRead{Done{a}, DWant.Color{}}
        case False{}:
          DRead{dasked.other(a, w, T.strip_prefix(w, "--color=")), DWant.No{}}

def dasked.done(a: DiffAsked, +w: String, want: DWant) -> DRead:
  match want:
    case DWant.No{}:
      dasked.plain(a, w, String.eq(w, "--onto"), String.eq(w, "--color"))
    case DWant.Onto{}:
      DRead{Done{dasked.onto(a, w)}, DWant.No{}}
    case DWant.Color{}:
      DRead{dasked.color(a, w, color_ok(w)), DWant.No{}}

def dasked.eat(r: DRead, +w: String) -> DRead:
  match r:
    case DRead{Fail{e}, want}:
      DRead{Fail{e}, want}
    case DRead{Done{a}, want}:
      dasked.done(a, w, want)

def dasked.run(args: List<&2, String>, r: DRead) -> DRead:
  match args:
    case Nil{}:
      r
    case w <> rest:
      dasked.run(rest, dasked.eat(r, w))

def dasked.end.of(a: DiffAsked, want: DWant) -> Result<&2, &2, String, DiffAsked>:
  match want:
    case DWant.No{}:
      Done{a}
    case DWant.Onto{}:
      Fail{"`--onto` wants a value"}
    case DWant.Color{}:
      Fail{"`--color` wants `auto`, `always`, or `never`"}

def dasked.end(r: DRead) -> Result<&2, &2, String, DiffAsked>:
  match r:
    case DRead{Fail{e}, want}:
      Fail{e}
    case DRead{Done{a}, want}:
      dasked.end.of(a, want)

def dasked.go(args: List<&2, String>) -> Result<&2, &2, String, DiffAsked>:
  dasked.end(dasked.run(args, DRead{Done{DiffAsked{None{}, "auto", Nil{}}}, DWant.No{}}))

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

def sole_parent.r(+id: String, ps: List<&2, String>) -> Result<&2, &2, Refused, Maybe<&2, String>>:
  match ps:
    case Nil{}:
      Done{None{}}
    case p <> Nil{}:
      Done{Some{p}}
    case +several:
      Fail{Refused{1, String.take(id, 12n) ++ " is a merge, so what it did depends on which side you are asking about; name one with --onto:" ++ sole_parent.named(id, several)}}

def onto.r(+fs: List<&2, Full>, +bs: List<&2, Bm.Bookmark>, +t: String) -> Result<&2, &2, Refused, Maybe<&2, String>>:
  do Result<&2, &2, Refused, Maybe<&2, String>>:
    f : Full <- resolved.r(fs, bs, t)
    return Some{id_of(f)}

# What a revision is compared with: what `--onto` names, or its one parent.
def diff.left.r(+fs: List<&2, Full>, +bs: List<&2, Bm.Bookmark>, +right: Full, onto: Maybe<&2, String>) -> Result<&2, &2, Refused, Maybe<&2, String>>:
  match onto:
    case Some{+t}:
      onto.r(fs, bs, t)
    case None{}:
      sole_parent.r(id_of(right), parents_of(right))

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

def diff.limit.tree(+bs: List<&2, Bm.Bookmark>, +right: String, +sp: String, +t: Tree.Tree()) -> Result<&2, &2, Refused, Limit>:
  do Result<&2, &2, Refused, Limit>:
    f : String <- file_in.r(right, bs, sp, t)
    return Limit.File{f}

def diff.limit.file.r(+fs: List<&2, Full>, +bs: List<&2, Bm.Bookmark>, +right: String, +sp: String) -> Result<&2, &2, Refused, Limit>:
  do Result<&2, &2, Refused, Limit>:
    t : Tree.Tree() <- tree.r(fs, right)
    diff.limit.tree(bs, right, sp, t)

def diff.limit.spelled(+fs: List<&2, Full>, +bs: List<&2, Bm.Bookmark>, +right: String, +sp: String, file: Bool) -> Result<&2, &2, Refused, Limit>:
  match file:
    case True{}:
      diff.limit.file.r(fs, bs, right, sp)
    case False{}:
      Done{Limit.Path{Maybe.default(&2, String, T.strip_prefix(sp, "path:"), sp)}}

def diff.limit.r(+fs: List<&2, Full>, +bs: List<&2, Bm.Bookmark>, +right: String, only: Maybe<&2, String>) -> Result<&2, &2, Refused, Limit>:
  match only:
    case None{}:
      Done{Limit.None{}}
    case Some{+sp}:
      diff.limit.spelled(fs, bs, right, sp, String.starts_with(sp, "file:"))

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

def both(xs: List<&2, Tree.Entry>, ys: List<&2, Tree.Entry>) -> List<&2, Both>:
  +xs2 = List.sort(~Tree.Entry, ~(a => b => String.is_le(Tree.entry_file(a), Tree.entry_file(b))), xs)
  +ys2 = List.sort(~Tree.Entry, ~(a => b => String.is_le(Tree.entry_file(a), Tree.entry_file(b))), ys)
  both.go(1n+Nat.add(List.length(&2, Tree.Entry, xs2), List.length(&2, Tree.Entry, ys2)), xs2, ys2, both.cmp(xs2, ys2))

# What `diff` pairs, file by file: the pairs `both` lists under one file are
# the entries each side holds under it, paired in order as far as either
# goes (`LAWS.diff_pairs_each_file`) — so where each side holds a file once,
# `diff` compares it once, with each side's entry for it.
def entries.at(+f: String, xs: List<&2, Tree.Entry>) -> List<&2, Tree.Entry>:
  match xs:
    case Nil{}:
      Nil{}
    case +x <> +rest:
      Bool.pick(List<&2, Tree.Entry>, String.eq(Tree.entry_file(x), f), x <> entries.at(f, rest), entries.at(f, rest))

def both.at(+f: String, bs: List<&2, Both>) -> List<&2, Both>:
  match bs:
    case Nil{}:
      Nil{}
    case Both{+file, was, now} <> +rest:
      Bool.pick(List<&2, Both>, String.eq(file, f), Both{file, was, now} <> both.at(f, rest), both.at(f, rest))

def both.zip(+f: String, was: List<&2, Tree.Entry>, now: List<&2, Tree.Entry>) -> List<&2, Both>:
  match was now:
    case w <> ws n <> ns:
      Both{f, Some{w}, Some{n}} <> both.zip(f, ws, ns)
    case w <> ws Nil{}:
      Both{f, Some{w}, None{}} <> both.zip(f, ws, Nil{})
    case Nil{} n <> ns:
      Both{f, None{}, Some{n}} <> both.zip(f, Nil{}, ns)
    case Nil{} Nil{}:
      Nil{}

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

# What `diff` shows: only files whose two sides differ, and under a path
# limit only a file at that path on one side or the other.
# `LAWS.diff_shows_what_differs` holds `compare` to it.
def limit.shows(l: Limit, c: Compared) -> Bool:
  match l:
    case Limit.None{}:
      True{}
    case Limit.File{f}:
      True{}
    case Limit.Path{+p}:
      match c:
        case Compared{from, to, b, a, m, t}:
          Bool.or(maybe_eq(from, Some{p}), maybe_eq(to, Some{p}))

def all.shown(+l: Limit, cs: List<&2, Compared>) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case +c <> rest:
      Bool.and(Bool.and(pair.differs(c), limit.shows(l, c)), all.shown(l, rest))

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

# Where `LAWS.diff_sizes_what_the_host_stated` looks. The host states a
# size for a digest where it answered a line beginning with that digest,
# the size after it.
def nat.is(m: Maybe<&2, Nat>, +n: Nat) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{k}:
      Nat.is_eq(k, n)

def stat.says(stats: List<&2, String>, +d: String, +n: Nat) -> Bool:
  match stats:
    case Nil{}:
      False{}
    case +st <> rest:
      Bool.or(Bool.and(String.eq(T.word(st), d), nat.is(Nat.read(String.drop(st, 65n)), n)), stat.says(rest, d, n))

# Two sides hold the same: the same lines, or the same digest and size.
def size.same(m: Maybe<&2, Nat>, k: Maybe<&2, Nat>) -> Bool:
  match m k:
    case None{} None{}:
      True{}
    case Some{a} Some{b}:
      Nat.is_eq(a, b)
    case _ _:
      False{}

def side.same(s: Maybe<&2, Side>, t: Maybe<&2, Side>) -> Bool:
  match s t:
    case None{} None{}:
      True{}
    case Some{Side.Lines{a}} Some{Side.Lines{b}}:
      items_eq(a, b)
    case Some{Side.Whole{d, m}} Some{Side.Whole{e, k}}:
      Bool.and(String.eq(d, e), size.same(m, k))
    case _ _:
      False{}

# A side whose size was unknown keeps its digest, and has a size only where
# the host stated one for that digest; any other side is as it was.
def side.given(+stats: List<&2, String>, +d: String, t: Maybe<&2, Side>) -> Bool:
  match t:
    case Some{Side.Whole{e, None{}}}:
      String.eq(d, e)
    case Some{Side.Whole{e, Some{+n}}}:
      Bool.and(String.eq(d, e), stat.says(stats, d, n))
    case _:
      False{}

def side.told(+stats: List<&2, String>, s: Maybe<&2, Side>, t: Maybe<&2, Side>) -> Bool:
  match s:
    case Some{Side.Whole{+d, None{}}}:
      side.given(stats, d, t)
    case other:
      side.same(other, t)

def sizes.told(+stats: List<&2, String>, cs: List<&2, Compared>, ds: List<&2, Compared>) -> Bool:
  match cs ds:
    case Nil{} Nil{}:
      True{}
    case Compared{f, t, b, a, m, g} <> rest Compared{f2, t2, b2, a2, m2, g2} <> more:
      Bool.and(Bool.and(side.told(stats, b, b2), side.told(stats, a, a2)), sizes.told(stats, rest, more))
    case _ _:
      False{}

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

def tree.maybe.r(+fs: List<&2, Full>, at: Maybe<&2, String>) -> Result<&2, &2, Refused, Tree.Tree()>:
  match at:
    case None{}:
      Done{Nil{}}
    case Some{+id}:
      tree.r(fs, id)

def tree.maybe(+fs: List<&2, Full>, at: Maybe<&2, String>) -> IO(Tree.Tree()):
  refused.io(Tree.Tree(), tree.maybe.r(fs, at))

def diff.revisions(+root: String, +fs: List<&2, Full>, +bs: List<&2, Bm.Bookmark>, +right: Full, +paint: Bool, only: Maybe<&2, String>, left: Maybe<&2, String>) -> IO(Unit):
  do IO<Unit>:
    +l : Maybe<&2, String> = left
    +r : String = id_of(right)
    lim : Limit <- refused.io(Limit, diff.limit.r(fs, bs, r, only))
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
def the_head.r(+fs: List<&2, Full>, +bs: List<&2, Bm.Bookmark>, heads: List<&2, String>) -> Result<&2, &2, Refused, Maybe<&2, String>>:
  match heads:
    case Nil{}:
      Done{None{}}
    case only <> Nil{}:
      Done{Some{only}}
    case +several:
      Fail{Refused{1, "this store has " ++ Nat.show(List.length(&2, String, several)) ++ " heads, so nothing here is `the` latest; name one with --onto, or join them with `historica merge`:" ++ described(fs, bs, List.sort(~String, ~(a => b => String.is_le(a, b)), several))}}

def the_head(+fs: List<&2, Full>, +bs: List<&2, Bm.Bookmark>, heads: List<&2, String>) -> IO(Maybe<&2, String>):
  refused.io(Maybe<&2, String>, the_head.r(fs, bs, heads))

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

def chain.go(fuel: Nat, +fs: List<&2, Full>, at: Maybe<&2, Full>) -> List<&2, Full>:
  match fuel at:
    case 0n _:
      Nil{}
    case 1n+q None{}:
      Nil{}
    case 1n+q Some{+f}:
      f <> chain.go(q, fs, first_parent(fs, parents_of(f)))

def chain(+fs: List<&2, Full>, at: Maybe<&2, String>) -> List<&2, Full>:
  match at:
    case None{}:
      Nil{}
    case Some{+id}:
      chain.go(1n+List.length(&2, Full, fs), fs, find(fs, id))

# Where `LAWS.chain_follows_first_parents` looks: revisions the store holds,
# the first the one wanted, and each after it the first parent of the one
# before.
def parent.first(ps: List<&2, String>) -> Maybe<&2, String>:
  match ps:
    case Nil{}:
      None{}
    case p <> rest:
      Some{p}

def first_parents(+fs: List<&2, Full>, xs: List<&2, Full>, want: Maybe<&2, String>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case +x <> rest:
      Bool.and(Bool.and(Rev.member(ids(fs), id_of(x)), maybe_eq(want, Some{id_of(x)})), first_parents(fs, rest, parent.first(parents_of(x))))

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

# Every path `diff` over the folder goes on with is one the limit wants.
# `LAWS.diff_folder_keeps_what_the_limit_wants` holds `heres` to it.
def all.wanted(+l: Limit, hs: List<&2, Here>) -> Bool:
  match hs:
    case Nil{}:
      True{}
    case +h <> rest:
      Bool.and(here.wanted(l, h), all.wanted(l, rest))

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

# The digest the host gave the folder's file at a path: the first word of
# the line it answered for the path.
def here.digest(+dg: Map<&2, String>, h: Here) -> String:
  +path = here.path(h)
  T.word(stat_of(path, Map.get(String, SNil{}, dg, path)))

# Whether a file's nearest statement leaves it with this digest.
def here.same(+eds: List<&2, Store.Doc>, +os: Map<&2, T.Split>, h: Here, +digest: String) -> Bool:
  maybe_eq(stated_digest(eds, origin(os, here.file(h))), Some{digest})

# Whether the position holds a file at a path.
def here.held(h: Here) -> Bool:
  match h:
    case Here{p, Some{e}, found}:
      True{}
    case Here{p, None{}, found}:
      False{}

def plan.of(+h: Here, +digest: String, +lines: Bool, +regular: Bool, +same: Bool) -> Planned:
  Planned{h, digest, Bool.and(lines, Bool.not(Bool.and(regular, same))), Bool.and(regular, Bool.or(Bool.not(here.held(h)), Bool.and(lines, Bool.not(same))))}

def plan(+dg: Map<&2, String>, +os: Map<&2, T.Split>, +eds: List<&2, Store.Doc>, h: Here) -> Planned:
  +h2 = h
  +digest = here.digest(dg, h2)
  plan.of(h2, digest, here.lines(h2), here.regular(h2), here.same(eds, os, h2, digest))

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

# What the digests stated leave open. A file of lines is settled where the
# folder holds a regular file at its path with the digest the file's nearest
# statement leaves; a file of bytes or a link the position holds is settled
# by its digest or its target, whatever the folder holds there.
# `LAWS.diff_folder_replays_what_is_unsettled` and
# `LAWS.diff_folder_reads_what_is_unsettled` hold `plans` to it.
def here.settled(+dg: Map<&2, String>, +os: Map<&2, T.Split>, +eds: List<&2, Store.Doc>, h: Here) -> Bool:
  +h2 = h
  Bool.and(Bool.and(here.lines(h2), here.regular(h2)), here.same(eds, os, h2, here.digest(dg, h2)))

def here.kept(h: Here) -> Bool:
  +h2 = h
  Bool.and(here.held(h2), Bool.not(here.lines(h2)))

# The files of lines no statement settles, by file; and the folder's regular
# files nothing the position holds settles, by path.
def unsettled.files(+dg: Map<&2, String>, +os: Map<&2, T.Split>, +eds: List<&2, Store.Doc>, hs: List<&2, Here>) -> List<&2, String>:
  match hs:
    case Nil{}:
      Nil{}
    case +h <> rest:
      Rev.keep(Bool.and(here.lines(h), Bool.not(here.settled(dg, os, eds, h))), here.file(h), unsettled.files(dg, os, eds, rest))

def unsettled.paths(+dg: Map<&2, String>, +os: Map<&2, T.Split>, +eds: List<&2, Store.Doc>, hs: List<&2, Here>) -> List<&2, String>:
  match hs:
    case Nil{}:
      Nil{}
    case +h <> rest:
      Rev.keep(Bool.and(here.regular(h), Bool.not(Bool.or(here.kept(h), here.settled(dg, os, eds, h)))), here.path(h), unsettled.paths(dg, os, eds, rest))

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

# What the folder is compared with: what `--onto` names, or the head.
def wc.left.r(+fs: List<&2, Full>, +bs: List<&2, Bm.Bookmark>, onto: Maybe<&2, String>) -> Result<&2, &2, Refused, Maybe<&2, String>>:
  match onto:
    case Some{+t}:
      onto.r(fs, bs, t)
    case None{}:
      the_head.r(fs, bs, current_heads(history(fs)))

def wc.limit.file.r(+fs: List<&2, Full>, +bs: List<&2, Bm.Bookmark>, +sp: String, left: Maybe<&2, String>) -> Result<&2, &2, Refused, Limit>:
  match left:
    case None{}:
      Fail{Refused{1, "there is no revision here to name a file against"}}
    case Some{+id}:
      diff.limit.file.r(fs, bs, id, sp)

def wc.limit.spelled(+fs: List<&2, Full>, +bs: List<&2, Bm.Bookmark>, +left: Maybe<&2, String>, +sp: String, file: Bool) -> Result<&2, &2, Refused, Limit>:
  match file:
    case True{}:
      wc.limit.file.r(fs, bs, sp, left)
    case False{}:
      Done{Limit.Path{Maybe.default(&2, String, T.strip_prefix(sp, "path:"), sp)}}

def wc.limit.r(+fs: List<&2, Full>, +bs: List<&2, Bm.Bookmark>, +left: Maybe<&2, String>, only: Maybe<&2, String>) -> Result<&2, &2, Refused, Limit>:
  match only:
    case None{}:
      Done{Limit.None{}}
    case Some{+sp}:
      wc.limit.spelled(fs, bs, left, sp, String.starts_with(sp, "file:"))

# What `diff <target>` compares the target with: what `--onto` names, a
# revision the store holds, or else its one parent — nothing for a root.
# `LAWS.diff_compares_with_the_parent` holds `diff.left.r` to it, and
# `LAWS.diff_folder_compares_with_a_held_revision` holds `wc.left.r` to
# `left.ok`.
def left.ok(+fs: List<&2, Full>, l: Maybe<&2, String>) -> Bool:
  match l:
    case None{}:
      True{}
    case Some{id}:
      Rev.member(ids(fs), id)

def maybe.list(m: Maybe<&2, String>) -> List<&2, String>:
  match m:
    case None{}:
      Nil{}
    case Some{x}:
      [x]

def diff.left.ok(+fs: List<&2, Full>, +right: Full, onto: Maybe<&2, String>, +l: Maybe<&2, String>) -> Bool:
  match onto:
    case Some{t}:
      Bool.and(Maybe.is_some(&2, String, l), left.ok(fs, l))
    case None{}:
      same_list(maybe.list(l), parents_of(right))

# A file a comparison is limited to is one the tree of the revision it was
# named at holds. `LAWS.diff_limits_to_a_held_file` holds `diff.limit.r`
# and `wc.limit.r` to it.
def tree.holds.r(r: Result<&2, &2, Refused, Tree.Tree()>, +file: String) -> Bool:
  match r:
    case Fail{e}:
      False{}
    case Done{t}:
      Tree.holds(t, file)

def limit.held(+fs: List<&2, Full>, lim: Limit, at: Maybe<&2, String>) -> Bool:
  match lim:
    case Limit.None{}:
      True{}
    case Limit.Path{p}:
      True{}
    case Limit.File{+f}:
      match at:
        case None{}:
          False{}
        case Some{+id}:
          tree.holds.r(tree.r(fs, id), f)

# `diff` with no target: the folder against the position — the head, or
# what `--onto` names. A file of lines is replayed only where the folder's
# digest is not the one its nearest statement leaves, and the folder's file
# read only where the two differ or the position does not hold it.
def diff.folder(+root: String, +fs: List<&2, Full>, +bs: List<&2, Bm.Bookmark>, +onto: Maybe<&2, String>, +paint: Bool, only: Maybe<&2, String>) -> IO(Unit):
  do IO<Unit>:
    rules : List<&2, Folder.Scope> <- Folder.rules(root)
    left : Maybe<&2, String> <- refused.io(Maybe<&2, String>, wc.left.r(fs, bs, onto))
    +l : Maybe<&2, String> = left
    lim : Limit <- refused.io(Limit, wc.limit.r(fs, bs, l, only))
    +repo : String = repository(root)
    found : List<&2, Folder.Found> <- Folder.walk(repo, rules)
    t : Tree.Tree() <- tree.maybe(fs, l)
    +t2 : Tree.Tree() = t
    +hs : List<&2, Here> = heres(t2, found, lim)
    +os : Map<&2, T.Split> = origins.map(chain(fs, l), Map.new(&2, T.Split))
    eds : List<&2, Store.Doc> <- Store.fetch(root, distinct(List.sort(~String, ~(a => b => String.is_le(a, b)), edits_of(os, hs))))
    +eds2 : List<&2, Store.Doc> = eds
    readable.docs(eds2, edits_of(os, hs))
    +paths : List<&2, String> = regular_paths(hs)
    stats : List<&2, String> <- Store.stats(repo, paths)
    +ps : List<&2, Planned> = plans(stats.map(paths, stats, Map.new(&2, String)), os, eds2, hs)
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
        left : Maybe<&2, String> <- refused.io(Maybe<&2, String>, diff.left.r(fs, bs, f2, onto))
        diff.revisions(root, fs, bs, f2, paint, only, left)

# `NO_COLOR` set to anything settles `auto` and leaves `always` alone,
# which is the point of having said `always` out loud.
def no_color(r: Result<&1, &1, U32 & String, String>) -> Bool:
  match r:
    case Fail{e}:
      False{}
    case Done{v}:
      Bool.not(String.is_empty(v))

# `auto` colours a terminal and nothing else.
def decorates(color: String) -> IO(Bool):
  match color:
    case "always":
      IO.pure(Bool, True{})
    case "never":
      IO.pure(Bool, False{})
    case _:
      do IO<Bool>:
        t : Bool <- Store.terminal()
        nc : Result<&1, &1, U32 & String, String> <- IO.get_env("NO_COLOR")
        return Bool.and(t, Bool.not(no_color(nc)))

# What `diff` was asked: a target, if one was named, a file, if one was,
# `--onto`, and `--color`.
type DiffCmd is Data:
  DiffCmd{named: Maybe<&2, String>, only: Maybe<&2, String>, onto: Maybe<&2, String>, color: String}

def diff.first.r(+first: String, onto: Maybe<&2, String>, color: String, target: Bool) -> Result<&2, &2, Refused, DiffCmd>:
  match target:
    case True{}:
      Done{DiffCmd{Some{first}, None{}, onto, color}}
    case False{}:
      Done{DiffCmd{None{}, Some{first}, onto, color}}

def diff.split.r(+bs: List<&2, Bm.Bookmark>, onto: Maybe<&2, String>, color: String, rest: List<&2, String>) -> Result<&2, &2, Refused, DiffCmd>:
  match rest:
    case Nil{}:
      Done{DiffCmd{None{}, None{}, onto, color}}
    case +first <> Nil{}:
      diff.first.r(first, onto, color, could_be_target(bs, first))
    case first <> second <> Nil{}:
      Done{DiffCmd{Some{first}, Some{second}, onto, color}}
    case first <> second <> third <> more:
      Fail{Refused{2, "`diff` takes a target and a path, and `" ++ third ++ "` is a third argument"}}

def diff.asked.r(+bs: List<&2, Bm.Bookmark>, r: Result<&2, &2, String, DiffAsked>) -> Result<&2, &2, Refused, DiffCmd>:
  match r:
    case Fail{e}:
      Fail{Refused{2, e}}
    case Done{DiffAsked{onto, color, rest}}:
      diff.split.r(bs, onto, color, rest)

def diff.args.r(+bs: List<&2, Bm.Bookmark>, +args: List<&2, String>) -> Result<&2, &2, Refused, DiffCmd>:
  diff.asked.r(bs, dasked.go(args))

# What `diff`'s arguments say, read plainly: `--onto` and `--color` take the
# word after them, `--color=` spells a colour in the word itself, the last
# of each counting; every other word is the target or the path, in order.
# `LAWS.diff_reads_its_words` holds `diff.args.r` to it.
def dargs.other(m: Maybe<&2, String>, +w: String, ws: List<&2, String>) -> List<&2, String>:
  match m:
    case None{}:
      w <> ws
    case Some{v}:
      ws

def dargs.words(args: List<&2, String>, want: DWant) -> List<&2, String>:
  match args:
    case Nil{}:
      Nil{}
    case +w <> +rest:
      match want:
        case DWant.No{}:
          Bool.pick(List<&2, String>, String.eq(w, "--onto"), dargs.words(rest, DWant.Onto{}),
            Bool.pick(List<&2, String>, String.eq(w, "--color"), dargs.words(rest, DWant.Color{}), dargs.other(T.strip_prefix(w, "--color="), w, dargs.words(rest, DWant.No{}))))
        case DWant.Onto{}:
          dargs.words(rest, DWant.No{})
        case DWant.Color{}:
          dargs.words(rest, DWant.No{})

def dargs.onto(args: List<&2, String>, want: DWant, +last: Maybe<&2, String>) -> Maybe<&2, String>:
  match args:
    case Nil{}:
      last
    case +w <> +rest:
      match want:
        case DWant.No{}:
          Bool.pick(Maybe<&2, String>, String.eq(w, "--onto"), dargs.onto(rest, DWant.Onto{}, last),
            Bool.pick(Maybe<&2, String>, String.eq(w, "--color"), dargs.onto(rest, DWant.Color{}, last), dargs.onto(rest, DWant.No{}, last)))
        case DWant.Onto{}:
          dargs.onto(rest, DWant.No{}, Some{w})
        case DWant.Color{}:
          dargs.onto(rest, DWant.No{}, last)

def dargs.color(args: List<&2, String>, want: DWant, +last: String) -> String:
  match args:
    case Nil{}:
      last
    case +w <> +rest:
      match want:
        case DWant.No{}:
          Bool.pick(String, String.eq(w, "--onto"), dargs.color(rest, DWant.Onto{}, last),
            Bool.pick(String, String.eq(w, "--color"), dargs.color(rest, DWant.Color{}, last), dargs.color(rest, DWant.No{}, Maybe.default(&2, String, T.strip_prefix(w, "--color="), last))))
        case DWant.Onto{}:
          dargs.color(rest, DWant.No{}, last)
        case DWant.Color{}:
          dargs.color(rest, DWant.No{}, w)

type DSaid is Data:
  DSaid{words: List<&2, String>, onto: Maybe<&2, String>, color: String}

def dargs.said(+args: List<&2, String>) -> DSaid:
  DSaid{dargs.words(args, DWant.No{}), dargs.onto(args, DWant.No{}, None{}), dargs.color(args, DWant.No{}, "auto")}

def diff.names(named: Maybe<&2, String>, only: Maybe<&2, String>) -> List<&2, String>:
  match named only:
    case None{} None{}:
      Nil{}
    case Some{t} None{}:
      [t]
    case None{} Some{p}:
      [p]
    case Some{t} Some{p}:
      [t, p]

def diff.said(d: DiffCmd) -> DSaid:
  match d:
    case DiffCmd{named, only, onto, color}:
      DSaid{diff.names(named, only), onto, color}

def diff.of(+root: String, +fs: List<&2, Full>, +bs: List<&2, Bm.Bookmark>, a: DiffCmd) -> IO(Unit):
  match a:
    case DiffCmd{named, only, +onto, color}:
      do IO<Unit>:
        paint : Bool <- decorates(color)
        diff.named(root, fs, bs, onto, paint, named, only)

def diff(+args: List<&2, String>) -> IO(Unit):
  do IO<Unit>:
    root : String <- Store.root()
    +r : String = root
    rs : List<&2, Store.Doc> <- Store.revisions(r)
    bs : List<&2, Bm.Bookmark> <- bookmarks(r)
    +bs2 : List<&2, Bm.Bookmark> = bs
    a : DiffCmd <- refused.io(DiffCmd, diff.args.r(bs2, args))
    diff.of(r, opened.fulls(r, rs), bs2, a)

# blame
# -----

# One line and the revision that wrote it: `None` for a line only the folder
# holds.
type Row is Data:
  Row{by: Maybe<&2, String>, item: Ops.Item}

# A line's origin through an edit: what stood keeps its author, what arrived
# is this revision's, and what left is gone.
def overlay.put(plus: Bool, +by: Maybe<&2, String>, it: Ops.Item, origins: List<&2, Row>, minus: Bool, r: List<&2, Row>) -> List<&2, Row>:
  match plus:
    case True{}:
      Row{by, it} <> r
    case False{}:
      match origins:
        case Nil{}:
          Nil{}
        case Row{b, i} <> more:
          match minus:
            case True{}:
              r
            case False{}:
              Row{b, it} <> r

def overlay.tail(rs: List<&2, Row>) -> List<&2, Row>:
  match rs:
    case Nil{}:
      Nil{}
    case r <> rest:
      rest

def overlay.next(plus: Bool, rs: List<&2, Row>) -> List<&2, Row>:
  match plus:
    case True{}:
      rs
    case False{}:
      overlay.tail(rs)

def overlay(ls: List<&2, Laid>, +origins: List<&2, Row>, +by: Maybe<&2, String>) -> List<&2, Row>:
  match ls:
    case Nil{}:
      Nil{}
    case Laid{+s, it} <> rest:
      overlay.put(String.eq(s, "+"), by, it, origins, String.eq(s, "-"), overlay(rest, overlay.next(String.eq(s, "+"), origins), by))

def rows.items(rs: List<&2, Row>) -> List<&2, Ops.Item>:
  match rs:
    case Nil{}:
      Nil{}
    case Row{b, it} <> rest:
      it <> rows.items(rest)

# Who wrote each line of the file at a revision: the walk, as the Rust
# tool's `merged_content` answers it, wherever decision 0032's rule reaches
# too. On one line of history the walk is plain replay (`merge_linear`), so
# the authors are the ones an overlay of each edit would give.
def walked.rows(ns: List<&2, Merge.Node>, +names: List<&2, String>) -> List<&2, Row>:
  match ns:
    case Nil{}:
      Nil{}
    case +n <> rest:
      Row{List.get(&2, String, names, Merge.Node.author(n)), Merge.Node.item(n)} <> walked.rows(rest, names)

# Who wrote each line of that file: the author of each element standing.
def walked.origins(w: Walked) -> List<&2, Row>:
  match w:
    case Walked{+names, t}:
      walked.rows(Merge.visible(t), names)

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

# A row and the number of its line, counting from one.
type Blamed is Data:
  Blamed{n: Nat, row: Row}

def rows.all(rs: List<&2, Row>, +k: Nat) -> List<&2, Blamed>:
  match rs:
    case Nil{}:
      Nil{}
    case r <> rest:
      Blamed{k, r} <> rows.all(rest, 1n+k)

def rows.keep(b: Bool, x: Blamed, rest: List<&2, Blamed>) -> List<&2, Blamed>:
  match b:
    case True{}:
      x <> rest
    case False{}:
      rest

# The rows whose numbers fall in `first..last`, this one numbered `k`.
def rows.in(rs: List<&2, Row>, +k: Nat, +first: Nat, +last: Nat) -> List<&2, Blamed>:
  match rs:
    case Nil{}:
      Nil{}
    case r <> rest:
      rows.keep(Bool.and(Nat.is_le(first, k), Nat.is_le(k, last)), Blamed{k, r}, rows.in(rest, 1n+k, first, last))

def shown.rows(+fs: List<&2, Full>, +all_changes: List<&2, String>, ns: List<&2, Blamed>) -> List<&2, Shown>:
  match ns:
    case Nil{}:
      Nil{}
    case Blamed{n, Row{by, it}} <> rest:
      Shown{n, columns(fs, all_changes, by), it} <> shown.rows(fs, all_changes, rest)

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

def blame.line(+l: String, term: Bool, rest: List<&2, String>) -> List<&2, String>:
  match term:
    case True{}:
      l <> rest
    case False{}:
      l <> "\\ no newline at end of file" <> rest

def blame.lines(ss: List<&2, Shown>, +cw: Nat, +ww: Nat, +dw: Nat, +nw: Nat) -> List<&2, String>:
  match ss:
    case Nil{}:
      Nil{}
    case Shown{n, Columns{c, w, d}, Ops.Item{t, +term, forgot}} <> rest:
      blame.line(pad_left(c, cw) ++ "  " ++ pad(w, ww) ++ "  " ++ pad(d, dw) ++ "  " ++ pad_left(Nat.show(n), nw) ++ "  " ++ Ops.shown(Ops.Item{t, term, forgot}), term, blame.lines(rest, cw, ww, dw, nw))

def blame.print(+ss: List<&2, Shown>) -> List<&2, String>:
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

# What a span asks for, said plainly: every line of the file with its
# number, counting from one, and of those the ones whose number falls in
# the span. `LAWS.blame_numbers_its_lines` holds `rows.all` and `rows.in`
# to it.
type NLine is Data:
  NLine{n: Nat, item: Ops.Item}

def lines.numbered(items: List<&2, Ops.Item>, +k: Nat) -> List<&2, NLine>:
  match items:
    case Nil{}:
      Nil{}
    case it <> rest:
      NLine{k, it} <> lines.numbered(rest, 1n+k)

def nline.keep(b: Bool, x: NLine, rest: List<&2, NLine>) -> List<&2, NLine>:
  match b:
    case True{}:
      x <> rest
    case False{}:
      rest

def lines.in_span(ls: List<&2, NLine>, +first: Nat, +last: Nat) -> List<&2, NLine>:
  match ls:
    case Nil{}:
      Nil{}
    case NLine{+n, it} <> rest:
      nline.keep(Bool.and(Nat.is_le(first, n), Nat.is_le(n, last)), NLine{n, it}, lines.in_span(rest, first, last))

def lines.asked(ls: List<&2, NLine>, span: Maybe<&2, Wanted>) -> List<&2, NLine>:
  match span:
    case None{}:
      ls
    case Some{Wanted{+first, +last}}:
      lines.in_span(ls, first, last)

def blamed.lines(bs: List<&2, Blamed>) -> List<&2, NLine>:
  match bs:
    case Nil{}:
      Nil{}
    case Blamed{n, Row{by, it}} <> rest:
      NLine{n, it} <> blamed.lines(rest)

def lines.items(ls: List<&2, NLine>) -> List<&2, Ops.Item>:
  match ls:
    case Nil{}:
      Nil{}
    case NLine{n, it} <> rest:
      it <> lines.items(rest)

def shown.items(ss: List<&2, Shown>) -> List<&2, Ops.Item>:
  match ss:
    case Nil{}:
      Nil{}
    case Shown{n, c, it} <> rest:
      it <> shown.items(rest)

# What each printed line of these ends with: the line as `Ops.shown` spells
# it, and after a line without a newline, the marker saying so.
def blame.ends.item(+s: String, term: Bool, rest: List<&2, String>) -> List<&2, String>:
  match term:
    case True{}:
      s <> rest
    case False{}:
      s <> "\\ no newline at end of file" <> rest

def blame.ends(its: List<&2, Ops.Item>) -> List<&2, String>:
  match its:
    case Nil{}:
      Nil{}
    case Ops.Item{t, +term, f} <> rest:
      blame.ends.item(Ops.shown(Ops.Item{t, term, f}), term, blame.ends(rest))

# One line for each ending, each ending with it.
def ends_all(ls: List<&2, String>, es: List<&2, String>) -> Bool:
  match ls es:
    case Nil{} Nil{}:
      True{}
    case l <> lr e <> er:
      Bool.and(String.ends_with(l, e), ends_all(lr, er))
    case _ _:
      False{}

# The rows asked for, each with its number, or where a span begins past the
# end.
def blame.span.at(+rs: List<&2, Row>, +first: Nat, +last: Nat, past: Bool) -> Result<&2, &2, Refused, List<&2, Blamed>>:
  match past:
    case True{}:
      Fail{Refused{1, "that span begins past the end: the file has " ++ Nat.show(List.length(&2, Row, rs)) ++ " lines"}}
    case False{}:
      Done{rows.in(rs, 1n, first, last)}

def blame.span.r(+rs: List<&2, Row>, span: Maybe<&2, Wanted>) -> Result<&2, &2, Refused, List<&2, Blamed>>:
  match span:
    case None{}:
      Done{rows.all(rs, 1n)}
    case Some{Wanted{+first, +last}}:
      blame.span.at(rs, first, last, Nat.is_gt(first, List.length(&2, Row, rs)))

# What `blame` prints of these rows.
def blame.shown(+fs: List<&2, Full>, +all_changes: List<&2, String>, r: Result<&2, &2, Refused, List<&2, Blamed>>) -> Result<&2, &2, Refused, List<&2, String>>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{ns}:
      Done{blame.print(shown.rows(fs, all_changes, ns))}

def blame.limited.r(+fs: List<&2, Full>, +all_changes: List<&2, String>, +rs: List<&2, Row>, span: Maybe<&2, Wanted>) -> Result<&2, &2, Refused, List<&2, String>>:
  blame.shown(fs, all_changes, blame.span.r(rs, span))

# Arguments
# ---------

type BlameAsked is Data:
  BlameAsked{lines: Maybe<&2, String>, rest: List<&2, String>}

def basked.lines(a: BlameAsked, v: String) -> BlameAsked:
  match a:
    case BlameAsked{l, r}:
      BlameAsked{Some{v}, r}

def basked.push(a: BlameAsked, w: String) -> BlameAsked:
  match a:
    case BlameAsked{l, r}:
      BlameAsked{l, List.append(&2, String, r, [w])}

def basked.word(a: BlameAsked, +w: String, flag: Bool) -> Result<&2, &2, String, BlameAsked>:
  match flag:
    case True{}:
      Fail{"`" ++ w ++ "` is not an argument `blame` takes"}
    case False{}:
      Done{basked.push(a, w)}

# The arguments read in one pass: what has been read, and whether the word
# before was `--lines`, whose value this word is.
type BRead is Data:
  BRead{asked: Result<&2, &2, String, BlameAsked>, want: Bool}

def basked.plain(a: BlameAsked, +w: String, lines: Bool) -> BRead:
  match lines:
    case True{}:
      BRead{Done{a}, True{}}
    case False{}:
      BRead{basked.word(a, w, String.starts_with(w, "-")), False{}}

def basked.done(a: BlameAsked, +w: String, want: Bool) -> BRead:
  match want:
    case True{}:
      BRead{Done{basked.lines(a, w)}, False{}}
    case False{}:
      basked.plain(a, w, String.eq(w, "--lines"))

def basked.eat(r: BRead, +w: String) -> BRead:
  match r:
    case BRead{Fail{e}, want}:
      BRead{Fail{e}, want}
    case BRead{Done{a}, want}:
      basked.done(a, w, want)

def basked.run(args: List<&2, String>, r: BRead) -> BRead:
  match args:
    case Nil{}:
      r
    case w <> rest:
      basked.run(rest, basked.eat(r, w))

def basked.end.of(r: Result<&2, &2, String, BlameAsked>, want: Bool) -> Result<&2, &2, String, BlameAsked>:
  match want:
    case True{}:
      Fail{"`--lines` wants a span, as `<first>..<last>`"}
    case False{}:
      r

def basked.end(r: BRead) -> Result<&2, &2, String, BlameAsked>:
  match r:
    case BRead{Fail{e}, want}:
      Fail{e}
    case BRead{Done{a}, want}:
      basked.end.of(Done{a}, want)

def basked.go(args: List<&2, String>) -> Result<&2, &2, String, BlameAsked>:
  basked.end(basked.run(args, BRead{Done{BlameAsked{None{}, Nil{}}}, False{}}))

# What `blame`'s arguments say, read plainly: each `--lines` takes the word
# after it as its value, the last one counting, and every other word is one
# of the target and the path, in order. `LAWS.blame_reads_its_words` holds
# `blame.args.r` to it.
def bargs.words(args: List<&2, String>, want: Bool) -> List<&2, String>:
  match args:
    case Nil{}:
      Nil{}
    case +w <> +rest:
      match want:
        case True{}:
          bargs.words(rest, False{})
        case False{}:
          Bool.pick(List<&2, String>, String.eq(w, "--lines"), bargs.words(rest, True{}), w <> bargs.words(rest, False{}))

def bargs.lines(args: List<&2, String>, want: Bool, +last: Maybe<&2, String>) -> Maybe<&2, String>:
  match args:
    case Nil{}:
      last
    case +w <> +rest:
      match want:
        case True{}:
          bargs.lines(rest, False{}, Some{w})
        case False{}:
          Bool.pick(Maybe<&2, String>, String.eq(w, "--lines"), bargs.lines(rest, True{}, last), bargs.lines(rest, False{}, last))

def usage.io(-A: Data, r: Result<&2, &2, String, A>) -> IO(A):
  match r:
    case Fail{e}:
      die(A, 2, e)
    case Done{a}:
      IO.pure(A, a)

# What `blame` was asked: the target, if one was named, the file, and the
# span.
type Blame is Data:
  Blame{named: Maybe<&2, String>, path: String, span: Maybe<&2, Wanted>}

def blame.wanted.r(r: Result<&2, &2, String, Wanted>) -> Result<&2, &2, Refused, Maybe<&2, Wanted>>:
  match r:
    case Fail{e}:
      Fail{Refused{2, e}}
    case Done{w}:
      Done{Some{w}}

def blame.span.of(lines: Maybe<&2, String>) -> Result<&2, &2, Refused, Maybe<&2, Wanted>>:
  match lines:
    case None{}:
      Done{None{}}
    case Some{+l}:
      blame.wanted.r(lines.of(l))

def blame.asked.span(named: Maybe<&2, String>, path: String, r: Result<&2, &2, Refused, Maybe<&2, Wanted>>) -> Result<&2, &2, Refused, Blame>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{s}:
      Done{Blame{named, path, s}}

def blame.named.r(named: Maybe<&2, String>, only: Maybe<&2, String>, lines: Maybe<&2, String>) -> Result<&2, &2, Refused, Blame>:
  match only:
    case None{}:
      Fail{Refused{2, "`blame` wants a path: it answers who wrote each line of one file"}}
    case Some{sp}:
      blame.asked.span(named, sp, blame.span.of(lines))

def blame.first.r(+first: String, lines: Maybe<&2, String>, target: Bool) -> Result<&2, &2, Refused, Blame>:
  match target:
    case True{}:
      blame.named.r(Some{first}, None{}, lines)
    case False{}:
      blame.named.r(None{}, Some{first}, lines)

def blame.split.r(+bs: List<&2, Bm.Bookmark>, lines: Maybe<&2, String>, rest: List<&2, String>) -> Result<&2, &2, Refused, Blame>:
  match rest:
    case Nil{}:
      blame.named.r(None{}, None{}, lines)
    case +first <> Nil{}:
      blame.first.r(first, lines, could_be_target(bs, first))
    case first <> second <> Nil{}:
      blame.named.r(Some{first}, Some{second}, lines)
    case first <> second <> third <> more:
      Fail{Refused{2, "`blame` takes a target and a path, and `" ++ third ++ "` is a third argument"}}

def blame.asked.r(+bs: List<&2, Bm.Bookmark>, r: Result<&2, &2, String, BlameAsked>) -> Result<&2, &2, Refused, Blame>:
  match r:
    case Fail{e}:
      Fail{Refused{2, e}}
    case Done{BlameAsked{lines, rest}}:
      blame.split.r(bs, lines, rest)

def blame.args.r(+bs: List<&2, Bm.Bookmark>, +args: List<&2, String>) -> Result<&2, &2, Refused, Blame>:
  blame.asked.r(bs, basked.go(args))

# What `blame` was asked, as the plain reading of its arguments says it: the
# target and the path in order, and the span the last `--lines` spells.
type BSaid is Data:
  BSaid{words: List<&2, String>, span: Result<&2, &2, Refused, Maybe<&2, Wanted>>}

def bargs.said(+args: List<&2, String>) -> BSaid:
  BSaid{bargs.words(args, False{}), blame.span.of(bargs.lines(args, False{}, None{}))}

def blame.names(named: Maybe<&2, String>, +path: String) -> List<&2, String>:
  match named:
    case None{}:
      [path]
    case Some{t}:
      [t, path]

def blame.said(b: Blame) -> BSaid:
  match b:
    case Blame{named, +path, span}:
      BSaid{blame.names(named, path), Done{span}}

# A file of bytes has no lines, and a link holds where it points.
def lines_only.r(+path: String, k: Maybe<&2, Tree.FileKind>) -> Result<&2, &2, Refused, Unit>:
  match k:
    case Some{Tree.Whole{}}:
      Fail{Refused{1, path ++ " is a file of bytes: decision 0017 gives it no lines, and there is nothing to attribute line by line"}}
    case Some{Tree.Link{}}:
      Fail{Refused{1, path ++ " is a link: what it holds is where it points, which the revision that stated it is the whole of the answer for"}}
    case _:
      Done{Unit{}}

# A kind of file blame can attribute line by line: not a file of bytes, and
# not a link.
def kind.has_lines(k: Maybe<&2, Tree.FileKind>) -> Bool:
  match k:
    case None{}:
      True{}
    case Some{Tree.Lines{}}:
      True{}
    case Some{Tree.Whole{}}:
      False{}
    case Some{Tree.Link{}}:
      False{}

def tree.has_lines(r: Result<&2, &2, Refused, Tree.Tree()>, +file: String) -> Bool:
  match r:
    case Fail{e}:
      False{}
    case Done{+t}:
      Bool.and(Tree.holds(t, file), kind.has_lines(Tree.kind(t, file)))

# What `blame <target> <path>` reads is a revision the store holds, and a
# file with lines that revision's tree holds. `LAWS.blame_reads_a_held_file`
# holds `blame.picked.r` to it.
def picked.ok(+fs: List<&2, Full>, p: Picked) -> Bool:
  match p:
    case Picked{+id, +file}:
      Bool.and(Rev.member(ids(fs), id), tree.has_lines(tree.r(fs, id), file))

def blame.picked.file(+t: Tree.Tree(), +spelling: String, +id: String, +file: String) -> Result<&2, &2, Refused, Picked>:
  do Result<&2, &2, Refused, Picked>:
    lines_only.r(Maybe.default(&2, String, Tree.path(t, file), spelling), Tree.kind(t, file))
    return Picked{id, file}

def blame.picked.tree(+bs: List<&2, Bm.Bookmark>, +spelling: String, +id: String, +t: Tree.Tree()) -> Result<&2, &2, Refused, Picked>:
  do Result<&2, &2, Refused, Picked>:
    file : String <- file_in.r(id, bs, spelling, t)
    blame.picked.file(t, spelling, id, file)

def blame.picked.full(+fs: List<&2, Full>, +bs: List<&2, Bm.Bookmark>, +spelling: String, +id: String) -> Result<&2, &2, Refused, Picked>:
  do Result<&2, &2, Refused, Picked>:
    t : Tree.Tree() <- tree.r(fs, id)
    blame.picked.tree(bs, spelling, id, t)

def blame.picked.r(+fs: List<&2, Full>, +bs: List<&2, Bm.Bookmark>, +target: String, +spelling: String) -> Result<&2, &2, Refused, Picked>:
  do Result<&2, &2, Refused, Picked>:
    f : Full <- resolved.r(fs, bs, target)
    blame.picked.full(fs, bs, spelling, id_of(f))

# Who wrote each line of the file at a revision, from the documents behind
# it: the content rule must read the file, and the walk says who wrote it.
def blame.walked.r(r: Result<&2, &2, String, Walked>) -> Result<&2, &2, Refused, List<&2, Row>>:
  match r:
    case Fail{e}:
      Fail{Refused{1, e}}
    case Done{w}:
      Done{walked.origins(w)}

def blame.rows.of(+oldest: List<&2, Full>, +all: List<&2, Store.Doc>, +id: String, +file: String, r: Result<&2, &2, String, List<&2, Ops.Item>>) -> Result<&2, &2, Refused, List<&2, Row>>:
  match r:
    case Fail{e}:
      Fail{Refused{1, e}}
    case Done{items}:
      blame.walked.r(walked.of(oldest, all, id, file))

def blame.rows.r(+oldest: List<&2, Full>, +all: List<&2, Store.Doc>, +id: String, +file: String) -> Result<&2, &2, Refused, List<&2, Row>>:
  blame.rows.of(oldest, all, id, file, content.in(oldest, all, id, file))

def blame.recorded.r(+fs: List<&2, Full>, +all: List<&2, Store.Doc>, +id: String, +file: String, span: Maybe<&2, Wanted>) -> Result<&2, &2, Refused, List<&2, String>>:
  do Result<&2, &2, Refused, List<&2, String>>:
    rows : List<&2, Row> <- blame.rows.r(oldest_of(fs, Some{id}), all, id, file)
    blame.limited.r(fs, changes(fs), rows, span)

# The documents a file's history needs, and the documents they keep.
def blame.docs(+root: String, +fs: List<&2, Full>, +file: String) -> IO(List<&2, Store.Doc>):
  do IO<List<&2, Store.Doc>>:
    ds : List<&2, Store.Doc> <- Store.fetch(root, wanted(fs, file))
    +ds2 : List<&2, Store.Doc> = ds
    more : List<&2, Store.Doc> <- Store.fetch(root, kept_digests(ds2))
    return List.append(&2, Store.Doc, ds2, more)

def blame.fetched(+root: String, +fs: List<&2, Full>, span: Maybe<&2, Wanted>, p: Picked) -> IO(Unit):
  match p:
    case Picked{+id, +file}:
      do IO<Unit>:
        all : List<&2, Store.Doc> <- blame.docs(root, fs, file)
        out : List<&2, String> <- refused.io(List<&2, String>, blame.recorded.r(fs, all, id, file, span))
        print_lines(out)

# Who wrote each line of the file as a revision left it.
def blame.recorded(+root: String, +fs: List<&2, Full>, +bs: List<&2, Bm.Bookmark>, +target: String, +spelling: String, span: Maybe<&2, Wanted>) -> IO(Unit):
  do IO<Unit>:
    f : Full <- resolved(fs, bs, target)
    readable(fs, [id_of(f)])
    p : Picked <- refused.io(Picked, blame.picked.r(fs, bs, target, spelling))
    blame.fetched(root, fs, span, p)

# One file as the folder holds it: which file the argument names, and where
# the folder keeps it. A `file:` spelling names an identifier, which the
# folder does not have, so it is resolved against the position and the path
# comes back from the tree.
type Held is Data:
  Held{file: Maybe<&2, String>, path: String}

def wcf.at.r(+f: String, p: Maybe<&2, String>) -> Result<&2, &2, Refused, Held>:
  match p:
    case None{}:
      Fail{Refused{1, "the position holds no path for that file"}}
    case Some{path}:
      Done{Held{Some{f}, path}}

def wcf.path_of(+t: Tree.Tree(), +f: String) -> Result<&2, &2, Refused, Held>:
  wcf.at.r(f, Tree.path(t, f))

def wcf.file.r(+bs: List<&2, Bm.Bookmark>, +t: Tree.Tree(), +sp: String, left: Maybe<&2, String>) -> Result<&2, &2, Refused, Held>:
  match left:
    case None{}:
      Fail{Refused{1, "there are no revisions here to name a file against"}}
    case Some{+id}:
      do Result<&2, &2, Refused, Held>:
        f : String <- file_in.r(id, bs, sp, t)
        wcf.path_of(t, f)

def wcf.several.r(+bs: List<&2, Bm.Bookmark>, +t: Tree.Tree(), +path: String, left: Maybe<&2, String>) -> Result<&2, &2, Refused, Held>:
  match left:
    case None{}:
      Fail{Refused{1, "this store holds no position"}}
    case Some{+id}:
      do Result<&2, &2, Refused, Held>:
        f : String <- file_in.r(id, bs, path, t)
        return Held{Some{f}, path}

def wcf.path.r(+bs: List<&2, Bm.Bookmark>, +t: Tree.Tree(), +path: String, +left: Maybe<&2, String>, at: List<&2, String>) -> Result<&2, &2, Refused, Held>:
  match at:
    case Nil{}:
      Done{Held{None{}, path}}
    case only <> Nil{}:
      Done{Held{Some{only}, path}}
    case _:
      wcf.several.r(bs, t, path, left)

def wcf.spelled.r(+bs: List<&2, Bm.Bookmark>, +t: Tree.Tree(), +sp: String, +left: Maybe<&2, String>, file: Bool) -> Result<&2, &2, Refused, Held>:
  match file:
    case True{}:
      wcf.file.r(bs, t, sp, left)
    case False{}:
      +p = Maybe.default(&2, String, T.strip_prefix(sp, "path:"), sp)
      wcf.path.r(bs, t, p, left, Tree.at(t, p))

def wcf.held.r(+bs: List<&2, Bm.Bookmark>, +t: Tree.Tree(), +sp: String, +left: Maybe<&2, String>) -> Result<&2, &2, Refused, Held>:
  wcf.spelled.r(bs, t, sp, left, String.starts_with(sp, "file:"))

def found_at(fs: List<&2, Folder.Found>, +path: String) -> Maybe<&2, Folder.Found>:
  match fs:
    case Nil{}:
      None{}
    case +f <> rest:
      Bool.pick(Maybe<&2, Folder.Found>, String.eq(Folder.found.path(f), path), Some{f}, found_at(rest, path))

def wcf.found.r(+path: String, f: Maybe<&2, Folder.Found>) -> Result<&2, &2, Refused, Folder.Found>:
  match f:
    case None{}:
      Fail{Refused{1, "the folder holds no " ++ path ++ "; `historica blame <target> " ++ path ++ "` reads it as a revision left it"}}
    case Some{x}:
      Done{x}

# A link holds where it points, asked before anything is read through it.
def wcf.link.r(+path: String, f: Folder.Found) -> Result<&2, &2, Refused, Unit>:
  match f:
    case Folder.Found.Link{p, t}:
      lines_only.r(path, Some{Tree.Link{}})
    case Folder.Found.File{p, r, n}:
      Done{Unit{}}

def wcf.kind_of(+t: Tree.Tree(), f: Maybe<&2, String>) -> Maybe<&2, Tree.FileKind>:
  match f:
    case None{}:
      None{}
    case Some{+file}:
      Tree.kind(t, file)

# Where the folder's file is, and what kind the position says it is, before
# its bytes are read.
def wcf.checked.r(+path: String, +t: Tree.Tree(), file: Maybe<&2, String>, found: List<&2, Folder.Found>) -> Result<&2, &2, Refused, Maybe<&2, Tree.FileKind>>:
  do Result<&2, &2, Refused, Maybe<&2, Tree.FileKind>>:
    f : Folder.Found <- wcf.found.r(path, found_at(found, path))
    wcf.link.r(path, f)
    +k : Maybe<&2, Tree.FileKind> = wcf.kind_of(t, file)
    lines_only.r(path, k)
    return k

# What `blame <path>` reads from the folder is a file there rather than a
# link, and the kind it goes on with is the position's, one with lines.
# `LAWS.blame_reads_a_folder_file` holds `wcf.checked.r` to it.
def found.regular(m: Maybe<&2, Folder.Found>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{Folder.Found.File{p, r, n}}:
      True{}
    case Some{Folder.Found.Link{p, t}}:
      False{}

def kind.same(a: Maybe<&2, Tree.FileKind>, b: Maybe<&2, Tree.FileKind>) -> Bool:
  match a b:
    case None{} None{}:
      True{}
    case Some{x} Some{y}:
      Tree.kind_eq(x, y)
    case _ _:
      False{}

def checked.ok(found: List<&2, Folder.Found>, +path: String, +t: Tree.Tree(), +file: Maybe<&2, String>, +k: Maybe<&2, Tree.FileKind>) -> Bool:
  Bool.and(found.regular(found_at(found, path)), Bool.and(kind.same(k, wcf.kind_of(t, file)), kind.has_lines(k)))

# A file the position holds keeps the kind it was added with; one it does
# not is whatever the recorder would call it.
def wcf.sniffed.r(+path: String, text: Bool) -> Result<&2, &2, Refused, Unit>:
  match text:
    case True{}:
      Done{Unit{}}
    case False{}:
      lines_only.r(path, Some{Tree.Whole{}})

def wcf.kind.r(+path: String, k: Maybe<&2, Tree.FileKind>, +bs: List<&2, U32>) -> Result<&2, &2, Refused, Unit>:
  match k:
    case Some{kind}:
      lines_only.r(path, Some{kind})
    case None{}:
      wcf.sniffed.r(path, Folder.is_text(bs))

# The folder's file has lines: the kind the position gave it, or text by
# the recorder's reckoning where the position holds nothing there.
def folder.has_lines(k: Maybe<&2, Tree.FileKind>, +bs: List<&2, U32>) -> Bool:
  match k:
    case Some{kind}:
      kind.has_lines(Some{kind})
    case None{}:
      Folder.is_text(bs)

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

# What `blame <path>` prints: the folder's text laid over the rows history
# holds, once the kind of file allows it.
def blame.folder.r(+fs: List<&2, Full>, +path: String, k: Maybe<&2, Tree.FileKind>, +bs: List<&2, U32>, rows: List<&2, Row>, span: Maybe<&2, Wanted>) -> Result<&2, &2, Refused, List<&2, String>>:
  do Result<&2, &2, Refused, List<&2, String>>:
    wcf.kind.r(path, k, bs)
    blame.limited.r(fs, changes(fs), wc.overlay(rows, Ops.from_text(Folder.lossy(bs))), span)

def wcf.origins(+root: String, +fs: List<&2, Full>, +left: Maybe<&2, String>, file: Maybe<&2, String>) -> IO(List<&2, Row>):
  match left file:
    case Some{+id} Some{+f}:
      do IO<List<&2, Row>>:
        all : List<&2, Store.Doc> <- blame.docs(root, fs, f)
        +all2 : List<&2, Store.Doc> = all
        refused.io(List<&2, Row>, blame.rows.r(oldest_of(fs, Some{id}), all2, id, f))
    case _ _:
      IO.pure(List<&2, Row>, Nil{})

def blame.held(+root: String, +fs: List<&2, Full>, +repo: String, +t: Tree.Tree(), +l: Maybe<&2, String>, found: List<&2, Folder.Found>, h: Held, span: Maybe<&2, Wanted>) -> IO(Unit):
  match h:
    case Held{+file, +path}:
      do IO<Unit>:
        k : Maybe<&2, Tree.FileKind> <- refused.io(Maybe<&2, Tree.FileKind>, wcf.checked.r(path, t, file, found))
        +k2 : Maybe<&2, Tree.FileKind> = k
        bs : List<&2, U32> <- Utf8.read_file(repo ++ "/" ++ path)
        +bs2 : List<&2, U32> = bs
        refused.io(Unit, wcf.kind.r(path, k2, bs2))
        rows : List<&2, Row> <- wcf.origins(root, fs, l, file)
        out : List<&2, String> <- refused.io(List<&2, String>, blame.folder.r(fs, path, k2, bs2, rows, span))
        print_lines(out)

# The position `blame <path>` compares the folder with, its tree, and the
# file the argument names there.
type Position is Data:
  Position{left: Maybe<&2, String>, tree: Tree.Tree(), held: Held}

def wcf.position.tree(+bs: List<&2, Bm.Bookmark>, +sp: String, +l: Maybe<&2, String>, +t: Tree.Tree()) -> Result<&2, &2, Refused, Position>:
  do Result<&2, &2, Refused, Position>:
    h : Held <- wcf.held.r(bs, t, sp, l)
    return Position{l, t, h}

def wcf.position.left(+fs: List<&2, Full>, +bs: List<&2, Bm.Bookmark>, +sp: String, +l: Maybe<&2, String>) -> Result<&2, &2, Refused, Position>:
  do Result<&2, &2, Refused, Position>:
    t : Tree.Tree() <- tree.maybe.r(fs, l)
    wcf.position.tree(bs, sp, l, t)

def wcf.position.r(+fs: List<&2, Full>, +bs: List<&2, Bm.Bookmark>, +sp: String) -> Result<&2, &2, Refused, Position>:
  do Result<&2, &2, Refused, Position>:
    l : Maybe<&2, String> <- the_head.r(fs, bs, current_heads(history(fs)))
    wcf.position.left(fs, bs, sp, l)

# What `blame <path>` compares the folder with is a revision the store
# holds, or none in an empty store; and the file the argument names is one
# that revision's tree holds, or the tree holds nothing at the path and the
# folder's file is its own. `LAWS.blame_reads_the_position` holds
# `wcf.position.r` to it.
def held.ok(+t: Tree.Tree(), h: Held) -> Bool:
  match h:
    case Held{None{}, +path}:
      List.is_empty(&2, String, Tree.at(t, path))
    case Held{Some{f}, path}:
      Tree.holds(t, f)

def position.ok(+fs: List<&2, Full>, p: Position) -> Bool:
  match p:
    case Position{l, +t, h}:
      Bool.and(left.ok(fs, l), held.ok(t, h))

def blame.position(+root: String, +fs: List<&2, Full>, +repo: String, found: List<&2, Folder.Found>, span: Maybe<&2, Wanted>, p: Position) -> IO(Unit):
  match p:
    case Position{+l, +t, h}:
      blame.held(root, fs, repo, t, l, found, h, span)

# `blame <path>`: the file as the folder holds it, attributed as far as the
# store can.
def blame.folder(+root: String, +fs: List<&2, Full>, +bs: List<&2, Bm.Bookmark>, +sp: String, span: Maybe<&2, Wanted>) -> IO(Unit):
  do IO<Unit>:
    rules : List<&2, Folder.Scope> <- Folder.rules(root)
    +repo : String = repository(root)
    found : List<&2, Folder.Found> <- Folder.walk(repo, rules)
    p : Position <- refused.io(Position, wcf.position.r(fs, bs, sp))
    blame.position(root, fs, repo, found, span, p)

def blame.side(+root: String, +fs: List<&2, Full>, +bs: List<&2, Bm.Bookmark>, named: Maybe<&2, String>, +sp: String, span: Maybe<&2, Wanted>) -> IO(Unit):
  match named:
    case Some{+t}:
      blame.recorded(root, fs, bs, t, sp, span)
    case None{}:
      blame.folder(root, fs, bs, sp, span)

def blame.of(+root: String, +fs: List<&2, Full>, +bs: List<&2, Bm.Bookmark>, a: Blame) -> IO(Unit):
  match a:
    case Blame{named, +sp, span}:
      blame.side(root, fs, bs, named, sp, span)

def blame(+args: List<&2, String>) -> IO(Unit):
  do IO<Unit>:
    root : String <- Store.root()
    +r : String = root
    rs : List<&2, Store.Doc> <- Store.revisions(r)
    bs : List<&2, Bm.Bookmark> <- bookmarks(r)
    +bs2 : List<&2, Bm.Bookmark> = bs
    a : Blame <- refused.io(Blame, blame.args.r(bs2, args))
    blame.of(r, opened.fulls(r, rs), bs2, a)

# replay
# ------

def replay.step(state: Result<&2, &2, String, List<&2, Ops.Item>>, parsed: Result<&2, &2, String, Ops.Doc>) -> Result<&2, &2, String, List<&2, Ops.Item>>:
  do Result<&2, &2, String, List<&2, Ops.Item>>:
    items : List<&2, Ops.Item> <- state
    doc : Ops.Doc <- parsed
    Ops.apply(items, doc)

# A document that is not an operation document is a payload: the file
# created whole, which decision 0017 makes the same as an insert at 0. A
# chain already refused stays refused: a payload after a document that did
# not apply does not make the chain one that works
# (`LAWS.replay_keeps_a_refusal`).
def replay.payload(state: Result<&2, &2, String, List<&2, Ops.Item>>, text: String) -> Result<&2, &2, String, List<&2, Ops.Item>>:
  match state:
    case Fail{e}:
      Fail{e}
    case Done{items}:
      Done{Ops.from_text(text)}

def replay.doc(state: Result<&2, &2, String, List<&2, Ops.Item>>, text: String, is_ops: Bool) -> Result<&2, &2, String, List<&2, Ops.Item>>:
  match is_ops:
    case True{}:
      replay.step(state, Ops.parse(text))
    case False{}:
      replay.payload(state, text)

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

# status
# ------

# `status [--onto <target>] [--merge <target>]..`, read as the Rust tool
# reads it: `--onto` takes the word after it, the last counting, and each
# `--merge` names one more revision being joined.
type StatusCmd is Data:
  StatusCmd{onto: Maybe<&2, String>, merges: List<&2, String>}

# What a word is to `status`: a flag that takes the next word, or not.
type SWord is Data:
  SWord.Onto{}
  SWord.Merge{}
  SWord.Other{}

def sword.of(onto: Bool, merge: Bool) -> SWord:
  match onto:
    case True{}:
      SWord.Onto{}
    case False{}:
      Bool.pick(SWord, merge, SWord.Merge{}, SWord.Other{})

def sword(args: List<&2, String>) -> SWord:
  match args:
    case Nil{}:
      SWord.Other{}
    case +w <> rest:
      sword.of(String.eq(w, "--onto"), String.eq(w, "--merge"))

# `k` is what the first word is.
def status.args.go(args: List<&2, String>, onto: Maybe<&2, String>, merges: List<&2, String>, k: SWord) -> Result<&2, &2, Refused, StatusCmd>:
  match args k:
    case Nil{} _:
      Done{StatusCmd{onto, merges}}
    case w <> Nil{} SWord.Onto{}:
      Fail{Refused{2, "`--onto` wants a value"}}
    case w <> v <> +rest SWord.Onto{}:
      status.args.go(rest, Some{v}, merges, sword(rest))
    case w <> Nil{} SWord.Merge{}:
      Fail{Refused{2, "`--merge` wants a value"}}
    case w <> v <> +rest SWord.Merge{}:
      status.args.go(rest, onto, List.append(&2, String, merges, [v]), sword(rest))
    case w <> rest SWord.Other{}:
      Fail{Refused{2, "`" ++ w ++ "` is not an argument `status` takes"}}

def status.args.r(+args: List<&2, String>) -> Result<&2, &2, Refused, StatusCmd>:
  status.args.go(args, None{}, Nil{}, sword(args))

# What `status`'s words say, read plainly: the word after a flag is its
# value, whatever it is; the value of `--onto` is where the folder is
# compared from, the last counting, and each `--merge`'s one more revision
# joined, in order. `LAWS.status_reads_its_words` holds `status.args.r` to
# it.
def sargs.onto(args: List<&2, String>, last: Maybe<&2, String>, k: SWord) -> Maybe<&2, String>:
  match args k:
    case Nil{} _:
      last
    case w <> v <> +rest SWord.Onto{}:
      sargs.onto(rest, Some{v}, sword(rest))
    case w <> v <> +rest SWord.Merge{}:
      sargs.onto(rest, last, sword(rest))
    case w <> +rest _:
      sargs.onto(rest, last, sword(rest))

def sargs.merges(args: List<&2, String>, k: SWord) -> List<&2, String>:
  match args k:
    case Nil{} _:
      Nil{}
    case w <> v <> +rest SWord.Onto{}:
      sargs.merges(rest, sword(rest))
    case w <> v <> +rest SWord.Merge{}:
      v <> sargs.merges(rest, sword(rest))
    case w <> +rest _:
      sargs.merges(rest, sword(rest))

# A rule covering a file the position holds is refused before anything is
# described: the walk never offered the path, so it would read as dropped,
# and a person who wrote the rule for privacy would get the opposite.
def skipped_held(+rules: List<&2, Folder.Scope>, t: Tree.Tree()) -> List<&2, String>:
  match t:
    case Nil{}:
      Nil{}
    case +e <> rest:
      +later = skipped_held(rules, rest)
      Bool.pick(List<&2, String>, Folder.skips(rules, Tree.entry_path(e)), Tree.entry_path(e) <> later, later)

def skips_held.lines(ps: List<&2, String>) -> String:
  match ps:
    case Nil{}:
      SNil{}
    case p <> rest:
      "\n  " ++ p ++ skips_held.lines(rest)

def skips_held.r(+ps: List<&2, String>) -> Result<&2, &2, Refused, Unit>:
  +one = Nat.is_eq(List.length(&2, String, ps), 1n)
  Bool.pick(Result<&2, &2, Refused, Unit>, List.is_empty(&2, String, ps), Done{Unit{}},
    Fail{Refused{1, "`history/skipped/` skips " ++ Bool.pick(String, one, "a file", Nat.show(List.length(&2, String, ps)) ++ " files") ++ " history already holds, so recording would spell " ++ Bool.pick(String, one, "it", "them") ++ " as a deletion; delete the " ++ Bool.pick(String, one, "file", "files") ++ " first and record that, or drop the rule — history holds what it holds, and `forget` is what removes recorded content:" ++ skips_held.lines(ps)}})

# What the survey needs to know of a path's content at the position: the
# digest of a file of lines, where the folder holds a file there to compare
# with or holds nothing and an arrival might be it moved.
def status.lines(h: Here) -> Bool:
  match h:
    case Here{p, Some{Tree.Entry{f, q, Tree.Lines{}, y, g, m}}, Some{Folder.Found.File{r, x, n}}}:
      True{}
    case Here{p, Some{Tree.Entry{f, q, Tree.Lines{}, y, g, m}}, None{}}:
      True{}
    case _:
      False{}

def status.edits(+os: Map<&2, T.Split>, hs: List<&2, Here>) -> List<&2, String>:
  match hs:
    case Nil{}:
      Nil{}
    case +h <> rest:
      List.append(&2, String, edit_of(os, h, status.lines(h)), status.edits(os, rest))

# The files whose digest nothing states, which are replayed.
def status.unknown(+eds: List<&2, Store.Doc>, +os: Map<&2, T.Split>, hs: List<&2, Here>) -> List<&2, String>:
  match hs:
    case Nil{}:
      Nil{}
    case +h <> rest:
      +later = status.unknown(eds, os, rest)
      Bool.pick(List<&2, String>, Bool.and(status.lines(h), Maybe.is_none(&2, String, stated_digest(eds, origin(os, here.file(h))))), here.file(h) <> later, later)

def status.digest.of(+stated: Maybe<&2, String>, +older: List<&2, Full>, +ds: List<&2, Store.Doc>, +left: String, +file: String) -> Result<&2, &2, String, String>:
  match stated:
    case Some{d}:
      Done{d}
    case None{}:
      Result.map(&2, &2, String, List<&2, Ops.Item>, String, items => Ops.state_digest(items), content.in(older, ds, left, file))

# Each such file's digest at the position, by file: stated where the
# nearest statement says it, replayed where it does not.
def status.lined(hs: List<&2, Here>) -> List<&2, Here>:
  match hs:
    case Nil{}:
      Nil{}
    case +h <> rest:
      +later = status.lined(rest)
      Bool.pick(List<&2, Here>, status.lines(h), h <> later, later)

def status.befores.go(+older: List<&2, Full>, +ds: List<&2, Store.Doc>, +left: String, +eds: List<&2, Store.Doc>, +os: Map<&2, T.Split>, hs: List<&2, Here>, m: Map<&2, String>) -> Result<&2, &2, String, Map<&2, String>>:
  match hs:
    case Nil{}:
      Done{m}
    case +h <> rest:
      +file = here.file(h)
      do Result<&2, &2, String, Map<&2, String>>:
        d : String <- status.digest.of(stated_digest(eds, origin(os, file)), older, ds, left, file)
        status.befores.go(older, ds, left, eds, os, rest, Map.set(&2, String, m, file, d))

def status.befores(+older: List<&2, Full>, +ds: List<&2, Store.Doc>, +left: String, +eds: List<&2, Store.Doc>, +os: Map<&2, T.Split>, hs: List<&2, Here>, m: Map<&2, String>) -> Result<&2, &2, String, Map<&2, String>>:
  status.befores.go(older, ds, left, eds, os, status.lined(hs), m)

def status.befores.r(r: Result<&2, &2, String, Map<&2, String>>) -> Result<&2, &2, Refused, Map<&2, String>>:
  match r:
    case Fail{e}:
      Fail{Refused{1, e}}
    case Done{m}:
      Done{m}

# Where `LAWS.status_believes_what_is_stated` looks for a refusal: a file
# no statement gives the digest of, whose content replayed is refused so.
def status.fails_as(r: Result<&2, &2, String, List<&2, Ops.Item>>, +e: String) -> Bool:
  match r:
    case Fail{x}:
      String.eq(x, e)
    case Done{items}:
      False{}

def status.replay_fails.one(+older: List<&2, Full>, +ds: List<&2, Store.Doc>, +left: String, +e: String, stated: Maybe<&2, String>, +file: String) -> Bool:
  match stated:
    case Some{d}:
      False{}
    case None{}:
      status.fails_as(content.in(older, ds, left, file), e)

def status.replay_fails(+older: List<&2, Full>, +ds: List<&2, Store.Doc>, +left: String, +eds: List<&2, Store.Doc>, +os: Map<&2, T.Split>, hs: List<&2, Here>, +e: String) -> Bool:
  match hs:
    case Nil{}:
      False{}
    case +h <> rest:
      Bool.or(status.replay_fails.one(older, ds, left, e, stated_digest(eds, origin(os, here.file(h))), here.file(h)), status.replay_fails(older, ds, left, eds, os, rest, e))

def looked_up(+key: String, r: Map<&2, String> & String) -> Maybe<&2, String>:
  (m, v) = r
  +v2 = v
  Bool.pick(Maybe<&2, String>, String.is_empty(v2), None{}, Some{v2})

# What the position's content has for the survey: the payload of a file of
# bytes, the digest of a file of lines, and nothing for a link.
def status.before(+bf: Map<&2, String>, e: Maybe<&2, Tree.Entry>) -> Maybe<&2, String>:
  match e:
    case Some{Tree.Entry{+f, p, Tree.Lines{}, y, g, m}}:
      looked_up(f, Map.get(String, SNil{}, bf, f))
    case Some{Tree.Entry{f, p, Tree.Whole{}, y, g, m}}:
      y
    case _:
      None{}

def status.folder_digest(+dg: Map<&2, String>, +path: String) -> String:
  T.word(stat_of(path, Map.get(String, SNil{}, dg, path)))

# A file of lines is read only where its digest differs from the
# position's: that is where it has to be text still.
def status.read(+dg: Map<&2, String>, +bf: Map<&2, String>, h: Here) -> Bool:
  match h:
    case Here{+path, Some{Tree.Entry{+f, q, Tree.Lines{}, y, g, m}}, Some{Folder.Found.File{r, x, n}}}:
      Bool.not(Sv.same(looked_up(f, Map.get(String, SNil{}, bf, f)), status.folder_digest(dg, path)))
    case _:
      False{}

def status.reads(+dg: Map<&2, String>, +bf: Map<&2, String>, hs: List<&2, Here>) -> List<&2, String>:
  match hs:
    case Nil{}:
      Nil{}
    case +h <> rest:
      Rev.keep(status.read(dg, bf, h), here.path(h), status.reads(dg, bf, rest))

# What the last `update` wrote for a recorded link: spelled from where it
# sat at the position, `t`, since a `mv` of the link no more rewrites its
# own string than a `mv` of its target does.
def status.shown(+t: Tree.Tree(), e: Maybe<&2, Tree.Entry>) -> Maybe<&2, String>:
  match e:
    case Some{Tree.Entry{+f, p, Tree.Link{}, y, Some{g}, m}}:
      Some{materialise(t, Maybe.default(&2, String, Tree.path(t, f), p), g)}
    case _:
      None{}

# Where the parents being joined leave a file of lines differently, its
# digest is `-`: there is none to compare with.
def status.proposed(+bf: Map<&2, String>, e: Maybe<&2, Tree.Entry>) -> Bool:
  match e:
    case Some{Tree.Entry{+f, p, Tree.Lines{}, y, g, m}}:
      String.eq(stat_of(f, Map.get(String, SNil{}, bf, f)), "-")
    case _:
      False{}

def status.seen(+t: Tree.Tree(), +dg: Map<&2, String>, +bf: Map<&2, String>, +reads: Map<&2, List<&2, U32>>, h: Here) -> Sv.Seen:
  match h:
    case Here{+path, +e, found}:
      +proposed = status.proposed(bf, e)
      Sv.Seen{path, e, found, status.folder_digest(dg, path), Bool.pick(Maybe<&2, String>, proposed, None{}, status.before(bf, e)), Folder.is_utf8(bytes_of(path, Map.get(List<&2, U32>, Nil{}, reads, path))), status.shown(t, e), proposed}

# `t` is the position's tree as it stands, before any rename a person
# stated moved a file in it.
def status.seens(+t: Tree.Tree(), +dg: Map<&2, String>, +bf: Map<&2, String>, +reads: Map<&2, List<&2, U32>>, hs: List<&2, Here>) -> List<&2, Sv.Seen>:
  match hs:
    case Nil{}:
      Nil{}
    case h <> rest:
      status.seen(t, dg, bf, reads, h) <> status.seens(t, dg, bf, reads, rest)

# What `LAWS.status_surveys_each_path` reads in what the survey is told:
# each path compared, once and in order, and where the parents being
# joined leave a file of lines differently, no digest to compare it with.
def status.surveys.one(h: Here, s: Sv.Seen) -> Bool:
  match h s:
    case Here{p, e, f} Sv.Seen{q, e2, f2, d, before, text, shown, proposed}:
      Bool.and(String.eq(p, q), Bool.or(Bool.not(proposed), Maybe.is_none(&2, String, before)))

def status.surveys(hs: List<&2, Here>, ss: List<&2, Sv.Seen>) -> Bool:
  match hs ss:
    case Nil{} Nil{}:
      True{}
    case h <> hr s <> sr:
      Bool.and(status.surveys.one(h, s), status.surveys(hr, sr))
    case _ _:
      False{}

# Joining
# -------

# One parent's content of a file, as a digest: `None` where that parent's
# history never mentions it, which disagrees with nobody.
def status.joined.found(+older: List<&2, Full>, +ds: List<&2, Store.Doc>, +p: String, +file: String, found: Maybe<&2, Result<&2, &2, String, Rule>>) -> Result<&2, &2, String, Maybe<&2, String>>:
  match found:
    case None{}:
      Done{None{}}
    case Some{r}:
      Result.map(&2, &2, String, List<&2, Ops.Item>, Maybe<&2, String>, items => Some{Ops.state_digest(items)}, content.found(older, ds, p, file, Some{r}))

def status.joined.one(+fs: List<&2, Full>, +ds: List<&2, Store.Doc>, +file: String, +p: String) -> Result<&2, &2, String, Maybe<&2, String>>:
  +older = oldest_of(fs, Some{p})
  status.joined.found(older, ds, p, file, content_of(contents.go(older, ds, file, Nil{}), p))

def status.joined.each(+fs: List<&2, Full>, +ds: List<&2, Store.Doc>, +file: String, ps: List<&2, String>) -> Result<&2, &2, String, List<&2, Maybe<&2, String>>>:
  match ps:
    case Nil{}:
      Done{Nil{}}
    case +p <> rest:
      do Result<&2, &2, String, List<&2, Maybe<&2, String>>>:
        x : Maybe<&2, String> <- status.joined.one(fs, ds, file, p)
        xs : List<&2, Maybe<&2, String>> <- status.joined.each(fs, ds, file, rest)
        return x <> xs

def somes(xs: List<&2, Maybe<&2, String>>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case None{} <> rest:
      somes(rest)
    case Some{x} <> rest:
      x <> somes(rest)

def all_eq(xs: List<&2, String>, +d: String) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case x <> rest:
      Bool.and(String.eq(x, d), all_eq(rest, d))

# `record::joined_content`, as a digest: what every parent that mentions the
# file leaves it as, nothing where none does, and `-` where they differ.
def status.agree(+xs: List<&2, String>) -> String:
  match xs:
    case Nil{}:
      Sv.EMPTY()
    case +d <> rest:
      Bool.pick(String, all_eq(rest, d), d, "-")

def status.joined.go(+fs: List<&2, Full>, +ds: List<&2, Store.Doc>, +ps: List<&2, String>, hs: List<&2, Here>, m: Map<&2, String>) -> Result<&2, &2, String, Map<&2, String>>:
  match hs:
    case Nil{}:
      Done{m}
    case +h <> rest:
      +file = here.file(h)
      do Result<&2, &2, String, Map<&2, String>>:
        xs : List<&2, Maybe<&2, String>> <- status.joined.each(fs, ds, file, ps)
        status.joined.go(fs, ds, ps, rest, Map.set(&2, String, m, file, status.agree(somes(xs))))

# Where `LAWS.status_joins_what_it_reads` looks for a refusal: a file
# compared, and a parent whose content of it could not be read.
def status.one_fails(r: Result<&2, &2, String, Maybe<&2, String>>, +e: String) -> Bool:
  match r:
    case Fail{x}:
      String.eq(x, e)
    case Done{d}:
      False{}

def status.parents_fail(+fs: List<&2, Full>, +ds: List<&2, Store.Doc>, +file: String, ps: List<&2, String>, +e: String) -> Bool:
  match ps:
    case Nil{}:
      False{}
    case +p <> rest:
      Bool.or(status.one_fails(status.joined.one(fs, ds, file, p), e), status.parents_fail(fs, ds, file, rest, e))

def status.joined_fails(+fs: List<&2, Full>, +ds: List<&2, Store.Doc>, +ps: List<&2, String>, hs: List<&2, Here>, +e: String) -> Bool:
  match hs:
    case Nil{}:
      False{}
    case +h <> rest:
      Bool.or(status.parents_fail(fs, ds, here.file(h), ps, e), status.joined_fails(fs, ds, ps, rest, e))

# The digests at one parent: stated where the nearest statement says, and
# replayed where it does not.
def status.befores.one(+root: String, +fs: List<&2, Full>, +left: String, +hs: List<&2, Here>) -> IO(Map<&2, String>):
  do IO<Map<&2, String>>:
    +l : Maybe<&2, String> = Some{left}
    +os : Map<&2, T.Split> = origins.map(chain(fs, l), Map.new(&2, T.Split))
    eds : List<&2, Store.Doc> <- Store.fetch(root, distinct(List.sort(~String, ~(a => b => String.is_le(a, b)), status.edits(os, hs))))
    +eds2 : List<&2, Store.Doc> = eds
    readable.docs(eds2, status.edits(os, hs))
    ds : List<&2, Store.Doc> <- Store.fetch(root, wanted_all(fs, status.unknown(eds2, os, hs)))
    +ds2 : List<&2, Store.Doc> = ds
    more : List<&2, Store.Doc> <- Store.fetch(root, kept_digests(ds2))
    refused.io(Map<&2, String>, status.befores.r(status.befores(oldest_of(fs, l), List.append(&2, Store.Doc, ds2, more), left, eds2, os, hs, Map.new(&2, String))))

# The digests where several parents are joined, every one replayed.
def status.befores.joined(+root: String, +fs: List<&2, Full>, +ps: List<&2, String>, +hs: List<&2, Here>) -> IO(Map<&2, String>):
  do IO<Map<&2, String>>:
    +lined : List<&2, Here> = status.lined(hs)
    ds : List<&2, Store.Doc> <- Store.fetch(root, distinct(List.sort(~String, ~(a => b => String.is_le(a, b)), wanted_all(fs, T.map(~Here, ~String, ~(h => here.file(h)), lined)))))
    +ds2 : List<&2, Store.Doc> = ds
    more : List<&2, Store.Doc> <- Store.fetch(root, kept_digests(ds2))
    refused.io(Map<&2, String>, status.befores.r(status.joined.go(fs, List.append(&2, Store.Doc, ds2, more), ps, lined, Map.new(&2, String))))

def status.befores.io(+root: String, +fs: List<&2, Full>, ps: List<&2, String>, +hs: List<&2, Here>) -> IO(Map<&2, String>):
  match ps:
    case Nil{}:
      IO.pure(Map<&2, String>, Map.new(&2, String))
    case +p <> Nil{}:
      status.befores.one(root, fs, p, hs)
    case +several:
      status.befores.joined(root, fs, several, hs)

# The file set the parents leave, and where concurrent work met deciding
# it: `store::merged_tree_of`, over everything they reach.
def status.tree.of.r(+id: String, merged: Result<&2, &2, Tree.Fault, Tree.Merged>) -> Result<&2, &2, Refused, Tree.Merged>:
  match merged:
    case Fail{e}:
      Fail{Refused{1, id ++ ": " ++ Tree.fault_show(e)}}
    case Done{m}:
      Done{m}

def status.tree.r(+fs: List<&2, Full>, +ps: List<&2, String>) -> Result<&2, &2, Refused, Tree.Merged>:
  match ps:
    case Nil{}:
      Done{Tree.Merged{Nil{}, Nil{}}}
    case +first <> rest:
      status.tree.of.r(first, Tree.merge(events_of(picked(reached.all(fs, ps), Pick{waiting(fs), Nil{}}))))

# `target::parents`: `--onto`, then each `--merge`, none named twice; the
# head where nothing is named, or where one `--merge` is all there is; in
# digest order.
def status.onto.r(+fs: List<&2, Full>, +bs: List<&2, Bm.Bookmark>, onto: Maybe<&2, String>) -> Result<&2, &2, Refused, List<&2, String>>:
  match onto:
    case None{}:
      Done{Nil{}}
    case Some{+t}:
      do Result<&2, &2, Refused, List<&2, String>>:
        f : Full <- resolved.r(fs, bs, t)
        return [id_of(f)]

def status.named(+m: String, +id: String, +ps: List<&2, String>, twice: Bool) -> Result<&2, &2, Refused, List<&2, String>>:
  match twice:
    case True{}:
      Fail{Refused{1, "`" ++ m ++ "` is named twice, and a revision is its own parent exactly never"}}
    case False{}:
      Done{List.append(&2, String, ps, [id])}

def status.named.of(+m: String, +f: Full, +ps: List<&2, String>) -> Result<&2, &2, Refused, List<&2, String>>:
  status.named(m, id_of(f), ps, Rev.member(ps, id_of(f)))

def status.merged.r(+fs: List<&2, Full>, +bs: List<&2, Bm.Bookmark>, ms: List<&2, String>, +ps: List<&2, String>) -> Result<&2, &2, Refused, List<&2, String>>:
  match ms:
    case Nil{}:
      Done{ps}
    case +m <> rest:
      do Result<&2, &2, Refused, List<&2, String>>:
        f : Full <- resolved.r(fs, bs, m)
        more : List<&2, String> <- status.named.of(m, f, ps)
        status.merged.r(fs, bs, rest, more)

def status.with_head(h: Maybe<&2, String>, +ps: List<&2, String>) -> List<&2, String>:
  match h:
    case None{}:
      ps
    case Some{+id}:
      Bool.pick(List<&2, String>, Rev.member(ps, id), ps, List.append(&2, String, ps, [id]))

def status.head.r(+fs: List<&2, Full>, +bs: List<&2, Bm.Bookmark>, +ps: List<&2, String>, wants: Bool) -> Result<&2, &2, Refused, List<&2, String>>:
  match wants:
    case False{}:
      Done{ps}
    case True{}:
      do Result<&2, &2, Refused, List<&2, String>>:
        h : Maybe<&2, String> <- the_head.r(fs, bs, current_heads(history(fs)))
        return status.with_head(h, ps)

# The head is wanted where nothing is named, or where one `--merge` is all.
def status.wants(+n: List<&2, String>, +ms: List<&2, String>, +onto: Maybe<&2, String>) -> Bool:
  Bool.or(Nat.is_eq(List.length(&2, String, n), 0n), Bool.and(Nat.is_eq(List.length(&2, String, n), 1n), Bool.and(Bool.not(List.is_empty(&2, String, ms)), Maybe.is_none(&2, String, onto))))

def status.head.of(+fs: List<&2, Full>, +bs: List<&2, Bm.Bookmark>, +n: List<&2, String>, +ms: List<&2, String>, +onto: Maybe<&2, String>) -> Result<&2, &2, Refused, List<&2, String>>:
  status.head.r(fs, bs, n, status.wants(n, ms, onto))

# Each revision once, in digest order.
def status.sorted(all: List<&2, String>) -> List<&2, String>:
  distinct(List.sort(~String, ~(a => b => String.is_le(a, b)), all))

# `LAWS.status_joins_held_revisions`: every one is a revision the store holds.
def status.parents.r(+fs: List<&2, Full>, +bs: List<&2, Bm.Bookmark>, +onto: Maybe<&2, String>, +ms: List<&2, String>) -> Result<&2, &2, Refused, List<&2, String>>:
  do Result<&2, &2, Refused, List<&2, String>>:
    first : List<&2, String> <- status.onto.r(fs, bs, onto)
    named : List<&2, String> <- status.merged.r(fs, bs, ms, first)
    all : List<&2, String> <- status.head.of(fs, bs, named, ms, onto)
    return status.sorted(all)

def all_held(+ids: List<&2, String>, ps: List<&2, String>) -> Bool:
  match ps:
    case Nil{}:
      True{}
    case +p <> rest:
      Bool.and(Rev.member(ids, p), all_held(ids, rest))

# `render::contest_line`: one tree contest, as a person needs to hear it.
# A path several files claim is said as `claimed` instead.
def ab8(xs: List<&2, String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> rest:
      String.take(x, 8n) <> ab8(rest)

def lower_of(+what: String, +cs: List<&2, Tree.Claim>) -> String:
  what ++ Tree.first_what(cs, SNil{}) ++ ", which is the lower digest of " ++ String.join(Tree.claims_what(cs), " and ")

def contest.line(c: Tree.Contest) -> Maybe<&2, String>:
  match c:
    case Tree.Dropped{f, by}:
      Some{"kept " ++ String.take(f, 8n) ++ " : " ++ String.join(ab8(by), ", ") ++ " dropped it, and concurrent work did not"}
    case Tree.Moved{f, +cs}:
      Some{"moved " ++ String.take(f, 8n) ++ lower_of(" to ", cs)}
    case Tree.Content{f, cs}:
      Some{String.take(f, 8n) ++ " was stated whole by " ++ Nat.show(List.length(&2, Tree.Claim, cs)) ++ " concurrent revisions, and bytes do not merge; put the version you mean in the folder"}
    case Tree.ModeOf{f, +cs}:
      Some{String.take(f, 8n) ++ lower_of(" is ", cs)}
    case Tree.TargetOf{f, +cs}:
      Some{String.take(f, 8n) ++ lower_of(" points at ", cs)}
    case Tree.Referenced{f, by, +links}:
      Some{"kept " ++ String.take(f, 8n) ++ " : " ++ String.join(ab8(by), ", ") ++ " dropped it, and " ++ String.join(ab8(links), ", ") ++ " still " ++ Bool.pick(String, Nat.is_eq(List.length(&2, String, links), 1n), "points", "point") ++ " at it"}
    case Tree.Path{p, fs}:
      None{}

def contest.push(m: Maybe<&2, String>, rest: List<&2, String>) -> List<&2, String>:
  match m:
    case None{}:
      rest
    case Some{x}:
      x <> rest

def contest.lines(cs: List<&2, Tree.Contest>) -> List<&2, String>:
  match cs:
    case Nil{}:
      Nil{}
    case c <> rest:
      contest.push(contest.line(c), contest.lines(rest))

# Only where a person is joining work: a contest deeper in the graph was
# settled when its merge was recorded.
def contests.said(+ps: List<&2, String>, cs: List<&2, Tree.Contest>) -> List<&2, String>:
  Bool.pick(List<&2, String>, Nat.is_gt(List.length(&2, String, ps), 1n), contest.lines(cs), Nil{})

# What `LAWS.status_says_each_contest` reads in the contests: where work
# is joined, a line for each contest the merge found, in its order, opening
# with the file contested — a path several files claim is said as `claimed`
# instead — and where it is not, none.
def contest.opens(c: Tree.Contest) -> Maybe<&2, String>:
  match c:
    case Tree.Dropped{f, by}:
      Some{"kept " ++ String.take(f, 8n)}
    case Tree.Moved{f, cs}:
      Some{"moved " ++ String.take(f, 8n)}
    case Tree.Content{f, cs}:
      Some{String.take(f, 8n)}
    case Tree.ModeOf{f, cs}:
      Some{String.take(f, 8n)}
    case Tree.TargetOf{f, cs}:
      Some{String.take(f, 8n)}
    case Tree.Referenced{f, by, links}:
      Some{"kept " ++ String.take(f, 8n)}
    case Tree.Path{p, fs}:
      None{}

def contests.opens(cs: List<&2, Tree.Contest>) -> List<&2, String>:
  match cs:
    case Nil{}:
      Nil{}
    case c <> rest:
      contest.push(contest.opens(c), contests.opens(rest))

def contests.open(ls: List<&2, String>, os: List<&2, String>) -> Bool:
  match ls os:
    case Nil{} Nil{}:
      True{}
    case l <> lr o <> or:
      Bool.and(String.starts_with(l, o), contests.open(lr, or))
    case _ _:
      False{}

def contests.shown(+ps: List<&2, String>, cs: List<&2, Tree.Contest>, ls: List<&2, String>) -> Bool:
  match ls:
    case Nil{}:
      Bool.or(Bool.not(Nat.is_gt(List.length(&2, String, ps), 1n)), List.is_empty(&2, String, contests.opens(cs)))
    case +some:
      Bool.and(Nat.is_gt(List.length(&2, String, ps), 1n), contests.open(some, contests.opens(cs)))

# Printing
# --------

# The revisions the folder is compared with, named as `log` names them,
# with the bookmarks on each.
def names_list(bs: List<&2, Bm.Bookmark>, +h: Rev.History(), +id: String) -> List<&2, String>:
  match bs:
    case Nil{}:
      Nil{}
    case Bm.Bookmark{+n, t, p} <> rest:
      Rev.keep(names_at.one(h, id, t), n, names_list(rest, h, id))

def status.parent(+bs: List<&2, Bm.Bookmark>, +all_ids: List<&2, String>, +all_changes: List<&2, String>, +heads: List<&2, String>, +gone: List<&2, String>, +h: Rev.History(), f: Maybe<&2, Full>) -> List<&2, String>:
  match f:
    case None{}:
      Nil{}
    case Some{Full{+id, +change, parents, supersedes, author, when, revised_by, revised, facts, message}}:
      [abbreviate(change, all_changes) ++ "  " ++ abbreviate(id, all_ids) ++ parenthesised(List.append(&2, String, marks.list(id, change, parents, supersedes, heads, gone, h), names_list(bs, h, id)))]

def status.parents(+fs: List<&2, Full>, +bs: List<&2, Bm.Bookmark>, +h: Rev.History(), ps: List<&2, String>) -> List<&2, String>:
  match ps:
    case Nil{}:
      Nil{}
    case +p <> rest:
      List.append(&2, String, status.parent(bs, ids(fs), changes(fs), Rev.heads(h), Rev.superseded(h), h, find(fs, p)), status.parents(fs, bs, h, rest))

def status.position(+fs: List<&2, Full>, +bs: List<&2, Bm.Bookmark>, +ps: List<&2, String>) -> List<&2, String>:
  Bool.pick(List<&2, String>, List.is_empty(&2, String, ps), ["no revisions here yet"], status.parents(fs, bs, history(fs), ps))

def splits.said(+pre: String, +mid: String, +post: String, xs: List<&2, T.Split>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case T.Split{a, b} <> rest:
      (pre ++ a ++ mid ++ b ++ post) <> splits.said(pre, mid, post, rest)

def facts.said(xs: List<&2, T.Split>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case T.Split{k, p} <> rest:
      (pad(k, 7n) ++ " " ++ p) <> facts.said(rest)

def print_facts(xs: List<&2, T.Split>) -> IO(Unit):
  print_lines(facts.said(xs))

def accepts.said(xs: List<&2, String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case +p <> rest:
      ("accept  " ++ p ++ ": selected revisions state different bytes; record with --accept " ++ p) <> accepts.said(rest)

def renames.said(xs: List<&2, T.Split>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case T.Split{+from, +to} <> rest:
      SNil{} <> (from ++ " and " ++ to ++ " hold the same bytes; if that is a rename,") <> ("say so with --move " ++ from ++ "=" ++ to) <> renames.said(rest)

# `render::status`: where the folder is, and what it differs by.
def status.report(+fs: List<&2, Full>, +bs: List<&2, Bm.Bookmark>, +ps: List<&2, String>, cs: List<&2, Tree.Contest>, +sv: Sv.Survey) -> List<&2, String>:
  match sv:
    case Sv.Survey{facts, refused, claimed, accept, renames}:
      List.append(&2, String, status.position(fs, bs, ps),
      List.append(&2, String, facts.said(facts),
      List.append(&2, String, splits.said("refused ", ": ", SNil{}, refused),
      List.append(&2, String, splits.said("claimed ", ": ", " files claim it; say where each goes with --at", claimed),
      List.append(&2, String, accepts.said(accept),
      List.append(&2, String, contests.said(ps, cs),
      List.append(&2, String, Bool.pick(List<&2, String>, Sv.is_quiet(sv), ["nothing here differs from what is recorded"], Nil{}),
        renames.said(renames))))))))

# What `LAWS.status_says_what_it_found` reads in the report: each fact,
# refusal, claim and accept the survey found, in the order found, on a line
# of its own that names it — a fact beginning with its kind and ending with
# its path, a refusal or a claim beginning with its word and the path, an
# accept beginning `accept` and the path and ending with it. A line is
# looked for among those after the one the line before was found on.
type Expect is Data:
  Expect{starts: String, ends: String}

def expect.met(+l: String, e: Expect) -> Bool:
  match e:
    case Expect{s, t}:
      Bool.and(String.starts_with(l, s), String.ends_with(l, t))

def expect.first(ls: List<&2, String>, es: List<&2, Expect>) -> Bool:
  match ls es:
    case +l <> lr e <> er:
      expect.met(l, e)
    case _ _:
      False{}

def expect.go(ls: List<&2, String>, es: List<&2, Expect>, m: Bool) -> Bool:
  match ls es m:
    case _ Nil{} _:
      True{}
    case Nil{} e <> er _:
      False{}
    case l <> +lr e <> +er True{}:
      expect.go(lr, er, expect.first(lr, er))
    case l <> +lr +e <> +er False{}:
      expect.go(lr, e <> er, expect.first(lr, e <> er))

def expect.in(+ls: List<&2, String>, +es: List<&2, Expect>) -> Bool:
  expect.go(ls, es, expect.first(ls, es))

def facts.expect(xs: List<&2, T.Split>) -> List<&2, Expect>:
  match xs:
    case Nil{}:
      Nil{}
    case T.Split{k, p} <> rest:
      Expect{k, p} <> facts.expect(rest)

def splits.expect(+pre: String, xs: List<&2, T.Split>) -> List<&2, Expect>:
  match xs:
    case Nil{}:
      Nil{}
    case T.Split{a, b} <> rest:
      Expect{pre ++ a, SNil{}} <> splits.expect(pre, rest)

def accepts.expect(xs: List<&2, String>) -> List<&2, Expect>:
  match xs:
    case Nil{}:
      Nil{}
    case +p <> rest:
      Expect{"accept  " ++ p, p} <> accepts.expect(rest)

def status.expects(sv: Sv.Survey) -> List<&2, Expect>:
  match sv:
    case Sv.Survey{facts, refused, claimed, accept, renames}:
      List.append(&2, Expect, facts.expect(facts), List.append(&2, Expect, splits.expect("refused ", refused), List.append(&2, Expect, splits.expect("claimed ", claimed), accepts.expect(accept))))

def status.surveyed(+root: String, +fs: List<&2, Full>, +bs: List<&2, Bm.Bookmark>, +ps: List<&2, String>) -> IO(Unit):
  do IO<Unit>:
    rules : List<&2, Folder.Scope> <- Folder.rules(root)
    +rs : List<&2, Folder.Scope> = rules
    +repo : String = repository(root)
    w : Folder.Walked <- Folder.walk.all(repo, rs)
    +w2 : Folder.Walked = w
    m : Tree.Merged <- refused.io(Tree.Merged, status.tree.r(fs, ps))
    +m2 : Tree.Merged = m
    +t2 : Tree.Tree() = Tree.merged_tree(m2)
    refused.io(Unit, skips_held.r(skipped_held(rs, t2)))
    +cs : List<&2, T.Split> = Sv.claims(t2)
    +hs : List<&2, Here> = heres(Sv.unclaimed(t2, cs), Sv.unclaimed_found(Folder.walked.found(w2), cs), Limit.None{})
    +paths : List<&2, String> = regular_paths(hs)
    stats : List<&2, String> <- Store.stats(repo, paths)
    +dg : Map<&2, String> = stats.map(paths, stats, Map.new(&2, String))
    bf : Map<&2, String> <- status.befores.io(root, fs, ps, hs)
    +bf2 : Map<&2, String> = bf
    reads : Map<&2, List<&2, U32>> <- read_all(repo, status.reads(dg, bf2, hs), Map.new(&2, List<&2, U32>))
    +held : Set() = Set.from_list(T.map(~Folder.Found, ~String, ~(f => Folder.found.path(f)), Folder.walked.found(w2)))
    print_lines(status.report(fs, bs, ps, Tree.merged_contested(m2), Sv.survey(t2, held, Folder.walked.refused(w2), status.seens(t2, dg, bf2, reads, hs))))

def status.of(+root: String, +fs: List<&2, Full>, +bs: List<&2, Bm.Bookmark>, a: StatusCmd) -> IO(Unit):
  match a:
    case StatusCmd{+onto, +ms}:
      do IO<Unit>:
        ps : List<&2, String> <- refused.io(List<&2, String>, status.parents.r(fs, bs, onto, ms))
        +ps2 : List<&2, String> = ps
        readable(fs, ps2)
        status.surveyed(root, fs, bs, ps2)

def status(+args: List<&2, String>) -> IO(Unit):
  do IO<Unit>:
    root : String <- Store.root()
    +r : String = root
    rs : List<&2, Store.Doc> <- Store.revisions(r)
    bs : List<&2, Bm.Bookmark> <- bookmarks(r)
    +bs2 : List<&2, Bm.Bookmark> = bs
    a : StatusCmd <- refused.io(StatusCmd, status.args.r(args))
    status.of(r, opened.fulls(r, rs), bs2, a)

# record
# ------

# `record [<path>..] [-m <message>] [--onto <target>] [--merge <target>]..
# [--accept <path>].. [--at <file>=<path>].. [--move <old>=<new>]..
# [--bytes <path>].. [--lines <path>].. --dry-run`, read as the Rust tool
# reads it. Only the dry run is here: what recording would state is said,
# and nothing is written but the renames a person stated, which the Rust
# tool performs before it surveys, dry run or not.
type RecordCmd is Data:
  RecordCmd{onto: Maybe<&2, String>, merges: List<&2, String>, accepted: List<&2, String>, at: List<&2, T.Split>,
            moves: List<&2, T.Split>, kinds: List<&2, T.Split>, named: List<&2, String>, dry: Bool, fields: Bool,
            message: Maybe<&2, String>}

# What a word is to `record`: a flag and what it takes, or a path.
type RWord is Data:
  RWord.Message{}
  RWord.Onto{}
  RWord.Merge{}
  RWord.Accept{}
  RWord.At{}
  RWord.Move{}
  RWord.Bytes{}
  RWord.Lines{}
  RWord.Dry{}
  RWord.Fields{}
  RWord.Flag{}
  RWord.Path{}

def rword.of(+w: String) -> RWord:
  Bool.pick(RWord, Bool.or(String.eq(w, "-m"), String.eq(w, "--message")), RWord.Message{},
  Bool.pick(RWord, String.eq(w, "--onto"), RWord.Onto{},
  Bool.pick(RWord, String.eq(w, "--merge"), RWord.Merge{},
  Bool.pick(RWord, String.eq(w, "--accept"), RWord.Accept{},
  Bool.pick(RWord, String.eq(w, "--at"), RWord.At{},
  Bool.pick(RWord, String.eq(w, "--move"), RWord.Move{},
  Bool.pick(RWord, String.eq(w, "--bytes"), RWord.Bytes{},
  Bool.pick(RWord, String.eq(w, "--lines"), RWord.Lines{},
  Bool.pick(RWord, Bool.or(String.eq(w, "-n"), String.eq(w, "--dry-run")), RWord.Dry{},
  Bool.pick(RWord, String.eq(w, "--fields"), RWord.Fields{},
  Bool.pick(RWord, String.starts_with(w, "-"), RWord.Flag{}, RWord.Path{})))))))))))

def rword(args: List<&2, String>) -> RWord:
  match args:
    case Nil{}:
      RWord.Path{}
    case +w <> rest:
      rword.of(w)

def rc.onto(c: RecordCmd, v: String) -> RecordCmd:
  match c:
    case RecordCmd{o, ms, ac, at, mv, ks, ns, d, f, mg}:
      RecordCmd{Some{v}, ms, ac, at, mv, ks, ns, d, f, mg}

def rc.merge(c: RecordCmd, v: String) -> RecordCmd:
  match c:
    case RecordCmd{o, ms, ac, at, mv, ks, ns, d, f, mg}:
      RecordCmd{o, List.append(&2, String, ms, [v]), ac, at, mv, ks, ns, d, f, mg}

def rc.accept(c: RecordCmd, v: String) -> RecordCmd:
  match c:
    case RecordCmd{o, ms, ac, at, mv, ks, ns, d, f, mg}:
      RecordCmd{o, ms, v <> ac, at, mv, ks, ns, d, f, mg}

def rc.at(c: RecordCmd, v: T.Split) -> RecordCmd:
  match c:
    case RecordCmd{o, ms, ac, at, mv, ks, ns, d, f, mg}:
      RecordCmd{o, ms, ac, List.append(&2, T.Split, at, [v]), mv, ks, ns, d, f, mg}

def rc.move(c: RecordCmd, v: T.Split) -> RecordCmd:
  match c:
    case RecordCmd{o, ms, ac, at, mv, ks, ns, d, f, mg}:
      RecordCmd{o, ms, ac, at, List.append(&2, T.Split, mv, [v]), ks, ns, d, f, mg}

def rc.kind(c: RecordCmd, v: T.Split) -> RecordCmd:
  match c:
    case RecordCmd{o, ms, ac, at, mv, ks, ns, d, f, mg}:
      RecordCmd{o, ms, ac, at, mv, List.append(&2, T.Split, ks, [v]), ns, d, f, mg}

def rc.named(c: RecordCmd, v: String) -> RecordCmd:
  match c:
    case RecordCmd{o, ms, ac, at, mv, ks, ns, d, f, mg}:
      RecordCmd{o, ms, ac, at, mv, ks, v <> ns, d, f, mg}

def rc.dry(c: RecordCmd) -> RecordCmd:
  match c:
    case RecordCmd{o, ms, ac, at, mv, ks, ns, d, f, mg}:
      RecordCmd{o, ms, ac, at, mv, ks, ns, True{}, f, mg}

def rc.fields(c: RecordCmd) -> RecordCmd:
  match c:
    case RecordCmd{o, ms, ac, at, mv, ks, ns, d, f, mg}:
      RecordCmd{o, ms, ac, at, mv, ks, ns, d, True{}, mg}

def rc.message(c: RecordCmd, v: String) -> RecordCmd:
  match c:
    case RecordCmd{o, ms, ac, at, mv, ks, ns, d, f, mg}:
      RecordCmd{o, ms, ac, at, mv, ks, ns, d, f, Some{v}}

# `<one>=<other>`, cut at the first `=`.
def record.split.of(+msg: String, parts: List<&2, String>) -> Result<&2, &2, Refused, T.Split>:
  match parts:
    case a <> b <> rest:
      Done{T.Split{a, String.join(b <> rest, "=")}}
    case _:
      Fail{Refused{2, msg}}

def record.split(+v: String, +msg: String) -> Result<&2, &2, Refused, T.Split>:
  record.split.of(msg, String.split(v, '='))

# A path, with the slashes a shell leaves on a directory taken off.
def heads_slash(s: String) -> Bool:
  match s:
    case SCon{c, t}:
      Char.is_eq(c, '/')
    case SNil{}:
      False{}

def drop_slashes(s: String, slash: Bool) -> String:
  match s slash:
    case SCon{c, +t} True{}:
      drop_slashes(t, heads_slash(t))
    case other _:
      other

def trimmed(+p: String) -> String:
  +r = String.reverse(p)
  String.reverse(drop_slashes(r, heads_slash(r)))

def record.path(c: RecordCmd, +p: String) -> Result<&2, &2, Refused, RecordCmd>:
  Bool.pick(Result<&2, &2, Refused, RecordCmd>, String.is_empty(p), Fail{Refused{2, "`record` takes the paths to record, and an empty one names nothing"}}, Done{rc.named(c, p)})

def record.args.go(args: List<&2, String>, c: RecordCmd, k: RWord) -> Result<&2, &2, Refused, RecordCmd>:
  match args k:
    case Nil{} _:
      Done{c}
    case w <> Nil{} RWord.Message{}:
      Fail{Refused{2, "`-m` wants a value"}}
    case w <> v <> +rest RWord.Message{}:
      record.args.go(rest, rc.message(c, v), rword(rest))
    case w <> Nil{} RWord.Onto{}:
      Fail{Refused{2, "`--onto` wants a value"}}
    case w <> v <> +rest RWord.Onto{}:
      record.args.go(rest, rc.onto(c, v), rword(rest))
    case w <> Nil{} RWord.Merge{}:
      Fail{Refused{2, "`--merge` wants a value"}}
    case w <> v <> +rest RWord.Merge{}:
      record.args.go(rest, rc.merge(c, v), rword(rest))
    case w <> Nil{} RWord.Accept{}:
      Fail{Refused{2, "`--accept` wants a value"}}
    case w <> v <> +rest RWord.Accept{}:
      record.args.go(rest, rc.accept(c, v), rword(rest))
    case w <> Nil{} RWord.At{}:
      Fail{Refused{2, "`--at` wants a value"}}
    case w <> +v <> +rest RWord.At{}:
      do Result<&2, &2, Refused, RecordCmd>:
        s : T.Split <- record.split(v, "`--at` is spelled `--at <file>=<path>`")
        record.args.go(rest, rc.at(c, s), rword(rest))
    case w <> Nil{} RWord.Move{}:
      Fail{Refused{2, "`--move` wants a value"}}
    case w <> +v <> +rest RWord.Move{}:
      do Result<&2, &2, Refused, RecordCmd>:
        s : T.Split <- record.split(v, "`--move` is spelled `--move <old>=<new>`")
        record.args.go(rest, rc.move(c, s), rword(rest))
    case w <> Nil{} RWord.Bytes{}:
      Fail{Refused{2, "`--bytes` wants a value"}}
    case w <> v <> +rest RWord.Bytes{}:
      record.args.go(rest, rc.kind(c, T.Split{v, "bytes"}), rword(rest))
    case w <> Nil{} RWord.Lines{}:
      Fail{Refused{2, "`--lines` wants a value"}}
    case w <> v <> +rest RWord.Lines{}:
      record.args.go(rest, rc.kind(c, T.Split{v, "lines"}), rword(rest))
    case w <> +rest RWord.Dry{}:
      record.args.go(rest, rc.dry(c), rword(rest))
    case w <> +rest RWord.Fields{}:
      record.args.go(rest, rc.fields(c), rword(rest))
    case w <> rest RWord.Flag{}:
      Fail{Refused{2, "`" ++ w ++ "` is not an argument `record` takes"}}
    case +w <> +rest RWord.Path{}:
      do Result<&2, &2, Refused, RecordCmd>:
        more : RecordCmd <- record.path(c, trimmed(w))
        record.args.go(rest, more, rword(rest))

def record.args.r(+args: List<&2, String>) -> Result<&2, &2, Refused, RecordCmd>:
  record.args.go(args, RecordCmd{None{}, Nil{}, Nil{}, Nil{}, Nil{}, Nil{}, Nil{}, False{}, False{}, None{}}, rword(args))

# What `record`'s words say, read plainly. Each word is read as a flag and
# what it says: the word after a flag that takes a value is that value,
# whatever it is, and a word that is no flag is a path, with the slashes a
# shell leaves on a directory taken off. What each flag's words then mean
# is `rargs.said`; `LAWS.record_reads_its_words` holds `record.args.r` to it.
def rargs.read(args: List<&2, String>, k: RWord) -> List<&2, T.Split>:
  match args k:
    case Nil{} _:
      Nil{}
    case w <> v <> +rest RWord.Message{}:
      T.Split{"-m", v} <> rargs.read(rest, rword(rest))
    case w <> v <> +rest RWord.Onto{}:
      T.Split{"--onto", v} <> rargs.read(rest, rword(rest))
    case w <> v <> +rest RWord.Merge{}:
      T.Split{"--merge", v} <> rargs.read(rest, rword(rest))
    case w <> v <> +rest RWord.Accept{}:
      T.Split{"--accept", v} <> rargs.read(rest, rword(rest))
    case w <> v <> +rest RWord.At{}:
      T.Split{"--at", v} <> rargs.read(rest, rword(rest))
    case w <> v <> +rest RWord.Move{}:
      T.Split{"--move", v} <> rargs.read(rest, rword(rest))
    case w <> v <> +rest RWord.Bytes{}:
      T.Split{"--bytes", v} <> rargs.read(rest, rword(rest))
    case w <> v <> +rest RWord.Lines{}:
      T.Split{"--lines", v} <> rargs.read(rest, rword(rest))
    case w <> +rest RWord.Dry{}:
      T.Split{"--dry-run", SNil{}} <> rargs.read(rest, rword(rest))
    case w <> +rest RWord.Fields{}:
      T.Split{"--fields", SNil{}} <> rargs.read(rest, rword(rest))
    case +w <> +rest RWord.Path{}:
      T.Split{"path", trimmed(w)} <> rargs.read(rest, rword(rest))
    case w <> +rest _:
      rargs.read(rest, rword(rest))

# Every value a flag was given, in order.
def rargs.values(items: List<&2, T.Split>, +key: String) -> List<&2, String>:
  match items:
    case Nil{}:
      Nil{}
    case T.Split{+k, v} <> rest:
      +later = rargs.values(rest, key)
      Bool.pick(List<&2, String>, String.eq(k, key), v <> later, later)

# The last value a flag was given, or `last` where it was given none.
def rargs.last(items: List<&2, T.Split>, +key: String, last: Maybe<&2, String>) -> Maybe<&2, String>:
  match items:
    case Nil{}:
      last
    case T.Split{+k, v} <> rest:
      rargs.last(rest, key, Bool.pick(Maybe<&2, String>, String.eq(k, key), Some{v}, last))

# Whether a flag is there, or `had`.
def rargs.has(items: List<&2, T.Split>, +key: String, had: Bool) -> Bool:
  match items:
    case Nil{}:
      had
    case T.Split{+k, v} <> rest:
      rargs.has(rest, key, Bool.pick(Bool, String.eq(k, key), True{}, had))

# Each path `--bytes` and `--lines` name, with the kind it is said to be.
def rargs.kinds(items: List<&2, T.Split>) -> List<&2, T.Split>:
  match items:
    case Nil{}:
      Nil{}
    case T.Split{+k, +v} <> rest:
      +later = rargs.kinds(rest)
      Bool.pick(List<&2, T.Split>, String.eq(k, "--bytes"), T.Split{v, "bytes"} <> later,
      Bool.pick(List<&2, T.Split>, String.eq(k, "--lines"), T.Split{v, "lines"} <> later, later))

# `<one>=<other>` cut at its first `=`.
def rargs.cut.of(+v: String, parts: List<&2, String>) -> T.Split:
  match parts:
    case a <> b <> rest:
      T.Split{a, String.join(b <> rest, "=")}
    case _:
      T.Split{v, SNil{}}

def rargs.cut(+v: String) -> T.Split:
  rargs.cut.of(v, String.split(v, '='))

def rargs.cuts(vs: List<&2, String>) -> List<&2, T.Split>:
  match vs:
    case Nil{}:
      Nil{}
    case +v <> rest:
      rargs.cut(v) <> rargs.cuts(rest)

# What the words mean: the last `--onto`; each `--merge`, `--at`, `--move`,
# `--bytes` and `--lines`, in order, an `--at` or a `--move` cut at its
# first `=`; `-n` and `--fields` if they are there; the last `-m`. Each
# `--accept` and each path is kept too, the last first.
def rargs.said(+items: List<&2, T.Split>) -> RecordCmd:
  RecordCmd{rargs.last(items, "--onto", None{}), rargs.values(items, "--merge"), List.reverse(&2, String, rargs.values(items, "--accept")),
    rargs.cuts(rargs.values(items, "--at")), rargs.cuts(rargs.values(items, "--move")), rargs.kinds(items),
    List.reverse(&2, String, rargs.values(items, "path")), rargs.has(items, "--dry-run", False{}), rargs.has(items, "--fields", False{}),
    rargs.last(items, "-m", None{})}

# One path, two kinds, is a person who typed something they did not mean.
def kinds.differs(ks: List<&2, T.Split>, +p: String, +k: String) -> Bool:
  match ks:
    case Nil{}:
      False{}
    case T.Split{q, j} <> rest:
      Bool.or(Bool.and(String.eq(q, p), Bool.not(String.eq(j, k))), kinds.differs(rest, p, k))

def kinds.clash.r(ks: List<&2, T.Split>, +seen: List<&2, T.Split>) -> Result<&2, &2, Refused, Unit>:
  match ks:
    case Nil{}:
      Done{Unit{}}
    case T.Split{+p, +k} <> rest:
      Bool.pick(Result<&2, &2, Refused, Unit>, kinds.differs(seen, p, k),
        Fail{Refused{2, "`" ++ p ++ "` is stated as both bytes and lines, and it is one or the other"}},
        kinds.clash.r(rest, T.Split{p, k} <> seen))

def split_le(a: T.Split, b: T.Split) -> Bool:
  match a b:
    case T.Split{x, i} T.Split{y, j}:
      String.is_le(x, y)

def split_key(s: T.Split) -> String:
  match s:
    case T.Split{k, v}:
      k

def kinds.distinct(ks: List<&2, T.Split>) -> List<&2, T.Split>:
  match ks:
    case +a <> +b <> rest:
      +later = kinds.distinct(b <> rest)
      Bool.pick(List<&2, T.Split>, String.eq(split_key(a), split_key(b)), later, a <> later)
    case other:
      other

# What each kind is stated for, a path once, in path order.
def kinds.of(ks: List<&2, T.Split>) -> List<&2, T.Split>:
  kinds.distinct(List.sort(~T.Split, ~(a => b => split_le(a, b)), ks))

def lines.stated(ks: List<&2, T.Split>, +p: String) -> Bool:
  match ks:
    case Nil{}:
      False{}
    case T.Split{q, j} <> rest:
      Bool.or(Bool.and(String.eq(q, p), String.eq(j, "lines")), lines.stated(rest, p))

# A kind is a fact about a file, so a path with no file under it has none.
def kinds.unheld.r(ks: List<&2, T.Split>, +found: Set()) -> Result<&2, &2, Refused, Unit>:
  match ks:
    case Nil{}:
      Done{Unit{}}
    case T.Split{+p, k} <> rest:
      Bool.pick(Result<&2, &2, Refused, Unit>, Sv.has(found, p), kinds.unheld.r(rest, found),
        Fail{Refused{2, "`" ++ p ++ "` is not a file in this folder, so there is no kind for it to be"}})

# Every path given a kind is a file the folder holds.
# `LAWS.record_gives_kinds_only_to_files`.
def kinds.found(ks: List<&2, T.Split>, +found: Set()) -> Bool:
  match ks:
    case Nil{}:
      True{}
    case T.Split{+p, k} <> rest:
      Bool.and(Sv.has(found, p), kinds.found(rest, found))

# `--at`'s file, by a file bookmark or an identifier: `target::file_by_name`.
def at.file.of(+s: String, found: Maybe<&2, Bm.Target>) -> Result<&2, &2, Refused, String>:
  match found:
    case Some{Bm.Target.File{f}}:
      Done{f}
    case Some{other}:
      Fail{Refused{2, "the bookmark `" ++ s ++ "` names a " ++ Bm.kind(other) ++ ", and this position names a file"}}
    case None{}:
      Bool.pick(Result<&2, &2, Refused, String>, Id.is_assigned(s), Done{s}, Fail{Refused{2, "`" ++ s ++ "` is not a file identifier"}})

def at.files.r(+bs: List<&2, Bm.Bookmark>, ats: List<&2, T.Split>) -> Result<&2, &2, Refused, List<&2, T.Split>>:
  match ats:
    case Nil{}:
      Done{Nil{}}
    case T.Split{+f, to} <> rest:
      do Result<&2, &2, Refused, List<&2, T.Split>>:
        file : String <- at.file.of(f, Bm.find(bs, f))
        more : List<&2, T.Split> <- at.files.r(bs, rest)
        return T.Split{file, to} <> more

# `check_restriction`: a merge states every contested file, and a rename
# has two ends to name.
def restricted.half.r(+named: List<&2, String>, moves: List<&2, T.Split>) -> Result<&2, &2, Refused, Unit>:
  match moves:
    case Nil{}:
      Done{Unit{}}
    case T.Split{+from, +to} <> rest:
      Bool.pick(Result<&2, &2, Refused, Unit>, Bool.and(Sv.covers(named, from), Sv.covers(named, to)), restricted.half.r(named, rest),
        Fail{Refused{1, "`" ++ from ++ "` and `" ++ to ++ "` are one rename, and only one of them is among the paths this would record, which would spell the other end as a file appearing or disappearing; name both `" ++ from ++ "` and `" ++ to ++ "`, or record with no paths named"}})

def restricted.r(+named: List<&2, String>, +ps: List<&2, String>, moves: List<&2, T.Split>) -> Result<&2, &2, Refused, Unit>:
  Bool.pick(Result<&2, &2, Refused, Unit>, List.is_empty(&2, String, named), Done{Unit{}},
  Bool.pick(Result<&2, &2, Refused, Unit>, Nat.is_gt(List.length(&2, String, ps), 1n),
    Fail{Refused{1, "a merge states what every contested file is, and a merge of some of them would leave the rest joined and unstated; record the merge with no paths named, and restrict the record after it:" ++ skips_held.lines(named)}},
    restricted.half.r(named, moves)))

# A record restricted to some paths is no merge, and every rename it
# states is among those paths at both its ends.
# `LAWS.record_restricts_no_merge_and_no_half_rename`.
def renames.covered(+named: List<&2, String>, moves: List<&2, T.Split>) -> Bool:
  match moves:
    case Nil{}:
      True{}
    case T.Split{+from, +to} <> rest:
      Bool.and(Bool.and(Sv.covers(named, from), Sv.covers(named, to)), renames.covered(named, rest))

def restriction.whole(+named: List<&2, String>, +ps: List<&2, String>, +moves: List<&2, T.Split>) -> Bool:
  Bool.or(List.is_empty(&2, String, named), Bool.and(Bool.not(Nat.is_gt(List.length(&2, String, ps), 1n)), renames.covered(named, moves)))

# `--fields`'s header, and a refusal that owes it first: `historica-wrote-1`
# goes out before any refusal but a usage error, wherever the command stops.
def WROTE() -> String:
  "historica-wrote-1"

def name.header(b: Bool) -> IO(Unit):
  Bool.pick(IO(Unit), b, IO.print(WROTE()), IO.pure(Unit, Unit{}))

def stated.io(-A: Data, +late: Bool, r: Result<&2, &2, Refused, A>) -> IO(A):
  match r:
    case Fail{Refused{+code, msg}}:
      do IO<A>:
        name.header(Bool.and(late, Bool.not(U32.is_eq(code, 2))))
        die(A, code, msg)
    case Done{x}:
      IO.pure(A, x)

def header.refused(r: Result<&2, &2, String, Unit>) -> Result<&2, &2, Refused, Unit>:
  match r:
    case Fail{msg}:
      Fail{Refused{1, msg}}
    case Done{u}:
      Done{u}

# What opening the store refuses, asked without refusing: the header, then
# each bookmark, then each rule of `skipped/`, the first that is not what it
# should be named as `bookmarks` and `Folder.rules` name it.
def opening.bookmark(+file: String, r: Result<&2, &2, String, Bm.Stated>) -> Result<&2, &2, String, Unit>:
  match r:
    case Fail{e}:
      Fail{file ++ ": " ++ e}
    case Done{x}:
      Done{Unit{}}

def opening.rule(+file: String, st: Folder.Stated) -> Result<&2, &2, String, Unit>:
  match st:
    case Folder.Stated.Wrong{e}:
      Fail{file ++ ": " ++ e}
    case _:
      Done{Unit{}}

# A file of names or rules whose bytes are not UTF-8 refuses the opening.
def opening.read(+file: String, t: Result<&2, &2, String, String>, k: String -> Result<&2, &2, String, Unit>) -> Result<&2, &2, String, Unit>:
  match t:
    case Fail{e}:
      Fail{file ++ ": " ++ e}
    case Done{x}:
      k(x)

def opening.names(+root: String, ns: List<&2, Named>, r: Result<&2, &2, String, Unit>) -> IO(Result<&2, &2, String, Unit>):
  match ns r:
    case _ Fail{e}:
      IO.pure(Result<&2, &2, String, Unit>, Fail{e})
    case Nil{} Done{u}:
      IO.pure(Result<&2, &2, String, Unit>, Done{u})
    case Named{n, +p} <> rest Done{u}:
      do IO<Result<&2, &2, String, Unit>>:
        t : Result<&2, &2, String, String> <- Store.read_utf8(root ++ "/" ++ p)
        opening.names(root, rest, opening.read(root ++ "/" ++ p, t, x => opening.bookmark(root ++ "/" ++ p, Bm.parse(x))))

def opening.rules(+root: String, ps: List<&2, String>, r: Result<&2, &2, String, Unit>) -> IO(Result<&2, &2, String, Unit>):
  match ps r:
    case _ Fail{e}:
      IO.pure(Result<&2, &2, String, Unit>, Fail{e})
    case Nil{} Done{u}:
      IO.pure(Result<&2, &2, String, Unit>, Done{u})
    case +p <> rest Done{u}:
      do IO<Result<&2, &2, String, Unit>>:
        t : Result<&2, &2, String, String> <- Store.read_utf8(root ++ "/" ++ p)
        opening.rules(root, rest, opening.read(root ++ "/" ++ p, t, x => opening.rule(root ++ "/" ++ p, Folder.rule_in(x))))

def opening(+root: String, h: Result<&2, &2, String, Unit>) -> IO(Result<&2, &2, String, Unit>):
  match h:
    case Fail{e}:
      IO.pure(Result<&2, &2, String, Unit>, Fail{e})
    case Done{u}:
      do IO<Result<&2, &2, String, Unit>>:
        ns : List<&2, String> <- Store.name_paths(root)
        n : Result<&2, &2, String, Unit> <- opening.names(root, List.sort(~Named, ~(a => b => named.le(a, b)), named(ns)), Done{Unit{}})
        ps : List<&2, String> <- Store.skipped_paths(root)
        opening.rules(root, Folder.rules.kept(ps), n)

# The store opened by a command that owes `--fields` a statement (decision
# 0074): whatever opening it would refuse — a header this reader does not
# read, a bookmark or a rule that is not one — is refused here, the
# statement said first.
def opened.stated(+st: Bool, +root: String) -> IO(Unit):
  do IO<Unit>:
    h : Result<&2, &2, String, Unit> <- Store.header(root)
    o : Result<&2, &2, String, Unit> <- opening(root, h)
    stated.io(Unit, st, header.refused(o))

# The renames a person stated, done in the folder before it is read, as
# the Rust tool does them — whichever state the folder is in. Except for
# one that would leave the folder: an absolute path, or one climbing out
# with `..`, is refused once the survey asks, with the Rust tool's words,
# and moving first would have put the file wherever `/abs` or `../x`
# lands before saying no.
def escapes(+p: String) -> Bool:
  Bool.or(String.starts_with(p, "/"), List.any(~&2, ~String, ~(c => String.eq(c, "..")), String.split(p, '/')))

def performed(+st: Bool, +from: String, +to: String, r: Result<&1, &1, U32 & String, String>) -> IO(Unit):
  match r:
    case Fail{Tuple{code, msg}}:
      stated.io(Unit, st, Fail{Refused{1, msg}})
    case Done{"both"}:
      stated.io(Unit, st, Fail{Refused{1, "`" ++ from ++ "` and `" ++ to ++ "` are both here, so which one is the file is not something to guess at"}})
    case Done{"neither"}:
      stated.io(Unit, st, Fail{Refused{1, "neither `" ++ from ++ "` nor `" ++ to ++ "` is here"}})
    case Done{done}:
      IO.pure(Unit, Unit{})

def perform.one(+st: Bool, +repo: String, +from: String, +to: String, ok: Bool) -> IO(Unit):
  match ok:
    case False{}:
      IO.pure(Unit, Unit{})
    case True{}:
      do IO<Unit>:
        r : Result<&1, &1, U32 & String, String> <- Store.moved(repo ++ "\n" ++ from ++ "\n" ++ to)
        performed(st, from, to, r)

# `st` is whether a refusal owes `--fields`'s header first.
def perform(+st: Bool, +repo: String, moves: List<&2, T.Split>) -> IO(Unit):
  match moves:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case T.Split{+from, +to} <> rest:
      do IO<Unit>:
        perform.one(st, repo, from, to, Bool.not(Bool.or(escapes(from), escapes(to))))
        perform(st, repo, rest)

# Where the stated renames put each file: `--at` first, each naming a file
# the position holds, then each `--move` from a path one file holds to a
# path the format can.
type Placed is Data:
  Placed{tree: Tree.Tree(), moved: List<&2, T.Split>}

def placed.holds(+t: Tree.Tree(), ats: List<&2, T.Split>) -> Bool:
  match ats:
    case Nil{}:
      True{}
    case T.Split{+f, to} <> rest:
      Tree.holds(t, f)

def placed.at.r(ats: List<&2, T.Split>, +t: Tree.Tree(), moved: List<&2, T.Split>, held: Bool) -> Result<&2, &2, Refused, Placed>:
  match ats held:
    case Nil{} _:
      Done{Placed{t, moved}}
    case T.Split{f, to} <> rest False{}:
      Fail{Refused{1, "`" ++ f ++ "` is not a file this history holds, so nothing can be moved from it"}}
    case T.Split{+f, +to} <> +rest True{}:
      +t2 = Sv.relocated(t, f, to)
      placed.at.r(rest, t2, List.append(&2, T.Split, moved, [T.Split{f, to}]), placed.holds(t2, rest))

def contested.msg(+p: String, +fs: List<&2, String>) -> String:
  Nat.show(List.length(&2, String, fs)) ++ " files hold `" ++ p ++ "` here, so the path does not name one of them; say where each goes with --at:" ++ String.concat(T.map(~String, ~String, ~(f => "\n  --at " ++ f ++ "=<path>"), fs))

def files_at(+t: Tree.Tree(), +p: String) -> List<&2, String>:
  List.sort(~String, ~(a => b => String.is_le(a, b)), Tree.at(t, p))

def placed.head(+t: Tree.Tree(), ms: List<&2, T.Split>) -> List<&2, String>:
  match ms:
    case Nil{}:
      Nil{}
    case T.Split{+from, to} <> rest:
      files_at(t, from)

def placed.fault(ms: List<&2, T.Split>) -> Maybe<&2, String>:
  match ms:
    case Nil{}:
      None{}
    case T.Split{from, +to} <> rest:
      Sv.path_check(to)

def placed.move.r(ms: List<&2, T.Split>, +t: Tree.Tree(), moved: List<&2, T.Split>, at: List<&2, String>, fault: Maybe<&2, String>) -> Result<&2, &2, Refused, Placed>:
  match ms at fault:
    case Nil{} _ _:
      Done{Placed{t, moved}}
    case T.Split{from, to} <> rest Nil{} _:
      Fail{Refused{1, "`" ++ from ++ "` is not a file this history holds, so nothing can be moved from it"}}
    case T.Split{from, +to} <> +rest +f <> Nil{} None{}:
      +t2 = Sv.relocated(t, f, to)
      placed.move.r(rest, t2, List.append(&2, T.Split, moved, [T.Split{f, to}]), placed.head(t2, rest), placed.fault(rest))
    case T.Split{from, to} <> rest f <> Nil{} Some{because}:
      Fail{Refused{1, "`" ++ to ++ "` cannot be a path here: " ++ because}}
    case T.Split{+from, to} <> rest +several _:
      Fail{Refused{1, contested.msg(from, several)}}

def placed.of.r(p: Placed, +ms: List<&2, T.Split>) -> Result<&2, &2, Refused, Placed>:
  match p:
    case Placed{+t, moved}:
      placed.move.r(ms, t, moved, placed.head(t, ms), placed.fault(ms))

def placed.r(+t: Tree.Tree(), +ats: List<&2, T.Split>, +ms: List<&2, T.Split>) -> Result<&2, &2, Refused, Placed>:
  do Result<&2, &2, Refused, Placed>:
    p : Placed <- placed.at.r(ats, t, Nil{}, placed.holds(t, ats))
    placed.of.r(p, ms)

# Every file a stated rename moves is one of `files`: `--at` names a file
# the position holds, and `--move` a path one file alone holds there.
# `LAWS.record_moves_only_held_files`.
def moved.held(+files: List<&2, String>, moved: List<&2, T.Split>) -> Bool:
  match moved:
    case Nil{}:
      True{}
    case T.Split{+f, to} <> rest:
      Bool.and(Rev.member(files, f), moved.held(files, rest))

def placed.moved(p: Placed) -> List<&2, T.Split>:
  match p:
    case Placed{t, moved}:
      moved

# A named path nothing answers to, and whether a rule keeps it out.
def these(+ps: List<&2, String>, +one: String, +many: String) -> String:
  Bool.pick(String, Nat.is_eq(List.length(&2, String, ps), 1n), one, many)

def named.r(+rules: List<&2, Folder.Scope>, +named: List<&2, String>, +folder: List<&2, String>, +was: List<&2, String>, +placed: List<&2, String>) -> Result<&2, &2, Refused, Unit>:
  +unknown = Sv.unknown(named, folder, was, placed)
  +out = Sv.kept_out(rules, unknown, True{})
  +absent = Sv.kept_out(rules, unknown, False{})
  Bool.pick(Result<&2, &2, Refused, Unit>, Bool.not(List.is_empty(&2, String, out)),
    Fail{Refused{1, "`history/skipped/` says history does not take " ++ these(out, "this", "these") ++ ", and naming " ++ these(out, "it", "them") ++ " here does not make " ++ these(out, "it", "them") ++ " an exception; remove the rule if " ++ these(out, "it is", "they are") ++ " to be recorded:" ++ skips_held.lines(out)}},
  Bool.pick(Result<&2, &2, Refused, Unit>, Bool.not(List.is_empty(&2, String, absent)),
    Fail{Refused{1, these(absent, "this path is", "these paths are") ++ " neither in the folder nor in this history, so there is nothing there to observe; check the spelling, or name no paths at all and record everything the folder says:" ++ skips_held.lines(absent)}},
    Done{Unit{}}))

def record.fault.r(m: Maybe<&2, String>) -> Result<&2, &2, Refused, Unit>:
  match m:
    case None{}:
      Done{Unit{}}
    case Some{e}:
      Fail{Refused{1, e}}

# A file arriving that a person said is lines is read, and has to be text.
def lined_added(+ks: List<&2, T.Split>, hs: List<&2, Here>) -> List<&2, String>:
  match hs:
    case Nil{}:
      Nil{}
    case Here{+p, None{}, Some{Folder.Found.File{q, r, n}}} <> rest:
      Rev.keep(lines.stated(ks, p), p, lined_added(ks, rest))
    case h <> rest:
      lined_added(ks, rest)

def not_lines(+ks: List<&2, T.Split>, +reads: Map<&2, List<&2, U32>>, hs: List<&2, Here>) -> Maybe<&2, String>:
  match hs:
    case Nil{}:
      None{}
    case Here{+p, None{}, Some{Folder.Found.File{q, r, n}}} <> rest:
      Bool.pick(Maybe<&2, String>, Bool.and(lines.stated(ks, p), Bool.not(Folder.is_utf8(bytes_of(p, Map.get(List<&2, U32>, Nil{}, reads, p))))),
        Some{"`" ++ p ++ "` cannot be recorded as lines: its bytes are not UTF-8, and a line is text whoever says otherwise. Record it as bytes, or convert the file first"},
        not_lines(ks, reads, rest))
    case h <> rest:
      not_lines(ks, reads, rest)

# Every file `record` reads because a person said it is lines is text
# where recording goes on. `LAWS.record_reads_lines_as_text`.
def utf8.all(+reads: Map<&2, List<&2, U32>>, ps: List<&2, String>) -> Bool:
  match ps:
    case Nil{}:
      True{}
    case +p <> rest:
      Bool.and(Folder.is_utf8(bytes_of(p, Map.get(List<&2, U32>, Nil{}, reads, p))), utf8.all(reads, rest))

# What recording refuses that `status` only describes, in the order the
# Rust tool asks: a link left dangling, a path several files claim, what
# nothing here can take, what a merge would empty, and contested bytes
# accepted or not.
def minus(xs: List<&2, String>, +ys: List<&2, String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case +x <> rest:
      Rev.keep(Bool.not(Rev.member(ys, x)), x, minus(rest, ys))

def claimed.msg(+looked: Tree.Tree(), cs: List<&2, T.Split>) -> String:
  match cs:
    case Nil{}:
      SNil{}
    case T.Split{+p, n} <> rest:
      contested.msg(p, files_at(looked, p))

def refused.line(r: T.Split) -> String:
  match r:
    case T.Split{p, b}:
      "\n  " ++ p ++ " (" ++ b ++ ")"

def refused.msg(+rs: List<&2, T.Split>) -> String:
  +n = List.length(&2, T.Split, rs)
  +one = Nat.is_eq(n, 1n)
  Bool.pick(String, one, "one file", Nat.show(n) ++ " files") ++ " the folder holds " ++ Bool.pick(String, one, "is", "are") ++ " not something this format can record; rename or `skip` " ++ Bool.pick(String, one, "it", "them") ++ " in `history/skipped/`:" ++ String.concat(T.map(~T.Split, ~String, ~(r => refused.line(r)), rs))

def accept.lines(ps: List<&2, String>) -> String:
  match ps:
    case Nil{}:
      SNil{}
    case p <> rest:
      "\n  --accept " ++ p ++ accept.lines(rest)

def planned.r(+looked: Tree.Tree(), pl: Sv.Planned, +accepted: List<&2, String>) -> Result<&2, &2, Refused, Sv.Planned>:
  match pl:
    case Sv.Planned{facts, +refused, +claimed, +accept, +emptied, Some{m}, obs, links}:
      Fail{Refused{1, m}}
    case Sv.Planned{facts, +refused, +claimed, +accept, +emptied, None{}, obs, links}:
      +un = minus(accept, accepted)
      +needless = minus(accepted, accept)
      Bool.pick(Result<&2, &2, Refused, Sv.Planned>, Bool.not(List.is_empty(&2, T.Split, claimed)), Fail{Refused{1, claimed.msg(looked, claimed)}},
      Bool.pick(Result<&2, &2, Refused, Sv.Planned>, Bool.not(List.is_empty(&2, T.Split, refused)), Fail{Refused{1, refused.msg(refused)}},
      Bool.pick(Result<&2, &2, Refused, Sv.Planned>, Bool.not(List.is_empty(&2, String, emptied)),
        Fail{Refused{1, "a merge states what each contested file is, and there is no way to state that one is empty; leave " ++ these(emptied, "it", "them") ++ " something and remove it in the revision after, or drop it here:" ++ skips_held.lines(emptied)}},
      Bool.pick(Result<&2, &2, Refused, Sv.Planned>, Bool.not(List.is_empty(&2, String, un)),
        Fail{Refused{1, "concurrent work states different bytes for " ++ these(un, "one attachment", "these attachments") ++ "; inspect " ++ these(un, "it", "them") ++ " and explicitly accept what the folder holds:" ++ accept.lines(un)}},
      Bool.pick(Result<&2, &2, Refused, Sv.Planned>, Bool.not(List.is_empty(&2, String, needless)),
        Fail{Refused{1, these(needless, "this path is not a contested attachment", "these paths are not contested attachments") ++ "; remove the unnecessary acceptance:" ++ accept.lines(needless)}},
        Done{Sv.Planned{facts, refused, claimed, accept, emptied, None{}, obs, links}})))))

# What `record` goes on to write is a plan the survey settled: no path
# several files claim, nothing the format cannot record, nothing a merge
# would leave empty, no fault, and the attachments accepted exactly the
# ones concurrent work contests. `LAWS.record_writes_only_what_is_settled`.
def planned.settled(pl: Sv.Planned, +accepted: List<&2, String>) -> Bool:
  match pl:
    case Sv.Planned{facts, refused, claimed, +accept, emptied, fault, obs, links}:
      Bool.and(List.is_empty(&2, T.Split, claimed), Bool.and(List.is_empty(&2, T.Split, refused), Bool.and(List.is_empty(&2, String, emptied),
        Bool.and(Maybe.is_none(&2, String, fault), Bool.and(List.is_empty(&2, String, minus(accept, accepted)), List.is_empty(&2, String, minus(accepted, accept)))))))

def record.print.lines(fs: List<&2, T.Split>) -> List<&2, String>:
  match fs:
    case Nil{}:
      ["nothing here differs from what is recorded"]
    case some:
      facts.said(some)

def record.print(fs: List<&2, T.Split>) -> IO(Unit):
  print_lines(record.print.lines(fs))

def found_paths(fs: List<&2, Folder.Found>) -> List<&2, String>:
  T.map(~Folder.Found, ~String, ~(f => Folder.found.path(f)), fs)

# Writing
# -------

# What a record that writes knows before it surveys: who, when, why, and
# whether it states what it wrote for a machine.
type Writing is Data:
  Writing{author: String, when: String, message: String, fields: Bool}

def split.head(s: T.Split) -> String:
  match s:
    case T.Split{h, r}:
      h

def split.rest(s: T.Split) -> String:
  match s:
    case T.Split{h, r}:
      r

def by_head(+xs: List<&2, T.Split>) -> List<&2, T.Split>:
  List.sort(~T.Split, ~(a => b => String.is_le(split.head(a), split.head(b))), xs)

def lookup(xs: List<&2, T.Split>, +key: String) -> Maybe<&2, String>:
  match xs:
    case Nil{}:
      None{}
    case T.Split{+k, v} <> rest:
      Bool.pick(Maybe<&2, String>, String.eq(k, key), Some{v}, lookup(rest, key))

# Minting: hex from the host, cut into identifiers twelve bytes each, and
# spelled as the format spells one.
def hex_nibble(c: Char) -> U32:
  match c:
    case Chr{+x}:
      Bool.pick(U32, U32.is_ge(x, 97), (x - 87 : U32), (x - 48 : U32))

def hex_bytes(s: String) -> List<&2, U32>:
  match s:
    case SCon{hi, SCon{lo, rest}}:
      (((hex_nibble(hi) << 4n) .|. hex_nibble(lo)) : U32) <> hex_bytes(rest)
    case _:
      Nil{}

def ids.minted(n: Nat, +hex: String) -> List<&2, String>:
  match n:
    case 0n:
      Nil{}
    case 1n+k:
      Id.spell(hex_bytes(String.take(hex, 24n))) <> ids.minted(k, String.drop(hex, 24n))

def zipped(ps: List<&2, String>, ids: List<&2, String>) -> List<&2, T.Split>:
  match ps ids:
    case p <> rest i <> more:
      T.Split{p, i} <> zipped(rest, more)
    case _ _:
      Nil{}

# The one file at a path of the tree this revision states: minted here, or
# the only file the position holds there.
def file_at.held(fs: List<&2, String>) -> Maybe<&2, String>:
  match fs:
    case f <> Nil{}:
      Some{f}
    case _:
      None{}

def file_at(+mint: List<&2, T.Split>, +t: Tree.Tree(), +path: String) -> Maybe<&2, String>:
  Maybe.or(&2, String, lookup(mint, path), file_at.held(Tree.at(t, path)))

# What a record says a file holds now: an operation document, the text of
# a file arriving, or a payload of bytes the folder still has.
type Content is Data:
  Content.Ops{file: String, path: String, doc: String}
  Content.Text{file: String, path: String, bytes: List<&2, U32>}
  Content.Whole{file: String, path: String, digest: String}

def content.held(c: Content) -> String:
  match c:
    case Content.Ops{f, p, doc}:
      Sha.digest(Utf8.encode(doc))
    case Content.Text{f, p, bs}:
      Sha.digest(bs)
    case Content.Whole{f, p, d}:
      d

def content.file(c: Content) -> String:
  match c:
    case Content.Ops{f, p, doc}:
      f
    case Content.Text{f, p, bs}:
      f
    case Content.Whole{f, p, d}:
      f

def content.path(c: Content) -> String:
  match c:
    case Content.Ops{f, p, doc}:
      p
    case Content.Text{f, p, bs}:
      p
    case Content.Whole{f, p, d}:
      p

def content.key(c: Content) -> String:
  match c:
    case Content.Ops{f, p, doc}:
      "edit"
    case Content.Text{f, p, bs}:
      "text"
    case Content.Whole{f, p, d}:
      "bytes"

def content.document(c: Content) -> Bool:
  match c:
    case Content.Ops{f, p, doc}:
      True{}
    case _:
      False{}

def content.filing(+c: Content) -> Naming.Filing:
  Naming.Filing{content.held(c), content.path(c), content.document(c)}

def content.line(+c: Content) -> T.Split:
  T.Split{content.file(c), content.key(c) ++ " " ++ content.file(c) ++ " " ++ content.held(c)}

# What the position's content of a file of lines is, replayed, by file.
type Before is Data:
  Before{file: String, items: List<&2, Ops.Item>}

def befores.of(+f: String, got: Result<&2, &2, String, List<&2, Ops.Item>>, more: Result<&2, &2, Refused, List<&2, Before>>) -> Result<&2, &2, Refused, List<&2, Before>>:
  match got:
    case Fail{e}:
      Fail{Refused{1, e}}
    case Done{items}:
      do Result<&2, &2, Refused, List<&2, Before>>:
        later : List<&2, Before> <- more
        return Before{f, items} <> later

def befores.r(+older: List<&2, Full>, +ds: List<&2, Store.Doc>, +left: String, files: List<&2, String>) -> Result<&2, &2, Refused, List<&2, Before>>:
  match files:
    case Nil{}:
      Done{Nil{}}
    case +f <> rest:
      befores.of(f, content.in(older, ds, left, f), befores.r(older, ds, left, rest))

def befores.io(+st: Bool, +root: String, +fs: List<&2, Full>, ps: List<&2, String>, files: List<&2, String>) -> IO(List<&2, Before>):
  match ps files:
    case +left <> Nil{} +some <> +others:
      do IO<List<&2, Before>>:
        ds : List<&2, Store.Doc> <- Store.fetch(root, distinct(List.sort(~String, ~(a => b => String.is_le(a, b)), wanted_all(fs, some <> others))))
        +ds2 : List<&2, Store.Doc> = ds
        more : List<&2, Store.Doc> <- Store.fetch(root, kept_digests(ds2))
        stated.io(List<&2, Before>, st, befores.r(oldest_of(fs, Some{left}), List.append(&2, Store.Doc, ds2, more), left, some <> others))
    case _ _:
      IO.pure(List<&2, Before>, Nil{})

def before_of(bs: List<&2, Before>, +file: String) -> List<&2, Ops.Item>:
  match bs:
    case Nil{}:
      Nil{}
    case Before{+f, items} <> rest:
      Bool.pick(List<&2, Ops.Item>, String.eq(f, file), items, before_of(rest, file))

# The files of lines a record edits, whose position's content it replays.
def edited.lines(+edited: List<&2, String>, hs: List<&2, Here>) -> List<&2, String>:
  match hs:
    case Nil{}:
      Nil{}
    case Here{+p, Some{Tree.Entry{f, q, Tree.Lines{}, y, g, m}}, Some{Folder.Found.File{r, x, n}}} <> rest:
      Rev.keep(Rev.member(edited, p), f, edited.lines(edited, rest))
    case h <> rest:
      edited.lines(edited, rest)

# A file the folder holds that a record is adding, and so reads: every
# regular file with no entry at its path, or an entry that is a link.
def added.regular(hs: List<&2, Here>) -> List<&2, String>:
  match hs:
    case Nil{}:
      Nil{}
    case Here{p, None{}, Some{Folder.Found.File{q, r, n}}} <> rest:
      p <> added.regular(rest)
    case Here{p, Some{Tree.Entry{f, q, Tree.Link{}, y, g, m}}, Some{Folder.Found.File{r, x, n}}} <> rest:
      p <> added.regular(rest)
    case h <> rest:
      added.regular(rest)

def kind.stated(ks: List<&2, T.Split>, +p: String) -> Maybe<&2, String>:
  lookup(ks, p)

# Decision 0017's sniff, or what a person said: bytes that are UTF-8 with
# no NUL are lines, and a file of lines with nothing in it states nothing.
def arriving.kind(+file: String, +p: String, +digest: String, +bs: List<&2, U32>, lines: Bool) -> List<&2, Content>:
  match lines:
    case True{}:
      Bool.pick(List<&2, Content>, List.is_empty(&2, U32, bs), Nil{}, [Content.Text{file, p, bs}])
    case False{}:
      [Content.Whole{file, p, digest}]

def arriving.of(+file: String, +p: String, +digest: String, +bs: List<&2, U32>, stated: Maybe<&2, String>) -> List<&2, Content>:
  match stated:
    case Some{k}:
      Bool.pick(List<&2, Content>, String.eq(k, "bytes"), [Content.Whole{file, p, digest}], arriving.kind(file, p, digest, bs, True{}))
    case None{}:
      arriving.kind(file, p, digest, bs, Bool.and(Folder.is_utf8(bs), Bool.not(Folder.has_nul(bs))))

# What each path contributes: the content of a file arriving or edited, and
# the mode of one arriving that can be run.
type Stating is Data:
  Stating{contents: List<&2, Content>, modes: List<&2, T.Split>}

def edited.content(+f: String, +p: String, d: Maybe<&2, Ops.Doc>) -> List<&2, Content>:
  match d:
    case None{}:
      Nil{}
    case Some{doc}:
      [Content.Ops{f, p, Ops.write(doc)}]

def stating.held(+edited: List<&2, String>, +befores: List<&2, Before>, +p: String, e: Maybe<&2, Tree.Entry>, +digest: String, +bs: List<&2, U32>) -> Stating:
  match e:
    case Some{Tree.Entry{+f, q, Tree.Whole{}, y, g, m}}:
      Stating{Bool.pick(List<&2, Content>, Rev.member(edited, p), [Content.Whole{f, p, digest}], Nil{}), Nil{}}
    case Some{Tree.Entry{+f, q, Tree.Lines{}, y, g, m}}:
      Stating{Bool.pick(List<&2, Content>, Rev.member(edited, p), edited.content(f, p, Ops.diff(before_of(befores, f), Ops.from_text(Utf8.decode(bs)))), Nil{}), Nil{}}
    case _:
      Stating{Nil{}, Nil{}}

def stating.at(+mint: List<&2, T.Split>, +edited: List<&2, String>, +ks: List<&2, T.Split>, +befores: List<&2, Before>, +p: String, e: Maybe<&2, Tree.Entry>, +digest: String, +bs: List<&2, U32>, +runs: Bool, arriving: Bool) -> Stating:
  match arriving:
    case True{}:
      +file = Maybe.default(&2, String, lookup(mint, p), SNil{})
      Stating{arriving.of(file, p, digest, bs, kind.stated(ks, p)), Bool.pick(List<&2, T.Split>, runs, [T.Split{file, "executable"}], Nil{})}
    case False{}:
      stating.held(edited, befores, p, e, digest, bs)

def stating.of(+mint: List<&2, T.Split>, +arriving: List<&2, String>, +edited: List<&2, String>, +ks: List<&2, T.Split>, +dg: Map<&2, String>, +reads: Map<&2, List<&2, U32>>, +befores: List<&2, Before>, h: Here) -> Stating:
  match h:
    case Here{+p, e, Some{Folder.Found.File{q, +runs, n}}}:
      stating.at(mint, edited, ks, befores, p, e, status.folder_digest(dg, p), bytes_of(p, Map.get(List<&2, U32>, Nil{}, reads, p)), runs, Rev.member(arriving, p))
    case _:
      Stating{Nil{}, Nil{}}

def stating.join(a: Stating, b: Stating) -> Stating:
  match a b:
    case Stating{c1, m1} Stating{c2, m2}:
      Stating{List.append(&2, Content, c1, c2), List.append(&2, T.Split, m1, m2)}

def stating.all(+mint: List<&2, T.Split>, +arriving: List<&2, String>, +edited: List<&2, String>, +ks: List<&2, T.Split>, +dg: Map<&2, String>, +reads: Map<&2, List<&2, U32>>, +befores: List<&2, Before>, hs: List<&2, Here>) -> Stating:
  match hs:
    case Nil{}:
      Stating{Nil{}, Nil{}}
    case h <> rest:
      stating.join(stating.of(mint, arriving, edited, ks, dg, reads, befores, h), stating.all(mint, arriving, edited, ks, dg, reads, befores, rest))

# The mode each held file now has where it changed: the folder's bit.
def mode.held(changed: Bool, f: Maybe<&2, String>, runs: Bool, later: List<&2, T.Split>) -> List<&2, T.Split>:
  match changed f:
    case True{} Some{file}:
      T.Split{file, Bool.pick(String, runs, "executable", "plain")} <> later
    case _ _:
      later

def modes.held(+mint: List<&2, T.Split>, +t: Tree.Tree(), +changed: List<&2, String>, hs: List<&2, Here>) -> List<&2, T.Split>:
  match hs:
    case Nil{}:
      Nil{}
    case Here{+p, e, Some{Folder.Found.File{q, runs, n}}} <> rest:
      mode.held(Rev.member(changed, p), file_at(mint, t, p), runs, modes.held(mint, t, changed, rest))
    case h <> rest:
      modes.held(mint, t, changed, rest)

# Each link the record states, spelled: `file:` and the identifier where the
# folder's string resolves to one file of the tree this revision states,
# and the string otherwise.
def link.resolved(+at: String, f: Maybe<&2, String>) -> String:
  match f:
    case Some{file}:
      "file:" ++ file
    case None{}:
      at

def link.spelled.of(+mint: List<&2, T.Split>, +t: Tree.Tree(), +observed: String, r: Maybe<&2, String>) -> String:
  match r:
    case Some{+at}:
      link.resolved(at, file_at(mint, t, at))
    case None{}:
      String.drop(observed, 1n)

def link.spelled(+mint: List<&2, T.Split>, +t: Tree.Tree(), +observed: String) -> String:
  link.spelled.of(mint, t, observed, T.strip_prefix(observed, "r"))

def link.stated(f: Maybe<&2, String>, spelled: String, later: List<&2, T.Split>) -> List<&2, T.Split>:
  match f:
    case None{}:
      later
    case Some{file}:
      T.Split{file, spelled} <> later

def links.stated(+mint: List<&2, T.Split>, +t: Tree.Tree(), +gone: Set(), +arriving: Set(), +pointing: List<&2, T.Split>, ls: List<&2, String>) -> List<&2, T.Split>:
  match ls:
    case Nil{}:
      Nil{}
    case +p <> rest:
      link.stated(file_at(mint, t, p), link.spelled(mint, t, Sv.observed(t, gone, arriving, p, Maybe.default(&2, String, lookup(pointing, p), SNil{}))), links.stated(mint, t, gone, arriving, pointing, rest))

def headers(+key: String, xs: List<&2, T.Split>) -> List<&2, Rev.Header>:
  match xs:
    case Nil{}:
      Nil{}
    case T.Split{f, +v} <> rest:
      Rev.Header{key, f ++ Bool.pick(String, String.is_empty(v), SNil{}, " " ++ v)} <> headers(key, rest)

def content.headers(cs: List<&2, T.Split>) -> List<&2, Rev.Header>:
  match cs:
    case Nil{}:
      Nil{}
    case T.Split{f, line} <> rest:
      +parts = T.split_once(line)
      Rev.Header{Maybe.default(&2, String, Maybe.map(&2, T.Split, String, s => split.head(s), parts), SNil{}), Maybe.default(&2, String, Maybe.map(&2, T.Split, String, s => split.rest(s), parts), SNil{})} <> content.headers(rest)

def keyed(+key: String, cs: List<&2, Content>) -> List<&2, T.Split>:
  match cs:
    case Nil{}:
      Nil{}
    case +c <> rest:
      +later = keyed(key, rest)
      Bool.pick(List<&2, T.Split>, String.eq(content.key(c), key), content.line(c) <> later, later)

# The facts in the order the format fixes, each kind sorted by file.
def record.facts(+added: List<&2, T.Split>, +moved: List<&2, T.Split>, +modes: List<&2, T.Split>, +dropped: List<&2, String>, +cs: List<&2, Content>, +links: List<&2, T.Split>) -> List<&2, Rev.Header>:
  List.concat(&2, Rev.Header, [
    headers("add", by_head(added)), headers("move", by_head(moved)), headers("mode", by_head(modes)),
    headers("drop", by_head(T.map(~String, ~T.Split, ~(f => T.Split{f, SNil{}}), dropped))),
    content.headers(by_head(keyed("edit", cs))), content.headers(by_head(keyed("text", cs))), content.headers(by_head(keyed("bytes", cs))),
    headers("link", by_head(links))])

def swapped(xs: List<&2, T.Split>) -> List<&2, T.Split>:
  match xs:
    case Nil{}:
      Nil{}
    case T.Split{a, b} <> rest:
      T.Split{b, a} <> swapped(rest)

def full.named(f: Full) -> Naming.Named:
  match f:
    case Full{i, change, ps, ss, a, when, rb, rv, fs, message}:
      Naming.Named{when, message, change}

def full.dated(f: Full) -> T.Split:
  match f:
    case Full{i, change, ps, ss, a, when, rb, rv, fs, message}:
      T.Split{i, when}

def full.change_of(fs: List<&2, Full>, +id: String) -> Maybe<&2, String>:
  match fs:
    case Nil{}:
      None{}
    case Full{+i, change, ps, ss, a, when, rb, rv, facts, message} <> rest:
      Bool.pick(Maybe<&2, String>, String.eq(i, id), Some{change}, full.change_of(rest, id))

def parents.changes(+fs: List<&2, Full>, ps: List<&2, String>) -> List<&2, String>:
  match ps:
    case Nil{}:
      Nil{}
    case +p <> rest:
      List.append(&2, String, Maybe.default(&2, List<&2, String>, Maybe.map(&2, String, List<&2, String>, c => [c], full.change_of(fs, p)), Nil{}), parents.changes(fs, rest))

# The bookmarks that follow the work forward: every one naming the change
# of a parent. A `revision` pin does not move, nor does a file's.
def advancing(+changes: List<&2, String>, bs: List<&2, Bm.Bookmark>) -> List<&2, Bm.Bookmark>:
  match bs:
    case Nil{}:
      Nil{}
    case Bm.Bookmark{+n, Bm.Target.Change{+c}, +p} <> rest:
      +later = advancing(changes, rest)
      Bool.pick(List<&2, Bm.Bookmark>, Rev.member(changes, c), Bm.Bookmark{n, Bm.Target.Change{c}, p} <> later, later)
    case b <> rest:
      advancing(changes, rest)

def wrote.io(+st: Bool, r: Result<&1, &1, U32 & String, String>) -> IO(String):
  match r:
    case Fail{Tuple{code, msg}}:
      stated.io(String, st, Fail{Refused{1, msg}})
    case Done{answer}:
      IO.pure(String, answer)

def advance(+st: Bool, +root: String, +change: String, bs: List<&2, Bm.Bookmark>) -> IO(List<&2, String>):
  match bs:
    case Nil{}:
      IO.pure(List<&2, String>, Nil{})
    case Bm.Bookmark{+n, t, +private} <> rest:
      do IO<List<&2, String>>:
        w : Result<&1, &1, U32 & String, String> <- Store.written(root ++ "/names/" ++ n ++ ".txt\n" ++ Bm.write(Bm.Stated{Bm.Target.Change{change}, private}))
        done_w : String <- wrote.io(st, w)
        later : List<&2, String> <- advance(st, root, change, rest)
        return n <> later

def filed.one(+repo: String, +name: String, c: Content) -> IO(Result<&1, &1, U32 & String, String>):
  match c:
    case Content.Ops{f, p, doc}:
      Store.filed(name ++ "\n" ++ doc)
    case Content.Text{f, p, bs}:
      Store.filed(name ++ "\n" ++ Utf8.decode(bs))
    case Content.Whole{f, p, d}:
      Store.copied(repo ++ "/" ++ p ++ "\n" ++ name ++ "\n" ++ d)

# Each file of content filed under the revision's stem, unless the store
# already holds its digest anywhere: then it is there, and stays where it is.
def filed.io(+st: Bool, +root: String, +repo: String, +stem: String, +names: List<&2, T.Split>, cs: List<&2, Content>, at: List<&2, String>) -> IO(Unit):
  match cs at:
    case +c <> rest "-" <> more:
      +name = root ++ "/operations/" ++ stem ++ "/" ++ Naming.filed_as(names, content.held(c))
      do IO<Unit>:
        w : Result<&1, &1, U32 & String, String> <- filed.one(repo, name, c)
        done_w : String <- wrote.io(st, w)
        filed.io(st, root, repo, stem, names, rest, more)
    case c <> rest a <> more:
      filed.io(st, root, repo, stem, names, rest, more)
    case _ _:
      IO.pure(Unit, Unit{})

def said.lines(+prefix: String, +suffix: String, ns: List<&2, String>) -> List<&2, String>:
  match ns:
    case Nil{}:
      Nil{}
    case n <> rest:
      (prefix ++ n ++ suffix) <> said.lines(prefix, suffix, rest)

def said.names(+prefix: String, +suffix: String, ns: List<&2, String>) -> IO(Unit):
  print_lines(said.lines(prefix, suffix, ns))

# What a record says it did: for a machine, decision 0074's header, the
# revision, and each bookmark moved; for a person, the facts, the change
# and the revision, each bookmark moved, and whether this is a root.
def record.said.lines(w: Writing, +facts: List<&2, T.Split>, +change: String, +id: String, +names: List<&2, String>, +ps: List<&2, String>) -> List<&2, String>:
  match w:
    case Writing{a, when, m, True{}}:
      WROTE() <> ("revision " ++ id) <> said.lines("name ", SNil{}, names)
    case Writing{a, when, m, False{}}:
      List.concat(&2, String, [facts.said(facts), ["recorded " ++ String.take(change, 8n) ++ " as " ++ String.take(id, 12n)], said.lines(SNil{}, " -> " ++ String.take(change, 8n), names),
        Bool.pick(List<&2, String>, List.is_empty(&2, String, ps), ["this is a root: it has no parent"], Nil{})])

def record.said(+w: Writing, +facts: List<&2, T.Split>, +change: String, +id: String, +names: List<&2, String>, +ps: List<&2, String>) -> IO(Unit):
  print_lines(record.said.lines(w, facts, change, id, names, ps))

def stating.contents(s: Stating) -> List<&2, Content>:
  match s:
    case Stating{cs, ms}:
      cs

def stating.modes(s: Stating) -> List<&2, T.Split>:
  match s:
    case Stating{cs, ms}:
      ms

def writing.rev(w: Writing, +change: String, +ps: List<&2, String>, +facts: List<&2, Rev.Header>) -> Rev.Rev:
  match w:
    case Writing{author, when, message, f}:
      Rev.Rev{change, List.sort(~String, ~(a => b => String.is_le(a, b)), ps), Nil{}, author, when, None{}, None{}, facts, message}

def writing.stem(w: Writing, +change: String, +id: String, +ns: List<&2, Naming.Named>) -> String:
  match w:
    case Writing{author, when, message, f}:
      Naming.stem(when, message, change, id, ns)

# What a record states about the folder, once each file arriving has its
# identifier: the content of each file, and every fact in the format's order.
type Drafted is Data:
  Drafted{contents: List<&2, Content>, facts: List<&2, Rev.Header>}

# `befores` is the position's content of each file of lines it edits.
def drafted.of(+befores: List<&2, Before>, +t: Tree.Tree(), +hs: List<&2, Here>, +dg: Map<&2, String>, +reads: Map<&2, List<&2, U32>>, +ks: List<&2, T.Split>, +moves: List<&2, T.Split>, +obs: List<&2, Sv.Obs>, +ls: List<&2, String>, +mint: List<&2, T.Split>) -> Drafted:
  +arriving = Sv.sorted(Sv.added(obs))
  +gone = Sv.dropped_files(obs)
  +said = stating.all(mint, arriving, Sv.edited(obs), ks, dg, reads, befores, hs)
  +cs = stating.contents(said)
  +modes = List.append(&2, T.Split, stating.modes(said), modes.held(mint, t, Sv.modes(obs), hs))
  +links = links.stated(mint, t, Set.from_list(gone), Set.from_list(arriving), Sv.pointing(obs), ls)
  Drafted{cs, record.facts(swapped(mint), Sv.moved.final(moves, Set.from_list(gone)), modes, gone, cs, links)}

def drafted(+st: Bool, +root: String, +fs: List<&2, Full>, +ps: List<&2, String>, +t: Tree.Tree(), +hs: List<&2, Here>, +dg: Map<&2, String>, +reads: Map<&2, List<&2, U32>>, +ks: List<&2, T.Split>, +moves: List<&2, T.Split>, +obs: List<&2, Sv.Obs>, +ls: List<&2, String>, +mint: List<&2, T.Split>) -> IO(Drafted):
  do IO<Drafted>:
    befores : List<&2, Before> <- befores.io(st, root, fs, ps, edited.lines(Sv.edited(obs), hs))
    return drafted.of(befores, t, hs, dg, reads, ks, moves, obs, ls, mint)

# What `record` states a file holds is what the folder holds there: an
# edit is the written form of the document that replays the position's
# lines of the file to the folder's, text is the folder's bytes, and a
# payload is named by the digest of the folder's. `befores` is the
# position's content of each file of lines. `LAWS.record_states_the_folder`.
def content.applied(r: Result<&2, &2, String, List<&2, Ops.Item>>, +after: List<&2, Ops.Item>) -> Bool:
  match r:
    case Done{xs}:
      items_eq(xs, after)
    case Fail{e}:
      False{}

def content.replays(+before: List<&2, Ops.Item>, +after: List<&2, Ops.Item>, +doc: String, d: Maybe<&2, Ops.Doc>) -> Bool:
  match d:
    case None{}:
      False{}
    case Some{+x}:
      Bool.and(String.eq(Ops.write(x), doc), content.applied(Ops.apply(before, x), after))

def bytes.same(a: List<&2, U32>, b: List<&2, U32>) -> Bool:
  match a b:
    case x <> xs y <> ys:
      Bool.and(U32.is_eq(x, y), bytes.same(xs, ys))
    case Nil{} Nil{}:
      True{}
    case _ _:
      False{}

def content.states(+befores: List<&2, Before>, +dg: Map<&2, String>, +reads: Map<&2, List<&2, U32>>, c: Content) -> Bool:
  match c:
    case Content.Ops{+f, +p, +doc}:
      +before = before_of(befores, f)
      +after = Ops.from_text(Utf8.decode(bytes_of(p, Map.get(List<&2, U32>, Nil{}, reads, p))))
      content.replays(before, after, doc, Ops.diff(before, after))
    case Content.Text{f, +p, bs}:
      bytes.same(bs, bytes_of(p, Map.get(List<&2, U32>, Nil{}, reads, p)))
    case Content.Whole{f, +p, d}:
      String.eq(d, status.folder_digest(dg, p))

def contents.state(+befores: List<&2, Before>, +dg: Map<&2, String>, +reads: Map<&2, List<&2, U32>>, cs: List<&2, Content>) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case c <> rest:
      Bool.and(content.states(befores, dg, reads, c), contents.state(befores, dg, reads, rest))

# The position's content `record` reads for the files it edits: one
# reading of each file asked about, in order, and each the store's replay
# of that file at the position. `LAWS.record_reads_the_position`.
def befores.read(+older: List<&2, Full>, +ds: List<&2, Store.Doc>, +left: String, files: List<&2, String>, bs: List<&2, Before>) -> Bool:
  match files bs:
    case +f <> rest Before{+g, +items} <> more:
      Bool.and(String.eq(g, f), Bool.and(content.applied(content.in(older, ds, left, f), items), befores.read(older, ds, left, rest, more)))
    case Nil{} Nil{}:
      True{}
    case _ _:
      False{}

def drafted.contents(d: Drafted) -> List<&2, Content>:
  match d:
    case Drafted{cs, fs}:
      cs

def drafted.facts(d: Drafted) -> List<&2, Rev.Header>:
  match d:
    case Drafted{cs, fs}:
      fs

# Each file of content filed under the revision's stem, as `filed.io` does.
def contents.filed(+st: Bool, +root: String, +repo: String, +stem: String, +cs: List<&2, Content>) -> IO(Unit):
  +names = Naming.filed(T.map(~Content, ~Naming.Filing, ~(x => content.filing(x)), cs))
  do IO<Unit>:
    at : List<&2, String> <- Store.located(root, T.map(~Content, ~String, ~(x => content.held(x)), cs))
    filed.io(st, root, repo, stem, names, cs, at)

def revision.filed(+st: Bool, +root: String, +stem: String, +text: String) -> IO(Unit):
  do IO<Unit>:
    wr : Result<&1, &1, U32 & String, String> <- Store.filed(root ++ "/revisions/" ++ stem ++ ".rev.txt\n" ++ text)
    done_wr : String <- wrote.io(st, wr)
    IO.pure(Unit, Unit{})

# What a record writes, once its identifiers are drawn and the position's
# content of each file it edits is read: an identifier minted for each
# file arriving, in path order, and one after them for the change; the
# content of each file; the revision, named by the digest of its text and
# filed under the stem its moment, message and change give it; and the
# bookmarks that follow the work. `t` is the tree where the stated renames
# put each file, and `hs` every path the record looks at.
type Recorded is Data:
  Recorded{mint: List<&2, T.Split>, change: String, contents: List<&2, Content>, doc: Rev.Rev, id: String, stem: String, moving: List<&2, Bm.Bookmark>}

def record.planned(+w: Writing, +hex: String, +befores: List<&2, Before>, +fs: List<&2, Full>, +bs: List<&2, Bm.Bookmark>, +ps: List<&2, String>, +t: Tree.Tree(), +hs: List<&2, Here>, +dg: Map<&2, String>, +reads: Map<&2, List<&2, U32>>, +ks: List<&2, T.Split>, +moves: List<&2, T.Split>, +obs: List<&2, Sv.Obs>, +ls: List<&2, String>) -> Recorded:
  +arriving = Sv.sorted(Sv.added(obs))
  +n = List.length(&2, String, arriving)
  +ids = ids.minted(Nat.add(n, 1n), hex)
  +mint = zipped(arriving, ids)
  +change = Maybe.default(&2, String, List.get(&2, String, ids, n), SNil{})
  +dr = drafted.of(befores, t, hs, dg, reads, ks, moves, obs, ls, mint)
  +doc = writing.rev(w, change, ps, drafted.facts(dr))
  +id = Sha.digest(Utf8.encode(Rev.write(doc)))
  Recorded{mint, change, drafted.contents(dr), doc, id, writing.stem(w, change, id, T.map(~Full, ~Naming.Named, ~(f => full.named(f)), fs)), advancing(parents.changes(fs, ps), bs)}

# A record, written: the content filed, the revision, and the bookmarks
# that follow the work.
def record.written(+st: Bool, +root: String, +repo: String, +w: Writing, +facts: List<&2, T.Split>, +ps: List<&2, String>, r: Recorded) -> IO(Unit):
  match r:
    case Recorded{mint, +change, +cs, +doc, +id, +stem, moving}:
      do IO<Unit>:
        contents.filed(st, root, repo, stem, cs)
        revision.filed(st, root, stem, Rev.write(doc))
        advanced : List<&2, String> <- advance(st, root, change, moving)
        record.said(w, facts, change, id, List.sort(~String, ~(a => b => String.is_le(a, b)), advanced), ps)

# A record that states nothing is refused; otherwise identifiers are drawn
# for the files arriving and the change, the position's content read, and
# what that makes written.
def record.write(+st: Bool, +root: String, +repo: String, +fs: List<&2, Full>, +bs: List<&2, Bm.Bookmark>, +ps: List<&2, String>, +t: Tree.Tree(), +hs: List<&2, Here>, +dg: Map<&2, String>, +reads: Map<&2, List<&2, U32>>, +ks: List<&2, T.Split>, +moves: List<&2, T.Split>, pl: Sv.Planned, +w: Writing) -> IO(Unit):
  match pl:
    case Sv.Planned{+facts, r, c, a, e, d, +obs, +ls}:
      +n = List.length(&2, String, Sv.sorted(Sv.added(obs)))
      do IO<Unit>:
        stated.io(Unit, st, Bool.pick(Result<&2, &2, Refused, Unit>, Bool.and(List.is_empty(&2, T.Split, facts), Nat.is_lt(List.length(&2, String, ps), 2n)),
          Fail{Refused{1, "nothing here differs from what is already recorded, and a revision that states nothing would mean nothing"}}, Done{Unit{}}))
        drew : Result<&1, &1, U32 & String, String> <- Store.drawn(Nat.show(Nat.mul(12n, Nat.add(n, 1n))))
        hex : String <- wrote.io(st, drew)
        befores : List<&2, Before> <- befores.io(st, root, fs, ps, edited.lines(Sv.edited(obs), hs))
        record.written(st, root, repo, w, facts, ps, record.planned(w, hex, befores, fs, bs, ps, t, hs, dg, reads, ks, moves, obs, ls))

# What a record writes is named as it says: each file arriving is added
# under the identifier minted for it, in path order; the revision is named
# by the digest of its text, and filed under the name its moment, message
# and change compose; and each bookmark it moves names the change of one
# of its parents. `LAWS.record_names_what_it_writes`.
def strings.same(a: List<&2, String>, b: List<&2, String>) -> Bool:
  match a b:
    case x <> xs y <> ys:
      Bool.and(String.eq(x, y), strings.same(xs, ys))
    case Nil{} Nil{}:
      True{}
    case _ _:
      False{}

def follows(+changes: List<&2, String>, bs: List<&2, Bm.Bookmark>) -> Bool:
  match bs:
    case Nil{}:
      True{}
    case Bm.Bookmark{n, Bm.Target.Change{+c}, p} <> rest:
      Bool.and(Rev.member(changes, c), follows(changes, rest))
    case b <> rest:
      False{}

def record.named(w: Writing, +arriving: List<&2, String>, +changes: List<&2, String>, r: Recorded) -> Bool:
  match w r:
    case Writing{a, +when, +message, f} Recorded{mint, +change, cs, +doc, +id, +stem, moving}:
      Bool.and(strings.same(T.map(~T.Split, ~String, ~(s => split.head(s)), mint), arriving), Bool.and(String.eq(id, Sha.digest(Utf8.encode(Rev.write(doc)))),
        Bool.and(String.starts_with(stem, Naming.compose(when, message, change)), follows(changes, moving))))

def sorted_distinct(xs: List<&2, String>) -> List<&2, String>:
  distinct(List.sort(~String, ~(a => b => String.is_le(a, b)), xs))

def planned.facts(pl: Sv.Planned) -> List<&2, T.Split>:
  match pl:
    case Sv.Planned{facts, r, c, a, e, d, o, l}:
      facts

def planned.obs(pl: Sv.Planned) -> List<&2, Sv.Obs>:
  match pl:
    case Sv.Planned{facts, r, c, a, e, d, o, l}:
      o

# `record --dry-run` says a file arriving once: of the facts a plan states,
# only an `added` line, and a `moved` or `dropped` one, names a path being
# added, since the add carries the file's content, mode and target in with
# it. `LAWS.record_says_an_arrival_once`.
def recorded.once(+arriving: Set(), fs: List<&2, T.Split>) -> Bool:
  match fs:
    case Nil{}:
      True{}
    case T.Split{+k, +p} <> rest:
      Bool.and(Bool.or(String.eq(k, "added"), Bool.or(String.eq(k, "moved"), Bool.or(String.eq(k, "dropped"), Bool.not(Sv.has(arriving, p))))), recorded.once(arriving, rest))

# Rewrites
# --------

# The graph, as the Rust tool's store walks it: in digest order.
def sorted(xs: List<&2, String>) -> List<&2, String>:
  List.sort(~String, ~(a => b => String.is_le(a, b)), xs)

def ab12(+id: String) -> String:
  String.take(id, 12n)

def listed12(xs: List<&2, String>) -> String:
  match xs:
    case Nil{}:
      SNil{}
    case x <> rest:
      "\n  " ++ ab12(x) ++ listed12(rest)

def map12(xs: List<&2, String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> rest:
      ab12(x) <> map12(rest)

def standing.of(fs: List<&2, Full>, +id: String) -> List<&2, String>:
  match fs:
    case Nil{}:
      Nil{}
    case Full{i, c, ps, ss, a, w, rb, rv, facts, m} <> rest:
      Rev.keep(Rev.member(ps, id), i, standing.of(rest, id))

# The revisions naming `id` as a parent.
def standing_on(+fs: List<&2, Full>, +id: String) -> List<&2, String>:
  sorted(standing.of(fs, id))

def superseding.of(fs: List<&2, Full>, +id: String) -> List<&2, String>:
  match fs:
    case Nil{}:
      Nil{}
    case Full{i, c, ps, ss, a, w, rb, rv, facts, m} <> rest:
      Rev.keep(Rev.member(ss, id), i, superseding.of(rest, id))

# The revisions stating that they supersede `id`.
def successors(+fs: List<&2, Full>, +id: String) -> List<&2, String>:
  sorted(superseding.of(fs, id))

def withdrawn(+fs: List<&2, Full>, +id: String) -> Bool:
  Bool.not(List.is_empty(&2, String, superseding.of(fs, id)))

def full.parents(f: Maybe<&2, Full>) -> List<&2, String>:
  match f:
    case Some{x}:
      parents_of(x)
    case None{}:
      Nil{}

def revised_of(f: Full) -> Maybe<&2, String>:
  match f:
    case Full{id, change, parents, supersedes, author, when, revised_by, revised, facts, message}:
      revised

def revised_by_of(f: Full) -> Maybe<&2, String>:
  match f:
    case Full{id, change, parents, supersedes, author, when, revised_by, revised, facts, message}:
      revised_by

def rev.full(+id: String, r: Rev.Rev) -> Full:
  match r:
    case Rev.Rev{change, parents, supersedes, author, when, revised_by, revised, facts, message}:
      Full{id, change, parents, supersedes, author, when, revised_by, revised, facts, message}

def full.rev(f: Full) -> Rev.Rev:
  match f:
    case Full{id, change, parents, supersedes, author, when, revised_by, revised, facts, message}:
      Rev.Rev{change, parents, supersedes, author, when, revised_by, revised, facts, message}

# Decision 0005: `revised-by` is written only where it differs from the
# author, since a fact equal to another fact is a second spelling of it.
def revised_by(+by: String, +author: String) -> Maybe<&2, String>:
  Bool.pick(Maybe<&2, String>, String.eq(by, author), None{}, Some{by})

def meets(xs: List<&2, String>, +ys: List<&2, String>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case +x <> rest:
      Bool.or(Rev.member(ys, x), meets(rest, ys))

# Decision 0023's refusal of a second rewrite, which every act owes.
def already.r(+fs: List<&2, Full>, +id: String) -> Result<&2, &2, Refused, Unit>:
  +ss = successors(fs, id)
  Bool.pick(Result<&2, &2, Refused, Unit>, List.is_empty(&2, String, ss), Done{Unit{}},
    Fail{Refused{1, ab12(id) ++ " has already been rewritten, and superseding it again would leave one change with two current revisions; amend what replaced it:" ++ listed12(ss)}})

# Carrying: decision 0059. What stands on a rewritten revision is restated
# against its successor, every fact derived from what the store holds.
def parents.withdrawn(ps: List<&2, String>, +fs: List<&2, Full>) -> Bool:
  match ps:
    case Nil{}:
      False{}
    case +p <> rest:
      Bool.or(withdrawn(fs, p), parents.withdrawn(rest, fs))

def parents.by(ps: List<&2, String>, +fs: List<&2, Full>, +causes: List<&2, String>) -> Bool:
  match ps:
    case Nil{}:
      False{}
    case +p <> rest:
      Bool.or(meets(superseding.of(fs, p), causes), parents.by(rest, fs, causes))

# One nothing supersedes, standing on one something does: `check`'s note.
def stranded(+fs: List<&2, Full>, +id: String) -> Bool:
  Bool.and(Bool.not(withdrawn(fs, id)), parents.withdrawn(full.parents(find(fs, id)), fs))

def stranded.all(each: List<&2, Full>, +fs: List<&2, Full>) -> List<&2, String>:
  match each:
    case Nil{}:
      Nil{}
    case Full{+i, c, ps, ss, a, w, rb, rv, facts, m} <> rest:
      Rev.keep(Bool.and(Bool.not(withdrawn(fs, i)), parents.withdrawn(ps, fs)), i, stranded.all(rest, fs))

def stranded.by(each: List<&2, Full>, +fs: List<&2, Full>, +causes: List<&2, String>) -> List<&2, String>:
  match each:
    case Nil{}:
      Nil{}
    case Full{+i, c, ps, ss, a, w, rb, rv, facts, m} <> rest:
      Rev.keep(Bool.and(Bool.not(withdrawn(fs, i)), parents.by(ps, fs, causes)), i, stranded.by(rest, fs, causes))

def not_stranded(+id: String) -> String:
  ab12(id) ++ " does not stand on a rewritten revision, so there is nothing to carry it across"

# Everything standing on what is carried, which writing a successor for it
# would strand; a withdrawn revision is never carried.
def closure.more(each: List<&2, Full>, +fs: List<&2, Full>, +set: List<&2, String>) -> List<&2, String>:
  match each:
    case Nil{}:
      Nil{}
    case Full{+i, c, ps, ss, a, w, rb, rv, facts, m} <> rest:
      Rev.keep(Bool.and(Bool.and(Bool.not(Rev.member(set, i)), Bool.not(withdrawn(fs, i))), meets(ps, set)), i, closure.more(rest, fs, set))

def closure(fuel: Nat, +fs: List<&2, Full>, +set: List<&2, String>) -> List<&2, String>:
  match fuel:
    case 0n:
      set
    case 1n+k:
      closure(k, fs, List.append(&2, String, set, closure.more(fs, fs, set)))

# The head of a superseded revision's chain: a rewrite may itself have been
# rewritten, and two heads is divergence, which a person resolves first.
def superseded.step(+fs: List<&2, Full>, current: List<&2, String>) -> List<&2, String>:
  match current:
    case Nil{}:
      Nil{}
    case +c <> rest:
      +ss = successors(fs, c)
      List.append(&2, String, Bool.pick(List<&2, String>, List.is_empty(&2, String, ss), [c], ss), superseded.step(fs, rest))

def superseded.go(fuel: Nat, +fs: List<&2, Full>, current: List<&2, String>) -> List<&2, String>:
  match fuel:
    case 0n:
      current
    case 1n+k:
      superseded.go(k, fs, sorted_distinct(superseded.step(fs, current)))

def successor.of(+of: String, heads: List<&2, String>) -> Result<&2, &2, String, String>:
  match heads:
    case h <> Nil{}:
      Done{h}
    case +several:
      Fail{ab12(of) ++ " was rewritten two ways, and nothing here can choose which rewrite to carry the work onto; abandon one of them first:" ++ listed12(several)}

def successor(+fs: List<&2, Full>, +of: String) -> Result<&2, &2, String, String>:
  successor.of(of, superseded.go(Nat.add(List.length(&2, Full, fs), 1n), fs, [of]))

# Parents before children, where a parent is the carried revision itself or
# the carried head of its supersession chain.
type Dep is Data:
  Dep{id: String, on: List<&2, String>}

def dep.head(+set: List<&2, String>, +more: List<&2, String>, r: Result<&2, &2, String, String>) -> Result<&2, &2, String, List<&2, String>>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{+h}:
      Done{Bool.pick(List<&2, String>, Rev.member(set, h), h <> more, more)}

def dep.one(+fs: List<&2, Full>, +set: List<&2, String>, +p: String, +more: List<&2, String>, held: Bool, gone: Bool) -> Result<&2, &2, String, List<&2, String>>:
  match held gone:
    case True{} _:
      Done{p <> more}
    case False{} True{}:
      dep.head(set, more, successor(fs, p))
    case False{} False{}:
      Done{more}

def dep.on(+fs: List<&2, Full>, +set: List<&2, String>, ps: List<&2, String>) -> Result<&2, &2, String, List<&2, String>>:
  match ps:
    case Nil{}:
      Done{Nil{}}
    case +p <> rest:
      do Result<&2, &2, String, List<&2, String>>:
        more : List<&2, String> <- dep.on(fs, set, rest)
        dep.one(fs, set, p, more, Rev.member(set, p), withdrawn(fs, p))

def deps.r(+fs: List<&2, Full>, +set: List<&2, String>, ids: List<&2, String>) -> Result<&2, &2, String, List<&2, Dep>>:
  match ids:
    case Nil{}:
      Done{Nil{}}
    case +id <> rest:
      do Result<&2, &2, String, List<&2, Dep>>:
        on : List<&2, String> <- dep.on(fs, set, full.parents(find(fs, id)))
        more : List<&2, Dep> <- deps.r(fs, set, rest)
        return Dep{id, on} <> more

def all_in(xs: List<&2, String>, +ys: List<&2, String>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case +x <> rest:
      Bool.and(Rev.member(ys, x), all_in(rest, ys))

def order.pass(ds: List<&2, Dep>, +placed: List<&2, String>) -> List<&2, String>:
  match ds:
    case Nil{}:
      placed
    case Dep{+id, on} <> rest:
      order.pass(rest, Bool.pick(List<&2, String>, Bool.and(Bool.not(Rev.member(placed, id)), all_in(on, placed)), List.append(&2, String, placed, [id]), placed))

def order.go(fuel: Nat, +ds: List<&2, Dep>, +placed: List<&2, String>) -> List<&2, String>:
  match fuel:
    case 0n:
      placed
    case 1n+k:
      order.go(k, ds, order.pass(ds, placed))

# The facts a revision states under one key, each cut at its first space.
def facts.keyed(hs: List<&2, Rev.Header>, +key: String) -> List<&2, T.Split>:
  match hs:
    case Nil{}:
      Nil{}
    case Rev.Header{+k, +v} <> rest:
      +later = facts.keyed(rest, key)
      Bool.pick(List<&2, T.Split>, String.eq(k, key), Maybe.default(&2, T.Split, T.split_once(v), T.Split{v, SNil{}}) <> later, later)

def heads_of(xs: List<&2, T.Split>) -> List<&2, String>:
  T.map(~T.Split, ~String, ~(s => split.head(s)), xs)

# What one file set is doing across one rewrite, at some point in the
# carried line: each file of lines whose content differs, as the old side
# and the new; what the old side holds and the new does not; the paths the
# new side holds and the old does not; and whole files whose bytes differ.
type Base is Data:
  Base{file: String, old: List<&2, Ops.Item>, new: List<&2, Ops.Item>}

type Moving is Data:
  Moving{lines: List<&2, Base>, lost: List<&2, T.Split>, introduced: List<&2, String>, payloads: List<&2, String>}

# A restated document to write: its digest, the path the file had, and it.
type Write is Data:
  Write{held: String, path: String, doc: Ops.Doc}

# One revision restated: what it supersedes, what it is, what it stands
# on, the paths whose operations were restated, the documents to write, and
# what its content hands the steps above.
type Step is Data:
  Step{pred: String, id: String, onto: List<&2, String>, doc: Rev.Rev, restated: List<&2, String>, writes: List<&2, Write>, moving: Moving}

def moving.lines(m: Moving) -> List<&2, Base>:
  match m:
    case Moving{ls, lo, i, p}:
      ls

def moving.none() -> Moving:
  Moving{Nil{}, Nil{}, Nil{}, Nil{}}

def base.file(b: Base) -> String:
  match b:
    case Base{f, o, n}:
      f

def base.of(bs: List<&2, Base>, +file: String) -> Maybe<&2, Base>:
  match bs:
    case Nil{}:
      None{}
    case Base{+f, o, n} <> rest:
      Bool.pick(Maybe<&2, Base>, String.eq(f, file), Some{Base{f, o, n}}, base.of(rest, file))

def base.without(bs: List<&2, Base>, +file: String) -> List<&2, Base>:
  match bs:
    case Nil{}:
      Nil{}
    case Base{+f, o, n} <> rest:
      +later = base.without(rest, file)
      Bool.pick(List<&2, Base>, String.eq(f, file), later, Base{f, o, n} <> later)

def split.without(xs: List<&2, T.Split>, +key: String) -> List<&2, T.Split>:
  match xs:
    case Nil{}:
      Nil{}
    case T.Split{+k, v} <> rest:
      +later = split.without(rest, key)
      Bool.pick(List<&2, T.Split>, String.eq(k, key), later, T.Split{k, v} <> later)

# Whether any content moved: the condition under which a merge cannot be
# carried, since its parents' agreement would have to be recomputed.
def moving.moved(m: Moving) -> Bool:
  match m:
    case Moving{ls, lo, i, p}:
      Bool.not(Bool.and(List.is_empty(&2, Base, ls), Bool.and(List.is_empty(&2, T.Split, lo), List.is_empty(&2, String, p))))

# The union of what several parents hand down; a later parent's pair for a
# file is the one kept, as a map extended in turn keeps it.
def moving.join2(a: Moving, b: Moving) -> Moving:
  match a b:
    case Moving{ls, lo, i, p} Moving{ls2, lo2, i2, p2}:
      Moving{List.append(&2, Base, ls2, ls), List.append(&2, T.Split, lo2, lo), List.append(&2, String, i, i2), List.append(&2, String, p, p2)}

def moving.join(ms: List<&2, Moving>) -> Moving:
  match ms:
    case Nil{}:
      moving.none()
    case m <> rest:
      moving.join2(m, moving.join(rest))

# Two rewrites in sequence, read as one: a file both legs moved runs from
# the first's old side to the second's new, and one the second put back is
# not moving at all.
def compose.put(+f: String, +old: List<&2, Ops.Item>, middle: List<&2, Ops.Item>, found: Maybe<&2, Base>, +later: List<&2, Base>) -> List<&2, Base>:
  match found:
    case Some{Base{g, m, +new}}:
      Bool.pick(List<&2, Base>, items_eq(old, new), later, Base{f, old, new} <> later)
    case None{}:
      Base{f, old, middle} <> later

def compose.lines(first: List<&2, Base>, +second: List<&2, Base>) -> List<&2, Base>:
  match first:
    case Nil{}:
      second
    case Base{+f, +old, middle} <> rest:
      +later = compose.lines(rest, base.without(second, f))
      compose.put(f, old, middle, base.of(second, f), later)

def moving.compose(first: Moving, second: Moving) -> Moving:
  match first second:
    case Moving{ls, lo, i, p} Moving{ls2, lo2, i2, p2}:
      Moving{compose.lines(ls, ls2), List.append(&2, T.Split, lo, lo2), List.append(&2, String, i, i2), List.append(&2, String, p, p2)}

# The tree a revision holds, as `status` builds one.
def tree.fault(r: Result<&2, &2, Refused, Tree.Merged>) -> Result<&2, &2, String, List<&2, Tree.Entry>>:
  match r:
    case Fail{Refused{c, m}}:
      Fail{m}
    case Done{m}:
      Done{Tree.merged_tree(m)}

def tree.at.r(+fs: List<&2, Full>, +id: String) -> Result<&2, &2, String, List<&2, Tree.Entry>>:
  tree.fault(status.tree.r(fs, [id]))

def entry.of(t: List<&2, Tree.Entry>, +file: String) -> Maybe<&2, Tree.Entry>:
  match t:
    case Nil{}:
      None{}
    case Tree.Entry{+f, p, k, y, g, m} <> rest:
      Bool.pick(Maybe<&2, Tree.Entry>, String.eq(f, file), Some{Tree.Entry{f, p, k, y, g, m}}, entry.of(rest, file))

def path.of(+t: List<&2, Tree.Entry>, +file: String) -> Maybe<&2, String>:
  Maybe.map(&2, Tree.Entry, String, e => Tree.entry_path(e), entry.of(t, file))

def held.in(+t: List<&2, Tree.Entry>, +file: String) -> Bool:
  Maybe.is_some(&2, Tree.Entry, entry.of(t, file))

# The content of a file of lines at a revision, replayed.
def content.at(+fs: List<&2, Full>, +ds: List<&2, Store.Doc>, +id: String, +file: String) -> Result<&2, &2, String, List<&2, Ops.Item>>:
  content.in(oldest_of(fs, Some{id}), ds, id, file)

def between.line(+f: String, old: Result<&2, &2, String, List<&2, Ops.Item>>, new: Result<&2, &2, String, List<&2, Ops.Item>>, later: Result<&2, &2, String, Moving>) -> Result<&2, &2, String, Moving>:
  match old new later:
    case Fail{e} _ _:
      Fail{e}
    case _ Fail{e} _:
      Fail{e}
    case _ _ Fail{e}:
      Fail{e}
    case Done{+o} Done{+n} Done{Moving{+ls, lo, i, p}}:
      Done{Moving{Bool.pick(List<&2, Base>, items_eq(o, n), ls, Base{f, o, n} <> ls), lo, i, p}}

def between.put(+t: List<&2, Tree.Entry>, later: Result<&2, &2, String, Moving>, +f: String, +p: String, t2: Maybe<&2, Tree.Entry>, whole: Bool, pay: Maybe<&2, String>) -> Result<&2, &2, String, Moving>:
  match later t2 whole:
    case Fail{e} _ _:
      Fail{e}
    case Done{Moving{ls, lo, i, ps}} None{} _:
      Done{Moving{ls, T.Split{f, p} <> lo, i, ps}}
    case Done{Moving{ls, lo, i, +ps}} Some{Tree.Entry{f2, p2, k2, +y2, g2, m2}} True{}:
      Done{Moving{ls, lo, i, Bool.pick(List<&2, String>, maybe_eq(pay, y2), ps, f <> ps)}}
    case Done{m} Some{e} False{}:
      Done{m}

def is_lines(k: Tree.FileKind) -> Bool:
  match k:
    case Tree.Lines{}:
      True{}
    case _:
      False{}

def is_whole(k: Tree.FileKind) -> Bool:
  match k:
    case Tree.Whole{}:
      True{}
    case _:
      False{}

# `ot` walked: each file the old side holds, lost, of lines, or whole.
def between.walk(+fs: List<&2, Full>, +ds: List<&2, Store.Doc>, +old: String, +new: String, ot: List<&2, Tree.Entry>, +nt: List<&2, Tree.Entry>) -> Result<&2, &2, String, Moving>:
  match ot:
    case Nil{}:
      Done{moving.none()}
    case Tree.Entry{+f, +p, +k, y, g, m} <> rest:
      +later = between.walk(fs, ds, old, new, rest, nt)
      +there = held.in(nt, f)
      Bool.pick(Result<&2, &2, String, Moving>, Bool.and(there, is_lines(k)),
        between.line(f, content.at(fs, ds, old, f), content.at(fs, ds, new, f), later),
        between.put(nt, later, f, p, entry.of(nt, f), is_whole(k), y))

def introduced(nt: List<&2, Tree.Entry>, +ot: List<&2, Tree.Entry>) -> List<&2, String>:
  match nt:
    case Nil{}:
      Nil{}
    case Tree.Entry{+f, p, k, y, g, m} <> rest:
      Rev.keep(Bool.not(held.in(ot, f)), p, introduced(rest, ot))

def with_introduced(+i: List<&2, String>, r: Result<&2, &2, String, Moving>) -> Result<&2, &2, String, Moving>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{Moving{ls, lo, x, p}}:
      Done{Moving{ls, lo, i, p}}

# What one file set is doing across one rewrite: the store's answer at the
# superseded revision, compared with its answer at the successor.
def between(+fs: List<&2, Full>, +ds: List<&2, Store.Doc>, +old: String, +new: String) -> Result<&2, &2, String, Moving>:
  do Result<&2, &2, String, Moving>:
    ot : List<&2, Tree.Entry> <- tree.at.r(fs, old)
    nt : List<&2, Tree.Entry> <- tree.at.r(fs, new)
    +ot2 : List<&2, Tree.Entry> = ot
    +nt2 : List<&2, Tree.Entry> = nt
    with_introduced(introduced(nt2, ot2), between.walk(fs, ds, old, new, ot2, nt2))

# Contested regions
# -----------------
#
# `merge.rs`'s report of where concurrent work met, read off a walk's
# finished tree: siblings at one place written by authors who had not seen
# each other; an element removed next to something a concurrent author
# wrote; each counted over the run its author wrote, and every item but the
# last that has no terminator.
def concurrent(+g: List<&2, Merge.Rev>, +a: Nat, +b: Nat) -> Bool:
  Bool.and(Bool.not(Nat.is_eq(a, b)), Bool.and(Bool.not(Merge.has(Merge.past(g, a), b)), Bool.not(Merge.has(Merge.past(g, b), a))))

def any_concurrent(+g: List<&2, Merge.Rev>, +a: Nat, bs: List<&2, Nat>) -> Bool:
  match bs:
    case Nil{}:
      False{}
    case +b <> rest:
      Bool.or(concurrent(g, a, b), any_concurrent(g, a, rest))

def place.eq(a: Merge.Place, b: Merge.Place) -> Bool:
  match a b:
    case Merge.Place{p1, r1} Merge.Place{p2, r2}:
      Bool.and(Merge.Name.same(p1, p2), Bool.not(Bool.xor(r1, r2)))

def sibling.contested(+g: List<&2, Merge.Rev>, +n: Merge.Node, ns: List<&2, Merge.Node>) -> Bool:
  match ns:
    case Nil{}:
      False{}
    case +m <> rest:
      Bool.or(Bool.and(Bool.not(Merge.Name.eq(Merge.Node.name(n), Merge.Node.name(m))), Bool.and(place.eq(Merge.Node.place(n), Merge.Node.place(m)), concurrent(g, Merge.Node.author(n), Merge.Node.author(m)))),
        sibling.contested(g, n, rest))

def insertions(+g: List<&2, Merge.Rev>, ns: List<&2, Merge.Node>, +t: List<&2, Merge.Node>) -> List<&2, Merge.Name>:
  match ns:
    case Nil{}:
      Nil{}
    case +n <> rest:
      +later = insertions(g, rest, t)
      Bool.pick(List<&2, Merge.Name>, sibling.contested(g, n, t), Merge.Node.name(n) <> later, later)

def node.deleted(n: Merge.Node) -> List<&2, Nat>:
  match n:
    case Merge.Node{nm, it, pl, d}:
      d

def before.marked(+g: List<&2, Merge.Rev>, before: Maybe<&2, Merge.Node>, +by: List<&2, Nat>) -> List<&2, Merge.Name>:
  match before:
    case None{}:
      Nil{}
    case Some{+b}:
      Bool.pick(List<&2, Merge.Name>, any_concurrent(g, Merge.Node.author(b), by), [Merge.Node.name(b)], Nil{})

def deletions(+g: List<&2, Merge.Rev>, ns: List<&2, Merge.Node>, +before: Maybe<&2, Merge.Node>, +pending: List<&2, Nat>) -> List<&2, Merge.Name>:
  match ns:
    case Nil{}:
      Nil{}
    case +n <> +rest:
      +d = node.deleted(n)
      Bool.pick(List<&2, Merge.Name>, List.is_empty(&2, Nat, d),
        List.append(&2, Merge.Name, Bool.pick(List<&2, Merge.Name>, any_concurrent(g, Merge.Node.author(n), pending), [Merge.Node.name(n)], Nil{}), deletions(g, rest, Some{n}, Nil{})),
        List.append(&2, Merge.Name, before.marked(g, before, d), deletions(g, rest, before, List.append(&2, Nat, pending, d))))

def name.in(ms: List<&2, Merge.Name>, +n: Merge.Name) -> Bool:
  match ms:
    case Nil{}:
      False{}
    case m <> rest:
      Bool.or(Merge.Name.eq(m, n), name.in(rest, n))

# Runs of one author among what stands, each counted once if any of it met.
def regions(ns: List<&2, Merge.Node>, +marks: List<&2, Merge.Name>, run: Maybe<&2, Nat>, +hit: Bool) -> Nat:
  match ns:
    case Nil{}:
      Bool.pick(Nat, hit, 1n, 0n)
    case +n <> rest:
      +a = Merge.Node.author(n)
      +same = Maybe.default(&2, Bool, Maybe.map(&2, Nat, Bool, r => Nat.is_eq(r, a), run), False{})
      +mine = name.in(marks, Merge.Node.name(n))
      Nat.add(Bool.pick(Nat, Bool.and(Bool.not(same), hit), 1n, 0n), regions(rest, marks, Some{a}, Bool.or(Bool.and(same, hit), mine)))

def unterminated(items: List<&2, Ops.Item>) -> Nat:
  match items:
    case Nil{}:
      0n
    case Ops.Item{t, n, f} <> Nil{}:
      0n
    case Ops.Item{t, n, f} <> rest:
      Nat.add(Bool.pick(Nat, n, 0n, 1n), unterminated(rest))

def contested(+g: List<&2, Merge.Rev>, +t: List<&2, Merge.Node>) -> Nat:
  +marks = List.append(&2, Merge.Name, insertions(g, t, t), deletions(g, Merge.order(t), None{}, Nil{}))
  Nat.add(regions(Merge.visible(t), marks, None{}, False{}), unterminated(Merge.file(t)))

# Restating
# ---------

# What restating one file came to: the document it now names, if any, the
# document to write, and what the file is doing for the steps above.
type Restated is Data:
  Restated{file: String, edit: Maybe<&2, String>, write: Maybe<&2, Ops.Doc>, after: Maybe<&2, Base>}

def merge.rev(+x: String, +old: String, +new: String, +i_old: Nat, +creation: Maybe<&2, Merge.Statement>, +delta: Merge.Statement, +ops: Merge.Statement) -> Merge.Rev:
  Bool.pick(Merge.Rev, String.eq(x, old), Merge.Rev{Nil{}, creation},
    Bool.pick(Merge.Rev, String.eq(x, new), Merge.Rev{[i_old], Some{delta}}, Merge.Rev{[i_old], Some{ops}}))

def merge.graph(names: List<&2, String>, +old: String, +new: String, +i_old: Nat, +creation: Maybe<&2, Merge.Statement>, +delta: Merge.Statement, +ops: Merge.Statement) -> List<&2, Merge.Rev>:
  match names:
    case Nil{}:
      Nil{}
    case x <> rest:
      merge.rev(x, old, new, i_old, creation, delta, ops) <> merge.graph(rest, old, new, i_old, creation, delta, ops)

def creation(items: List<&2, Ops.Item>) -> Maybe<&2, Merge.Statement>:
  match items:
    case Nil{}:
      None{}
    case +some:
      Some{Merge.Edits{[Ops.Op{Ops.Insert{}, 0n, some}]}}

def doc.ops(d: Ops.Doc) -> List<&2, Ops.Op>:
  match d:
    case Ops.Doc{f, r, ops}:
      ops

def forgets.any(xs: List<&2, Ops.Op>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Ops.Op{v, a, items} <> rest:
      Bool.or(Ops.any_forgotten(items), forgets.any(rest))

def doc.parsed(+id: String, +named: String, found: Maybe<&2, String>) -> Result<&2, &2, String, Ops.Doc>:
  match found:
    case None{}:
      Fail{"restating " ++ ab12(id) ++ " needs the operation document " ++ ab12(named) ++ ", which is not here yet"}
    case Some{text}:
      Ops.parse(text)

def regions.said(+n: Nat) -> String:
  Bool.pick(String, Nat.is_eq(n, 1n), "one region", Nat.show(n) ++ " regions")

def restated.of(+file: String, +old_after: List<&2, Ops.Item>, +new: List<&2, Ops.Item>, +carried: List<&2, Ops.Item>) -> Restated:
  +doc = Ops.diff(new, carried)
  Restated{file, Maybe.map(&2, Ops.Doc, String, d => Sha.digest(Utf8.encode(Ops.write(d))), doc), doc, Bool.pick(Maybe<&2, Base>, items_eq(old_after, carried), None{}, Some{Base{file, old_after, carried}})}

def restated.walked(+id: String, +file: String, +g: List<&2, Merge.Rev>, +old_after: List<&2, Ops.Item>, +new: List<&2, Ops.Item>, mt: Maybe<&2, List<&2, Merge.Node>>) -> Result<&2, &2, String, Restated>:
  match mt:
    case None{}:
      Fail{"what " ++ ab12(id) ++ " did to " ++ file ++ " does not replay against the base it was recorded on"}
    case Some{+t}:
      +n = contested(g, t)
      Bool.pick(Result<&2, &2, String, Restated>, Nat.is_eq(n, 0n),
        Done{restated.of(file, old_after, new, Merge.file(t))},
        Fail{"what " ++ ab12(id) ++ " did and what the rewrite did meet in " ++ regions.said(n) ++ " of one file (" ++ file ++ "); resolving concurrent work is a person's, so amend it onto the rewrite by hand"})

def restated.go(+id: String, +file: String, +old_parent: String, +new_parent: String, +old: List<&2, Ops.Item>, +new: List<&2, Ops.Item>, +ops: Ops.Doc) -> Result<&2, &2, String, Restated>:
  +names : List<&2, String> = sorted([old_parent, new_parent, id])
  +i_old : Nat = index_of(names, old_parent, 0n)
  +i_new : Nat = index_of(names, new_parent, 0n)
  +i_id : Nat = index_of(names, id, 0n)
  +delta : Merge.Statement = Merge.Edits{doc.ops(Maybe.default(&2, Ops.Doc, Ops.diff(old, new), Ops.Doc{None{}, None{}, Nil{}}))}
  +g : List<&2, Merge.Rev> = merge.graph(names, old_parent, new_parent, i_old, creation(old), delta, Merge.Edits{doc.ops(ops)})
  +o : List<&2, Nat> = i_old <> List.sort(~Nat, ~(a => b => Nat.is_le(a, b)), [i_new, i_id])
  do Result<&2, &2, String, Restated>:
    old_after : List<&2, Ops.Item> <- Ops.apply(old, ops)
    restated.walked(id, file, g, old_after, new, Merge.walk(o, g, Some{Nil{}}))

# One file whose base moved, put through 0007's merge: the delta from the
# old base to the new replays concurrently with what this revision did, and
# where the two meet the carry is contested and refuses.
def restate(+ds: List<&2, Store.Doc>, +id: String, +old_parent: String, +new_parent: String, +file: String, +named: String, b: Base) -> Result<&2, &2, String, Restated>:
  match b:
    case Base{f, +old, +new}:
      do Result<&2, &2, String, Restated>:
        ops : Ops.Doc <- doc.parsed(id, named, doc_by_id(ds, named))
        +ops2 : Ops.Doc = ops
        c : Unit <- Bool.pick(Result<&2, &2, String, Unit>, Bool.or(forgets.any(doc.ops(ops2)), Bool.or(Ops.any_forgotten(old), Ops.any_forgotten(new))),
          Fail{"restating what " ++ ab12(id) ++ " did to " ++ file ++ " would re-record content a forgetting destroyed, which no carry may do; amend the work onto the rewrite by hand"}, Done{Unit{}})
        restated.go(id, file, old_parent, new_parent, old, new, ops2)

def restate.found(+ds: List<&2, Store.Doc>, +id: String, +old_parent: String, +new_parent: String, +file: String, +named: String, found: Maybe<&2, Base>) -> Result<&2, &2, String, Restated>:
  match found:
    case None{}:
      Done{Restated{file, Some{named}, None{}, None{}}}
    case Some{b}:
      restate(ds, id, old_parent, new_parent, file, named, b)

def restate.one(+ds: List<&2, Store.Doc>, +id: String, +old_parent: String, +new_parent: String, +moving: Moving, e: T.Split) -> Result<&2, &2, String, Restated>:
  match e:
    case T.Split{+file, +named}:
      restate.found(ds, id, old_parent, new_parent, file, named, base.of(moving.lines(moving), file))

def restate.all(+ds: List<&2, Store.Doc>, +id: String, +old_parent: String, +new_parent: String, +moving: Moving, es: List<&2, T.Split>) -> Result<&2, &2, String, List<&2, Restated>>:
  match es:
    case Nil{}:
      Done{Nil{}}
    case +e <> rest:
      do Result<&2, &2, String, List<&2, Restated>>:
        one : Restated <- restate.one(ds, id, old_parent, new_parent, moving, e)
        more : List<&2, Restated> <- restate.all(ds, id, old_parent, new_parent, moving, rest)
        return one <> more

# Mapping each parent across the rewrite
# --------------------------------------

type Mapped is Data:
  Mapped{old: String, new: String, moving: Moving}

type Handed is Data:
  Handed{id: String, moving: Moving}

def handed.of(hs: List<&2, Handed>, +id: String) -> Moving:
  match hs:
    case Nil{}:
      moving.none()
    case Handed{+i, m} <> rest:
      Bool.pick(Moving, String.eq(i, id), m, handed.of(rest, id))

# The authored move's own pairing: which revision moves, from which parent,
# onto which.
type Moved is Data:
  Moved{target: String, from: String, to: String}

def mapped.planned(+fs: List<&2, Full>, +ds: List<&2, Store.Doc>, +handed: List<&2, Handed>, +p: String, +head: String, found: Maybe<&2, String>) -> Result<&2, &2, String, Mapped>:
  match found:
    case Some{new}:
      do Result<&2, &2, String, Mapped>:
        first : Moving <- between(fs, ds, p, head)
        return Mapped{p, new, moving.compose(first, handed.of(handed, head))}
    case None{}:
      do Result<&2, &2, String, Mapped>:
        delta : Moving <- between(fs, ds, p, head)
        return Mapped{p, head, delta}

def mapped.headed(+fs: List<&2, Full>, +ds: List<&2, Store.Doc>, +planned: List<&2, T.Split>, +handed: List<&2, Handed>, +p: String, r: Result<&2, &2, String, String>) -> Result<&2, &2, String, Mapped>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{+head}:
      mapped.planned(fs, ds, handed, p, head, lookup(planned, head))

def mapped.found(+fs: List<&2, Full>, +ds: List<&2, Store.Doc>, +planned: List<&2, T.Split>, +handed: List<&2, Handed>, +p: String, found: Maybe<&2, String>, gone: Bool) -> Result<&2, &2, String, Mapped>:
  match found gone:
    case Some{new} _:
      Done{Mapped{p, new, handed.of(handed, p)}}
    case None{} True{}:
      mapped.headed(fs, ds, planned, handed, p, successor(fs, p))
    case None{} False{}:
      Done{Mapped{p, p, moving.none()}}

def mapped.moved(+fs: List<&2, Full>, +ds: List<&2, Store.Doc>, +planned: List<&2, T.Split>, +handed: List<&2, Handed>, +id: String, +p: String, mv: Maybe<&2, Moved>) -> Result<&2, &2, String, Mapped>:
  match mv:
    case Some{Moved{+target, +from, +to}}:
      Bool.pick(Result<&2, &2, String, Mapped>, Bool.and(String.eq(target, id), String.eq(from, p)),
        Result.map(&2, &2, String, Moving, Mapped, m => Mapped{from, to, m}, between(fs, ds, from, to)),
        mapped.found(fs, ds, planned, handed, p, lookup(planned, p), withdrawn(fs, p)))
    case None{}:
      mapped.found(fs, ds, planned, handed, p, lookup(planned, p), withdrawn(fs, p))

def mapped.all(+fs: List<&2, Full>, +ds: List<&2, Store.Doc>, +planned: List<&2, T.Split>, +handed: List<&2, Handed>, +id: String, +mv: Maybe<&2, Moved>, ps: List<&2, String>) -> Result<&2, &2, String, List<&2, Mapped>>:
  match ps:
    case Nil{}:
      Done{Nil{}}
    case +p <> rest:
      do Result<&2, &2, String, List<&2, Mapped>>:
        one : Mapped <- mapped.moved(fs, ds, planned, handed, id, p, mv)
        more : List<&2, Mapped> <- mapped.all(fs, ds, planned, handed, id, mv, rest)
        return one <> more

def mapped.moving(ms: List<&2, Mapped>) -> List<&2, Moving>:
  match ms:
    case Nil{}:
      Nil{}
    case Mapped{o, n, m} <> rest:
      m <> mapped.moving(rest)

def mapped.news(ms: List<&2, Mapped>) -> List<&2, String>:
  match ms:
    case Nil{}:
      Nil{}
    case Mapped{o, n, m} <> rest:
      n <> mapped.news(rest)

def mapped.changed(ms: List<&2, Mapped>) -> List<&2, String>:
  match ms:
    case Nil{}:
      Nil{}
    case Mapped{+o, +n, m} <> rest:
      Rev.keep(Bool.not(String.eq(o, n)), n, mapped.changed(rest))

def mapped.new_of(ms: List<&2, Mapped>, +old: String) -> String:
  match ms:
    case Nil{}:
      old
    case Mapped{+o, n, m} <> rest:
      Bool.pick(String, String.eq(o, old), n, mapped.new_of(rest, old))

def last_of(xs: List<&2, String>) -> String:
  match xs:
    case Nil{}:
      SNil{}
    case x <> Nil{}:
      x
    case x <> rest:
      last_of(rest)

# The refusals a step meets before any content is read
# ---------------------------------------------------

def first_taken(ps: List<&2, T.Split>, +intro: List<&2, String>) -> Maybe<&2, String>:
  match ps:
    case Nil{}:
      None{}
    case T.Split{f, +p} <> rest:
      Bool.pick(Maybe<&2, String>, Rev.member(intro, p), Some{p}, first_taken(rest, intro))

def first_lost(fs: List<&2, String>, +lost: List<&2, T.Split>) -> Maybe<&2, String>:
  match fs:
    case Nil{}:
      None{}
    case +f <> rest:
      Maybe.or(&2, String, lookup(lost, f), first_lost(rest, lost))

def link.refs(ls: List<&2, T.Split>) -> List<&2, String>:
  match ls:
    case Nil{}:
      Nil{}
    case T.Split{f, +v} <> rest:
      List.append(&2, String, Maybe.default(&2, List<&2, String>, Maybe.map(&2, String, List<&2, String>, x => [x], T.strip_prefix(v, "file:")), Nil{}), link.refs(rest))

def first_payload(fs: List<&2, String>, +ps: List<&2, String>) -> Maybe<&2, String>:
  match fs:
    case Nil{}:
      None{}
    case +f <> rest:
      Bool.pick(Maybe<&2, String>, Rev.member(ps, f), Some{f}, first_payload(rest, ps))

def maybe.refused(m: Maybe<&2, String>, +msg: String, +tail: String) -> Result<&2, &2, String, Unit>:
  match m:
    case None{}:
      Done{Unit{}}
    case Some{x}:
      Fail{msg ++ x ++ tail}

def dropped.of(hs: List<&2, Rev.Header>) -> List<&2, String>:
  match hs:
    case Nil{}:
      Nil{}
    case Rev.Header{+k, v} <> rest:
      +later = dropped.of(rest)
      Bool.pick(List<&2, String>, String.eq(k, "drop"), v <> later, later)

def early.r(+id: String, +facts: List<&2, Rev.Header>, +moving: Moving, +parents: List<&2, String>, +ps: List<&2, String>) -> Result<&2, &2, String, Unit>:
  match moving:
    case Moving{ls, +lost, +intro, +pays}:
      do Result<&2, &2, String, Unit>:
        a : Unit <- Bool.pick(Result<&2, &2, String, Unit>, Bool.and(Nat.is_lt(1n, List.length(&2, String, ps)), moving.moved(Moving{ls, lost, intro, pays})),
          Fail{ab12(id) ++ " is a merge, and the rewrite moved content beneath it; restating a merge means recomputing what its parents agreed on, which is not built — amend the work onto the rewrite by hand, tip first"}, Done{Unit{}})
        b : Unit <- Bool.pick(Result<&2, &2, String, Unit>, Nat.is_lt(List.length(&2, String, parents), List.length(&2, String, ps)),
          Fail{"the rewrite folded two of " ++ ab12(id) ++ "'s parents into one revision, and carrying it would quietly turn a merge into a chain"}, Done{Unit{}})
        c : Unit <- maybe.refused(first_taken(List.append(&2, T.Split, facts.keyed(facts, "add"), facts.keyed(facts, "move")), intro), ab12(id) ++ " puts a file at `", "`, and the rewrite also put one there; two files cannot hold one path, so say where each goes by amending the work onto the rewrite by hand")
        d : Unit <- maybe.refused(first_lost(List.concat(&2, String, [heads_of(facts.keyed(facts, "edit")), heads_of(facts.keyed(facts, "text")), heads_of(facts.keyed(facts, "bytes")), heads_of(facts.keyed(facts, "move")), heads_of(facts.keyed(facts, "mode")), heads_of(facts.keyed(facts, "link")), dropped.of(facts), link.refs(facts.keyed(facts, "link"))]), lost),
          ab12(id) ++ " says something about `", "`, which the rewrite removed; what stands on the removal has to be restated by hand")
        maybe.refused(first_payload(heads_of(facts.keyed(facts, "bytes")), pays), ab12(id) ++ " and the rewrite state different bytes for ", ", and nothing here can choose between attachments; record the one that is meant, by hand")

# Steps
# -----

def restated.edits(rs: List<&2, Restated>) -> List<&2, T.Split>:
  match rs:
    case Nil{}:
      Nil{}
    case Restated{f, Some{e}, w, a} <> rest:
      T.Split{f, e} <> restated.edits(rest)
    case Restated{f, None{}, w, a} <> rest:
      restated.edits(rest)

def restated.files(rs: List<&2, Restated>) -> List<&2, String>:
  match rs:
    case Nil{}:
      Nil{}
    case Restated{f, e, None{}, None{}} <> rest:
      restated.files(rest)
    case Restated{f, e, w, a} <> rest:
      f <> restated.files(rest)

# The restated files: every one that was put through the merge, which is
# every one whose document is not the one named before.
def restated.put(+moved: List<&2, Base>, rs: List<&2, Restated>) -> List<&2, String>:
  match rs:
    case Nil{}:
      Nil{}
    case Restated{+f, e, w, a} <> rest:
      Rev.keep(Maybe.is_some(&2, Base, base.of(moved, f)), f, restated.put(moved, rest))

def restated.writes(+t: List<&2, Tree.Entry>, rs: List<&2, Restated>) -> List<&2, Write>:
  match rs:
    case Nil{}:
      Nil{}
    case Restated{+f, e, Some{+d}, a} <> rest:
      Write{Sha.digest(Utf8.encode(Ops.write(d))), Maybe.default(&2, String, path.of(t, f), SNil{}), d} <> restated.writes(t, rest)
    case Restated{f, e, None{}, a} <> rest:
      restated.writes(t, rest)

# What the file set is doing for the steps above: each restated file's new
# pair, whatever this revision states whole on both sides now, and whatever
# it drops gone from both.
def base.drop_all(bs: List<&2, Base>, +gone: List<&2, String>) -> List<&2, Base>:
  match bs:
    case Nil{}:
      Nil{}
    case Base{+f, o, n} <> rest:
      +later = base.drop_all(rest, gone)
      Bool.pick(List<&2, Base>, Rev.member(gone, f), later, Base{f, o, n} <> later)

def moving.after(rs: List<&2, Restated>, m: Moving, +whole: List<&2, String>, +dropped: List<&2, String>) -> Moving:
  match rs m:
    case Nil{} Moving{ls, lo, i, p}:
      Moving{base.drop_all(ls, dropped), lo, i, minus(p, List.append(&2, String, whole, dropped))}
    case Restated{+f, e, w, None{}} <> rest Moving{ls, lo, i, p}:
      moving.after(rest, Moving{base.without(ls, f), lo, i, p}, whole, dropped)
    case Restated{+f, e, w, Some{b}} <> rest Moving{ls, lo, i, p}:
      moving.after(rest, Moving{List.append(&2, Base, base.without(ls, f), [b]), lo, i, p}, whole, dropped)

def keyed.not(hs: List<&2, Rev.Header>, +keys: List<&2, String>, +want: Bool) -> List<&2, Rev.Header>:
  match hs:
    case Nil{}:
      Nil{}
    case Rev.Header{+k, v} <> rest:
      +later = keyed.not(rest, keys, want)
      Bool.pick(List<&2, Rev.Header>, Bool.not(Bool.xor(Rev.member(keys, k), want)), Rev.Header{k, v} <> later, later)

# The document's facts with its `edit` lines replaced: the format's order
# puts them after add, move, mode and drop.
def facts.edited(+facts: List<&2, Rev.Header>, edits: List<&2, T.Split>) -> List<&2, Rev.Header>:
  +early : List<&2, String> = ["add", "move", "mode", "drop"]
  List.concat(&2, Rev.Header, [keyed.not(facts, early, True{}), headers("edit", edits), keyed.not(facts, "edit" <> early, False{})])

# Decision 0010's derived row: `revised` from the rewrite that caused the
# carry — where several parents were rewritten, the greater digest's — or
# the person's own reading, for the revision a move names.
def stamp.of(+id: String, +cause: String, f: Maybe<&2, Full>) -> Result<&2, &2, String, T.Split>:
  match f:
    case Some{Full{i, change, ps, ss, author, when, rb, Some{+rv}, facts, m}}:
      Done{T.Split{rv, Maybe.default(&2, String, rb, author)}}
    case _:
      Fail{ab12(id) ++ " would take its `revised` from " ++ ab12(cause) ++ ", which carries none — a revision that supersedes without a stamp is one no writer produces"}

def stamp.r(+fs: List<&2, Full>, +docs: List<&2, Full>, +id: String, +mapped: List<&2, Mapped>, authored: Maybe<&2, T.Split>) -> Result<&2, &2, String, T.Split>:
  match authored:
    case Some{s}:
      Done{s}
    case None{}:
      +cause = last_of(sorted(mapped.changed(mapped)))
      stamp.of(id, cause, Maybe.or(&2, Full, find(docs, cause), find(fs, cause)))

def empty.r(+id: String, +facts: List<&2, Rev.Header>, +parents: List<&2, String>) -> Result<&2, &2, String, Unit>:
  Bool.pick(Result<&2, &2, String, Unit>, Bool.and(List.is_empty(&2, Rev.Header, facts), Nat.is_lt(List.length(&2, String, parents), 2n)),
    Fail{"everything " ++ ab12(id) ++ " states, the rewrite already states, and a revision saying nothing would mean nothing; abandon it instead, with the reason"}, Done{Unit{}})

# One revision restated, worked out to the last byte.
def paths.of(+t: List<&2, Tree.Entry>, fs: List<&2, String>) -> List<&2, String>:
  match fs:
    case Nil{}:
      Nil{}
    case +f <> rest:
      List.append(&2, String, Maybe.default(&2, List<&2, String>, Maybe.map(&2, String, List<&2, String>, p => [p], path.of(t, f)), Nil{}), paths.of(t, rest))

# What restating a revision works out beyond what it keeps: the parents it
# now stands on, its facts, its `revised` stamp, and what its step says,
# writes and hands on.
type Worked is Data:
  Worked{parents: List<&2, String>, facts: List<&2, Rev.Header>, stamp: T.Split, onto: List<&2, String>, restated: List<&2, String>, writes: List<&2, Write>, moving: Moving}

def step.worked(+fs: List<&2, Full>, +ds: List<&2, Store.Doc>, +docs: List<&2, Full>, +id: String, +ps: List<&2, String>, +facts: List<&2, Rev.Header>, +mapped: List<&2, Mapped>, +authored: Maybe<&2, T.Split>) -> Result<&2, &2, String, Worked>:
  +parents = sorted_distinct(mapped.news(mapped))
  +moving = moving.join(mapped.moving(mapped))
  +old_parent = Maybe.default(&2, String, List.get(&2, String, sorted(ps), 0n), SNil{})
  do Result<&2, &2, String, Worked>:
    e : Unit <- early.r(id, facts, moving, parents, ps)
    rs : List<&2, Restated> <- restate.all(ds, id, old_parent, mapped.new_of(mapped, old_parent), moving, facts.keyed(facts, "edit"))
    +rs2 : List<&2, Restated> = rs
    +redone : List<&2, String> = restated.put(moving.lines(moving), rs2)
    +new_facts : List<&2, Rev.Header> = facts.edited(facts, restated.edits(rs2))
    n : Unit <- empty.r(id, new_facts, parents)
    stamp : T.Split <- stamp.r(fs, docs, id, mapped, authored)
    t : List<&2, Tree.Entry> <- Bool.pick(Result<&2, &2, String, List<&2, Tree.Entry>>, List.is_empty(&2, String, redone), Done{Nil{}}, tree.at.r(fs, id))
    +t2 : List<&2, Tree.Entry> = t
    return Worked{parents, new_facts, stamp, mapped.news(mapped), paths.of(t2, redone), restated.writes(t2, rs2), moving.after(rs2, moving, heads_of(facts.keyed(facts, "bytes")), dropped.of(facts))}

# The restated revision: the change, author, moment and message of the one
# it supersedes, and what restating worked out.
def step.made(+id: String, +change: String, +author: String, +when: String, +message: String, w: Worked) -> Step:
  match w:
    case Worked{parents, new_facts, +stamp, onto, restated, writes, moving}:
      +doc = {Rev.Rev{change, parents, [id], author, when, revised_by(split.rest(stamp), author), Some{split.head(stamp)}, new_facts, message} : Rev.Rev}
      Step{id, Sha.digest(Utf8.encode(Rev.write(doc))), onto, doc, restated, writes, moving}

def step.of(+fs: List<&2, Full>, +ds: List<&2, Store.Doc>, +docs: List<&2, Full>, +id: String, prev: Full, +mapped: List<&2, Mapped>, +authored: Maybe<&2, T.Split>) -> Result<&2, &2, String, Step>:
  match prev:
    case Full{i, +change, +ps, ss, +author, +when, rb, rv, +facts, +message}:
      Result.map(&2, &2, String, Worked, Step, w => step.made(id, change, author, when, message, w), step.worked(fs, ds, docs, id, ps, facts, mapped, authored))

def step.id(s: Step) -> String:
  match s:
    case Step{p, id, o, d, r, w, m}:
      id

def step.full(s: Step) -> Full:
  match s:
    case Step{p, +id, o, d, r, w, m}:
      rev.full(id, d)

def step.handed(s: Step) -> Handed:
  match s:
    case Step{p, id, o, d, r, w, m}:
      Handed{p, m}

def held.r(f: Maybe<&2, Full>) -> Result<&2, &2, String, Full>:
  match f:
    case Some{x}:
      Done{x}
    case None{}:
      Fail{"a member of the plan is not held"}

# The revision a move names takes the person's reading; nothing else does.
def authored.of(+id: String, mv: Maybe<&2, Moved>, +stamp: Maybe<&2, T.Split>) -> Maybe<&2, T.Split>:
  match mv:
    case Some{Moved{+t, f, to}}:
      Bool.pick(Maybe<&2, T.Split>, String.eq(t, id), stamp, None{})
    case None{}:
      None{}

def steps.go(order: List<&2, String>, +fs: List<&2, Full>, +ds: List<&2, Store.Doc>, +mv: Maybe<&2, Moved>, +stamp: Maybe<&2, T.Split>, +docs: List<&2, Full>, +planned: List<&2, T.Split>, +handed: List<&2, Handed>) -> Result<&2, &2, String, List<&2, Step>>:
  match order:
    case Nil{}:
      Done{Nil{}}
    case +id <> rest:
      do Result<&2, &2, String, List<&2, Step>>:
        prev : Full <- held.r(find(fs, id))
        +prev2 : Full = prev
        mapped : List<&2, Mapped> <- mapped.all(fs, ds, planned, handed, id, mv, sorted(parents_of(prev2)))
        step : Step <- step.of(fs, ds, docs, id, prev2, mapped, authored.of(id, mv, stamp))
        +s : Step = step
        more : List<&2, Step> <- steps.go(rest, fs, ds, mv, stamp, step.full(s) <> docs, T.Split{id, step.id(s)} <> planned, step.handed(s) <> handed)
        return s <> more

# What a carry keeps of what it restates: each revision it writes has the
# change, author, moment and message of the one the store holds under the
# identifier it supersedes, supersedes that one alone, and is named by the
# digest of its own text. `LAWS.carry_keeps_what_it_restates` holds every
# plan to it.
def only.one(xs: List<&2, String>, +x: String) -> Bool:
  match xs:
    case y <> Nil{}:
      String.eq(y, x)
    case _:
      False{}

def rev.kept(+pred: String, f: Maybe<&2, Full>, doc: Rev.Rev) -> Bool:
  match f doc:
    case Some{Full{i, change, ps, ss, author, when, rb, rv, facts, message}} Rev.Rev{change2, ps2, ss2, author2, when2, rb2, rv2, facts2, message2}:
      Bool.and(String.eq(change, change2), Bool.and(String.eq(author, author2), Bool.and(String.eq(when, when2), Bool.and(String.eq(message, message2), only.one(ss2, pred)))))
    case None{} _:
      False{}

def step.kept(+fs: List<&2, Full>, s: Step) -> Bool:
  match s:
    case Step{+p, id, o, +doc, r, w, m}:
      Bool.and(String.eq(id, Sha.digest(Utf8.encode(Rev.write(doc)))), rev.kept(p, find(fs, p), doc))

def steps.kept(+fs: List<&2, Full>, ss: List<&2, Step>) -> Bool:
  match ss:
    case Nil{}:
      True{}
    case s <> rest:
      Bool.and(step.kept(fs, s), steps.kept(fs, rest))

# The authored move's refusals, which belong to deciding rather than to
# restating.
def onto.checked(+fs: List<&2, Full>, +target: String, +onto: String) -> Result<&2, &2, String, Moved>:
  +ps = full.parents(find(fs, target))
  +ss = successors(fs, target)
  Bool.pick(Result<&2, &2, String, Moved>, Bool.not(List.is_empty(&2, String, ss)),
    Fail{ab12(target) ++ " was rewritten two ways, and nothing here can choose which rewrite to carry the work onto; abandon one of them first:" ++ listed12(ss)},
  Bool.pick(Result<&2, &2, String, Moved>, Nat.is_lt(1n, List.length(&2, String, ps)),
    Fail{ab12(target) ++ " is a merge, and standing it somewhere new would mean working out afresh what its parents agree on — which is real work rather than something to guess at on anyone's behalf"},
  Bool.pick(Result<&2, &2, String, Moved>, List.is_empty(&2, String, ps),
    Fail{ab12(target) ++ " is where this history starts, and a history that started somewhere else is a different history"},
  Bool.pick(Result<&2, &2, String, Moved>, Rev.member(ps, onto),
    Fail{ab12(target) ++ " already stands on " ++ ab12(onto) ++ ", so there is nothing to restate"},
    Done{Moved{target, Maybe.default(&2, String, List.get(&2, String, ps, 0n), SNil{}), onto}}))))

def onto.inside(+set: List<&2, String>, mv: Maybe<&2, Moved>) -> Result<&2, &2, String, Unit>:
  match mv:
    case Some{Moved{+t, f, +to}}:
      Bool.pick(Result<&2, &2, String, Unit>, Rev.member(set, to),
        Fail{ab12(to) ++ " stands on " ++ ab12(t) ++ ", which is part of what moving " ++ ab12(t) ++ " would restate — the result would stand on a revision this act supersedes"}, Done{Unit{}})
    case None{}:
      Done{Unit{}}

# Which revisions a carry reaches: the repair's sweep, one revision named,
# an inline act's own strandings, or a person's move of one revision.
type Carrying is Data:
  Carrying.Everything{}
  Carrying.One{id: String}
  Carrying.By{causes: List<&2, String>}
  Carrying.Onto{target: String, onto: String, revised: String, reviser: String}

def carrying.move(+fs: List<&2, Full>, c: Carrying) -> Result<&2, &2, String, Maybe<&2, Moved>>:
  match c:
    case Carrying.Onto{+t, +o, r, by}:
      Result.map(&2, &2, String, Moved, Maybe<&2, Moved>, m => Some{m}, onto.checked(fs, t, o))
    case _:
      Done{None{}}

def carrying.stamp(c: Carrying) -> Maybe<&2, T.Split>:
  match c:
    case Carrying.Onto{t, o, r, by}:
      Some{T.Split{r, by}}
    case _:
      None{}

def carrying.start(+fs: List<&2, Full>, c: Carrying) -> Result<&2, &2, String, List<&2, String>>:
  match c:
    case Carrying.Everything{}:
      Done{stranded.all(fs, fs)}
    case Carrying.One{+id}:
      Bool.pick(Result<&2, &2, String, List<&2, String>>, stranded(fs, id), Done{[id]}, Fail{not_stranded(id)})
    case Carrying.By{+causes}:
      Done{stranded.by(fs, fs, causes)}
    case Carrying.Onto{+t, o, r, by}:
      Done{[t]}

# Work out what carrying would restate, without writing anything. `fs` is
# the store, and the rewrite an inline act is holding provisionally; `ds`
# the documents it names.
def carry.plan(+fs: List<&2, Full>, +ds: List<&2, Store.Doc>, +c: Carrying) -> Result<&2, &2, String, List<&2, Step>>:
  +fuel = Nat.add(List.length(&2, Full, fs), 1n)
  do Result<&2, &2, String, List<&2, Step>>:
    mv : Maybe<&2, Moved> <- carrying.move(fs, c)
    +mv2 : Maybe<&2, Moved> = mv
    start : List<&2, String> <- carrying.start(fs, c)
    +set : List<&2, String> = sorted(closure(fuel, fs, sorted(start)))
    i : Unit <- onto.inside(set, mv2)
    ds2 : List<&2, Dep> <- deps.r(fs, set, set)
    steps.go(order.go(fuel, ds2, Nil{}), fs, ds, mv2, carrying.stamp(c), Nil{}, Nil{}, Nil{})

# Every operation document a store's revisions name, for a plan to read.
def named.docs(fs: List<&2, Full>) -> List<&2, String>:
  match fs:
    case Nil{}:
      Nil{}
    case Full{i, c, ps, ss, a, w, rb, rv, +facts, m} <> rest:
      List.concat(&2, String, [T.map(~T.Split, ~String, ~(s => split.rest(s)), facts.keyed(facts, "edit")), T.map(~T.Split, ~String, ~(s => split.rest(s)), facts.keyed(facts, "text")), named.docs(rest)])

def carry.docs(+root: String, +fs: List<&2, Full>) -> IO(List<&2, Store.Doc>):
  do IO<List<&2, Store.Doc>>:
    ds : List<&2, Store.Doc> <- Store.fetch(root, sorted_distinct(named.docs(fs)))
    +ds2 : List<&2, Store.Doc> = ds
    more : List<&2, Store.Doc> <- Store.fetch(root, kept_digests(ds2))
    return List.append(&2, Store.Doc, ds2, more)

def step.named(s: Step) -> Naming.Named:
  match s:
    case Step{p, id, o, Rev.Rev{change, ps, ss, a, when, rb, rv, facts, message}, r, w, m}:
      Naming.Named{when, message, change}

def write.filing(w: Write) -> Naming.Filing:
  match w:
    case Write{h, p, d}:
      Naming.Filing{h, p, True{}}

# Each restated document, unless the store holds its digest by now.
def writes.one(+st: Bool, +root: String, +stem: String, +names: List<&2, T.Split>, +h: String, d: Ops.Doc, at: List<&2, String>) -> IO(Unit):
  match at:
    case "-" <> more:
      do IO<Unit>:
        w : Result<&1, &1, U32 & String, String> <- Store.filed(root ++ "/operations/" ++ stem ++ "/" ++ Naming.filed_as(names, h) ++ "\n" ++ Ops.write(d))
        done_w : String <- wrote.io(st, w)
        IO.pure(Unit, Unit{})
    case _:
      IO.pure(Unit, Unit{})

def writes.filed(+st: Bool, +root: String, +stem: String, +names: List<&2, T.Split>, ws: List<&2, Write>) -> IO(Unit):
  match ws:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case Write{+h, p, d} <> rest:
      do IO<Unit>:
        at : List<&2, String> <- Store.located(root, [h])
        writes.one(st, root, stem, names, h, d, at)
        writes.filed(st, root, stem, names, rest)

# Each step written, parents first, documents before revisions, named
# against everything the store holds by then — the steps before it included.
def carry.write(+st: Bool, +root: String, steps: List<&2, Step>, +ns: List<&2, Naming.Named>) -> IO(Unit):
  match steps:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case +s <> rest:
      match s:
        case Step{p, +id, o, +doc, r, +ws, m}:
          match doc:
            case Rev.Rev{+change, ps, ss, a, +when, rb, rv, facts, +message}:
              +stem = Naming.stem(when, message, change, id, ns)
              do IO<Unit>:
                writes.filed(st, root, stem, Naming.filed(T.map(~Write, ~Naming.Filing, ~(x => write.filing(x)), ws)), ws)
                revision.filed(st, root, stem, Rev.write(doc))
                carry.write(st, root, rest, List.append(&2, Naming.Named, ns, [step.named(s)]))

def carried.lines(+prefix: String, steps: List<&2, Step>) -> List<&2, String>:
  match steps:
    case Nil{}:
      Nil{}
    case Step{p, id, o, d, r, w, m} <> rest:
      (prefix ++ ab12(p) ++ " to " ++ ab12(id)) <> carried.lines(prefix, rest)

def carried.said(+prefix: String, steps: List<&2, Step>) -> IO(Unit):
  print_lines(carried.lines(prefix, steps))

def carried.ids(steps: List<&2, Step>) -> List<&2, String>:
  match steps:
    case Nil{}:
      Nil{}
    case Step{p, id, o, d, r, w, m} <> rest:
      id <> carried.ids(rest)

# An inline act's carries: what its own rewrite stranded, planned against a
# store holding the rewrite, and refused whole.
def inline.of(r: Result<&2, &2, String, List<&2, Step>>) -> Result<&2, &2, Refused, List<&2, Step>>:
  match r:
    case Done{steps}:
      Done{steps}
    case Fail{e}:
      Fail{Refused{1, "work stands on this, and restating it against the rewrite refused, so nothing was written: " ++ e}}

def inline.io(+st: Bool, +root: String, +fs: List<&2, Full>, +id: String, doc: Rev.Rev) -> IO(List<&2, Step>):
  +all = List.append(&2, Full, fs, [rev.full(id, doc)])
  do IO<List<&2, Step>>:
    ds : List<&2, Store.Doc> <- carry.docs(root, all)
    stated.io(List<&2, Step>, st, inline.of(carry.plan(all, ds, Carrying.By{[id]})))

# amend
# -----

# Decision 0023: which kind each file the amended revision added is, as it
# said — a file it listed under `bytes` is bytes, and every other is lines.
def kinds.prev(adds: List<&2, T.Split>, +whole: List<&2, String>) -> List<&2, T.Split>:
  match adds:
    case Nil{}:
      Nil{}
    case T.Split{+f, p} <> rest:
      T.Split{p, Bool.pick(String, Rev.member(whole, f), "bytes", "lines")} <> kinds.prev(rest, whole)

# The identifiers a path arriving takes: the amended revision's, where it
# added one there, and one freshly minted otherwise, in path order.
def lookups(ps: List<&2, String>, +kept: List<&2, T.Split>) -> List<&2, Maybe<&2, String>>:
  match ps:
    case Nil{}:
      Nil{}
    case +p <> rest:
      lookup(kept, p) <> lookups(rest, kept)

def amend.mint(arriving: List<&2, String>, found: List<&2, Maybe<&2, String>>, ids: List<&2, String>) -> List<&2, T.Split>:
  match arriving found ids:
    case p <> rest Some{f} <> more _:
      T.Split{p, f} <> amend.mint(rest, more, ids)
    case p <> rest None{} <> more i <> others:
      T.Split{p, i} <> amend.mint(rest, more, others)
    case _ _ _:
      Nil{}

# The identifiers an amendment gives the files arriving, `kept` being what
# the amended revision added, by path, and `hex` what was drawn for the
# rest.
def amend.minted(+arriving: List<&2, String>, +kept: List<&2, T.Split>, +hex: String) -> List<&2, T.Split>:
  amend.mint(arriving, lookups(arriving, kept), ids.minted(List.length(&2, String, minus(arriving, heads_of(kept))), hex))

# An amendment gives every file arriving an identifier, in path order,
# and each file the amended revision added keeps the identifier it was
# added under. `LAWS.amend_keeps_what_it_added`.
def keeps.one(m: Maybe<&2, String>, +f: String) -> Bool:
  match m:
    case Some{g}:
      String.eq(f, g)
    case None{}:
      True{}

def minted.keeps(+kept: List<&2, T.Split>, mint: List<&2, T.Split>) -> Bool:
  match mint:
    case Nil{}:
      True{}
    case T.Split{+p, +f} <> rest:
      Bool.and(keeps.one(lookup(kept, p), f), minted.keeps(kept, rest))

def amend.minted.ok(+arriving: List<&2, String>, +kept: List<&2, T.Split>, +mint: List<&2, T.Split>) -> Bool:
  Bool.and(strings.same(T.map(~T.Split, ~String, ~(s => split.head(s)), mint), arriving), minted.keeps(kept, mint))

def amend.draw(+st: Bool, +n: Nat, none: Bool) -> IO(String):
  match none:
    case True{}:
      IO.pure(String, SNil{})
    case False{}:
      do IO<String>:
        drew : Result<&1, &1, U32 & String, String> <- Store.drawn(Nat.show(Nat.mul(12n, n)))
        wrote.io(st, drew)

# Whether a rewrite says exactly what it rewrites: `supersedes`, `revised`
# and `revised-by` describe the rewrite, not the work, and are set aside.
def bare(r: Rev.Rev) -> String:
  match r:
    case Rev.Rev{change, parents, ss, author, when, rb, rv, facts, message}:
      Rev.write(Rev.Rev{change, sorted(parents), Nil{}, author, when, None{}, None{}, facts, message})

def same.r(+id: String, prev: Rev.Rev, doc: Rev.Rev) -> Result<&2, &2, Refused, Unit>:
  Bool.pick(Result<&2, &2, Refused, Unit>, String.eq(bare(prev), bare(doc)),
    Fail{Refused{1, ab12(id) ++ " already says exactly this, and a revision superseding one identical to itself would mean nothing"}},
    Done{Unit{}})

# What amending says it did, or would do.
def amend.told.lines(machine: Bool, +id: String, +change: String, +prev: String, +facts: List<&2, T.Split>, +steps: List<&2, Step>) -> List<&2, String>:
  match machine:
    case True{}:
      WROTE() <> said.lines("revision ", SNil{}, sorted_distinct(id <> carried.ids(steps)))
    case False{}:
      List.concat(&2, String, [facts.said(facts), ["amended " ++ String.take(change, 8n) ++ " as " ++ ab12(id), "it supersedes " ++ ab12(prev) ++ ", which is still here"], carried.lines("carried ", steps)])

def amend.said.lines(machine: Bool, planning: Bool, +facts: List<&2, T.Split>, +prev: String, +change: String, +id: String, +carrying: List<&2, String>, +steps: List<&2, Step>) -> List<&2, String>:
  match planning:
    case True{}:
      List.concat(&2, String, [facts.said(facts), ["this would supersede " ++ ab12(prev)], said.lines("would carry ", SNil{}, map12(carrying))])
    case False{}:
      amend.told.lines(machine, id, change, prev, facts, steps)

def amend.said(machine: Bool, planning: Bool, +facts: List<&2, T.Split>, +prev: String, +change: String, +id: String, +carrying: List<&2, String>, +steps: List<&2, Step>) -> IO(Unit):
  print_lines(amend.said.lines(machine, planning, facts, prev, change, id, carrying, steps))

# The amendment written: its content, the revision, and what it carries.
def amend.written(+st: Bool, planning: Bool, +root: String, +repo: String, +fs: List<&2, Full>, +cs: List<&2, Content>, +id: String, +doc: Rev.Rev, +steps: List<&2, Step>) -> IO(Unit):
  match planning doc:
    case True{} _:
      IO.pure(Unit, Unit{})
    case False{} Rev.Rev{+change, ps, ss, a, +when, rb, rv, facts, +message}:
      +ns = T.map(~Full, ~Naming.Named, ~(f => full.named(f)), fs)
      +stem = Naming.stem(when, message, change, id, ns)
      do IO<Unit>:
        contents.filed(st, root, repo, stem, cs)
        revision.filed(st, root, stem, Rev.write(Rev.Rev{change, ps, ss, a, when, rb, rv, facts, message}))
        carry.write(st, root, steps, List.append(&2, Naming.Named, ns, [Naming.Named{when, message, change}]))

# Decision 0023's amendment: the amended revision's change, parents, author
# and moment, `revised` now, and everything else surveyed afresh against
# those parents.
def amend.write(+st: Bool, +root: String, +repo: String, +fs: List<&2, Full>, +ps: List<&2, String>, +t: Tree.Tree(), +hs: List<&2, Here>, +dg: Map<&2, String>, +reads: Map<&2, List<&2, U32>>, +ks: List<&2, T.Split>, +moves: List<&2, T.Split>, pl: Sv.Planned, +prev: Full, +reviser: String, +revised: String, +m: Maybe<&2, String>, +fields: Bool, +dry: Bool) -> IO(Unit):
  match pl:
    case Sv.Planned{+facts, r, c, a, e, d, +obs, +ls}:
      +arriving = Sv.sorted(Sv.added(obs))
      +kept = swapped(facts.keyed(facts_of(prev), "add"))
      +n = List.length(&2, String, minus(arriving, heads_of(kept)))
      +pid = id_of(prev)
      do IO<Unit>:
        hex : String <- amend.draw(st, n, Bool.or(dry, Nat.is_eq(n, 0n)))
        +mint : List<&2, T.Split> = amend.minted(arriving, kept, hex)
        dr : Drafted <- drafted(st, root, fs, ps, t, hs, dg, reads, ks, moves, obs, ls, mint)
        +dr2 : Drafted = dr
        +doc : Rev.Rev = Rev.Rev{change_of(prev), sorted(ps), [pid], author_of(prev), when_of(prev), revised_by(reviser, author_of(prev)), Some{revised}, drafted.facts(dr2), Maybe.default(&2, String, m, message_of(prev))}
        +id : String = Sha.digest(Utf8.encode(Rev.write(doc)))
        stated.io(Unit, st, same.r(pid, full.rev(prev), doc))
        amend.written(st, dry, root, repo, fs, drafted.contents(dr2), id, doc, Nil{})
        amend.said(fields, dry, facts, pid, change_of(prev), id, Nil{}, Nil{})


# Everything a rewrite of a revision would carry, for a dry run to name:
# the stack above it, breadth first from what stands on it.
def would_carry.go(fuel: Nat, +fs: List<&2, Full>, queue: List<&2, String>, +out: List<&2, String>, +seen: List<&2, String>) -> List<&2, String>:
  match fuel queue:
    case 0n _:
      out
    case _ Nil{}:
      out
    case 1n+k +on <> rest:
      +kids = minus(standing_on(fs, on), seen)
      would_carry.go(k, fs, List.append(&2, String, rest, kids), List.append(&2, String, out, kids), List.append(&2, String, seen, kids))


def would_carry(+fs: List<&2, Full>, +id: String, +standing: List<&2, String>) -> List<&2, String>:
  would_carry.go(Nat.add(List.length(&2, Full, fs), 1n), fs, standing, standing, id <> standing)

# What a survey is for: a plan to print, a record to write, or an
# amendment of `prev`, written or planned.
type Act is Data:
  Act.Plan{}
  Act.Record{w: Writing}
  Act.Amend{prev: Full, reviser: String, revised: String, message: Maybe<&2, String>, fields: Bool, dry: Bool}

def act.reads(a: Act) -> Bool:
  match a:
    case Act.Plan{}:
      False{}
    case _:
      True{}

def act.of(w: Maybe<&2, Writing>) -> Act:
  match w:
    case None{}:
      Act.Plan{}
    case Some{x}:
      Act.Record{x}

def record.then(+st: Bool, +root: String, +repo: String, +fs: List<&2, Full>, +bs: List<&2, Bm.Bookmark>, +ps: List<&2, String>, +t: Tree.Tree(), +hs: List<&2, Here>, +dg: Map<&2, String>, +reads: Map<&2, List<&2, U32>>, +ks: List<&2, T.Split>, +moves: List<&2, T.Split>, pl: Sv.Planned, act: Act) -> IO(Unit):
  match act:
    case Act.Plan{}:
      record.print(planned.facts(pl))
    case Act.Record{+wr}:
      record.write(st, root, repo, fs, bs, ps, t, hs, dg, reads, ks, moves, pl, wr)
    case Act.Amend{+prev, +reviser, +revised, +m, +fields, +dry}:
      amend.write(st, root, repo, fs, ps, t, hs, dg, reads, ks, moves, pl, prev, reviser, revised, m, fields, dry)

# The survey `record` plans from: `t0` is the position's tree, and `p`
# where the stated renames put its files. With nothing to write, the plan
# is printed; otherwise it is recorded.
def record.surveyed(+st: Bool, +root: String, +repo: String, +fs: List<&2, Full>, +bs: List<&2, Bm.Bookmark>, +ps: List<&2, String>, +rules: List<&2, Folder.Scope>, +found: List<&2, Folder.Found>, walked: List<&2, T.Split>, +t0: Tree.Tree(), p: Placed, +only: List<&2, String>, +kinds: List<&2, T.Split>, +accepted: List<&2, String>, +w: Act) -> IO(Unit):
  match p:
    case Placed{t1, +moved}:
      +t = Sv.by_file(t1)
      +folder = found_paths(found)
      +looked = Sv.only.tree(only, t)
      +cs = Sv.claims(looked)
      +hs = heres(Sv.unclaimed(looked, cs), Sv.unclaimed_found(Sv.only.found(only, found), cs), Limit.None{})
      +paths = regular_paths(hs)
      +writes = act.reads(w)
      do IO<Unit>:
        stated.io(Unit, st, skips_held.r(skipped_held(rules, t)))
        stated.io(Unit, st, named.r(rules, only, folder, Sv.paths(t0), Sv.paths(t)))
        stated.io(Unit, st, record.fault.r(Sv.kind_fault(only, t, kinds)))
        stats : List<&2, String> <- Store.stats(repo, paths)
        +dg : Map<&2, String> = stats.map(paths, stats, Map.new(&2, String))
        bf : Map<&2, String> <- status.befores.io(root, fs, ps, hs)
        +bf2 : Map<&2, String> = bf
        reads : Map<&2, List<&2, U32>> <- read_all(repo, List.append(&2, String, status.reads(dg, bf2, hs), Bool.pick(List<&2, String>, writes, added.regular(hs), lined_added(kinds, hs))), Map.new(&2, List<&2, U32>))
        +reads2 : Map<&2, List<&2, U32>> = reads
        stated.io(Unit, st, record.fault.r(not_lines(kinds, reads2, hs)))
        pl : Sv.Planned <- stated.io(Sv.Planned, st, planned.r(looked, Sv.planned(t, looked, Set.from_list(folder), Sv.only.refused(only, walked), status.seens(t0, dg, bf2, reads2, hs), moved), accepted))
        record.then(st, root, repo, fs, bs, ps, t, hs, dg, reads2, kinds, moved, pl, w)

def author.refused(r: Result<&2, &2, String, String>) -> Result<&2, &2, Refused, String>:
  match r:
    case Fail{msg}:
      Fail{Refused{1, msg}}
    case Done{a}:
      Done{a}

def found.repository(r: Result<&1, &1, U32 & String, String>) -> String:
  match r:
    case Done{+root}:
      repository(root)
    case Fail{e}:
      SNil{}

# Who is recording, as `identity::author_for` decides it for the repository
# around the store: `$HISTORICA_AUTHOR`, or what the identity file says of
# the repository (`identity.bend`). The store is found again, where the
# command found it, rather than carried here.
def author.io(+st: Bool) -> IO(String):
  do IO<String>:
    found : Result<&1, &1, U32 & String, String> <- Store.root.found()
    a : Result<&2, &2, String, String> <- Identity.author(found.repository(found))
    stated.io(String, st, author.refused(a))

def editor.refused(r: Result<&2, &2, Editor.Stop, String>) -> Result<&2, &2, Refused, String>:
  match r:
    case Fail{Editor.Stop{code, why}}:
      Fail{Refused{code, why}}
    case Done{m}:
      Done{m}

# Why, from `-m`, or from the editor the person chose (`editor.bend`).
def message.io(+st: Bool, m: Maybe<&2, String>) -> IO(String):
  match m:
    case Some{x}:
      IO.pure(String, x)
    case None{}:
      do IO<String>:
        r : Result<&2, &2, Editor.Stop, String> <- Editor.message()
        stated.io(String, st, editor.refused(r))

def when.r(r: Result<&1, &1, U32 & String, String>) -> Result<&2, &2, Refused, String>:
  match r:
    case Done{x}:
      Done{x}
    case Fail{Tuple{code, msg}}:
      Fail{Refused{1, msg}}

# Decision 0010: the failure worth catching is a machine that says 1970,
# since every later revision of the change copies what it says.
def clock.warned(+now: String, newest: Maybe<&2, String>) -> IO(Unit):
  match newest:
    case Some{+n}:
      Bool.pick(IO(Unit), Nat.is_lt(Naming.instant(now), Naming.instant(n)), IO.print_err("historica: this machine's clock reads " ++ now ++ ", and this store already holds work recorded at " ++ n), IO.pure(Unit, Unit{}))
    case None{}:
      IO.pure(Unit, Unit{})

def whens(ds: List<&2, T.Split>) -> List<&2, String>:
  match ds:
    case Nil{}:
      Nil{}
    case T.Split{i, w} <> rest:
      w <> whens(rest)

# What a record that writes asks before it surveys, in the Rust tool's
# order: who, what time it is, and why.
def record.writing(+st: Bool, +fs: List<&2, Full>, +dry: Bool, +fields: Bool, m: Maybe<&2, String>) -> IO(Maybe<&2, Writing>):
  match dry:
    case True{}:
      IO.pure(Maybe<&2, Writing>, None{})
    case False{}:
      do IO<Maybe<&2, Writing>>:
        author : String <- author.io(st)
        now : Result<&1, &1, U32 & String, String> <- Store.clock(SNil{})
        when : String <- stated.io(String, st, when.r(now))
        +when2 : String = when
        clock.warned(when2, Naming.newest(whens(by_head(T.map(~Full, ~T.Split, ~(f => full.dated(f)), fs))), None{}))
        message : String <- message.io(st, m)
        return Some{Writing{author, when2, message, fields}}

def record.go(+st: Bool, +root: String, +fs: List<&2, Full>, +bs: List<&2, Bm.Bookmark>, c: RecordCmd) -> IO(Unit):
  match c:
    case RecordCmd{+onto, +ms, ac, ats, +moves, ks, ns, +d, +f, mg}:
      +repo = repository(root)
      +only = sorted_distinct(ns)
      do IO<Unit>:
        at : List<&2, T.Split> <- stated.io(List<&2, T.Split>, st, at.files.r(bs, ats))
        ps : List<&2, String> <- stated.io(List<&2, String>, st, status.parents.r(fs, bs, onto, ms))
        +ps2 : List<&2, String> = ps
        stated.io(Unit, st, restricted.r(only, ps2, moves))
        perform(st, repo, moves)
        rules : List<&2, Folder.Scope> <- Folder.rules(root)
        +rs : List<&2, Folder.Scope> = rules
        w : Folder.Walked <- Folder.walk.all(repo, rs)
        +w2 : Folder.Walked = w
        +kinds : List<&2, T.Split> = kinds.of(ks)
        refused.io(Unit, kinds.unheld.r(kinds, Set.from_list(found_paths(Folder.walked.found(w2)))))
        wr : Maybe<&2, Writing> <- record.writing(st, fs, d, f, mg)
        m : Tree.Merged <- stated.io(Tree.Merged, st, status.tree.r(fs, ps2))
        +t0 : Tree.Tree() = Tree.merged_tree(m)
        p : Placed <- stated.io(Placed, st, placed.r(t0, at, moves))
        record.surveyed(st, root, repo, fs, bs, ps2, rs, Folder.walked.found(w2), Folder.walked.refused(w2), t0, p, only, kinds, sorted_distinct(ac), act.of(wr))

def record.stated.r(+d: Bool, +f: Bool) -> Result<&2, &2, Refused, Unit>:
  Bool.pick(Result<&2, &2, Refused, Unit>, Bool.and(d, f), Fail{Refused{2, "`record --dry-run --fields` is refused: `--fields` states what is on disk, and a plan is not on disk. ask for one or the other"}}, Done{Unit{}})

# A merge states a resolution of each contested file, which nothing here
# writes yet; `record --dry-run --merge` says what one would record.
def record.merge.r(d: Bool, ms: List<&2, String>) -> Result<&2, &2, Refused, Unit>:
  Bool.pick(Result<&2, &2, Refused, Unit>, Bool.or(d, List.is_empty(&2, String, ms)), Done{Unit{}}, Fail{Refused{1, "recording a merge writes resolutions, which this port does not do yet; `record --dry-run` says what it would record"}})

def record.checked(+st: Bool, +root: String, c: RecordCmd) -> IO(Unit):
  match c:
    case RecordCmd{o, +ms, ac, at, mv, +ks, ns, +d, +f, mg}:
      do IO<Unit>:
        refused.io(Unit, record.stated.r(d, f))
        refused.io(Unit, kinds.clash.r(ks, Nil{}))
        stated.io(Unit, st, record.merge.r(d, ms))
        opened.stated(st, root)
        rs : List<&2, Store.Doc> <- Store.revisions(root)
        bs : List<&2, Bm.Bookmark> <- bookmarks(root)
        record.go(st, root, fulls(root, rs), bs, RecordCmd{o, ms, ac, at, mv, ks, ns, d, f, mg})

# Where the store is, for the four commands the Rust tool finds it for
# before it reads their words. No statement is owed where there is none:
# the Rust tool's `?` on that search leaves `run` before decision 0074's
# header is considered.
def record.root(+st: Bool, r: Result<&1, &1, U32 & String, String>) -> IO(String):
  match r:
    case Fail{Tuple{code, msg}}:
      die(String, 1, msg)
    case Done{found}:
      IO.pure(String, found)

# `stating` is the Rust tool's own test for owing `--fields`'s header on a
# refusal: the word anywhere among the arguments.
def record(+args: List<&2, String>) -> IO(Unit):
  +st = Rev.member(args, "--fields")
  do IO<Unit>:
    found : Result<&1, &1, U32 & String, String> <- Store.root.found()
    root : String <- record.root(st, found)
    +r : String = root
    a : RecordCmd <- refused.io(RecordCmd, record.args.r(args))
    record.checked(st, r, a)

# Rewriting: amend, abandon, carry
# --------------------------------

# The three commands that supersede, read as the Rust tool reads them: in
# order, each flag the command takes and the first word that is not one,
# the rest refused as they come.
type RwCmd is Data:
  RwCmd{message: Maybe<&2, String>, moves: List<&2, T.Split>, onto: Maybe<&2, String>, named: Maybe<&2, String>,
        dry: Bool, fields: Bool, only: Bool}

type WWord is Data:
  WWord.Message{}
  WWord.Move{}
  WWord.Onto{}
  WWord.Only{}
  WWord.Dry{}
  WWord.Fields{}
  WWord.Flag{}
  WWord.Word{}

def wword.of(+cmd: String, +w: String) -> WWord:
  Bool.pick(WWord, Bool.and(Bool.not(String.eq(cmd, "carry")), Bool.or(String.eq(w, "-m"), String.eq(w, "--message"))), WWord.Message{},
  Bool.pick(WWord, Bool.and(String.eq(cmd, "amend"), String.eq(w, "--move")), WWord.Move{},
  Bool.pick(WWord, Bool.and(String.eq(cmd, "carry"), String.eq(w, "--onto")), WWord.Onto{},
  Bool.pick(WWord, Bool.and(String.eq(cmd, "abandon"), String.eq(w, "--only")), WWord.Only{},
  Bool.pick(WWord, Bool.or(String.eq(w, "-n"), String.eq(w, "--dry-run")), WWord.Dry{},
  Bool.pick(WWord, String.eq(w, "--fields"), WWord.Fields{},
  Bool.pick(WWord, String.starts_with(w, "-"), WWord.Flag{}, WWord.Word{})))))))

def wword(+cmd: String, args: List<&2, String>) -> WWord:
  match args:
    case Nil{}:
      WWord.Word{}
    case +w <> rest:
      wword.of(cmd, w)

def rw.message(c: RwCmd, v: String) -> RwCmd:
  match c:
    case RwCmd{m, mv, o, n, d, f, y}:
      RwCmd{Some{v}, mv, o, n, d, f, y}

def rw.move(c: RwCmd, v: T.Split) -> RwCmd:
  match c:
    case RwCmd{m, mv, o, n, d, f, y}:
      RwCmd{m, List.append(&2, T.Split, mv, [v]), o, n, d, f, y}

def rw.onto(c: RwCmd, v: String) -> RwCmd:
  match c:
    case RwCmd{m, mv, o, n, d, f, y}:
      RwCmd{m, mv, Some{v}, n, d, f, y}

def rw.only(c: RwCmd) -> RwCmd:
  match c:
    case RwCmd{m, mv, o, n, d, f, y}:
      RwCmd{m, mv, o, n, d, f, True{}}

def rw.dry(c: RwCmd) -> RwCmd:
  match c:
    case RwCmd{m, mv, o, n, d, f, y}:
      RwCmd{m, mv, o, n, True{}, f, y}

def rw.fields(c: RwCmd) -> RwCmd:
  match c:
    case RwCmd{m, mv, o, n, d, f, y}:
      RwCmd{m, mv, o, n, d, True{}, y}

def rw.second(+cmd: String, +w: String) -> String:
  Bool.pick(String, String.eq(cmd, "amend"), "`amend` rewrites one revision, and `" ++ w ++ "` is a second",
  Bool.pick(String, String.eq(cmd, "abandon"), "`abandon` abandons one run of work, and `" ++ w ++ "` is a second",
    "`carry` carries one line of work, and `" ++ w ++ "` is a second"))

def rw.word(+cmd: String, c: RwCmd, +w: String) -> Result<&2, &2, Refused, RwCmd>:
  match c:
    case RwCmd{m, mv, o, None{}, d, f, y}:
      Done{RwCmd{m, mv, o, Some{w}, d, f, y}}
    case RwCmd{m, mv, o, Some{n}, d, f, y}:
      Fail{Refused{2, rw.second(cmd, w)}}

def rw.args.go(+cmd: String, args: List<&2, String>, c: RwCmd, k: WWord) -> Result<&2, &2, Refused, RwCmd>:
  match args k:
    case Nil{} _:
      Done{c}
    case w <> Nil{} WWord.Message{}:
      Fail{Refused{2, "`-m` wants a value"}}
    case w <> v <> +rest WWord.Message{}:
      rw.args.go(cmd, rest, rw.message(c, v), wword(cmd, rest))
    case w <> Nil{} WWord.Move{}:
      Fail{Refused{2, "`--move` wants a value"}}
    case w <> +v <> +rest WWord.Move{}:
      do Result<&2, &2, Refused, RwCmd>:
        s : T.Split <- record.split(v, "`--move` is spelled `--move <old>=<new>`")
        rw.args.go(cmd, rest, rw.move(c, s), wword(cmd, rest))
    case w <> Nil{} WWord.Onto{}:
      Fail{Refused{2, "`--onto` wants a value"}}
    case w <> v <> +rest WWord.Onto{}:
      rw.args.go(cmd, rest, rw.onto(c, v), wword(cmd, rest))
    case w <> +rest WWord.Only{}:
      rw.args.go(cmd, rest, rw.only(c), wword(cmd, rest))
    case w <> +rest WWord.Dry{}:
      rw.args.go(cmd, rest, rw.dry(c), wword(cmd, rest))
    case w <> +rest WWord.Fields{}:
      rw.args.go(cmd, rest, rw.fields(c), wword(cmd, rest))
    case w <> rest WWord.Flag{}:
      Fail{Refused{2, "`" ++ w ++ "` is not an argument `" ++ cmd ++ "` takes"}}
    case w <> +rest WWord.Word{}:
      do Result<&2, &2, Refused, RwCmd>:
        more : RwCmd <- rw.word(cmd, c, w)
        rw.args.go(cmd, rest, more, wword(cmd, rest))

def rw.args.r(+cmd: String, +args: List<&2, String>) -> Result<&2, &2, Refused, RwCmd>:
  rw.args.go(cmd, args, RwCmd{None{}, Nil{}, None{}, None{}, False{}, False{}, False{}}, wword(cmd, args))

# What the words of `amend`, `abandon` and `carry` say, read plainly, as
# `rargs.read` reads `record`'s: each a flag the command takes and what it
# says, the word after one that takes a value being that value, or the
# target. `LAWS.rewrite_reads_its_words` holds `rw.args.r` to `wargs.said`.
def wargs.read(+cmd: String, args: List<&2, String>, k: WWord) -> List<&2, T.Split>:
  match args k:
    case Nil{} _:
      Nil{}
    case w <> v <> +rest WWord.Message{}:
      T.Split{"-m", v} <> wargs.read(cmd, rest, wword(cmd, rest))
    case w <> v <> +rest WWord.Move{}:
      T.Split{"--move", v} <> wargs.read(cmd, rest, wword(cmd, rest))
    case w <> v <> +rest WWord.Onto{}:
      T.Split{"--onto", v} <> wargs.read(cmd, rest, wword(cmd, rest))
    case w <> +rest WWord.Only{}:
      T.Split{"--only", SNil{}} <> wargs.read(cmd, rest, wword(cmd, rest))
    case w <> +rest WWord.Dry{}:
      T.Split{"--dry-run", SNil{}} <> wargs.read(cmd, rest, wword(cmd, rest))
    case w <> +rest WWord.Fields{}:
      T.Split{"--fields", SNil{}} <> wargs.read(cmd, rest, wword(cmd, rest))
    case w <> +rest WWord.Word{}:
      T.Split{"target", w} <> wargs.read(cmd, rest, wword(cmd, rest))
    case w <> +rest _:
      wargs.read(cmd, rest, wword(cmd, rest))

# What the words mean: the last `-m`; each `--move`, in order, cut at its
# first `=`; the last `--onto`; the target; and `-n`, `--fields` and
# `--only` if they are there.
def wargs.said(+items: List<&2, T.Split>) -> RwCmd:
  RwCmd{rargs.last(items, "-m", None{}), rargs.cuts(rargs.values(items, "--move")), rargs.last(items, "--onto", None{}),
    rargs.last(items, "target", None{}), rargs.has(items, "--dry-run", False{}), rargs.has(items, "--fields", False{}),
    rargs.has(items, "--only", False{})}

def rw.plan.r(+cmd: String, d: Bool, f: Bool) -> Result<&2, &2, Refused, Unit>:
  Bool.pick(Result<&2, &2, Refused, Unit>, Bool.and(d, f), Fail{Refused{2, "`" ++ cmd ++ " --dry-run --fields` is refused: `--fields` states what is on disk, and a plan is not on disk. ask for one or the other"}}, Done{Unit{}})

def joins.msg(+id: String) -> String:
  ab12(id) ++ " joins work from another line, and abandoning it would take that work out of the ancestry too; abandon up to the merge, or the other line first"

# Every revision after the first must stand on the run and nothing else.
def joins.r(+id: String, +ps: List<&2, String>, prev: Maybe<&2, String>) -> Result<&2, &2, Refused, Unit>:
  match prev:
    case None{}:
      Done{Unit{}}
    case Some{+p}:
      Bool.pick(Result<&2, &2, Refused, Unit>, Bool.and(Nat.is_eq(List.length(&2, String, ps), 1n), Rev.member(ps, p)), Done{Unit{}}, Fail{Refused{1, joins.msg(id)}})

# Decision 0013's run: the named revision and everything standing on it,
# which has to be a line. `standing` is what stands on `prev`, the last of
# the run so far, and what is found is the rest of the run.
def run.go(fuel: Nat, +fs: List<&2, Full>, +prev: String, standing: List<&2, String>) -> Result<&2, &2, Refused, List<&2, String>>:
  match fuel standing:
    case 0n _:
      Done{Nil{}}
    case _ Nil{}:
      Done{Nil{}}
    case 1n+k +n <> Nil{}:
      do Result<&2, &2, Refused, List<&2, String>>:
        a : Unit <- already.r(fs, n)
        j : Unit <- joins.r(n, full.parents(find(fs, n)), Some{prev})
        more : List<&2, String> <- run.go(k, fs, n, standing_on(fs, n))
        return n <> more
    case _ +several:
      Fail{Refused{1, Nat.show(List.length(&2, String, several)) ++ " lines of work stand on " ++ ab12(prev) ++ ", and abandoning it would abandon all of them; name the one you mean, or abandon each in turn:" ++ listed12(several)}}

def abandon.plan.r(+fs: List<&2, Full>, +id: String, only: Bool) -> Result<&2, &2, Refused, List<&2, String>>:
  match only:
    case True{}:
      do Result<&2, &2, Refused, List<&2, String>>:
        a : Unit <- already.r(fs, id)
        Bool.pick(Result<&2, &2, Refused, List<&2, String>>, Nat.is_lt(1n, List.length(&2, String, full.parents(find(fs, id)))), Fail{Refused{1, joins.msg(id)}}, Done{[id]})
    case False{}:
      do Result<&2, &2, Refused, List<&2, String>>:
        a : Unit <- already.r(fs, id)
        more : List<&2, String> <- run.go(Nat.add(List.length(&2, Full, fs), 1n), fs, id, standing_on(fs, id))
        return id <> more

# What `abandon` abandons is a line of work nothing has rewritten: it
# begins at the revision named, and each revision after that stands on the
# one before it and on nothing else; and with `--only` it is the revision
# named alone, which joins no other line. `LAWS.abandon_takes_a_line`.
def unrewritten(+fs: List<&2, Full>, +id: String) -> Bool:
  List.is_empty(&2, String, successors(fs, id))

def abandon.after(run: List<&2, String>, +fs: List<&2, Full>, +prev: String) -> Bool:
  match run:
    case Nil{}:
      True{}
    case +r <> rest:
      Bool.and(unrewritten(fs, r), Bool.and(only.one(full.parents(find(fs, r)), prev), abandon.after(rest, fs, r)))

def abandon.line(+fs: List<&2, Full>, +id: String, only: Bool, run: List<&2, String>) -> Bool:
  match run:
    case Nil{}:
      False{}
    case +r <> +rest:
      Bool.and(String.eq(r, id), Bool.and(unrewritten(fs, r), Bool.pick(Bool, only,
        Bool.and(List.is_empty(&2, String, rest), Bool.not(Nat.is_lt(1n, List.length(&2, String, full.parents(find(fs, r)))))),
        abandon.after(rest, fs, r))))

def each.lines(+prefix: String, xs: List<&2, String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> rest:
      (prefix ++ x) <> each.lines(prefix, rest)

def spelled_all(+bs: List<&2, Bm.Bookmark>, +h: Rev.History(), xs: List<&2, String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case +x <> rest:
      (ab12(x) ++ names_at(bs, h, x)) <> spelled_all(bs, h, rest)

# abandon
# -------

def abandon.dry.lines(+fs: List<&2, Full>, +bs: List<&2, Bm.Bookmark>, +id: String, +only: Bool, +run: List<&2, String>) -> List<&2, String>:
  +n = List.length(&2, String, run)
  List.concat(&2, String, [each.lines("would abandon ", spelled_all(bs, history(fs), run)),
    ["a tombstone would supersede " ++ Bool.pick(String, Nat.is_eq(n, 1n), "this revision", "these " ++ Nat.show(n) ++ " revisions") ++ ", and its message is required"],
    each.lines("would carry ", map12(Bool.pick(List<&2, String>, only, would_carry(fs, id, standing_on(fs, id)), Nil{})))])

def abandon.dry(+fs: List<&2, Full>, +bs: List<&2, Bm.Bookmark>, +id: String, +only: Bool, +run: List<&2, String>) -> IO(Unit):
  print_lines(abandon.dry.lines(fs, bs, id, only, run))

# A dry run of `abandon` begins by naming, in order, each revision it
# would abandon, by its digest's first twelve letters.
# `LAWS.abandon_dry_run_names_the_run`.
def said.first(xs: List<&2, String>, ls: List<&2, String>, +prefix: String) -> Bool:
  match xs ls:
    case Nil{} _:
      True{}
    case +x <> rest +l <> more:
      Bool.and(String.starts_with(l, prefix ++ ab12(x)), said.first(rest, more, prefix))
    case _ Nil{}:
      False{}

# What abandoning says it did: for a machine, decision 0074's header, each
# revision written and each bookmark moved; for a person, what was
# abandoned, the tombstone, each bookmark moved and what was carried.
def abandon.said.lines(fields: Bool, +id: String, +change: String, +run: List<&2, String>, +names: List<&2, String>, +steps: List<&2, Step>) -> List<&2, String>:
  match fields:
    case True{}:
      WROTE() <> List.append(&2, String, said.lines("revision ", SNil{}, sorted_distinct(id <> carried.ids(steps))), said.lines("name ", SNil{}, sorted_distinct(names)))
    case False{}:
      List.concat(&2, String, [each.lines("abandoned ", map12(run)), ["the tombstone is " ++ ab12(id) ++ " (" ++ String.take(change, 8n) ++ ")"],
        said.lines(SNil{}, " -> " ++ String.take(change, 8n), names), carried.lines("carried ", steps), ["what it supersedes is still here; `historica prune` is what removes it"]])

def abandon.said(+fields: Bool, +id: String, +change: String, +run: List<&2, String>, +names: List<&2, String>, +steps: List<&2, Step>) -> IO(Unit):
  print_lines(abandon.said.lines(fields, id, change, run, names, steps))

def reason.r(+m: String) -> Result<&2, &2, Refused, Unit>:
  Bool.pick(Result<&2, &2, Refused, Unit>, String.is_empty(Naming.trim_space(m)),
    Fail{Refused{1, "abandoning removes this work from what the history means, and the reason is the only thing the tombstone carries; say why with -m"}},
    Done{Unit{}})

# The tombstone: a revision of a newly minted change that states nothing,
# standing where the first of the run stood.
def abandon.real(+st: Bool, +root: String, +fs: List<&2, Full>, +bs: List<&2, Bm.Bookmark>, +id0: String, +only: Bool, w: Maybe<&2, Writing>) -> IO(Unit):
  match w:
    case None{}:
      IO.pure(Unit, Unit{})
    case Some{Writing{+author, +when, +message, +fields}}:
      do IO<Unit>:
        stated.io(Unit, st, reason.r(message))
        run : List<&2, String> <- stated.io(List<&2, String>, st, abandon.plan.r(fs, id0, only))
        +run2 : List<&2, String> = run
        drew : Result<&1, &1, U32 & String, String> <- Store.drawn("12")
        hex : String <- wrote.io(st, drew)
        +change : String = Maybe.default(&2, String, List.get(&2, String, ids.minted(1n, hex), 0n), SNil{})
        +doc : Rev.Rev = Rev.Rev{change, sorted(full.parents(find(fs, id0))), sorted(run2), author, when, None{}, Some{when}, Nil{}, message}
        +text : String = Rev.write(doc)
        +id : String = Sha.digest(Utf8.encode(text))
        steps : List<&2, Step> <- inline.io(st, root, fs, id, doc)
        +steps2 : List<&2, Step> = steps
        +ns : List<&2, Naming.Named> = T.map(~Full, ~Naming.Named, ~(f => full.named(f)), fs)
        +stem : String = Naming.stem(when, message, change, id, ns)
        revision.filed(st, root, stem, text)
        carry.write(st, root, steps2, List.append(&2, Naming.Named, ns, [Naming.Named{when, message, change}]))
        advanced : List<&2, String> <- advance(st, root, change, advancing(parents.changes(fs, run2), bs))
        abandon.said(fields, id, change, run2, advanced, steps2)

def abandon.act(+st: Bool, +root: String, +fs: List<&2, Full>, +bs: List<&2, Bm.Bookmark>, +id: String, +only: Bool, dry: Bool, +f: Bool, +m: Maybe<&2, String>) -> IO(Unit):
  match dry:
    case True{}:
      do IO<Unit>:
        run : List<&2, String> <- stated.io(List<&2, String>, st, abandon.plan.r(fs, id, only))
        abandon.dry(fs, bs, id, only, run)
    case False{}:
      do IO<Unit>:
        w : Maybe<&2, Writing> <- record.writing(st, fs, False{}, f, m)
        abandon.real(st, root, fs, bs, id, only, w)

def abandon.go(+st: Bool, +root: String, c: RwCmd) -> IO(Unit):
  match c:
    case RwCmd{m, mv, o, Some{+spelling}, +d, +f, +only}:
      do IO<Unit>:
        opened.stated(st, root)
        rs : List<&2, Store.Doc> <- Store.revisions(root)
        bs : List<&2, Bm.Bookmark> <- bookmarks(root)
        +fs : List<&2, Full> = fulls(root, rs)
        +bs2 : List<&2, Bm.Bookmark> = bs
        target : Full <- stated.io(Full, st, resolved.r(fs, bs2, spelling))
        +id : String = id_of(target)
        abandon.act(st, root, fs, bs2, id, only, d, f, m)
    case RwCmd{m, mv, o, None{}, d, f, y}:
      die(Unit, 2, "`abandon` wants the revision to abandon; it and everything standing on it go")

def abandon.named.r(n: Maybe<&2, String>) -> Result<&2, &2, Refused, Unit>:
  match n:
    case Some{x}:
      Done{Unit{}}
    case None{}:
      Fail{Refused{2, "`abandon` wants the revision to abandon; it and everything standing on it go"}}

# `abandon` is asked for a revision and a reason: where it goes on, a
# target was named, a dry run did not also ask for `--fields`, and the
# reason given is not blank. `LAWS.abandon_asks_for_a_revision_and_a_reason`.
def abandon.asked(c: RwCmd, +m: String) -> Bool:
  match c:
    case RwCmd{mg, mv, o, n, d, f, y}:
      Bool.and(Maybe.is_some(&2, String, n), Bool.and(Bool.not(Bool.and(d, f)), Bool.not(String.is_empty(Naming.trim_space(m)))))

def rw.named(c: RwCmd) -> Maybe<&2, String>:
  match c:
    case RwCmd{m, mv, o, n, d, f, y}:
      n

def rw.dry_of(c: RwCmd) -> Bool:
  match c:
    case RwCmd{m, mv, o, n, d, f, y}:
      d

def rw.fields_of(c: RwCmd) -> Bool:
  match c:
    case RwCmd{m, mv, o, n, d, f, y}:
      f

# `abandon <target> [-m <message>] [--only] [--dry-run] [--fields]`.
def abandon(+args: List<&2, String>) -> IO(Unit):
  +st = Rev.member(args, "--fields")
  do IO<Unit>:
    found : Result<&1, &1, U32 & String, String> <- Store.root.found()
    root : String <- record.root(st, found)
    +r : String = root
    c : RwCmd <- refused.io(RwCmd, rw.args.r("abandon", args))
    +c2 : RwCmd = c
    refused.io(Unit, abandon.named.r(rw.named(c2)))
    refused.io(Unit, rw.plan.r("abandon", rw.dry_of(c2), rw.fields_of(c2)))
    abandon.go(st, r, c2)

# amend
# -----

def amend.head.r(+fs: List<&2, Full>, h: Maybe<&2, String>) -> Result<&2, &2, Refused, Full>:
  match h:
    case None{}:
      Fail{Refused{1, "this store holds no revisions yet, so there is nothing to rewrite"}}
    case Some{+id}:
      resolved.found.r(id, find(fs, id))

# The revision named, or the one head there is.
def amend.target.r(+fs: List<&2, Full>, +bs: List<&2, Bm.Bookmark>, named: Maybe<&2, String>) -> Result<&2, &2, Refused, Full>:
  match named:
    case Some{+s}:
      resolved.r(fs, bs, s)
    case None{}:
      do Result<&2, &2, Refused, Full>:
        h : Maybe<&2, String> <- the_head.r(fs, bs, current_heads(history(fs)))
        amend.head.r(fs, h)

# Who is rewriting and when, asked as `record` asks them.
def amend.writing(+st: Bool, +fs: List<&2, Full>) -> IO(T.Split):
  do IO<T.Split>:
    author : String <- author.io(st)
    now : Result<&1, &1, U32 & String, String> <- Store.clock(SNil{})
    when : String <- stated.io(String, st, when.r(now))
    +when2 : String = when
    clock.warned(when2, Naming.newest(whens(by_head(T.map(~Full, ~T.Split, ~(f => full.dated(f)), fs))), None{}))
    return T.Split{author, when2}

def amend.act.io(+st: Bool, +fs: List<&2, Full>, +prev: Full, +m: Maybe<&2, String>, +f: Bool, planning: Bool) -> IO(Act):
  match planning:
    case True{}:
      IO.pure(Act, Act.Amend{prev, SNil{}, SNil{}, m, f, True{}})
    case False{}:
      do IO<Act>:
        w : T.Split <- amend.writing(st, fs)
        +w2 : T.Split = w
        return Act.Amend{prev, split.head(w2), split.rest(w2), m, f, False{}}

# An amendment of a revision nothing stands on: the folder surveyed against
# its parents, the renames it stated inherited as `--at`, the kinds of what
# it added kept, and the identifiers it minted reused.
def amend.folder(+st: Bool, +root: String, +fs: List<&2, Full>, +bs: List<&2, Bm.Bookmark>, +prev: Full, +moves: List<&2, T.Split>, +m: Maybe<&2, String>, +d: Bool, +f: Bool) -> IO(Unit):
  +repo = repository(root)
  +ps = sorted(parents_of(prev))
  +facts = facts_of(prev)
  do IO<Unit>:
    perform(st, repo, moves)
    rules : List<&2, Folder.Scope> <- Folder.rules(root)
    +rs : List<&2, Folder.Scope> = rules
    w : Folder.Walked <- Folder.walk.all(repo, rs)
    +w2 : Folder.Walked = w
    act : Act <- amend.act.io(st, fs, prev, m, f, d)
    stated.io(Unit, st, already.r(fs, id_of(prev)))
    mt : Tree.Merged <- stated.io(Tree.Merged, st, status.tree.r(fs, ps))
    +t0 : Tree.Tree() = Tree.merged_tree(mt)
    p : Placed <- stated.io(Placed, st, placed.r(t0, facts.keyed(facts, "move"), moves))
    record.surveyed(st, root, repo, fs, bs, ps, rs, Folder.walked.found(w2), Folder.walked.refused(w2), t0, p, Nil{}, kinds.prev(facts.keyed(facts, "add"), heads_of(facts.keyed(facts, "bytes"))), Nil{}, act)

def some_lines(+standing: List<&2, String>) -> String:
  +n = List.length(&2, String, standing)
  Bool.pick(String, Nat.is_eq(n, 1n), "some", Nat.show(n) ++ " lines of")

def reword.message.r(+id: String, +standing: List<&2, String>, m: Maybe<&2, String>) -> Result<&2, &2, Refused, String>:
  match m:
    case Some{x}:
      Done{x}
    case None{}:
      Fail{Refused{1, some_lines(standing) ++ " work stands on " ++ ab12(id) ++ ", so the folder cannot say what it holds and the act available is a reword: give -m to fix its message alone, which keeps every other fact it states:" ++ listed12(standing)}}

# Decision 0059's reword: the message alone, every other fact kept.
def reword.r(+fs: List<&2, Full>, prev: Full, +standing: List<&2, String>, +m: Maybe<&2, String>, +reviser: String, +revised: String) -> Result<&2, &2, Refused, Rev.Rev>:
  match prev:
    case Full{+id, +change, +parents, ss, +author, +when, rb, rv, +facts, message}:
      do Result<&2, &2, Refused, Rev.Rev>:
        a : Unit <- already.r(fs, id)
        msg : String <- reword.message.r(id, standing, m)
        +doc : Rev.Rev = Rev.Rev{change, parents, [id], author, when, revised_by(reviser, author), Some{revised}, facts, msg}
        s : Unit <- same.r(id, Rev.Rev{change, parents, ss, author, when, rb, rv, facts, message}, doc)
        return doc

# A reword changes the message alone: the message is the one `-m` gave and
# not the one the revision had, the reword supersedes that revision alone,
# and with the old message put back it says exactly what that revision
# said, as `bare` compares two revisions. `LAWS.reword_changes_only_the_message`.
def reword.ok(prev: Full, m: Maybe<&2, String>, doc: Rev.Rev) -> Bool:
  match prev doc:
    case Full{+id, change, parents, ss, author, when, rb, rv, facts, +message} Rev.Rev{c2, p2, +ss2, a2, w2, rb2, rv2, f2, +msg2}:
      Bool.and(Rev.maybe_eq(m, msg2), Bool.and(Bool.not(String.eq(msg2, message)), Bool.and(only.one(ss2, id),
        String.eq(bare(Rev.Rev{c2, p2, ss2, a2, w2, rb2, rv2, f2, message}), bare(Rev.Rev{change, parents, ss, author, when, rb, rv, facts, message})))))

def reword.go(+st: Bool, +root: String, +fs: List<&2, Full>, +prev: Full, +standing: List<&2, String>, +m: Maybe<&2, String>, planning: Bool, +f: Bool) -> IO(Unit):
  match planning:
    case True{}:
      do IO<Unit>:
        doc : Rev.Rev <- stated.io(Rev.Rev, st, reword.r(fs, prev, standing, m, SNil{}, SNil{}))
        amend.said(False{}, True{}, Nil{}, id_of(prev), change_of(prev), SNil{}, would_carry(fs, id_of(prev), standing), Nil{})
    case False{}:
      do IO<Unit>:
        w : T.Split <- amend.writing(st, fs)
        +w2 : T.Split = w
        doc : Rev.Rev <- stated.io(Rev.Rev, st, reword.r(fs, prev, standing, m, split.head(w2), split.rest(w2)))
        +doc2 : Rev.Rev = doc
        +id : String = Sha.digest(Utf8.encode(Rev.write(doc2)))
        steps : List<&2, Step> <- inline.io(st, root, fs, id, doc2)
        +steps2 : List<&2, Step> = steps
        amend.written(st, False{}, root, repository(root), fs, Nil{}, id, doc2, steps2)
        amend.said(f, False{}, Nil{}, id_of(prev), change_of(prev), id, Nil{}, steps2)

def amend.act(+st: Bool, +root: String, +fs: List<&2, Full>, +bs: List<&2, Bm.Bookmark>, +prev: Full, +standing: List<&2, String>, +moves: List<&2, T.Split>, +m: Maybe<&2, String>, +d: Bool, +f: Bool, fresh: Bool) -> IO(Unit):
  match fresh:
    case True{}:
      amend.folder(st, root, fs, bs, prev, moves, m, d, f)
    case False{}:
      do IO<Unit>:
        stated.io(Unit, st, Bool.pick(Result<&2, &2, Refused, Unit>, List.is_empty(&2, T.Split, moves), Done{Unit{}},
          Fail{Refused{1, "work stands on " ++ ab12(id_of(prev)) ++ ", so rewriting it is a reword and `--move` is not something a message can say"}}))
        reword.go(st, root, fs, prev, standing, m, d, f)

def amend.go(+st: Bool, +root: String, c: RwCmd) -> IO(Unit):
  match c:
    case RwCmd{+m, +moves, o, named, +d, +f, y}:
      do IO<Unit>:
        opened.stated(st, root)
        rs : List<&2, Store.Doc> <- Store.revisions(root)
        bs : List<&2, Bm.Bookmark> <- bookmarks(root)
        +fs : List<&2, Full> = fulls(root, rs)
        +bs2 : List<&2, Bm.Bookmark> = bs
        prev : Full <- stated.io(Full, st, amend.target.r(fs, bs2, named))
        +prev2 : Full = prev
        +standing : List<&2, String> = standing_on(fs, id_of(prev2))
        amend.act(st, root, fs, bs2, prev2, standing, moves, m, d, f, List.is_empty(&2, String, standing))

# `amend [<target>] [-m <message>] [--move <old>=<new>] [--dry-run] [--fields]`.
def amend(+args: List<&2, String>) -> IO(Unit):
  +st = Rev.member(args, "--fields")
  do IO<Unit>:
    found : Result<&1, &1, U32 & String, String> <- Store.root.found()
    root : String <- record.root(st, found)
    +r : String = root
    c : RwCmd <- refused.io(RwCmd, rw.args.r("amend", args))
    +c2 : RwCmd = c
    refused.io(Unit, rw.plan.r("amend", rw.dry_of(c2), rw.fields_of(c2)))
    amend.go(st, r, c2)

# carry
# -----

def step.line(+dry: Bool, s: Step) -> String:
  match s:
    case Step{p, id, o, d, r, w, m}:
      Bool.pick(String, dry, "would carry ", "carried ") ++ ab12(p) ++ " as " ++ ab12(id) ++ ", onto " ++ String.join(map12(o), " and ")

def steps.said(+dry: Bool, steps: List<&2, Step>) -> List<&2, String>:
  match steps:
    case Nil{}:
      Nil{}
    case +s <> rest:
      match s:
        case Step{p, id, o, d, +r, w, m}:
          List.append(&2, String, step.line(dry, Step{p, id, o, d, r, w, m}) <> said.lines("  restated ", SNil{}, r), steps.said(dry, rest))

def steps.restated(steps: List<&2, Step>) -> Bool:
  match steps:
    case Nil{}:
      False{}
    case Step{p, id, o, d, r, w, m} <> rest:
      Bool.or(Bool.not(List.is_empty(&2, String, r)), steps.restated(rest))

# What carrying says it did or would do: for a machine, decision 0074's
# header and each revision written; for a person, each step and what it
# restated, and what is left for `prune` and `update`.
def carry.said.lines(+fields: Bool, +dry: Bool, +steps: List<&2, Step>) -> List<&2, String>:
  Bool.pick(List<&2, String>, fields,
    WROTE() <> said.lines("revision ", SNil{}, sorted_distinct(carried.ids(steps))),
  Bool.pick(List<&2, String>, List.is_empty(&2, Step, steps),
    ["nothing stands on a rewritten revision; there is nothing to carry"],
    List.concat(&2, String, [steps.said(dry, steps),
      Bool.pick(List<&2, String>, dry, Nil{}, ["what was carried is still here, superseded; `historica prune` is what removes it"]),
      Bool.pick(List<&2, String>, Bool.and(Bool.not(dry), steps.restated(steps)), ["the folder is unchanged; `historica update` makes it hold the carried head"], Nil{})])))

def carry.said(+fields: Bool, +dry: Bool, +steps: List<&2, Step>) -> IO(Unit):
  print_lines(carry.said.lines(fields, dry, steps))

# What `--fields` says of the revisions an act wrote, as decision 0074 has
# it: `historica-wrote-1` first, and each revision written named once, in
# digest order, by a `revision` line. `LAWS.writes_say_what_they_wrote`.
def fields.revision(r: Maybe<&2, String>, later: List<&2, String>) -> List<&2, String>:
  match r:
    case Some{x}:
      x <> later
    case None{}:
      later

def fields.revisions(ls: List<&2, String>) -> List<&2, String>:
  match ls:
    case Nil{}:
      Nil{}
    case +l <> rest:
      fields.revision(T.strip_prefix(l, "revision "), fields.revisions(rest))

def rising.from(xs: List<&2, String>, +last: String) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case +x <> rest:
      Bool.and(Bool.and(String.is_le(last, x), Bool.not(String.eq(last, x))), rising.from(rest, x))

def rising(xs: List<&2, String>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case +x <> rest:
      rising.from(rest, x)

def fields.ok(+written: List<&2, String>, ls: List<&2, String>) -> Bool:
  match ls:
    case Nil{}:
      False{}
    case +l <> +rest:
      Bool.and(String.eq(l, WROTE()), Bool.and(rising(fields.revisions(rest)), all_held(written, fields.revisions(rest))))

def carry.target.r(+fs: List<&2, Full>, +bs: List<&2, Bm.Bookmark>, named: Maybe<&2, String>) -> Result<&2, &2, Refused, Maybe<&2, String>>:
  match named:
    case None{}:
      Done{None{}}
    case Some{+s}:
      Result.map(&2, &2, Refused, Full, Maybe<&2, String>, f => Some{id_of(f)}, resolved.r(fs, bs, s))

# Which carry was asked for. A destination is a person's decision about a
# particular piece of work, so it reads the clock and wants a target.
def carry.asked(+st: Bool, +fs: List<&2, Full>, +bs: List<&2, Bm.Bookmark>, target: Maybe<&2, String>, onto: Maybe<&2, String>) -> IO(Carrying):
  match target onto:
    case Some{+t} Some{+o}:
      do IO<Carrying>:
        dest : Full <- stated.io(Full, st, resolved.r(fs, bs, o))
        +dest2 : Full = dest
        w : T.Split <- amend.writing(st, fs)
        +w2 : T.Split = w
        return Carrying.Onto{t, id_of(dest2), split.rest(w2), split.head(w2)}
    case None{} Some{o}:
      die(Carrying, 2, "`--onto` wants the work to move: `historica carry <target> --onto <destination>`")
    case Some{t} None{}:
      IO.pure(Carrying, Carrying.One{t})
    case None{} None{}:
      IO.pure(Carrying, Carrying.Everything{})

def carry.planned.r(r: Result<&2, &2, String, List<&2, Step>>) -> Result<&2, &2, Refused, List<&2, Step>>:
  match r:
    case Done{s}:
      Done{s}
    case Fail{e}:
      Fail{Refused{1, e}}

def carry.written(+st: Bool, +root: String, +fs: List<&2, Full>, +steps: List<&2, Step>, dry: Bool) -> IO(Unit):
  match dry:
    case True{}:
      IO.pure(Unit, Unit{})
    case False{}:
      carry.write(st, root, steps, T.map(~Full, ~Naming.Named, ~(f => full.named(f)), fs))

def carry.go(+st: Bool, +root: String, c: RwCmd) -> IO(Unit):
  match c:
    case RwCmd{m, mv, onto, named, +d, +f, y}:
      do IO<Unit>:
        opened.stated(st, root)
        rs : List<&2, Store.Doc> <- Store.revisions(root)
        bs : List<&2, Bm.Bookmark> <- bookmarks(root)
        +fs : List<&2, Full> = fulls(root, rs)
        +bs2 : List<&2, Bm.Bookmark> = bs
        target : Maybe<&2, String> <- stated.io(Maybe<&2, String>, st, carry.target.r(fs, bs2, named))
        asked : Carrying <- carry.asked(st, fs, bs2, target, onto)
        +asked2 : Carrying = asked
        ds : List<&2, Store.Doc> <- carry.docs(root, fs)
        steps : List<&2, Step> <- stated.io(List<&2, Step>, st, carry.planned.r(carry.plan(fs, ds, asked2)))
        +steps2 : List<&2, Step> = steps
        carry.written(st, root, fs, steps2, d)
        carry.said(f, d, steps2)

# `carry [<target>] [--onto <destination>] [--dry-run] [--fields]`.
def carry(+args: List<&2, String>) -> IO(Unit):
  +st = Rev.member(args, "--fields")
  do IO<Unit>:
    found : Result<&1, &1, U32 & String, String> <- Store.root.found()
    root : String <- record.root(st, found)
    +r : String = root
    c : RwCmd <- refused.io(RwCmd, rw.args.r("carry", args))
    +c2 : RwCmd = c
    refused.io(Unit, rw.plan.r("carry", rw.dry_of(c2), rw.fields_of(c2)))
    carry.go(st, r, c2)

# name
# ----

# `name <bookmark> <target> [<path>] [--revision|--change]
# [--private|--shared] [--fields]` and `name --delete <bookmark>`, read as
# the Rust tool reads them: every flag wherever it stands, the last of
# `--revision` and `--change` and of `--private` and `--shared` counting,
# and every other word — one starting `-` too — the bookmark, the target
# and the path, in order. What the flags shaping a target were, as typed,
# is kept for `--delete`'s refusal of them.
type NameCmd is Data:
  NameCmd{pin: Bool, axis: Maybe<&2, Bool>, delete: Bool, fields: Bool, shaping: List<&2, String>, rest: List<&2, String>}

type NWord is Data:
  NWord.Revision{}
  NWord.Change{}
  NWord.Private{}
  NWord.Shared{}
  NWord.Delete{}
  NWord.Fields{}
  NWord.Other{}

def nword(+w: String) -> NWord:
  Bool.pick(NWord, String.eq(w, "--revision"), NWord.Revision{},
  Bool.pick(NWord, String.eq(w, "--change"), NWord.Change{},
  Bool.pick(NWord, String.eq(w, "--private"), NWord.Private{},
  Bool.pick(NWord, String.eq(w, "--shared"), NWord.Shared{},
  Bool.pick(NWord, String.eq(w, "--delete"), NWord.Delete{},
  Bool.pick(NWord, String.eq(w, "--fields"), NWord.Fields{}, NWord.Other{}))))))

def name.word(c: NameCmd, k: NWord, w: String) -> NameCmd:
  match c k:
    case NameCmd{p, a, d, f, sh, r} NWord.Revision{}:
      NameCmd{True{}, a, d, f, List.append(&2, String, sh, [w]), r}
    case NameCmd{p, a, d, f, sh, r} NWord.Change{}:
      NameCmd{False{}, a, d, f, List.append(&2, String, sh, [w]), r}
    case NameCmd{p, a, d, f, sh, r} NWord.Private{}:
      NameCmd{p, Some{True{}}, d, f, List.append(&2, String, sh, [w]), r}
    case NameCmd{p, a, d, f, sh, r} NWord.Shared{}:
      NameCmd{p, Some{False{}}, d, f, List.append(&2, String, sh, [w]), r}
    case NameCmd{p, a, d, f, sh, r} NWord.Delete{}:
      NameCmd{p, a, True{}, f, sh, r}
    case NameCmd{p, a, d, f, sh, r} NWord.Fields{}:
      NameCmd{p, a, d, True{}, sh, r}
    case NameCmd{p, a, d, f, sh, r} NWord.Other{}:
      NameCmd{p, a, d, f, sh, List.append(&2, String, r, [w])}

def name.args(ws: List<&2, String>, c: NameCmd) -> NameCmd:
  match ws:
    case Nil{}:
      c
    case +w <> rest:
      name.args(rest, name.word(c, nword(w), w))

# The words read a field at a time, as `LAWS.name_reads_its_words` holds
# `name.args` to: the last of `--revision` and `--change`, the last of
# `--private` and `--shared`, whether `--delete` and `--fields` are there,
# the flags shaping a target in the order typed, and every other word in
# order.
def nargs.pin.of(k: NWord, last: Bool) -> Bool:
  match k:
    case NWord.Revision{}:
      True{}
    case NWord.Change{}:
      False{}
    case _:
      last

def nargs.pin(ws: List<&2, String>, last: Bool) -> Bool:
  match ws:
    case Nil{}:
      last
    case +w <> rest:
      nargs.pin(rest, nargs.pin.of(nword(w), last))

def nargs.axis.of(k: NWord, last: Maybe<&2, Bool>) -> Maybe<&2, Bool>:
  match k:
    case NWord.Private{}:
      Some{True{}}
    case NWord.Shared{}:
      Some{False{}}
    case _:
      last

def nargs.axis(ws: List<&2, String>, last: Maybe<&2, Bool>) -> Maybe<&2, Bool>:
  match ws:
    case Nil{}:
      last
    case +w <> rest:
      nargs.axis(rest, nargs.axis.of(nword(w), last))

def nargs.delete.of(k: NWord, had: Bool) -> Bool:
  match k:
    case NWord.Delete{}:
      True{}
    case _:
      had

def nargs.delete(ws: List<&2, String>, had: Bool) -> Bool:
  match ws:
    case Nil{}:
      had
    case +w <> rest:
      nargs.delete(rest, nargs.delete.of(nword(w), had))

def nargs.fields.of(k: NWord, had: Bool) -> Bool:
  match k:
    case NWord.Fields{}:
      True{}
    case _:
      had

def nargs.fields(ws: List<&2, String>, had: Bool) -> Bool:
  match ws:
    case Nil{}:
      had
    case +w <> rest:
      nargs.fields(rest, nargs.fields.of(nword(w), had))

def nargs.shaping.of(k: NWord, w: String, rest: List<&2, String>) -> List<&2, String>:
  match k:
    case NWord.Revision{}:
      w <> rest
    case NWord.Change{}:
      w <> rest
    case NWord.Private{}:
      w <> rest
    case NWord.Shared{}:
      w <> rest
    case _:
      rest

def nargs.shaping(ws: List<&2, String>) -> List<&2, String>:
  match ws:
    case Nil{}:
      Nil{}
    case +w <> rest:
      nargs.shaping.of(nword(w), w, nargs.shaping(rest))

def nargs.words.of(k: NWord, w: String, rest: List<&2, String>) -> List<&2, String>:
  match k:
    case NWord.Other{}:
      w <> rest
    case _:
      rest

def nargs.words(ws: List<&2, String>) -> List<&2, String>:
  match ws:
    case Nil{}:
      Nil{}
    case +w <> rest:
      nargs.words.of(nword(w), w, nargs.words(rest))

def nargs.said(+ws: List<&2, String>) -> NameCmd:
  NameCmd{nargs.pin(ws, False{}), nargs.axis(ws, None{}), nargs.delete(ws, False{}), nargs.fields(ws, False{}), nargs.shaping(ws), nargs.words(ws)}

# `store::check_name`, and decision 0024's refusal of a name spelled as a
# file identifier, which would stop the identifier naming its own file.
def name_fault(+n: String) -> Maybe<&2, String>:
  Bool.pick(Maybe<&2, String>, String.is_empty(n), Some{"it is empty, and a bookmark with no name is not a bookmark"},
  Bool.pick(Maybe<&2, String>, List.any(~&2, ~Char, ~(c => Char.is_eq(c, '\\')), String.to_list(n)), Some{"it holds a backslash, which is a separator on some machines and a character on others; a bookmark that changed shape when its store was copied would be worse than one refused everywhere"},
    Sv.path_check(n)))

def name.usable.r(+n: String, fault: Maybe<&2, String>) -> Result<&2, &2, Refused, Unit>:
  match fault:
    case Some{because}:
      Fail{Refused{1, "`" ++ n ++ "` cannot be a bookmark: " ++ because}}
    case None{}:
      Done{Unit{}}

def name.checked.r(+n: String) -> Result<&2, &2, Refused, Unit>:
  Bool.pick(Result<&2, &2, Refused, Unit>, Id.is_assigned(n),
    Fail{Refused{1, "`" ++ n ++ "` is spelled as an identifier, and a bookmark that is one would stop that identifier naming its own file; give it a name a person would say"}},
    name.usable.r(n, name_fault(n)))

# Whether a bookmark already here keeps its names out of an export: what a
# bookmark being moved keeps, unless `--private` or `--shared` says.
def private_of(bs: List<&2, Bm.Bookmark>, +n: String) -> Bool:
  match bs:
    case Nil{}:
      False{}
    case Bm.Bookmark{+m, t, p} <> rest:
      Bool.pick(Bool, String.eq(m, n), p, private_of(rest, n))

def found_of(bs: List<&2, Bm.Bookmark>, +n: String) -> Maybe<&2, Bm.Bookmark>:
  match bs:
    case Nil{}:
      None{}
    case +b <> rest:
      Bool.pick(Maybe<&2, Bm.Bookmark>, String.eq(Bm.name_of(b), n), Some{b}, found_of(rest, n))

# What the bookmark will point at: a file where a path is given, resolved
# at the revision named; the revision itself where `--revision` pins it;
# and otherwise its change, which follows amend and rebase.
def name.target.r(+fs: List<&2, Full>, +bs: List<&2, Bm.Bookmark>, +f: Full, path: Maybe<&2, String>, pin: Bool) -> Result<&2, &2, Refused, Bm.Target>:
  match path pin:
    case Some{+p} _:
      Result.map(&2, &2, Refused, String, Bm.Target, file => Bm.Target.File{file}, show.file.r(fs, bs, id_of(f), p))
    case None{} True{}:
      Done{Bm.Target.Revision{id_of(f)}}
    case None{} False{}:
      Done{Bm.Target.Change{change_of(f)}}

def name.resolved.r(+fs: List<&2, Full>, +bs: List<&2, Bm.Bookmark>, +spelling: String) -> Result<&2, &2, Refused, Full>:
  Bool.pick(Result<&2, &2, Refused, Full>, String.is_empty(spelling), Fail{Refused{2, "a target cannot be empty"}}, resolved.r(fs, bs, spelling))

def name.io(r: Result<&1, &1, U32 & String, String>) -> IO(String):
  match r:
    case Fail{Tuple{code, msg}}:
      die(String, 1, msg)
    case Done{answer}:
      IO.pure(String, answer)

# Decision 0074: asked for a statement, `name` leaves one behind even where
# it stops — the header, and the refusal — except for a command line that
# was wrong, which did nothing. `early` is where the header is printed
# before the store is opened, so that a refusal inside opening it has it
# too; it is not, where the line may yet prove wrong (an empty target, or
# `file:` naming nothing), and the header then waits for a refusal the
# Bend side decides.
def name.head(b: Bool) -> List<&2, String>:
  Bool.pick(List<&2, String>, b, [WROTE()], Nil{})

def name.said.lines(+n: String, b: Bm.Bookmark, +fields: Bool, +early: Bool, shared: Bool) -> List<&2, String>:
  match fields:
    case True{}:
      List.append(&2, String, name.head(Bool.not(early)), ["name " ++ n])
    case False{}:
      (n ++ " -> " ++ Bm.show(b)) <> Bool.pick(List<&2, String>, shared, ["note: a replica still calling `" ++ n ++ "` private will make it private again on the next receive"], Nil{})

def name.said(+n: String, b: Bm.Bookmark, +fields: Bool, +early: Bool, shared: Bool) -> IO(Unit):
  print_lines(name.said.lines(n, b, fields, early, shared))

def name.shared(axis: Maybe<&2, Bool>) -> Bool:
  match axis:
    case Some{False{}}:
      True{}
    case _:
      False{}

# The bookmark a set writes, decided before anything is: the target
# resolved and pointed at as asked, the name checked, and whether it is
# private — as asked, or as the bookmark it replaces was. A refusal is the
# first of these to fail, as the Rust tool meets them.
def name.stated.r(+fs: List<&2, Full>, +bs: List<&2, Bm.Bookmark>, +n: String, +spelling: String, path: Maybe<&2, String>, +pin: Bool, +axis: Maybe<&2, Bool>) -> Result<&2, &2, Refused, Bm.Bookmark>:
  do Result<&2, &2, Refused, Bm.Bookmark>:
    f : Full <- name.resolved.r(fs, bs, spelling)
    t : Bm.Target <- name.target.r(fs, bs, f, path, pin)
    u : Unit <- name.checked.r(n)
    return Bm.Bookmark{n, t, Maybe.default(&2, Bool, axis, private_of(bs, n))}

# What its file says: the target line, and `private` where it is.
def name.text(b: Bm.Bookmark) -> String:
  match b:
    case Bm.Bookmark{n, t, p}:
      Bm.write(Bm.Stated{t, p})

def name.set(+n: String, +spelling: String, path: Maybe<&2, String>, +pin: Bool, +axis: Maybe<&2, Bool>, +fields: Bool, +early: Bool) -> IO(Unit):
  +late = Bool.and(fields, Bool.not(early))
  do IO<Unit>:
    print_lines(name.head(early))
    root : String <- Store.root()
    +r : String = root
    rs : List<&2, Store.Doc> <- Store.revisions(r)
    bs : List<&2, Bm.Bookmark> <- bookmarks(r)
    +bs2 : List<&2, Bm.Bookmark> = bs
    +fs : List<&2, Full> = fulls(r, rs)
    b : Bm.Bookmark <- stated.io(Bm.Bookmark, late, name.stated.r(fs, bs2, n, spelling, path, pin, axis))
    +b2 : Bm.Bookmark = b
    w : Result<&1, &1, U32 & String, String> <- Store.written(r ++ "/names/" ++ n ++ ".txt\n" ++ name.text(b2))
    done : String <- name.io(w)
    name.said(n, b2, fields, early, name.shared(axis))

def name.deleted.lines(+n: String, b: Bm.Bookmark, +fields: Bool, +early: Bool) -> List<&2, String>:
  match fields:
    case True{}:
      List.append(&2, String, name.head(Bool.not(early)), ["unname " ++ n])
    case False{}:
      ["deleted " ++ n ++ ", which was " ++ Bm.show(b), "note: a replica that still holds `" ++ n ++ "` will bring it back on the next receive"]

def name.deleted(+n: String, b: Bm.Bookmark, +fields: Bool, +early: Bool) -> IO(Unit):
  print_lines(name.deleted.lines(n, b, fields, early))

def name.present.r(+n: String, found: Maybe<&2, Bm.Bookmark>) -> Result<&2, &2, Refused, Bm.Bookmark>:
  match found:
    case None{}:
      Fail{Refused{1, "there is no bookmark `" ++ n ++ "` here; `names` lists the ones there are"}}
    case Some{b}:
      Done{b}

def name.delete(+n: String, +fields: Bool) -> IO(Unit):
  do IO<Unit>:
    print_lines(name.head(fields))
    root : String <- Store.root()
    +r : String = root
    rs : List<&2, Store.Doc> <- Store.revisions(r)
    bs : List<&2, Bm.Bookmark> <- bookmarks(r)
    +bs2 : List<&2, Bm.Bookmark> = bs
    b : Bm.Bookmark <- stated.io(Bm.Bookmark, False{}, name.present.r(n, found_of(bs2, n)))
    w : Result<&1, &1, U32 & String, String> <- Store.removed(r ++ "/names\n" ++ r ++ "/names/" ++ n ++ ".txt")
    done : String <- name.io(w)
    name.deleted(n, b, fields, fields)

# What a command line asks for, checked before anything is opened: a
# bookmark set, or one deleted — or the refusal a command line that is
# wrong gets, which does nothing.
type NamePlan is Data:
  NamePlan.Set{name: String, target: String, path: Maybe<&2, String>, pin: Bool, axis: Maybe<&2, Bool>, fields: Bool, early: Bool}
  NamePlan.Delete{name: String, fields: Bool}

def name.plan.r(c: NameCmd) -> Result<&2, &2, Refused, NamePlan>:
  match c:
    case NameCmd{pin, axis, True{}, fields, sh <> more, rest}:
      Fail{Refused{2, "`" ++ sh ++ "` shapes what a bookmark points at, and `--delete` is the bookmark going: there is nothing left for it to say"}}
    case NameCmd{pin, axis, True{}, fields, Nil{}, Nil{}}:
      Fail{Refused{2, "`name --delete` wants a bookmark"}}
    case NameCmd{pin, axis, True{}, fields, Nil{}, n <> extra <> more}:
      Fail{Refused{2, "`name --delete` takes one bookmark, and `" ++ extra ++ "` is a second: a deletion names what it is deleting"}}
    case NameCmd{pin, axis, True{}, fields, Nil{}, n <> Nil{}}:
      Done{NamePlan.Delete{n, fields}}
    case NameCmd{pin, axis, False{}, fields, sh, Nil{}}:
      Fail{Refused{2, "`name` wants a bookmark"}}
    case NameCmd{pin, axis, False{}, fields, sh, n <> Nil{}}:
      Fail{Refused{2, "`name` wants a target"}}
    case NameCmd{pin, axis, False{}, fields, sh, n <> t <> p <> extra <> more}:
      Fail{Refused{2, "`name` takes a bookmark, a target, and one path, and `" ++ extra ++ "` is a fourth argument"}}
    case NameCmd{True{}, axis, False{}, fields, sh, n <> t <> p <> Nil{}}:
      Fail{Refused{2, "a file bookmark has nothing to pin: a file identifier is minted once and survives every rename and every amendment, so `--revision` names nothing here"}}
    case NameCmd{False{}, axis, False{}, +fields, sh, n <> +t <> +p <> Nil{}}:
      Done{NamePlan.Set{n, t, Some{p}, False{}, axis, fields, Bool.and(fields, Bool.and(Bool.not(String.is_empty(t)), Bool.not(String.eq(p, "file:"))))}}
    case NameCmd{pin, axis, False{}, +fields, sh, n <> +t <> Nil{}}:
      Done{NamePlan.Set{n, t, None{}, pin, axis, fields, Bool.and(fields, Bool.not(String.is_empty(t)))}}

# What a plan is when it is what the words said, for
# `LAWS.name_does_what_it_reads`: a deletion only where `--delete` was
# said, of the one other word, with nothing shaping a target; a bookmark
# set otherwise, of the other words in order, with the flags as read, never
# a file pinned, and its header early only where `--fields` asked for one.
def nplan.words(xs: List<&2, String>, ys: List<&2, String>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case x <> xr y <> yr:
      Bool.and(String.eq(x, y), nplan.words(xr, yr))
    case _ _:
      False{}

def nplan.same(a: Bool, b: Bool) -> Bool:
  match a b:
    case True{} True{}:
      True{}
    case False{} False{}:
      True{}
    case _ _:
      False{}

def nplan.axis(a: Maybe<&2, Bool>, b: Maybe<&2, Bool>) -> Bool:
  match a b:
    case None{} None{}:
      True{}
    case Some{x} Some{y}:
      nplan.same(x, y)
    case _ _:
      False{}

def nplan.path(path: Maybe<&2, String>) -> List<&2, String>:
  match path:
    case None{}:
      Nil{}
    case Some{p}:
      [p]

def name.plan.meant(c: NameCmd, p: NamePlan) -> Bool:
  match c p:
    case NameCmd{pin, axis, d, f, sh, rest} NamePlan.Delete{n, f2}:
      Bool.and(d, Bool.and(List.is_empty(&2, String, sh), Bool.and(nplan.words(rest, [n]), nplan.same(f, f2))))
    case NameCmd{pin, axis, d, f, sh, rest} NamePlan.Set{n, t, +path, +pin2, axis2, +f2, early}:
      Bool.and(Bool.not(d), Bool.and(nplan.words(rest, n <> t <> nplan.path(path)), Bool.and(nplan.same(pin, pin2), Bool.and(nplan.axis(axis, axis2), Bool.and(nplan.same(f, f2),
        Bool.and(Bool.not(Bool.and(pin2, Maybe.is_some(&2, String, path))), Bool.or(Bool.not(early), f2)))))))

# Where a set points, as `LAWS.name_points_where_asked` holds it: the
# bookmark named as asked, under `names/`; at a revision the store holds
# where `--revision` pins it, at a change one of its revisions carries
# where a target alone is given, and at a file one of its revisions' trees
# holds where a path is; private as `--private` or `--shared` says, or as
# the bookmark of that name already is, or shared where there is none.
def name.somewhere(held: List<&2, String>, +fs: List<&2, Full>, +x: String) -> Bool:
  match held:
    case Nil{}:
      False{}
    case +i <> rest:
      Bool.or(tree.holds.r(tree.r(fs, i), x), name.somewhere(rest, fs, x))

def name.aimed(+fs: List<&2, Full>, path: Maybe<&2, String>, pin: Bool, t: Bm.Target) -> Bool:
  match path pin t:
    case None{} True{} Bm.Target.Revision{id}:
      Rev.member(ids(fs), id)
    case None{} False{} Bm.Target.Change{c}:
      Rev.member(changes(fs), c)
    case Some{p} _ Bm.Target.File{x}:
      name.somewhere(ids(fs), fs, x)
    case _ _ _:
      False{}

def name.kept.of(found: Maybe<&2, Bm.Bookmark>, p: Bool) -> Bool:
  match found:
    case None{}:
      Bool.not(p)
    case Some{b}:
      nplan.same(Bm.private_of(b), p)

def name.kept(bs: List<&2, Bm.Bookmark>, +n: String, axis: Maybe<&2, Bool>, p: Bool) -> Bool:
  match axis:
    case Some{x}:
      nplan.same(x, p)
    case None{}:
      name.kept.of(found_of(bs, n), p)

def name.points(+fs: List<&2, Full>, +bs: List<&2, Bm.Bookmark>, +n: String, path: Maybe<&2, String>, pin: Bool, axis: Maybe<&2, Bool>, b: Bm.Bookmark) -> Bool:
  match b:
    case Bm.Bookmark{+m, t, p}:
      Bool.and(String.eq(m, n), Bool.and(Bool.not(escapes(m)), Bool.and(name.aimed(fs, path, pin, t), name.kept(bs, n, axis, p))))

# What `--delete` finds, as `LAWS.name_deletes_the_bookmark_named` holds
# it: a refusal exactly where the store has no bookmark of that name, and
# otherwise a bookmark the store holds, of that name.
def name.any(bs: List<&2, Bm.Bookmark>, +n: String) -> Bool:
  match bs:
    case Nil{}:
      False{}
    case b <> rest:
      Bool.or(String.eq(Bm.name_of(b), n), name.any(rest, n))

def name.same(a: Bm.Bookmark, b: Bm.Bookmark) -> Bool:
  match a b:
    case Bm.Bookmark{m, s, p} Bm.Bookmark{n, t, q}:
      Bool.and(String.eq(m, n), Bool.and(String.eq(Bm.show_target(s), Bm.show_target(t)), nplan.same(p, q)))

def name.holds(bs: List<&2, Bm.Bookmark>, +b: Bm.Bookmark) -> Bool:
  match bs:
    case Nil{}:
      False{}
    case x <> rest:
      Bool.or(name.same(x, b), name.holds(rest, b))

def name.gone(bs: List<&2, Bm.Bookmark>, +n: String, r: Result<&2, &2, Refused, Bm.Bookmark>) -> Bool:
  match r:
    case Fail{e}:
      Bool.not(name.any(bs, n))
    case Done{+b}:
      Bool.and(String.eq(Bm.name_of(b), n), name.holds(bs, b))

def name.planned(p: NamePlan) -> IO(Unit):
  match p:
    case NamePlan.Set{+n, +t, path, +pin, +axis, +fields, +early}:
      name.set(n, t, path, pin, axis, fields, early)
    case NamePlan.Delete{+n, +fields}:
      name.delete(n, fields)

def name.of(c: NameCmd) -> IO(Unit):
  do IO<Unit>:
    p : NamePlan <- refused.io(NamePlan, name.plan.r(c))
    name.planned(p)

def name(+args: List<&2, String>) -> IO(Unit):
  name.of(name.args(args, NameCmd{False{}, None{}, False{}, False{}, Nil{}, Nil{}}))

# init
# ----

# `init [<dir>]`: the layout decision 0006 settled on, under `history/` in
# the directory named or this one — made with the parents it lacks — and
# refused where a store is already there. Where it lands is said as the
# path really is.

# `Path::join`: a path that is absolute replaces what it is joined to.
def path_join(+base: String, +p: String) -> String:
  Bool.pick(String, String.starts_with(p, "/"), p,
  Bool.pick(String, Bool.or(String.is_empty(base), String.ends_with(base, "/")), base ++ p, base ++ "/" ++ p))

def init.io(-A: Data, r: Result<&1, &1, U32 & String, A>) -> IO(A):
  match r:
    case Fail{Tuple{code, msg}}:
      die(A, 1, msg)
    case Done{x}:
      IO.pure(A, x)

def init.fresh(+root: String, r: Result<&1, &1, U32 & String, String>) -> IO(Unit):
  match r:
    case Done{there}:
      die(Unit, 1, root ++ " is already a store")
    case Fail{e}:
      IO.pure(Unit, Unit{})

def init.said(+root: String, r: Result<&1, &1, U32 & String, String>) -> String:
  match r:
    case Done{real}:
      real
    case Fail{e}:
      root

def init.write(+path: String, +text: String) -> IO(Unit):
  do IO<Unit>:
    w : Result<&1, &1, U32 & String, String> <- Store.written(path ++ "\n" ++ text)
    done : String <- init.io(String, w)
    IO.pure(Unit, Unit{})

def init.dirs(+root: String, ds: List<&2, String>) -> String:
  match ds:
    case Nil{}:
      SNil{}
    case d <> rest:
      root ++ "/" ++ d ++ "\n" ++ init.dirs(root, rest)

def init.base(+base: String, dir: Maybe<&2, String>) -> String:
  match dir:
    case None{}:
      base
    case Some{+d}:
      path_join(base, d)

def init.at(dir: Maybe<&2, String>) -> IO(Unit):
  do IO<Unit>:
    here : Result<&1, &1, U32 & String, String> <- Store.base()
    base : String <- init.io(String, here)
    +root : String = path_join(init.base(base, dir), "history")
    header : Result<&1, &1, U32 & String, String> <- Store.really(root ++ "/historica.txt")
    init.fresh(root, header)
    m : Result<&1, &1, U32 & String, String> <- Store.made(init.dirs(root, ["revisions", "operations", "names", "cache", "skipped"]))
    done : String <- init.io(String, m)
    init.write(root ++ "/historica.txt", Notes.HEADER_NOTE())
    init.write(root ++ "/skipped/README.txt", Notes.SKIPPED_NOTE())
    init.write(root ++ "/format.txt", Notes.FORMAT_NOTE())
    init.write(root ++ "/cache/README.txt", Notes.CACHE_NOTE())
    real : Result<&1, &1, U32 & String, String> <- Store.really(root)
    IO.print("made a store at " ++ init.said(root, real))

def init(args: List<&2, String>) -> IO(Unit):
  match args:
    case Nil{}:
      init.at(None{})
    case d <> Nil{}:
      init.at(Some{d})
    case d <> extra <> more:
      die(Unit, 2, "`init` takes one directory, and `" ++ extra ++ "` is a second")
