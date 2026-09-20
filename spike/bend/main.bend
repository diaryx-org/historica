# historica, in Bend: the readable core of the format, over the store it finds.
#
# The reading commands `historica` has, in the shape it has them: the store is
# the `history` directory here or above, and a target is `head`, a change ID
# or a revision digest, either abbreviated to any unambiguous prefix.
#
#   bend main.bend -- log [<target>]         the history, newest first
#   bend main.bend -- show <target> [<path>] one document as stored
#   bend main.bend -- files <target>         the file set at a revision
#   bend main.bend -- cat <target> <path>    one file's content at a revision
#   bend main.bend -- check                  every document, named by digest
#   bend main.bend -- replay <ops docs..>    the file a chain of documents makes
#   bend main.bend -- diff <parent> <child>  the operation document between two files
#
# Or compile it: `bend main.bend -o main.c`, then link the archive `ffi/`
# builds — `check.py` does both. What `bend main.bend` runs and what the
# binary runs are the same program over two adapters (`store.bend`).
#
# Not here: bookmarks (`names/`), links, and a merge's `keep` resolution,
# which `cat` refuses rather than guesses at.

import Base
import ./text.bend as T
import ./ident.bend as Id
import ./ops.bend as Ops
import ./revision.bend as Rev
import ./store.bend as Store

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

def describe(+id: String, found: Maybe<&2, Full>) -> String:
  match found:
    case None{}:
      "\n  " ++ String.take(id, 12n)
    case Some{Full{i, change, parents, supersedes, author, when, revised_by, revised, facts, message}}:
      "\n  " ++ String.take(id, 12n) ++ "  " ++ change ++ "\n      " ++ author ++ "  " ++ when ++ summary_line(message)

def described(+fs: List<&2, Full>, heads: List<&2, String>) -> String:
  match heads:
    case Nil{}:
      SNil{}
    case +h <> rest:
      describe(h, find(fs, h)) ++ described(fs, rest)

def head_target(+fs: List<&2, Full>, heads: List<&2, String>) -> Result<&2, &2, String, String>:
  match heads:
    case Nil{}:
      Fail{"this store holds no revisions yet"}
    case only <> Nil{}:
      Done{only}
    case +several:
      Fail{"this store has " ++ Nat.show(List.length(&2, String, several)) ++ " heads, so `head` names none of them; name one, or join them with `historica merge`:" ++ described(fs, List.sort(~String, ~(a => b => String.is_le(a, b)), several))}

def resolve.spelled(+fs: List<&2, Full>, +spelling: String, is_head: Bool, hex: Bool, change: Bool) -> Result<&2, &2, String, String>:
  match is_head:
    case True{}:
      head_target(fs, current_heads(history(fs)))
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

# The revision a target names. Bookmarks are not read here, so `head` is
# always the head and a word is a prefix or nothing.
def resolve(fs: List<&2, Full>, +spelling: String) -> Result<&2, &2, String, String>:
  match spelling:
    case SNil{}:
      Fail{"a target cannot be empty"}
    case +s:
      resolve.spelled(fs, s, String.eq(s, "head"), all_chars(~(c => is_hex(c)), s), all_chars(~(c => Id.is_letter(c)), s))

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

def resolved(+fs: List<&2, Full>, +spelling: String) -> IO(Full):
  resolved.of(fs, resolve(fs, spelling))

# log
# ---

# Newest first, and a parent never above its child: of the revisions nothing
# unprinted stands on, the latest by `when`, then by digest.
def is_parent_of_any(fs: List<&2, Full>, +id: String) -> Bool:
  match fs:
    case Nil{}:
      False{}
    case f <> rest:
      Bool.or(Rev.member(parents_of(f), id), is_parent_of_any(rest, id))

def ready(fs: List<&2, Full>, +all: List<&2, Full>) -> List<&2, Full>:
  match fs:
    case Nil{}:
      Nil{}
    case Full{+id, change, parents, supersedes, author, when, revised_by, revised, facts, message} <> rest:
      keep_full(Bool.not(is_parent_of_any(all, id)), Full{id, change, parents, supersedes, author, when, revised_by, revised, facts, message}, ready(rest, all))

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

# The walk: what is still to print, and what has been, newest first.
type Walk is Data:
  Walk{remaining: List<&2, Full>, printed: List<&2, Full>}

def presentation.pick(+remaining: List<&2, Full>, printed: List<&2, Full>, pick: Maybe<&2, Full>) -> Walk:
  match pick:
    case None{}:
      # A cycle cannot happen; if one did, showing the rest beats dropping it.
      Walk{Nil{}, List.append(&2, Full, List.reverse(&2, Full, remaining), printed)}
    case Some{+f}:
      Walk{remove(remaining, id_of(f)), f <> printed}

def presentation.step(w: Walk) -> Walk:
  match w:
    case Walk{+remaining, printed}:
      presentation.pick(remaining, printed, latest(ready(remaining, remaining)))

def presentation.go(fuel: Nat, w: Walk) -> Walk:
  match fuel:
    case 0n:
      w
    case 1n+n:
      presentation.go(n, presentation.step(w))

def presentation.done(w: Walk) -> List<&2, Full>:
  match w:
    case Walk{remaining, printed}:
      List.append(&2, Full, List.reverse(&2, Full, printed), remaining)

def presentation(+fs: List<&2, Full>) -> List<&2, Full>:
  presentation.done(presentation.go(1n+List.length(&2, Full, fs), Walk{fs, Nil{}}))

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

def ancestry(+fs: List<&2, Full>, +id: String) -> List<&2, Full>:
  among(fs, ancestry.seen(ancestry.go(Nat.mul(2n, 1n+List.length(&2, Full, fs)), fs, Reach{[id], Nil{}})))

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

# What a revision says it did to the file set, counted.
def count_facts(facts: List<&2, Rev.Header>, +key: String, +not_added: List<&2, String>, +exclude: Bool) -> Nat:
  match facts:
    case Nil{}:
      0n
    case Rev.Header{+k, +v} <> rest:
      Nat.add(Bool.pick(Nat, Bool.and(String.eq(k, key), Bool.or(Bool.not(exclude), Bool.not(Rev.member(not_added, T.word(v))))), 1n, 0n), count_facts(rest, key, not_added, exclude))

def fact.show(what: String, n: Nat, rest: List<&2, String>) -> List<&2, String>:
  match n:
    case 0n:
      rest
    case 1n+p:
      (what ++ " " ++ Nat.show(1n+p)) <> rest

def tree_facts(+facts: List<&2, Rev.Header>) -> String:
  +added = Rev.files_of(facts, "add")
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

def log.shown(+fs: List<&2, Full>, +shown: List<&2, Full>) -> IO(Unit):
  +h = history(fs)
  print_entries(presentation(shown), ids(fs), changes(fs), Rev.heads(h), Rev.superseded(h), h, True{})

def log.of(+fs: List<&2, Full>, target: Maybe<&2, String>) -> IO(Unit):
  match target:
    case None{}:
      log.shown(fs, fs)
    case Some{t}:
      do IO<Unit>:
        f : Full <- resolved(fs, t)
        log.shown(fs, ancestry(fs, id_of(f)))

def log(target: Maybe<&2, String>) -> IO(Unit):
  do IO<Unit>:
    root : String <- Store.root()
    +r : String = root
    ds : List<&2, Store.Doc> <- Store.documents(r)
    log.of(fulls(r, ds), target)

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

def check_doc.of(+d: Store.Doc, is_rev: Bool, is_ops: Bool) -> String:
  match is_rev:
    case True{}:
      check_rev(Store.id_of(d), Rev.parse(Store.text_of(d)))
    case False{}:
      Bool.pick(String, is_ops, check_ops.of(Store.id_of(d), Ops.parse(Store.text_of(d))), "payload  " ++ String.take(Store.id_of(d), 12n) ++ "  " ++ Nat.show(Store.size_of(d)) ++ " bytes")

def check_doc(+root: String, +d: Store.Doc) -> IO(Unit):
  IO.print(check_doc.of(d, Store.in_revisions(root, Store.path_of(d)), String.ends_with(Store.path_of(d), ".ops.txt")) ++ "  " ++ Store.relative(root, Store.path_of(d)))

def check_docs(+root: String, ds: List<&2, Store.Doc>) -> IO(Unit):
  match ds:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case d <> rest:
      do IO<Unit>:
        check_doc(root, d)
        check_docs(root, rest)

def check() -> IO(Unit):
  do IO<Unit>:
    root : String <- Store.root()
    +r : String = root
    ds : List<&2, Store.Doc> <- Store.documents(r)
    +ds2 : List<&2, Store.Doc> = ds
    check_docs(r, ds2)
    print_missing(Rev.missing_parents(history(fulls(r, ds2))))

# The file set at a revision
# --------------------------

# A file and where it is. What `add` and `move` say, less what `drop` says,
# on top of what the parents held — the union of them, since a file two
# parents both hold is one file.
type Entry is Data:
  Entry{file: String, path: String}

def entry_path(es: List<&2, Entry>, +file: String) -> Maybe<&2, String>:
  match es:
    case Nil{}:
      None{}
    case Entry{+f, p} <> rest:
      Bool.pick(Maybe<&2, String>, String.eq(f, file), Some{p}, entry_path(rest, file))

def entry_file(es: List<&2, Entry>, +path: String) -> Maybe<&2, String>:
  match es:
    case Nil{}:
      None{}
    case Entry{f, +p} <> rest:
      Bool.pick(Maybe<&2, String>, String.eq(p, path), Some{f}, entry_file(rest, path))

def keep_entry(b: Bool, e: Entry, rest: List<&2, Entry>) -> List<&2, Entry>:
  match b:
    case True{}:
      e <> rest
    case False{}:
      rest

def without_file(es: List<&2, Entry>, +file: String) -> List<&2, Entry>:
  match es:
    case Nil{}:
      Nil{}
    case Entry{+f, p} <> rest:
      keep_entry(Bool.not(String.eq(f, file)), Entry{f, p}, without_file(rest, file))

def place(es: List<&2, Entry>, +file: String, path: String) -> List<&2, Entry>:
  Entry{file, path} <> without_file(es, file)

def union(es: List<&2, Entry>, +into: List<&2, Entry>) -> List<&2, Entry>:
  match es:
    case Nil{}:
      into
    case Entry{+f, p} <> rest:
      union(rest, keep_entry(Maybe.is_none(&2, String, entry_path(into, f)), Entry{f, p}, into))

# `add` and `move` place a file; `drop` removes one; every other fact
# leaves the set as it is.
def apply_fact.placed(es: List<&2, Entry>, file: String, path: String, places: Bool) -> List<&2, Entry>:
  match places:
    case True{}:
      place(es, file, path)
    case False{}:
      es

def apply_fact.dropped(es: List<&2, Entry>, file: String, drops: Bool) -> List<&2, Entry>:
  match drops:
    case True{}:
      without_file(es, file)
    case False{}:
      es

def apply_fact.of(es: List<&2, Entry>, +key: String, value: String, cut: Maybe<&2, T.Split>) -> List<&2, Entry>:
  match cut:
    case Some{T.Split{file, path}}:
      apply_fact.placed(es, file, path, Bool.or(String.eq(key, "add"), String.eq(key, "move")))
    case None{}:
      apply_fact.dropped(es, value, String.eq(key, "drop"))

def apply_fact(es: List<&2, Entry>, +key: String, +value: String) -> List<&2, Entry>:
  apply_fact.of(es, key, value, T.split_once(value))

def apply_facts(facts: List<&2, Rev.Header>, es: List<&2, Entry>) -> List<&2, Entry>:
  match facts:
    case Nil{}:
      es
    case Rev.Header{k, v} <> rest:
      apply_facts(rest, apply_fact(es, k, v))

# The file set at every revision, built oldest first so that a parent's is
# there when its child's is wanted. `presentation` is newest first, and a
# parent is never above its child in it, so its reverse is the order.
type Trees is Data:
  Trees{entries: List<&2, Entry>, id: String}

def tree_of(ts: List<&2, Trees>, +id: String) -> List<&2, Entry>:
  match ts:
    case Nil{}:
      Nil{}
    case Trees{es, +i} <> rest:
      Bool.pick(List<&2, Entry>, String.eq(i, id), es, tree_of(rest, id))

def trees.parents(+ts: List<&2, Trees>, ps: List<&2, String>) -> List<&2, Entry>:
  match ps:
    case Nil{}:
      Nil{}
    case p <> rest:
      union(tree_of(ts, p), trees.parents(ts, rest))

def trees.go(oldest_first: List<&2, Full>, +ts: List<&2, Trees>) -> List<&2, Trees>:
  match oldest_first:
    case Nil{}:
      ts
    case Full{id, change, parents, supersedes, author, when, revised_by, revised, facts, message} <> rest:
      trees.go(rest, Trees{apply_facts(facts, trees.parents(ts, parents)), id} <> ts)

def trees(+fs: List<&2, Full>) -> List<&2, Trees>:
  trees.go(List.reverse(&2, Full, presentation(fs)), Nil{})

def tree(+fs: List<&2, Full>, +id: String) -> List<&2, Entry>:
  tree_of(trees(fs), id)

def pad(+s: String, width: Nat) -> String:
  s ++ String.repeat(" ", Nat.sub(width, String.length(s)))

def widest(es: List<&2, Entry>) -> Nat:
  match es:
    case Nil{}:
      0n
    case Entry{f, p} <> rest:
      Nat.max(String.length(p), widest(rest))

def by_path(+a: Entry, +b: Entry) -> Bool:
  match a b:
    case Entry{fa, pa} Entry{fb, pb}:
      String.is_le(pa, pb)

def print_files(es: List<&2, Entry>, +width: Nat) -> IO(Unit):
  match es:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case Entry{f, p} <> rest:
      do IO<Unit>:
        IO.print(pad(p, width) ++ "  " ++ f)
        print_files(rest, width)

def files.of(+es: List<&2, Entry>) -> IO(Unit):
  match es:
    case Nil{}:
      IO.print("no files here")
    case +some:
      print_files(List.sort(~Entry, ~(a => b => by_path(a, b)), some), widest(some))

def files(+target: String) -> IO(Unit):
  do IO<Unit>:
    root : String <- Store.root()
    +r : String = root
    ds : List<&2, Store.Doc> <- Store.documents(r)
    +fs : List<&2, Full> = fulls(r, ds)
    f : Full <- resolved(fs, target)
    files.of(tree(fs, id_of(f)))

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

def file_in.of(+id: String, +path: String, found: Maybe<&2, String>) -> IO(String):
  match found:
    case None{}:
      die(String, 1, String.take(id, 12n) ++ " holds no file at " ++ path ++ "; `historica files " ++ String.take(id, 12n) ++ "` lists what it holds")
    case Some{f}:
      IO.pure(String, f)

def file_in(+id: String, +path: String, es: List<&2, Entry>) -> IO(String):
  file_in.of(id, path, entry_file(es, path))

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
    ds : List<&2, Store.Doc> <- Store.documents(r)
    +ds2 : List<&2, Store.Doc> = ds
    +fs : List<&2, Full> = fulls(r, ds2)
    f : Full <- resolved(fs, target)
    +id : String = id_of(f)
    file : String <- file_in(id, path, tree(fs, id))
    +file2 : String = file
    cat.print(content(fs, ds2, id, file2))

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

def show.of(+fs: List<&2, Full>, +ds: List<&2, Store.Doc>, +f: Full, path: Maybe<&2, String>) -> IO(Unit):
  match path:
    case None{}:
      show.doc(id_of(f), id_of(f), doc_by_id(ds, id_of(f)))
    case Some{+p}:
      do IO<Unit>:
        file : String <- file_in(id_of(f), p, tree(fs, id_of(f)))
        +file2 : String = file
        show.said(id_of(f), file2, ds, said(facts_of(f), file2))

def show(+target: String, path: Maybe<&2, String>) -> IO(Unit):
  do IO<Unit>:
    root : String <- Store.root()
    +r : String = root
    ds : List<&2, Store.Doc> <- Store.documents(r)
    +ds2 : List<&2, Store.Doc> = ds
    +fs : List<&2, Full> = fulls(r, ds2)
    f : Full <- resolved(fs, target)
    show.of(fs, ds2, f, path)

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
  die(Unit, 2, "usage: log [<target>] | show <target> [<path>] | files <target> | cat <target> <path> | check | replay <ops docs..> | diff <parent> <child>")

def dispatch(args: List<&2, String>) -> IO(Unit):
  match args:
    case "log" <> Nil{}:
      log(None{})
    case "log" <> t <> Nil{}:
      log(Some{t})
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
