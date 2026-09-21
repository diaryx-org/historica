# The file set at a revision, and what a revision did to it — `tree.rs`.
#
# A revision records what it did to the files — `add`, `move`, `mode`,
# `drop`, `edit`, `bytes`, `link` — and the tree at a revision is what you
# get by replaying those facts from the root, exactly as a file is. Files
# are identified; a path is a fact about a file, which is what keeps a
# rename from breaking the operation chain recorded against it. There are
# no directories: one exists exactly when some file's path names it.
#
# Two halves, as in the crate. `apply` and `replay` do the linear case,
# where a revision either applies to the tree its parent left or the store
# contradicts itself. `merge` does the graph, with decision 0008's rules
# where two branches disagree: a `drop` concurrent with anything that says
# the file matters loses, two concurrent placements resolve to the lower
# digest, two concurrent payloads are refused a winner, and two files
# claiming one path both keep their identities. Every decision made by
# rule rather than by agreement is reported as a `Contest`.

import Base
import ./text.bend as T
import ./revision.bend as Rev

# The model
# ---------

# What a file's entry points at. Fixed when the file is added, so that no
# operation chain can become unreplayable under the identity that names it;
# a file that changed kind is a `drop` and an `add`.
type FileKind is Data:
  Lines{}
  Whole{}
  Link{}

def kind_show(k: FileKind) -> String:
  match k:
    case Lines{}:
      "lines"
    case Whole{}:
      "bytes"
    case Link{}:
      "a link"

def kind_eq(a: FileKind, b: FileKind) -> Bool:
  match a b:
    case Lines{} Lines{}:
      True{}
    case Whole{} Whole{}:
      True{}
    case Link{} Link{}:
      True{}
    case _ _:
      False{}

# Whether a file can be run. Unlike the kind, a mode changes: `chmod +x` is
# a thing people do to files they already have. A file no `mode` line ever
# named is plain.
type Mode is Data:
  Plain{}
  Executable{}

def mode_of(s: String) -> Mode:
  match s:
    case "executable":
      Executable{}
    case _:
      Plain{}

def mode_show(m: Mode) -> String:
  match m:
    case Plain{}:
      "plain"
    case Executable{}:
      "executable"

def mode_eq(a: Mode, b: Mode) -> Bool:
  match a b:
    case Plain{} Plain{}:
      True{}
    case Executable{} Executable{}:
      True{}
    case _ _:
      False{}

# What a link points at: a file in this history, whatever path it is at
# now, or a string exactly as the folder holds it.
type Target is Data:
  Reference{file: String}
  Verbatim{text: String}

def target_of.of(s: String, named: Maybe<&2, String>) -> Target:
  match named:
    case None{}:
      Verbatim{s}
    case Some{file}:
      Reference{file}

def target_of(+s: String) -> Target:
  target_of.of(s, T.strip_prefix(s, "file:"))

def target_show(t: Target) -> String:
  match t:
    case Reference{file}:
      "file:" ++ file
    case Verbatim{text}:
      text

def reference(t: Maybe<&2, Target>) -> Maybe<&2, String>:
  match t:
    case Some{Reference{file}}:
      Some{file}
    case _:
      None{}

# One file's entry: where it sits, and what its content is.
type Entry is Data:
  Entry{file: String, path: String, kind: FileKind, payload: Maybe<&2, String>, target: Maybe<&2, Target>, mode: Mode}

def entry_file(e: Entry) -> String:
  match e:
    case Entry{f, p, k, y, g, m}:
      f

def entry_path(e: Entry) -> String:
  match e:
    case Entry{f, p, k, y, g, m}:
      p

def entry_kind(e: Entry) -> FileKind:
  match e:
    case Entry{f, p, k, y, g, m}:
      k

def entry_payload(e: Entry) -> Maybe<&2, String>:
  match e:
    case Entry{f, p, k, y, g, m}:
      y

def entry_target(e: Entry) -> Maybe<&2, Target>:
  match e:
    case Entry{f, p, k, y, g, m}:
      g

def entry_mode(e: Entry) -> Mode:
  match e:
    case Entry{f, p, k, y, g, m}:
      m

def maybe_str_eq(a: Maybe<&2, String>, b: Maybe<&2, String>) -> Bool:
  match a b:
    case None{} None{}:
      True{}
    case Some{x} Some{y}:
      String.eq(x, y)
    case _ _:
      False{}

def target_eq(a: Target, b: Target) -> Bool:
  match a b:
    case Reference{x} Reference{y}:
      String.eq(x, y)
    case Verbatim{x} Verbatim{y}:
      String.eq(x, y)
    case _ _:
      False{}

def maybe_target_eq(a: Maybe<&2, Target>, b: Maybe<&2, Target>) -> Bool:
  match a b:
    case None{} None{}:
      True{}
    case Some{x} Some{y}:
      target_eq(x, y)
    case _ _:
      False{}

def entry_target_of(found: Maybe<&2, Entry>) -> Maybe<&2, Target>:
  match found:
    case None{}:
      None{}
    case Some{e}:
      entry_target(e)

def entry_eq(a: Entry, b: Entry) -> Bool:
  match a b:
    case Entry{f1, p1, k1, y1, t1, m1} Entry{f2, p2, k2, y2, t2, m2}:
      Bool.and(Bool.and(String.eq(f1, f2), String.eq(p1, p2)), Bool.and(Bool.and(kind_eq(k1, k2), maybe_str_eq(y1, y2)), Bool.and(maybe_target_eq(t1, t2), mode_eq(m1, m2))))

# List.filter for one element, decided by the caller.
def keep(~A: Data, b: Bool, x: A, rest: List<&2, A>) -> List<&2, A>:
  match b:
    case True{}:
      x <> rest
    case False{}:
      rest

def union_ids(xs: List<&2, String>, +ys: List<&2, String>) -> List<&2, String>:
  List.append(&2, String, Rev.without(xs, ys), ys)

def sorted_ids(xs: List<&2, String>) -> List<&2, String>:
  List.sort(~String, ~(a => b => String.is_le(a, b)), xs)

# The kind a file had, if it is still here: what a revision may leave a
# file's kind as.
def kind_kept(k: FileKind, m: Maybe<&2, FileKind>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{k2}:
      kind_eq(k, k2)

# The tree: the files that exist at one revision, in file order — the order
# a revision document writes them, and the one the crate's map iterates.
def Tree() -> Data:
  List<&2, Entry>

def empty() -> Tree():
  Nil{}

def lookup(t: Tree(), +file: String) -> Maybe<&2, Entry>:
  match t:
    case Nil{}:
      None{}
    case Entry{+f, p, k, y, g, m} <> rest:
      Bool.pick(Maybe<&2, Entry>, String.eq(f, file), Some{Entry{f, p, k, y, g, m}}, lookup(rest, file))

def holds(t: Tree(), +file: String) -> Bool:
  Maybe.is_some(&2, Entry, lookup(t, file))

def path(t: Tree(), +file: String) -> Maybe<&2, String>:
  Maybe.map(&2, Entry, String, e => entry_path(e), lookup(t, file))

def kind(t: Tree(), +file: String) -> Maybe<&2, FileKind>:
  Maybe.map(&2, Entry, FileKind, e => entry_kind(e), lookup(t, file))

def mode(t: Tree(), +file: String) -> Maybe<&2, Mode>:
  Maybe.map(&2, Entry, Mode, e => entry_mode(e), lookup(t, file))

# The files at a path: a list, because a merge can legitimately put two
# there. A tree replayed along one line of history never has more than one.
def at(t: Tree(), +p: String) -> List<&2, String>:
  match t:
    case Nil{}:
      Nil{}
    case Entry{f, +q, k, y, g, m} <> rest:
      Rev.keep(String.eq(q, p), f, at(rest, p))

# At most one: what one line of history leaves at any path.
def at_most_one(xs: List<&2, String>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case x <> Nil{}:
      True{}
    case _:
      False{}

def files(t: Tree()) -> List<&2, String>:
  match t:
    case Nil{}:
      Nil{}
    case Entry{f, p, k, y, g, m} <> rest:
      f <> files(rest)

def size(t: Tree()) -> Nat:
  List.length(&2, Entry, t)

# Insert in file order, replacing an entry the file already has. The
# comparison is a parameter of the step so that a proof can split on it.
def insert.at(c: Cmp, e: Entry, first: Entry, rest: Tree(), deeper: Tree()) -> Tree():
  match c:
    case LT{}:
      e <> first <> rest
    case EQ{}:
      e <> rest
    case GT{}:
      first <> deeper

def insert(t: Tree(), +e: Entry) -> Tree():
  match t:
    case Nil{}:
      [e]
    case +first <> +rest:
      insert.at(String.order(entry_file(e), entry_file(first)), e, first, rest, insert(rest, e))

def remove(t: Tree(), +file: String) -> Tree():
  match t:
    case Nil{}:
      Nil{}
    case Entry{+f, p, k, y, g, m} <> rest:
      keep(~Entry, Bool.not(String.eq(f, file)), Entry{f, p, k, y, g, m}, remove(rest, file))

def with_path(e: Entry, p: String) -> Entry:
  match e:
    case Entry{f, old, k, y, g, m}:
      Entry{f, p, k, y, g, m}

def with_mode(e: Entry, m: Mode) -> Entry:
  match e:
    case Entry{f, p, k, y, g, old}:
      Entry{f, p, k, y, g, m}

def with_target(e: Entry, g: Target) -> Entry:
  match e:
    case Entry{f, p, k, y, old, m}:
      Entry{f, p, k, y, Some{g}, m}

def with_payload(e: Entry, y: String) -> Entry:
  match e:
    case Entry{f, p, k, old, g, m}:
      Entry{f, p, k, Some{y}, g, m}

# Why a revision could not be applied to the file set it names. None of
# these mean the model failed: the store contradicts itself.
type Fault is Data:
  AddedTwice{file: String}
  WrongKind{key: String, file: String, held: FileKind}
  Unknown{key: String, file: String}
  Undelivered{parent: String, named_by: String}
  Cyclic{}
  Dangling{link: String, target: String}
  PathTaken{path: String, file: String, other: String}

def fault_show(e: Fault) -> String:
  match e:
    case AddedTwice{file}:
      "the file " ++ file ++ " already exists here and this revision adds it; a file that comes back after being dropped is a new file with a new ID"
    case WrongKind{key, file, held}:
      "`" ++ key ++ "` addresses the file " ++ file ++ " as the kind it is not: it holds " ++ kind_show(held) ++ ", and a file's kind is fixed when it is added; a file whose content model changed is a `drop` and an `add`"
    case Unknown{key, file}:
      "`" ++ key ++ "` names the file " ++ file ++ ", which does not exist at this revision's parent; check that the parents are the ones this revision was recorded against"
    case Undelivered{parent, named_by}:
      named_by ++ " names the parent " ++ parent ++ ", which this store does not hold yet, so what is concurrent with what cannot be decided"
    case Cyclic{}:
      "a parent edge names a descendant, which a digest cannot do"
    case Dangling{link, target}:
      "the link " ++ link ++ " names the file " ++ target ++ ", which this revision does not leave standing; a link to a file that is going away is a link to a string, so restate it as the path it holds on disk"
    case PathTaken{p, file, other}:
      "the files " ++ file ++ " and " ++ other ++ " would both hold `" ++ p ++ "` after this revision; one line of history cannot produce that, so move one of them"

def ensure(ok: Bool, e: Fault) -> Result<&2, &2, Fault, Unit>:
  match ok:
    case True{}:
      Done{Unit{}}
    case False{}:
      Fail{e}

# Facts
# -----

# A fact about one file: the file, and the rest of the header's value —
# a path, a digest, a target, a mode — or nothing, for `drop`.
type Fact is Data:
  Fact{file: String, rest: String}

def fact_of(v: String, cut: Maybe<&2, T.Split>) -> Fact:
  match cut:
    case None{}:
      Fact{v, ""}
    case Some{T.Split{file, rest}}:
      Fact{file, rest}

def facts_of(hs: List<&2, Rev.Header>, +key: String) -> List<&2, Fact>:
  match hs:
    case Nil{}:
      Nil{}
    case Rev.Header{+k, +v} <> rest:
      keep(~Fact, String.eq(k, key), fact_of(v, T.split_once(v)), facts_of(rest, key))

def fact_files(fs: List<&2, Fact>) -> List<&2, String>:
  match fs:
    case Nil{}:
      Nil{}
    case Fact{f, r} <> rest:
      f <> fact_files(rest)

# What one key says about one file, if it says anything.
def stated(fs: List<&2, Fact>, +file: String) -> Maybe<&2, String>:
  match fs:
    case Nil{}:
      None{}
    case Fact{+f, r} <> rest:
      Bool.pick(Maybe<&2, String>, String.eq(f, file), Some{r}, stated(rest, file))

def facts_about(r: Rev.Rev) -> List<&2, Rev.Header>:
  match r:
    case Rev.Rev{change, parents, supersedes, author, when, revised_by, revised, fs, message}:
      fs

def parents_of(r: Rev.Rev) -> List<&2, String>:
  match r:
    case Rev.Rev{change, parents, supersedes, author, when, revised_by, revised, fs, message}:
      parents

# Whether a revision states any fact about one file. Every key a file can
# be stated under is read, `mode`, `link` and a payload included, because
# a revision that only made a file executable is one that did something to
# it.
def touches.of(+fs: List<&2, Rev.Header>, +file: String) -> Bool:
  Bool.or(Bool.or(Bool.or(Rev.member(Rev.files_of(fs, "add"), file), Rev.member(Rev.files_of(fs, "move"), file)), Bool.or(Rev.member(Rev.files_of(fs, "mode"), file), Rev.member(Rev.files_of(fs, "drop"), file))), Bool.or(Bool.or(Rev.member(Rev.files_of(fs, "edit"), file), Rev.member(Rev.files_of(fs, "text"), file)), Bool.or(Rev.member(Rev.files_of(fs, "bytes"), file), Rev.member(Rev.files_of(fs, "link"), file))))

def touches(r: Rev.Rev, +file: String) -> Bool:
  touches.of(facts_about(r), file)

# The operation documents one file accumulates along a chain, oldest first:
# the bridge between the tree, which says which document belongs to which
# file, and the replay, which turns that list into content.
def operations_for.of(d: Maybe<&2, String>, rest: List<&2, String>) -> List<&2, String>:
  match d:
    case None{}:
      rest
    case Some{digest}:
      digest <> rest

def operations_for(rs: List<&2, Rev.Rev>, +file: String) -> List<&2, String>:
  match rs:
    case Nil{}:
      Nil{}
    case r <> rest:
      operations_for.of(stated(facts_of(facts_about(r), "edit"), file), operations_for(rest, file))

# The linear case
# ---------------

# Decision 0017: the kind is decided at the `add` and never again. A file
# added with `bytes` is bytes, one with `link` is a link, and anything else
# is lines, an empty file included.
def kind_of(target: Maybe<&2, Target>, payload: Maybe<&2, String>) -> FileKind:
  match target payload:
    case Some{g} _:
      Link{}
    case None{} Some{y}:
      Whole{}
    case None{} None{}:
      Lines{}

def mode_stated(m: Maybe<&2, String>) -> Mode:
  match m:
    case None{}:
      Plain{}
    case Some{s}:
      mode_of(s)

def add_one(taken: Bool, +file: String, p: String, +target: Maybe<&2, Target>, +payload: Maybe<&2, String>, m: Mode, t: Tree()) -> Result<&2, &2, Fault, Tree()>:
  match taken:
    case True{}:
      Fail{AddedTwice{file}}
    case False{}:
      Done{insert(t, Entry{file, p, kind_of(target, payload), payload, target, m})}

def adds(as: List<&2, Fact>, +bytes: List<&2, Fact>, +links: List<&2, Fact>, +ms: List<&2, Fact>, +t: Tree()) -> Result<&2, &2, Fault, Tree()>:
  match as:
    case Nil{}:
      Done{t}
    case Fact{+file, p} <> rest:
      do Result<&2, &2, Fault, Tree()>:
        t2 : Tree() <- add_one(holds(t, file), file, p, Maybe.map(&2, String, Target, s => target_of(s), stated(links, file)), stated(bytes, file), mode_stated(stated(ms, file)), t)
        adds(rest, bytes, links, ms, t2)

def move_one(found: Maybe<&2, Entry>, file: String, p: String, t: Tree()) -> Result<&2, &2, Fault, Tree()>:
  match found:
    case None{}:
      Fail{Unknown{"move", file}}
    case Some{e}:
      Done{insert(t, with_path(e, p))}

def moves(mvs: List<&2, Fact>, +t: Tree()) -> Result<&2, &2, Fault, Tree()>:
  match mvs:
    case Nil{}:
      Done{t}
    case Fact{+file, p} <> rest:
      do Result<&2, &2, Fault, Tree()>:
        t2 : Tree() <- move_one(lookup(t, file), file, p, t)
        moves(rest, t2)

# Decision 0034: after the move, because a mode is a fact about the file
# rather than about where it sits, and before the drop, because a file
# leaving the file set has no mode to have. A `mode` on a file this
# revision adds was applied with the `add`.
def mode_kind(k: FileKind, e: Entry, file: String, m: String, t: Tree()) -> Result<&2, &2, Fault, Tree()>:
  match k:
    case Link{}:
      Fail{WrongKind{"mode", file, Link{}}}
    case _:
      Done{insert(t, with_mode(e, mode_of(m)))}

def mode_one(fresh: Bool, found: Maybe<&2, Entry>, file: String, m: String, t: Tree()) -> Result<&2, &2, Fault, Tree()>:
  match fresh found:
    case True{} _:
      Done{t}
    case False{} None{}:
      Fail{Unknown{"mode", file}}
    case False{} Some{+e}:
      mode_kind(entry_kind(e), e, file, m, t)

def modes(ms: List<&2, Fact>, +added: List<&2, String>, +t: Tree()) -> Result<&2, &2, Fault, Tree()>:
  match ms:
    case Nil{}:
      Done{t}
    case Fact{+file, m} <> rest:
      do Result<&2, &2, Fault, Tree()>:
        t2 : Tree() <- mode_one(Rev.member(added, file), lookup(t, file), file, m, t)
        modes(rest, added, t2)

# Decision 0040: a retarget, in the same place a restated path is applied
# and for the same reason — the link is the same file it was, pointing
# somewhere else.
def link_kind(k: FileKind, e: Entry, file: String, g: String, t: Tree()) -> Result<&2, &2, Fault, Tree()>:
  match k:
    case Link{}:
      Done{insert(t, with_target(e, target_of(g)))}
    case other:
      Fail{WrongKind{"link", file, other}}

def link_one(fresh: Bool, found: Maybe<&2, Entry>, file: String, g: String, t: Tree()) -> Result<&2, &2, Fault, Tree()>:
  match fresh found:
    case True{} _:
      Done{t}
    case False{} None{}:
      Fail{Unknown{"link", file}}
    case False{} Some{+e}:
      link_kind(entry_kind(e), e, file, g, t)

def links(ls: List<&2, Fact>, +added: List<&2, String>, +t: Tree()) -> Result<&2, &2, Fault, Tree()>:
  match ls:
    case Nil{}:
      Done{t}
    case Fact{+file, g} <> rest:
      do Result<&2, &2, Fault, Tree()>:
        t2 : Tree() <- link_one(Rev.member(added, file), lookup(t, file), file, g, t)
        links(rest, added, t2)

def drop_one(held: Bool, file: String, t: Tree()) -> Result<&2, &2, Fault, Tree()>:
  match held:
    case False{}:
      Fail{Unknown{"drop", file}}
    case True{}:
      Done{remove(t, file)}

def drops(ds: List<&2, String>, +t: Tree()) -> Result<&2, &2, Fault, Tree()>:
  match ds:
    case Nil{}:
      Done{t}
    case +file <> rest:
      do Result<&2, &2, Fault, Tree()>:
        t2 : Tree() <- drop_one(holds(t, file), file, t)
        drops(rest, t2)

# Decision 0040's one cross-file rule: a `file:` link may not be left
# naming a file the tree does not hold. Held to the result rather than to
# each `drop`, so that a revision which drops a link and its target
# together is ordinary.
def dangling_one(named: Maybe<&2, String>, f: String, t: Tree()) -> Result<&2, &2, Fault, Unit>:
  match named:
    case None{}:
      Done{Unit{}}
    case Some{+target}:
      ensure(holds(t, target), Dangling{f, target})

def dangling(es: Tree(), +t: Tree()) -> Result<&2, &2, Fault, Unit>:
  match es:
    case Nil{}:
      Done{Unit{}}
    case Entry{f, p, k, y, g, m} <> rest:
      do Result<&2, &2, Fault, Unit>:
        dangling_one(reference(g), f, t)
        dangling(rest, t)

def edit_kind(k: FileKind, file: String) -> Result<&2, &2, Fault, Unit>:
  match k:
    case Lines{}:
      Done{Unit{}}
    case other:
      Fail{WrongKind{"edit", file, other}}

def edit_one(found: Maybe<&2, Entry>, file: String) -> Result<&2, &2, Fault, Unit>:
  match found:
    case None{}:
      Fail{Unknown{"edit", file}}
    case Some{e}:
      edit_kind(entry_kind(e), file)

def edits(es: List<&2, String>, +t: Tree()) -> Result<&2, &2, Fault, Unit>:
  match es:
    case Nil{}:
      Done{Unit{}}
    case +file <> rest:
      do Result<&2, &2, Fault, Unit>:
        edit_one(lookup(t, file), file)
        edits(rest, t)

def payload_kind(k: FileKind, e: Entry, file: String, y: String, t: Tree()) -> Result<&2, &2, Fault, Tree()>:
  match k:
    case Whole{}:
      Done{insert(t, with_payload(e, y))}
    case other:
      Fail{WrongKind{"bytes", file, other}}

def payload_one(fresh: Bool, found: Maybe<&2, Entry>, file: String, y: String, t: Tree()) -> Result<&2, &2, Fault, Tree()>:
  match fresh found:
    case True{} _:
      Done{t}
    case False{} None{}:
      Fail{Unknown{"bytes", file}}
    case False{} Some{+e}:
      payload_kind(entry_kind(e), e, file, y, t)

def payloads(bs: List<&2, Fact>, +added: List<&2, String>, +t: Tree()) -> Result<&2, &2, Fault, Tree()>:
  match bs:
    case Nil{}:
      Done{t}
    case Fact{+file, y} <> rest:
      do Result<&2, &2, Fault, Tree()>:
        t2 : Tree() <- payload_one(Rev.member(added, file), lookup(t, file), file, y, t)
        payloads(rest, added, t2)

# Two files at one path after the revision. `held` is what has been seen,
# path first, as the crate's map keys it.
def taken_one(other: Maybe<&2, String>, f: String, p: String) -> Result<&2, &2, Fault, Unit>:
  match other:
    case Some{o}:
      Fail{PathTaken{p, f, o}}
    case None{}:
      Done{Unit{}}

def path_taken(es: Tree(), +held: List<&2, Fact>) -> Result<&2, &2, Fault, Unit>:
  match es:
    case Nil{}:
      Done{Unit{}}
    case Entry{+f, +p, k, y, g, m} <> rest:
      do Result<&2, &2, Fault, Unit>:
        taken_one(stated(held, p), f, p)
        path_taken(rest, Fact{p, f} <> held)

# The file set after one revision, given the set at its parent. The moves
# are applied together, so a revision swapping two files' paths is ordinary
# rather than a collision with itself; a dangling reference and a taken
# path are held to the result for the same reason. One def per stage, each
# taking the last stage's result, so that a proof can open them one at a
# time.
def apply.taken(r: Result<&2, &2, Fault, Unit>, t6: Tree()) -> Result<&2, &2, Fault, Tree()>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{u}:
      Done{t6}

def apply.payloads(r: Result<&2, &2, Fault, Tree()>) -> Result<&2, &2, Fault, Tree()>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{+t6}:
      apply.taken(path_taken(t6, Nil{}), t6)

def apply.edits(r: Result<&2, &2, Fault, Unit>, +fs: List<&2, Rev.Header>, +added: List<&2, String>, +t5: Tree()) -> Result<&2, &2, Fault, Tree()>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{u}:
      apply.payloads(payloads(facts_of(fs, "bytes"), added, t5))

def apply.dangling(r: Result<&2, &2, Fault, Unit>, +fs: List<&2, Rev.Header>, +added: List<&2, String>, +t5: Tree()) -> Result<&2, &2, Fault, Tree()>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{u}:
      apply.edits(edits(fact_files(facts_of(fs, "edit")), t5), fs, added, t5)

def apply.drops(r: Result<&2, &2, Fault, Tree()>, +fs: List<&2, Rev.Header>, +added: List<&2, String>) -> Result<&2, &2, Fault, Tree()>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{+t5}:
      apply.dangling(dangling(t5, t5), fs, added, t5)

def apply.links(r: Result<&2, &2, Fault, Tree()>, +fs: List<&2, Rev.Header>, +added: List<&2, String>) -> Result<&2, &2, Fault, Tree()>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{t4}:
      apply.drops(drops(fact_files(facts_of(fs, "drop")), t4), fs, added)

def apply.modes(r: Result<&2, &2, Fault, Tree()>, +fs: List<&2, Rev.Header>, +added: List<&2, String>) -> Result<&2, &2, Fault, Tree()>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{t3}:
      apply.links(links(facts_of(fs, "link"), added, t3), fs, added)

def apply.moves(r: Result<&2, &2, Fault, Tree()>, +fs: List<&2, Rev.Header>, +added: List<&2, String>) -> Result<&2, &2, Fault, Tree()>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{t2}:
      apply.modes(modes(facts_of(fs, "mode"), added, t2), fs, added)

def apply.adds(r: Result<&2, &2, Fault, Tree()>, +fs: List<&2, Rev.Header>, +added: List<&2, String>) -> Result<&2, &2, Fault, Tree()>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{t1}:
      apply.moves(moves(facts_of(fs, "move"), t1), fs, added)

def apply(t: Tree(), r: Rev.Rev) -> Result<&2, &2, Fault, Tree()>:
  match r:
    case Rev.Rev{change, parents, supersedes, author, when, revised_by, revised, +fs, message}:
      apply.adds(adds(facts_of(fs, "add"), facts_of(fs, "bytes"), facts_of(fs, "link"), facts_of(fs, "mode"), t), fs, fact_files(facts_of(fs, "add")))

# Replay a linear chain, oldest first, into the file set it leaves behind.
def replay.go(rs: List<&2, Rev.Rev>, t: Tree()) -> Result<&2, &2, Fault, Tree()>:
  match rs:
    case Nil{}:
      Done{t}
    case r <> rest:
      do Result<&2, &2, Fault, Tree()>:
        t2 : Tree() <- apply(t, r)
        replay.go(rest, t2)

def replay(rs: List<&2, Rev.Rev>) -> Result<&2, &2, Fault, Tree()>:
  replay.go(rs, empty())

# The graph
# ---------

# One revision's contribution to the file set, with its place in the
# graph. A revision that said nothing about the tree still appears, because
# its causal edges are what decide whether anything else is concurrent.
type Ev is Data:
  Ev{id: String, doc: Rev.Rev}

def ev_id(e: Ev) -> String:
  match e:
    case Ev{id, doc}:
      id

def ev_ids(es: List<&2, Ev>) -> List<&2, String>:
  match es:
    case Nil{}:
      Nil{}
    case e <> rest:
      ev_id(e) <> ev_ids(rest)

# Who had seen whom: every revision with its ancestors, itself excluded.
type Seen is Data:
  Seen{id: String, ancestors: List<&2, String>}

def ancestors_of(ss: List<&2, Seen>, +id: String) -> List<&2, String>:
  match ss:
    case Nil{}:
      Nil{}
    case Seen{+i, as} <> rest:
      Bool.pick(List<&2, String>, String.eq(i, id), as, ancestors_of(rest, id))

def is_ancestor(+ss: List<&2, Seen>, +earlier: String, +later: String) -> Bool:
  Rev.member(ancestors_of(ss, later), earlier)

def is_seen(ss: List<&2, Seen>, +id: String) -> Bool:
  match ss:
    case Nil{}:
      False{}
    case Seen{+i, as} <> rest:
      Bool.or(String.eq(i, id), is_seen(rest, id))

def known(+ss: List<&2, Seen>, ps: List<&2, String>) -> Bool:
  match ps:
    case Nil{}:
      True{}
    case p <> rest:
      Bool.and(is_seen(ss, p), known(ss, rest))

# A parent outside the set is one the caller did not supply — a store
# hands over a whole ancestry — so it is undelivered rather than a root.
def delivered_one(missing: List<&2, String>, id: String) -> Result<&2, &2, Fault, Unit>:
  match missing:
    case Nil{}:
      Done{Unit{}}
    case p <> more:
      Fail{Undelivered{p, id}}

def delivered(es: List<&2, Ev>, +ids: List<&2, String>) -> Result<&2, &2, Fault, Unit>:
  match es:
    case Nil{}:
      Done{Unit{}}
    case Ev{id, doc} <> rest:
      do Result<&2, &2, Fault, Unit>:
        delivered_one(Rev.without(parents_of(doc), ids), id)
        delivered(rest, ids)

def ready(es: List<&2, Ev>, +ss: List<&2, Seen>) -> List<&2, Ev>:
  match es:
    case Nil{}:
      Nil{}
    case Ev{id, +doc} <> rest:
      keep(~Ev, known(ss, parents_of(doc)), Ev{id, doc}, ready(rest, ss))

def stuck(es: List<&2, Ev>, +ss: List<&2, Seen>) -> List<&2, Ev>:
  match es:
    case Nil{}:
      Nil{}
    case Ev{id, +doc} <> rest:
      keep(~Ev, Bool.not(known(ss, parents_of(doc))), Ev{id, doc}, stuck(rest, ss))

def closure(ps: List<&2, String>, +ss: List<&2, Seen>) -> List<&2, String>:
  match ps:
    case Nil{}:
      Nil{}
    case +p <> rest:
      union_ids(p <> ancestors_of(ss, p), closure(rest, ss))

def seen.add(rd: List<&2, Ev>, +ss: List<&2, Seen>) -> List<&2, Seen>:
  match rd:
    case Nil{}:
      ss
    case Ev{id, doc} <> more:
      Seen{id, closure(parents_of(doc), ss)} <> seen.add(more, ss)

def seen.done(finished: Bool, ss: List<&2, Seen>) -> Result<&2, &2, Fault, List<&2, Seen>>:
  match finished:
    case True{}:
      Done{ss}
    case False{}:
      Fail{Cyclic{}}

# The ancestor sets, built oldest first: an event whose parents are all
# known takes theirs and them. No progress with events left is a cycle,
# which digests make impossible and the check refuses anyway.
def seen(fuel: Nat, +es: List<&2, Ev>, +ss: List<&2, Seen>) -> Result<&2, &2, Fault, List<&2, Seen>>:
  match fuel:
    case 0n:
      seen.done(List.is_empty(&2, Ev, es), ss)
    case 1n+f:
      +rd = ready(es, ss)
      +rest = stuck(es, ss)
      Bool.pick(Result<&2, &2, Fault, List<&2, Seen>>, List.is_empty(&2, Ev, rd), seen.done(List.is_empty(&2, Ev, rest), ss), seen(f, rest, seen.add(rd, ss)))

# A claim one revision made about a file: a path, a payload, a mode, a
# target.
type Claim is Data:
  Claim{by: String, what: String}

def claim_by(c: Claim) -> String:
  match c:
    case Claim{by, what}:
      by

def claims_what(cs: List<&2, Claim>) -> List<&2, String>:
  match cs:
    case Nil{}:
      Nil{}
    case Claim{by, what} <> rest:
      what <> claims_what(rest)

# What every revision said about one file.
type Facts is Data:
  Facts{file: String, placements: List<&2, Claim>, touched: List<&2, String>, drops: List<&2, String>, added: List<&2, String>, wholes: List<&2, Claim>, modes: List<&2, Claim>, targets: List<&2, Claim>, whole: Bool, link: Bool}

def facts_file(x: Facts) -> String:
  match x:
    case Facts{file, p, t, d, a, w, m, g, wh, ln}:
      file

def fresh_facts(file: String) -> Facts:
  Facts{file, Nil{}, Nil{}, Nil{}, Nil{}, Nil{}, Nil{}, Nil{}, False{}, False{}}

# The facts table, in file order: the entry for a file, made if absent.
def table_get(xs: List<&2, Facts>, +file: String) -> Facts:
  match xs:
    case Nil{}:
      fresh_facts(file)
    case +x <> rest:
      Bool.pick(Facts, String.eq(facts_file(x), file), x, table_get(rest, file))

def table_put(xs: List<&2, Facts>, +x: Facts) -> List<&2, Facts>:
  match xs:
    case Nil{}:
      [x]
    case +y <> +rest:
      +c = String.order(facts_file(x), facts_file(y))
      Bool.pick(List<&2, Facts>, Cmp.is_lt(c), x <> y <> rest, Bool.pick(List<&2, Facts>, Cmp.is_eq(c), x <> rest, y <> table_put(rest, x)))

# Gathering, one key at a time.
def note_add(x: Facts, +by: String, p: String, whole: Bool, link: Bool) -> Facts:
  match x:
    case Facts{file, ps, ts, ds, as, ws, ms, gs, w, l}:
      Facts{file, List.append(&2, Claim, ps, [Claim{by, p}]), List.append(&2, String, ts, [by]), ds, List.append(&2, String, as, [by]), ws, ms, gs, whole, link}

def note_adds(fs: List<&2, Fact>, +by: String, +bytes: List<&2, String>, +links: List<&2, String>, +xs: List<&2, Facts>) -> List<&2, Facts>:
  match fs:
    case Nil{}:
      xs
    case Fact{+file, p} <> rest:
      note_adds(rest, by, bytes, links, table_put(xs, note_add(table_get(xs, file), by, p, Rev.member(bytes, file), Rev.member(links, file))))

def note_move(x: Facts, +by: String, p: String) -> Facts:
  match x:
    case Facts{file, ps, ts, ds, as, ws, ms, gs, w, l}:
      Facts{file, List.append(&2, Claim, ps, [Claim{by, p}]), List.append(&2, String, ts, [by]), ds, as, ws, ms, gs, w, l}

def note_moves(fs: List<&2, Fact>, +by: String, +xs: List<&2, Facts>) -> List<&2, Facts>:
  match fs:
    case Nil{}:
      xs
    case Fact{+file, p} <> rest:
      note_moves(rest, by, table_put(xs, note_move(table_get(xs, file), by, p)))

def note_drop(x: Facts, +by: String) -> Facts:
  match x:
    case Facts{file, ps, ts, ds, as, ws, ms, gs, w, l}:
      Facts{file, ps, ts, List.append(&2, String, ds, [by]), as, ws, ms, gs, w, l}

def note_drops(fs: List<&2, String>, +by: String, +xs: List<&2, Facts>) -> List<&2, Facts>:
  match fs:
    case Nil{}:
      xs
    case +file <> rest:
      note_drops(rest, by, table_put(xs, note_drop(table_get(xs, file), by)))

def note_mode(x: Facts, +by: String, m: String) -> Facts:
  match x:
    case Facts{file, ps, ts, ds, as, ws, ms, gs, w, l}:
      Facts{file, ps, List.append(&2, String, ts, [by]), ds, as, ws, List.append(&2, Claim, ms, [Claim{by, m}]), gs, w, l}

def note_modes(fs: List<&2, Fact>, +by: String, +xs: List<&2, Facts>) -> List<&2, Facts>:
  match fs:
    case Nil{}:
      xs
    case Fact{+file, m} <> rest:
      note_modes(rest, by, table_put(xs, note_mode(table_get(xs, file), by, m)))

def note_touch(x: Facts, +by: String) -> Facts:
  match x:
    case Facts{file, ps, ts, ds, as, ws, ms, gs, w, l}:
      Facts{file, ps, List.append(&2, String, ts, [by]), ds, as, ws, ms, gs, w, l}

def note_edits(fs: List<&2, String>, +by: String, +xs: List<&2, Facts>) -> List<&2, Facts>:
  match fs:
    case Nil{}:
      xs
    case +file <> rest:
      note_edits(rest, by, table_put(xs, note_touch(table_get(xs, file), by)))

def note_whole(x: Facts, +by: String, y: String) -> Facts:
  match x:
    case Facts{file, ps, ts, ds, as, ws, ms, gs, w, l}:
      Facts{file, ps, List.append(&2, String, ts, [by]), ds, as, List.append(&2, Claim, ws, [Claim{by, y}]), ms, gs, w, l}

def note_bytes(fs: List<&2, Fact>, +by: String, +xs: List<&2, Facts>) -> List<&2, Facts>:
  match fs:
    case Nil{}:
      xs
    case Fact{+file, y} <> rest:
      note_bytes(rest, by, table_put(xs, note_whole(table_get(xs, file), by, y)))

def note_target(x: Facts, +by: String, g: String) -> Facts:
  match x:
    case Facts{file, ps, ts, ds, as, ws, ms, gs, w, l}:
      Facts{file, ps, List.append(&2, String, ts, [by]), ds, as, ws, ms, List.append(&2, Claim, gs, [Claim{by, g}]), w, l}

def note_links(fs: List<&2, Fact>, +by: String, +xs: List<&2, Facts>) -> List<&2, Facts>:
  match fs:
    case Nil{}:
      xs
    case Fact{+file, g} <> rest:
      note_links(rest, by, table_put(xs, note_target(table_get(xs, file), by, g)))

def gather.one(+fs: List<&2, Rev.Header>, +by: String, xs: List<&2, Facts>) -> List<&2, Facts>:
  note_links(facts_of(fs, "link"), by, note_bytes(facts_of(fs, "bytes"), by, note_edits(fact_files(facts_of(fs, "edit")), by, note_modes(facts_of(fs, "mode"), by, note_drops(fact_files(facts_of(fs, "drop")), by, note_moves(facts_of(fs, "move"), by, note_adds(facts_of(fs, "add"), by, fact_files(facts_of(fs, "bytes")), fact_files(facts_of(fs, "link")), xs)))))))

def gather(es: List<&2, Ev>, xs: List<&2, Facts>) -> List<&2, Facts>:
  match es:
    case Nil{}:
      xs
    case Ev{by, doc} <> rest:
      gather(rest, gather.one(facts_about(doc), by, xs))

# A tree fact two branches disagreed about, resolved by rule and reported.
type Contest is Data:
  Dropped{file: String, by: List<&2, String>}
  Moved{file: String, paths: List<&2, Claim>}
  Content{file: String, payloads: List<&2, Claim>}
  ModeOf{file: String, modes: List<&2, Claim>}
  TargetOf{file: String, targets: List<&2, Claim>}
  Referenced{file: String, by: List<&2, String>, links: List<&2, String>}
  Path{path: String, files: List<&2, String>}

# The crate's derived order: by variant, then by the file or path, which
# is total here because a file has at most one contest of each kind.
def contest_rank(c: Contest) -> Nat:
  match c:
    case Dropped{f, b}:
      0n
    case Moved{f, p}:
      1n
    case Content{f, p}:
      2n
    case ModeOf{f, m}:
      3n
    case TargetOf{f, t}:
      4n
    case Referenced{f, b, l}:
      5n
    case Path{p, f}:
      6n

def contest_key(c: Contest) -> String:
  match c:
    case Dropped{f, b}:
      f
    case Moved{f, p}:
      f
    case Content{f, p}:
      f
    case ModeOf{f, m}:
      f
    case TargetOf{f, t}:
      f
    case Referenced{f, b, l}:
      f
    case Path{p, f}:
      p

def contest_le.of(c: Cmp, +ka: String, +kb: String) -> Bool:
  match c:
    case LT{}:
      True{}
    case GT{}:
      False{}
    case EQ{}:
      String.is_le(ka, kb)

def contest_le(+a: Contest, +b: Contest) -> Bool:
  contest_le.of(Nat.cmp(contest_rank(a), contest_rank(b)), contest_key(a), contest_key(b))

def contest_show(c: Contest) -> String:
  match c:
    case Dropped{f, b}:
      "dropped " ++ f ++ " by " ++ String.join(b, " ")
    case Moved{f, p}:
      "moved " ++ f ++ " to " ++ String.join(claims_what(p), " ")
    case Content{f, p}:
      "content " ++ f ++ " " ++ String.join(claims_what(p), " ")
    case ModeOf{f, m}:
      "mode " ++ f ++ " " ++ String.join(claims_what(m), " ")
    case TargetOf{f, t}:
      "target " ++ f ++ " " ++ String.join(claims_what(t), " ")
    case Referenced{f, b, l}:
      "referenced " ++ f ++ " by " ++ String.join(b, " ") ++ " from " ++ String.join(l, " ")
    case Path{p, f}:
      "path " ++ p ++ " held by " ++ String.join(f, " ")

# The file set at a set of heads, and where concurrent work met deciding it.
type Merged is Data:
  Merged{tree: Tree(), contested: List<&2, Contest>}

def merged_tree(m: Merged) -> Tree():
  match m:
    case Merged{t, c}:
      t

def merged_contested(m: Merged) -> List<&2, Contest>:
  match m:
    case Merged{t, c}:
      c

# The claims nothing later replaced: those no other claim descends from,
# in digest order. One is the answer; more is a contest.
def replaced(cs: List<&2, Claim>, +by: String, +ss: List<&2, Seen>) -> Bool:
  match cs:
    case Nil{}:
      False{}
    case Claim{+other, what} <> rest:
      Bool.or(Bool.and(Bool.not(String.eq(other, by)), is_ancestor(ss, by, other)), replaced(rest, by, ss))

def latest(cs: List<&2, Claim>, +all: List<&2, Claim>, +ss: List<&2, Seen>) -> List<&2, Claim>:
  match cs:
    case Nil{}:
      Nil{}
    case Claim{+by, what} <> rest:
      keep(~Claim, Bool.not(replaced(all, by, ss)), Claim{by, what}, latest(rest, all, ss))

def sorted_claims(cs: List<&2, Claim>) -> List<&2, Claim>:
  List.sort(~Claim, ~(a => b => String.is_le(claim_by(a), claim_by(b))), cs)

def current(+cs: List<&2, Claim>, +ss: List<&2, Seen>) -> List<&2, Claim>:
  sorted_claims(latest(cs, cs, ss))

# A `drop` wins only where nothing concurrent says the file matters.
def concurrent(ts: List<&2, String>, +drop: String, +ss: List<&2, Seen>) -> Bool:
  match ts:
    case Nil{}:
      False{}
    case +t <> rest:
      Bool.or(Bool.and(Bool.not(String.eq(t, drop)), Bool.not(is_ancestor(ss, t, drop))), concurrent(rest, drop, ss))

# The drops that took the file, and the drops something concurrent beat.
type Drops is Data:
  Drops{gone: List<&2, String>, lost: List<&2, String>}

def sort_drops.put(beaten: Bool, d: String, gone: List<&2, String>, lost: List<&2, String>) -> Drops:
  match beaten:
    case True{}:
      Drops{gone, d <> lost}
    case False{}:
      Drops{d <> gone, lost}

def sort_drops.of(beaten: Bool, d: String, acc: Drops) -> Drops:
  match acc:
    case Drops{gone, lost}:
      sort_drops.put(beaten, d, gone, lost)

def sort_drops(ds: List<&2, String>, +ts: List<&2, String>, +ss: List<&2, Seen>) -> Drops:
  match ds:
    case Nil{}:
      Drops{Nil{}, Nil{}}
    case +d <> rest:
      sort_drops.of(concurrent(ts, d, ss), d, sort_drops(rest, ts, ss))

def kind_flags(link: Bool, whole: Bool) -> FileKind:
  match link whole:
    case True{} _:
      Link{}
    case False{} True{}:
      Whole{}
    case False{} False{}:
      Lines{}

def first_what(cs: List<&2, Claim>, otherwise: String) -> String:
  match cs:
    case Nil{}:
      otherwise
    case Claim{by, what} <> rest:
      what

def first_what_maybe(cs: List<&2, Claim>) -> Maybe<&2, String>:
  match cs:
    case Nil{}:
      None{}
    case Claim{by, what} <> rest:
      Some{what}

# Two concurrent payloads are refused a winner: the file holds none until
# somebody records which.
def one_payload(cs: List<&2, Claim>) -> Maybe<&2, String>:
  match cs:
    case Claim{by, what} <> Nil{}:
      Some{what}
    case _:
      None{}

def several.of(more: Bool, c: Contest) -> List<&2, Contest>:
  match more:
    case True{}:
      [c]
    case False{}:
      Nil{}

def dropped_contest(file: String, lost: List<&2, String>) -> List<&2, Contest>:
  match lost:
    case Nil{}:
      Nil{}
    case l <> ls:
      [Dropped{file, l <> ls}]

def several(+file: String, +placed: List<&2, Claim>, +wholes: List<&2, Claim>, +modes: List<&2, Claim>, +targets: List<&2, Claim>) -> List<&2, Contest>:
  List.append(&2, Contest, several.of(Nat.is_gt(List.length(&2, Claim, placed), 1n), Moved{file, placed}), List.append(&2, Contest, several.of(Nat.is_gt(List.length(&2, Claim, wholes), 1n), Content{file, wholes}), List.append(&2, Contest, several.of(Nat.is_gt(List.length(&2, Claim, modes), 1n), ModeOf{file, modes}), several.of(Nat.is_gt(List.length(&2, Claim, targets), 1n), TargetOf{file, targets}))))

# One file's resolution: its entry, the drops that took it, and what would
# be reported about it, held until the file is known to survive.
type Decided is Data:
  Decided{file: String, entry: Entry, gone: List<&2, String>, contested: List<&2, Contest>}

def decide.of(+file: String, drops: Drops, +placed: List<&2, Claim>, +wholes: List<&2, Claim>, +modes: List<&2, Claim>, +targets: List<&2, Claim>, k: FileKind) -> Decided:
  match drops:
    case Drops{gone, lost}:
      Decided{file, Entry{file, first_what(placed, ""), k, one_payload(wholes), Maybe.map(&2, String, Target, s => target_of(s), first_what_maybe(targets)), mode_stated(first_what_maybe(modes))}, sorted_ids(gone), List.append(&2, Contest, dropped_contest(file, sorted_ids(lost)), several(file, placed, wholes, modes, targets))}

# Every fact about a file is recorded against its `add`, so a file nobody
# added is an ancestor nobody has delivered rather than a disagreement.
def decide.added(as: List<&2, String>, +file: String, +ps: List<&2, Claim>, +ts: List<&2, String>, +ds: List<&2, String>, +ws: List<&2, Claim>, +ms: List<&2, Claim>, +gs: List<&2, Claim>, l: Bool, w: Bool, +ss: List<&2, Seen>) -> Result<&2, &2, Fault, Decided>:
  match as:
    case Nil{}:
      Fail{Unknown{"move", file}}
    case a <> more:
      Done{decide.of(file, sort_drops(ds, ts, ss), current(ps, ss), current(ws, ss), current(ms, ss), current(gs, ss), kind_flags(l, w))}

def decide(x: Facts, +ss: List<&2, Seen>) -> Result<&2, &2, Fault, Decided>:
  match x:
    case Facts{file, ps, ts, ds, as, ws, ms, gs, w, l}:
      decide.added(as, file, ps, ts, ds, ws, ms, gs, l, w, ss)

# Every file decided; the survivors into the tree, the rest buried in case
# a link still names one.
type Placed is Data:
  Placed{tree: Tree(), buried: List<&2, Decided>, contested: List<&2, Contest>}

def place_decided(survives: Bool, file: String, entry: Entry, gone: List<&2, String>, mine: List<&2, Contest>, acc: Placed) -> Placed:
  match survives acc:
    case True{} Placed{t, b, c}:
      Placed{insert(t, entry), b, List.append(&2, Contest, c, mine)}
    case False{} Placed{t, b, c}:
      Placed{t, List.append(&2, Decided, b, [Decided{file, entry, gone, mine}]), c}

def place(d: Decided, acc: Placed) -> Placed:
  match d:
    case Decided{file, entry, +gone, mine}:
      place_decided(List.is_empty(&2, String, gone), file, entry, gone, mine, acc)

def decide_all(xs: List<&2, Facts>, +ss: List<&2, Seen>, acc: Placed) -> Result<&2, &2, Fault, Placed>:
  match xs:
    case Nil{}:
      Done{acc}
    case x <> rest:
      do Result<&2, &2, Fault, Placed>:
        d : Decided <- decide(x, ss)
        decide_all(rest, ss, place(d, acc))

# Decision 0040: destruction yields to reference. A file a `drop` took,
# that a surviving link still names, comes back — and so does whatever that
# file's own target names, which is why this runs to a fixed point.
def naming(t: Tree(), +named: String) -> List<&2, String>:
  match t:
    case Nil{}:
      Nil{}
    case Entry{f, p, k, y, g, m} <> rest:
      Rev.keep(maybe_str_eq(reference(g), Some{named}), f, naming(rest, named))

# The next buried file some surviving link still names — the first in
# file order, as the crate finds it.
def raised(b: List<&2, Decided>, +t: Tree()) -> Maybe<&2, Decided>:
  match b:
    case Nil{}:
      None{}
    case Decided{+file, entry, gone, mine} <> rest:
      Bool.pick(Maybe<&2, Decided>, List.is_empty(&2, String, naming(t, file)), raised(rest, t), Some{Decided{file, entry, gone, mine}})

def unbury(b: List<&2, Decided>, +file: String) -> List<&2, Decided>:
  match b:
    case Nil{}:
      Nil{}
    case Decided{+f, entry, gone, mine} <> rest:
      keep(~Decided, Bool.not(String.eq(f, file)), Decided{f, entry, gone, mine}, unbury(rest, file))

def raise.found(found: Maybe<&2, Decided>, +t: Tree(), b: List<&2, Decided>, c: List<&2, Contest>) -> Placed:
  match found:
    case None{}:
      Placed{t, b, c}
    case Some{Decided{+file, entry, gone, mine}}:
      Placed{insert(t, entry), unbury(b, file), List.append(&2, Contest, c, List.append(&2, Contest, mine, [Referenced{file, gone, naming(t, file)}]))}

def raise.step(acc: Placed) -> Placed:
  match acc:
    case Placed{+t, +b, c}:
      raise.found(raised(b, t), t, b, c)

# One step per event is fuel enough: each raises a file or changes nothing.
def raise(fuel: Nat, acc: Placed) -> Placed:
  match fuel:
    case 0n:
      acc
    case 1n+f:
      raise(f, raise.step(acc))

# Two files at one path is a legitimate state a person resolves, so it is
# reported rather than refused, and neither file is renamed to fit.
def path_contests(t: Tree(), +all: Tree(), +seen_paths: List<&2, String>) -> List<&2, Contest>:
  match t:
    case Nil{}:
      Nil{}
    case Entry{f, +p, k, y, g, m} <> rest:
      +done = Rev.member(seen_paths, p)
      +holders = at(all, p)
      List.append(&2, Contest, several.of(Bool.and(Bool.not(done), Nat.is_gt(List.length(&2, String, holders), 1n)), Path{p, holders}), path_contests(rest, all, Bool.pick(List<&2, String>, done, seen_paths, p <> seen_paths)))

def merge.finish(p: Placed) -> Merged:
  match p:
    case Placed{+t, b, c}:
      Merged{t, List.sort(~Contest, ~(a => b => contest_le(a, b)), List.append(&2, Contest, c, path_contests(t, t, Nil{})))}

# The file set the whole graph leaves behind.
def merge(+es: List<&2, Ev>) -> Result<&2, &2, Fault, Merged>:
  do Result<&2, &2, Fault, Merged>:
    delivered(es, ev_ids(es))
    ss : List<&2, Seen> <- seen(List.length(&2, Ev, es), es, Nil{})
    placed : Placed <- decide_all(gather(es, Nil{}), ss, Placed{empty(), Nil{}, Nil{}})
    return merge.finish(raise(List.length(&2, Ev, es), placed))

def main() -> IO(Unit):
  IO.print("tree")
