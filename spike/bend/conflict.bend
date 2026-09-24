# Where concurrent work met in one file, and how a person is shown it:
# `merge.rs`'s contests and `conflict.rs`'s rendering, decision 0012.
#
# Nothing here is recorded and nothing is stored. A conflict is a function
# of the graph: the walk `merge.bend` models reads the file several heads
# leave, and what is read off its finished tree — which runs concurrent
# authors met in — is what the renderer fences, labelling each run with the
# revision that wrote it. `merge` writes the rendering into the folder;
# `status` and `record --merge` find the renderer's lines still standing
# in what a person left; and `record --merge` states what they left as a
# resolution, each surviving item named by the document that minted it.

import Base
import ./text.bend as T
import ./ops.bend as Ops
import ./merge.bend as Merge
import ./similar.bend as Sim
import ./resolution.bend as Res

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
# Where concurrent work met, as the names of the elements that met: both
# kinds `merge.rs` marks, over the whole tree, tombstones included.
def marks(+g: List<&2, Merge.Rev>, +t: List<&2, Merge.Node>) -> List<&2, Merge.Name>:
  List.append(&2, Merge.Name, insertions(g, t, t), deletions(g, Merge.order(t), None{}, Nil{}))

# One file as several heads leave it: the tree the walk built, the graph it
# walked, and for each event its revision and the document it minted from —
# `merge.rs`'s `Merged`, which the renderer, the marker check and the
# resolution writer all read.
type Joined is Data:
  Joined{names: List<&2, String>, digests: List<&2, String>, graph: List<&2, Merge.Rev>, tree: List<&2, Merge.Node>}

def name_at(names: List<&2, String>, n: Nat) -> String:
  match names n:
    case Nil{} _:
      SNil{}
    case x <> rest 0n:
      x
    case x <> rest 1n+k:
      name_at(rest, k)

# The file the walk reads: what every standing element holds, in order.
def items(j: Joined) -> List<&2, Ops.Item>:
  match j:
    case Joined{ns, ds, g, t}:
      Merge.file(t)

def plain(j: Joined) -> String:
  Ops.text(items(j))

# Whether anything met: a region, or a line but the last with no newline.
def met(j: Joined) -> Bool:
  match j:
    case Joined{ns, ds, +g, +t}:
      Nat.is_gt(contested(g, t), 0n)

# Rendering
# ---------

# A run of what stands, written by one author, and whether any of it met
# concurrent work: what `merge.rs` reports a contest over, since half a
# paragraph is not what a person needs to look at.
type Run is Data:
  Run{author: Nat, items: List<&2, Ops.Item>, met: Bool}

def runs.put(+a: Nat, +it: Ops.Item, +m: Bool, rs: List<&2, Run>) -> List<&2, Run>:
  match rs:
    case Nil{}:
      [Run{a, [it], m}]
    case Run{+b, +its, +x} <> +rest:
      Bool.pick(List<&2, Run>, Nat.is_eq(a, b), Run{b, it <> its, Bool.or(m, x)} <> rest, Run{a, [it], m} <> Run{b, its, x} <> rest)

def runs(ns: List<&2, Merge.Node>, +marked: List<&2, Merge.Name>) -> List<&2, Run>:
  match ns:
    case Nil{}:
      Nil{}
    case +n <> rest:
      runs.put(Merge.Node.author(n), Merge.Node.item(n), name.in(marked, Merge.Node.name(n)), runs(rest, marked))

# The renderer's lines: one before each run inside a fence, naming the
# revision that wrote it, and one closing the fence.
def label(+names: List<&2, String>, +a: Nat) -> String:
  "vvv historica: " ++ String.take(name_at(names, a), 8n) ++ " wrote vvv\n"

def closing() -> String:
  "^^^ historica: resolve, then delete these lines ^^^\n"

# Runs that met and meet each other are one fence: two runs that touch are
# one disagreement to a person looking at them.
def render.go(rs: List<&2, Run>, +names: List<&2, String>, open: Bool) -> String:
  match rs:
    case Nil{}:
      Bool.pick(String, open, closing(), SNil{})
    case Run{+a, +its, +m} <> rest:
      Bool.pick(String, m, label(names, a) ++ Ops.text(its), Bool.pick(String, open, closing(), SNil{}) ++ Ops.text(its)) ++ render.go(rest, names, m)

# The merged file as a person should see it, what met fenced. A file where
# nothing met renders as itself, byte for byte, which is what makes writing
# it into a folder safe. A line with no newline that met is followed by
# the fence on the same line, as the Rust tool's renderer leaves it; a
# terminator two sides disagree about is not fenced at all.
def render(j: Joined) -> String:
  match j:
    case Joined{+ns, ds, +g, +t}:
      render.go(runs(Merge.visible(t), marks(g, t)), ns, False{})

# The renderer's lines
# --------------------

# `str::lines`: split at each newline, a carriage return before one taken
# off, and nothing after a final newline.
def unreturned(+l: String) -> String:
  Bool.pick(String, String.ends_with(l, "\r"), String.take(l, Nat.sub(String.length(l), 1n)), l)

def lines.go(parts: List<&2, String>) -> List<&2, String>:
  match parts:
    case Nil{}:
      Nil{}
    case +last <> Nil{}:
      Bool.pick(List<&2, String>, String.is_empty(last), Nil{}, [unreturned(last)])
    case +l <> rest:
      unreturned(l) <> lines.go(rest)

def lines(s: String) -> List<&2, String>:
  lines.go(String.split(s, '\n'))

# Whether a line is one the renderer writes.
def is_marker(+line: String) -> Bool:
  +opened = String.starts_with(line, "vvv historica: ")
  Bool.or(Bool.and(opened, Bool.or(String.ends_with(line, "vvv"), String.ends_with(line, "^^^"))), String.starts_with(line, "^^^ historica: "))

def any_eq(xs: List<&2, String>, +x: String) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case y <> rest:
      Bool.or(String.eq(y, x), any_eq(rest, x))

def markers.go(ls: List<&2, String>, +plain: List<&2, String>) -> List<&2, String>:
  match ls:
    case Nil{}:
      Nil{}
    case +l <> rest:
      +later = markers.go(rest, plain)
      Bool.pick(List<&2, String>, Bool.and(is_marker(l), Bool.not(any_eq(plain, l))), l <> later, later)

# Every line the rendering writes on its own account: what `record` refuses
# to find standing, per line, since a person can edit inside a fence and
# leave it there. A line the file itself holds is not one.
def markers(+j: Joined) -> List<&2, String>:
  markers.go(lines(render(j)), lines(plain(j)))

def standing.go(ls: List<&2, String>, +ms: List<&2, String>) -> List<&2, String>:
  match ls:
    case Nil{}:
      Nil{}
    case +l <> rest:
      +later = standing.go(rest, ms)
      Bool.pick(List<&2, String>, any_eq(ms, l), l <> later, later)

# The renderer's lines still standing in `text`: scoped to one merge, which
# is what lets a document about markers be ordinary content otherwise.
def unresolved(+j: Joined, text: String) -> List<&2, String>:
  standing.go(lines(text), markers(j))

# The resolution
# --------------

# The name a `keep` quotes for each element standing — the document that
# minted it, and its ordinal in that document's order — beside the item
# standing under it.
type Ref is Data:
  Ref{document: String, minted: Nat}

type Named is Data:
  Named{name: Ref, item: Ops.Item}

def named.of(ns: List<&2, Merge.Node>, +digests: List<&2, String>) -> List<&2, Named>:
  match ns:
    case Nil{}:
      Nil{}
    case +n <> rest:
      Named{Ref{name_at(digests, Merge.Node.author(n)), Merge.Node.minted(n)}, Merge.Node.item(n)} <> named.of(rest, digests)

def named(j: Joined) -> List<&2, Named>:
  match j:
    case Joined{ns, +ds, g, t}:
      named.of(Merge.visible(t), ds)

# What survived of the proposal, by name, and what the person wrote: one
# element at a time, as `similar`'s Histogram diff aligns the proposal with
# what the folder holds.
type Said is Data:
  Said.Kept{n: Named}
  Said.Wrote{it: Ops.Item}

def said.of(ms: List<&2, Ops.Move>, named: List<&2, Named>) -> List<&2, Said>:
  match ms named:
    case Nil{} _:
      Nil{}
    case Ops.Keep{} <> rest n <> more:
      Said.Kept{n} <> said.of(rest, more)
    case Ops.Del{x} <> rest n <> more:
      said.of(rest, more)
    case Ops.Ins{y} <> rest more:
      Said.Wrote{y} <> said.of(rest, more)
    case m <> rest Nil{}:
      said.of(rest, Nil{})

def wrote.all(its: List<&2, Ops.Item>) -> List<&2, Said>:
  match its:
    case Nil{}:
      Nil{}
    case it <> rest:
      Said.Wrote{it} <> wrote.all(rest)

# The alignment is checked in one pass before anything is named by it, as
# `Sim.diff` checks one before a document is written from it; one that did
# not take the proposal to the folder — which the crate's cases never ask
# for — would name nothing, and state every line afresh.
def said.checked(+ms: List<&2, Ops.Move>, named: List<&2, Named>, after: List<&2, Ops.Item>, ok: Bool) -> List<&2, Said>:
  match ok:
    case True{}:
      said.of(ms, named)
    case False{}:
      wrote.all(after)

def said(+j: Joined, +after: List<&2, Ops.Item>) -> List<&2, Said>:
  +ms = Sim.walked.moves(Sim.walked.go(Sim.ops(items(j), after), Sim.Walked{items(j), after, Nil{}}))
  said.checked(ms, named(j), after, Sim.fit(ms, items(j), after))

# Pieces are maximal: a `keep` continuing the one after it is one run, and
# two inserts that meet are one insert — exactly one spelling parses.
def pieces.put(s: Said, ps: List<&2, Res.Piece>) -> List<&2, Res.Piece>:
  match s ps:
    case Said.Kept{Named{Ref{+d, +m}, it}} Res.Piece.Keep{+e, +first, +count} <> +rest:
      Bool.pick(List<&2, Res.Piece>, Bool.and(String.eq(d, e), Nat.is_eq(1n+m, first)), Res.Piece.Keep{d, m, 1n+count} <> rest, Res.Piece.Keep{d, m, 1n} <> Res.Piece.Keep{e, first, count} <> rest)
    case Said.Kept{Named{Ref{d, m}, it}} rest:
      Res.Piece.Keep{d, m, 1n} <> rest
    case Said.Wrote{it} Res.Piece.Insert{its} <> rest:
      Res.Piece.Insert{it <> its} <> rest
    case Said.Wrote{it} rest:
      Res.Piece.Insert{[it]} <> rest

def pieces(ss: List<&2, Said>) -> List<&2, Res.Piece>:
  match ss:
    case Nil{}:
      Nil{}
    case s <> rest:
      pieces.put(s, pieces(rest))

def resolution.of(+after: List<&2, Ops.Item>, ps: List<&2, Res.Piece>) -> Maybe<&2, Res.Doc>:
  match ps:
    case Nil{}:
      None{}
    case +some:
      Some{Res.Doc{None{}, Some{Ops.state_digest(after)}, some}}

# The resolution a merge states, given what the walk proposed and what the
# folder holds: `diff::resolve`. What survived is named rather than
# restated — a restated line would be a new item, and the first merge
# reaching across this one would meet the same text twice. Nothing where
# nothing is left: the grammar has no spelling for a file with no pieces.
def resolve(+j: Joined, +after: List<&2, Ops.Item>) -> Maybe<&2, Res.Doc>:
  resolution.of(after, pieces(said(j, after)))
