# The merge: Eg-walker over Fugue, as decision 0007 chose it. A revision is
# an event with a causal past and, when it edited this file, the operation
# document it stated. A walk replays the events in any causal order into one
# tree of elements, each named by the event that wrote it and its ordinal
# there, and the file is the in-order reading of what still stands.
#
# What an event does is decided from its own view alone: the tree restricted
# to what its author had seen (`restrict`), read into the positions its
# document counts, and anchored by Fugue's rule among the elements it knows.
# The actions that come out — attach here, mark that — are then applied to
# the whole tree, where siblings sit in name order whatever order they came.
# `LAWS.merge_converges` rests on exactly that: an event's actions are a
# function of a view later events cannot change, and the actions of two
# events that had not seen each other commute.
#
# Positions are unary, the tree is a flat list, and the reading carries
# fuel: made to be proven about, and still the merge `commands.bend` walks
# where a merge states no resolution.

import Base
import ./ops.bend as Ops

# Events
# ------

# A resolution's part (decision 0032): elements kept by name — the events
# that stated the document minting them, the first ordinal, how many — or
# items of its own.
type Part is Data:
  Kept{authors: List<&2, Nat>, first: Nat, count: Nat}
  Own{items: List<&2, Ops.Item>}

# What an event stated: operations counted into its author's view, or a
# resolution stating the file whole.
type Statement is Data:
  Edits{ops: List<&2, Ops.Op>}
  Resolves{parts: List<&2, Part>}

# One revision as an event: the events its author had seen — strictly its
# past, as indices
# into the graph, which is in digest order — and what it stated, if anything.
type Rev is Data:
  Rev{past: List<&2, Nat>, stated: Maybe<&2, Statement>}

def has(xs: List<&2, Nat>, +x: Nat) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case y <> ys:
      Bool.or(Nat.is_eq(y, x), has(ys, x))

# What an event had seen; nothing, for an index the graph does not hold.
def Rev.past(ev: Maybe<&2, Rev>) -> List<&2, Nat>:
  match ev:
    case None{}:
      Nil{}
    case Some{Rev{p, ops}}:
      p

def past(g: List<&2, Rev>, e: Nat) -> List<&2, Nat>:
  Rev.past(List.get(&2, Rev, g, e))

# Names and elements
# ------------------

# An element is named by the event that wrote it and its ordinal there.
# Sibling ties are broken by this name: digest order first, then ordinal.
type Name is Data:
  Name{author: Nat, minted: Nat}

def Name.cmp.of(c: Cmp, a2: Nat, b2: Nat) -> Cmp:
  match c:
    case LT{}:
      LT{}
    case GT{}:
      GT{}
    case EQ{}:
      Nat.cmp(a2, b2)

def Name.cmp(a: Name, b: Name) -> Cmp:
  match a b:
    case Name{a1, a2} Name{b1, b2}:
      Name.cmp.of(Nat.cmp(a1, b1), a2, b2)

def Name.eq(a: Name, b: Name) -> Bool:
  Cmp.is_eq(Name.cmp(a, b))

def Name.same(a: Maybe<&2, Name>, b: Maybe<&2, Name>) -> Bool:
  match a b:
    case None{} None{}:
      True{}
    case Some{x} Some{y}:
      Name.eq(x, y)
    case _ _:
      False{}

# Where an element hangs: under `parent` (the root when `None`), on its
# right side or its left.
type Place is Data:
  Place{parent: Maybe<&2, Name>, right: Bool}

# One element, alive or tombstoned. `deleted` holds every event that
# removed it, in index order; concurrent removals agree.
type Node is Data:
  Node{name: Name, item: Ops.Item, place: Place, deleted: List<&2, Nat>}

def Node.name(n: Node) -> Name:
  match n:
    case Node{nm, it, pl, d}:
      nm

def Node.author(n: Node) -> Nat:
  match n:
    case Node{Name{a, m}, it, pl, d}:
      a

def Node.place(n: Node) -> Place:
  match n:
    case Node{nm, it, pl, d}:
      pl

def Node.item(n: Node) -> Ops.Item:
  match n:
    case Node{nm, it, pl, d}:
      it

def Node.standing(n: Node) -> Bool:
  match n:
    case Node{nm, it, pl, Nil{}}:
      True{}
    case Node{nm, it, pl, d <> ds}:
      False{}

def Node.hangs(n: Node, parent: Maybe<&2, Name>, right: Bool) -> Bool:
  match n:
    case Node{nm, it, Place{p, r}, d}:
      Bool.and(Name.same(p, parent), Bool.not(Bool.xor(r, right)))

# The tree
# --------
#
# A flat list of elements in name order. Its shape is what makes a walk's
# result independent of the walk: attaching two elements, or marking one
# twice, gives one list whichever came first.

# Attach among its siblings — before the first whose name is greater.
def attach.put(n: Node, x: Node, xs: List<&2, Node>, rest: List<&2, Node>, first: Bool) -> List<&2, Node>:
  match first:
    case True{}:
      n <> x <> xs
    case False{}:
      x <> rest

def attach(t: List<&2, Node>, +n: Node) -> List<&2, Node>:
  match t:
    case Nil{}:
      [n]
    case +x <> +xs:
      attach.put(n, x, xs, attach(xs, n), Cmp.is_lt(Name.cmp(Node.name(n), Node.name(x))))

# An event joins the removals of an element, in index order.
def ins.put(by: Nat, y: Nat, ys: List<&2, Nat>, rest: List<&2, Nat>, first: Bool) -> List<&2, Nat>:
  match first:
    case True{}:
      by <> y <> ys
    case False{}:
      y <> rest

def ins(d: List<&2, Nat>, +by: Nat) -> List<&2, Nat>:
  match d:
    case Nil{}:
      [by]
    case +y <> +ys:
      ins.put(by, y, ys, ins(ys, by), Nat.is_lt(by, y))

def ins.if(d: List<&2, Nat>, by: Nat, hit: Bool) -> List<&2, Nat>:
  match hit:
    case True{}:
      ins(d, by)
    case False{}:
      d

def Node.mark(n: Node, target: Name, by: Nat) -> Node:
  match n:
    case Node{+nm, it, pl, d}:
      Node{nm, it, pl, ins.if(d, by, Name.eq(nm, target))}

def mark(t: List<&2, Node>, +target: Name, +by: Nat) -> List<&2, Node>:
  match t:
    case Nil{}:
      Nil{}
    case x <> xs:
      Node.mark(x, target, by) <> mark(xs, target, by)

# The view: what an event's author had seen. Elements written by events
# in `seen`, each carrying only the removals by events in `seen`.
def keep(d: List<&2, Nat>, +seen: List<&2, Nat>) -> List<&2, Nat>:
  match d:
    case Nil{}:
      Nil{}
    case +y <> ys:
      List.filter.put(Nat, y, keep(ys, seen), has(seen, y))

def Node.restrict(n: Node, seen: List<&2, Nat>) -> Node:
  match n:
    case Node{nm, it, pl, d}:
      Node{nm, it, pl, keep(d, seen)}

def restrict(t: List<&2, Node>, +seen: List<&2, Nat>) -> List<&2, Node>:
  match t:
    case Nil{}:
      Nil{}
    case +x <> xs:
      List.filter.put(Node, Node.restrict(x, seen), restrict(xs, seen), has(seen, Node.author(x)))

# Reading
# -------

def children(t: List<&2, Node>, +parent: Maybe<&2, Name>, +right: Bool) -> List<&2, Node>:
  match t:
    case Nil{}:
      Nil{}
    case +x <> xs:
      List.filter.put(Node, x, children(xs, parent, right), Node.hangs(x, parent, right))

# The in-order reading: left subtrees, the element, right subtrees. The
# fuel bounds the descent; one more than the element count is enough for
# any tree `attach` built, since a descent visits each element once.
def read_all(fuel: Nat, +t: List<&2, Node>, siblings: List<&2, Node>) -> List<&2, Node>:
  match fuel:
    case 0n:
      Nil{}
    case 1n++p:
      match siblings:
        case Nil{}:
          Nil{}
        case +s <> rest:
          List.append(&2, Node, read_all(p, t, children(t, Some{Node.name(s)}, False{})),
            s <> List.append(&2, Node, read_all(p, t, children(t, Some{Node.name(s)}, True{})), read_all(p, t, rest)))

def order(+t: List<&2, Node>) -> List<&2, Node>:
  read_all(1n+List.length(&2, Node, t), t, children(t, None{}, True{}))

def standing(ns: List<&2, Node>) -> List<&2, Node>:
  match ns:
    case Nil{}:
      Nil{}
    case +n <> rest:
      List.filter.put(Node, n, standing(rest), Node.standing(n))

# The positions an author's document counts into: their view, read, with
# what they had seen removed left out.
def visible(t: List<&2, Node>) -> List<&2, Node>:
  standing(order(t))

def file.of(ns: List<&2, Node>) -> List<&2, Ops.Item>:
  match ns:
    case Nil{}:
      Nil{}
    case n <> rest:
      Node.item(n) <> file.of(rest)

# The merged file: every element still standing, in order.
def file(t: List<&2, Node>) -> List<&2, Ops.Item>:
  file.of(visible(t))

# Anchoring
# ---------
#
# Fugue's rule on the view, where everything is known: an element attaches
# to its left neighbour's right when that neighbour has no right child yet,
# and otherwise as a left child of the leftmost element under the
# neighbour's first right child — the element that follows the neighbour in
# the author's view, tombstones included. A run written by one author so
# becomes one subtree, read out whole, which is the guarantee against
# interleaving decision 0007 chose Fugue for; and two elements are only ever
# same-side siblings when their authors had not seen each other, which is
# what entitles `attach` to break the tie by name.
def head_name(cs: List<&2, Node>, at: Name) -> Name:
  match cs:
    case Nil{}:
      at
    case c <> more:
      Node.name(c)

# Down the left children as far as they go; the fuel is the element count,
# and once there is no left child the descent stays put.
def leftmost(fuel: Nat, +t: List<&2, Node>, +at: Name) -> Name:
  match fuel:
    case 0n:
      at
    case 1n+p:
      leftmost(p, t, head_name(children(t, Some{at}, False{}), at))

def anchor.of(+t: List<&2, Node>, left: Maybe<&2, Name>, cs: List<&2, Node>) -> Place:
  match cs:
    case Nil{}:
      Place{left, True{}}
    case c <> more:
      Place{Some{leftmost(List.length(&2, Node, t), t, Node.name(c))}, False{}}

def anchor(+t: List<&2, Node>, +left: Maybe<&2, Name>) -> Place:
  anchor.of(t, left, children(t, left, True{}))

# Replaying one event
# -------------------
#
# What an event does to the tree, decided on its view: attach an element it
# minted, or mark one it saw as removed. The author is supplied when the
# actions are applied, so an event's actions are its own by construction.
type Action is Data:
  Attach{minted: Nat, item: Ops.Item, place: Place}
  Delete{target: Name}

# A delete's items, each held against the view at its own position.
def deletes.agreed(target: Name, more: Maybe<&2, List<&2, Action>>, agreed: Bool) -> Maybe<&2, List<&2, Action>>:
  match agreed:
    case False{}:
      None{}
    case True{}:
      Maybe.map(&2, List<&2, Action>, List<&2, Action>, acts => Delete{target} <> acts, more)

def deletes.at(it: Ops.Item, more: Maybe<&2, List<&2, Action>>, found: Maybe<&2, Node>) -> Maybe<&2, List<&2, Action>>:
  match found:
    case None{}:
      None{}
    case Some{Node{nm, item, pl, d}}:
      deletes.agreed(nm, more, Ops.agrees(it, item))

def deletes(items: List<&2, Ops.Item>, +prepare: List<&2, Node>, +at: Nat) -> Maybe<&2, List<&2, Action>>:
  match items:
    case Nil{}:
      Some{Nil{}}
    case it <> more:
      deletes.at(it, deletes(more, prepare, 1n+at), List.get(&2, Node, prepare, at))

# A run of inserted items, each anchored after the one before; the view
# grows with them, so the run attaches to itself.
type Inserted is Data:
  Inserted{view: List<&2, Node>, acts: List<&2, Action>, minted: Nat}

def inserts.of(minted: Nat, item: Ops.Item, place: Place, rest: Inserted) -> Inserted:
  match rest:
    case Inserted{v, acts, m}:
      Inserted{v, Attach{minted, item, place} <> acts, m}

def inserts(items: List<&2, Ops.Item>, +v: List<&2, Node>, +e: Nat, left: Maybe<&2, Name>, +minted: Nat) -> Inserted:
  match items:
    case Nil{}:
      Inserted{v, Nil{}, minted}
    case +it <> more:
      +place = anchor(v, left)
      inserts.of(minted, it, place, inserts(more, attach(v, Node{Name{e, minted}, it, place, Nil{}}), e, Some{Name{e, minted}}, 1n+minted))

# The element an insert at `at` follows in the view: nothing at zero, and
# past the view's end is refused.
def left_of(prepare: List<&2, Node>, at: Nat) -> Maybe<&2, Maybe<&2, Name>>:
  match at:
    case 0n:
      Some{None{}}
    case 1n+p:
      Maybe.map(&2, Node, Maybe<&2, Name>, x => Some{Node.name(x)}, List.get(&2, Node, prepare, p))

# A run in progress: the view as the event's own elements grow it, the
# count minted so far, and the actions decided. `None` once the document
# has contradicted its author's view.
type Running is Data:
  Running{view: List<&2, Node>, minted: Nat, acts: List<&2, Action>}

def run.deleted(+v: List<&2, Node>, minted: Nat, acts: List<&2, Action>, new: Maybe<&2, List<&2, Action>>) -> Maybe<&2, Running>:
  match new:
    case None{}:
      None{}
    case Some{a}:
      Some{Running{v, minted, List.append(&2, Action, acts, a)}}

def run.inserted(acts: List<&2, Action>, done: Inserted) -> Maybe<&2, Running>:
  match done:
    case Inserted{v2, new, m}:
      Some{Running{v2, m, List.append(&2, Action, acts, new)}}

def run.insert(items: List<&2, Ops.Item>, +v: List<&2, Node>, +e: Nat, minted: Nat, acts: List<&2, Action>, left: Maybe<&2, Maybe<&2, Name>>) -> Maybe<&2, Running>:
  match left:
    case None{}:
      None{}
    case Some{l}:
      run.inserted(acts, inserts(items, v, e, l, minted))

def run.step(st: Maybe<&2, Running>, op: Ops.Op, +e: Nat, +prepare: List<&2, Node>) -> Maybe<&2, Running>:
  match st:
    case None{}:
      None{}
    case Some{Running{v, minted, acts}}:
      match op:
        case Ops.Op{Ops.Delete{}, at, items}:
          run.deleted(v, minted, acts, deletes(items, prepare, at))
        case Ops.Op{Ops.Insert{}, at, items}:
          run.insert(items, v, e, minted, acts, left_of(prepare, at))

def run(ops: List<&2, Ops.Op>, st: Maybe<&2, Running>, +e: Nat, +prepare: List<&2, Node>) -> Maybe<&2, Running>:
  match ops:
    case Nil{}:
      st
    case op <> rest:
      run(rest, run.step(st, op, e, prepare), e, prepare)

def run.acts(st: Maybe<&2, Running>) -> Maybe<&2, List<&2, Action>>:
  match st:
    case None{}:
      None{}
    case Some{Running{v, minted, acts}}:
      Some{acts}

# An event's actions, decided on its view alone.
def actions(+t: List<&2, Node>, +seen: List<&2, Nat>, +e: Nat, ops: List<&2, Ops.Op>) -> Maybe<&2, List<&2, Action>>:
  +v = restrict(t, seen)
  run.acts(run(ops, Some{Running{v, 0n, Nil{}}}, e, visible(v)))

# Resolving
# ---------
#
# Decision 0032's resolution, walked as `merge.rs` walks it. On the author's
# view, a keep names elements as a `keep` line does, by the document that
# minted them and an ordinal there, and takes the first element standing
# in the view under that name that no earlier keep took. An insert is
# anchored after what came before it, kept or inserted, as a run is. Every
# element of the view left unkept is removed. What is kept stays where it
# is, under its own name, so a concurrent edit to it still lands.
def Node.minted(n: Node) -> Nat:
  match n:
    case Node{Name{a, m}, it, pl, d}:
      m

def res.taken(ks: List<&2, Name>, +nm: Name) -> Bool:
  match ks:
    case Nil{}:
      False{}
    case k <> rest:
      Bool.or(Name.eq(k, nm), res.taken(rest, nm))

def keepable(+n: Node, +authors: List<&2, Nat>, +m: Nat, +kept: List<&2, Name>) -> Bool:
  Bool.and(has(authors, Node.author(n)), Bool.and(Nat.is_eq(Node.minted(n), m), Bool.not(res.taken(kept, Node.name(n)))))

def res.find.at(+n: Node, rest: Maybe<&2, Name>, hit: Bool) -> Maybe<&2, Name>:
  match hit:
    case True{}:
      Some{Node.name(n)}
    case False{}:
      rest

# The first element of the view a keep of ordinal `m` may take.
def res.find(P: List<&2, Node>, +authors: List<&2, Nat>, +m: Nat, +kept: List<&2, Name>) -> Maybe<&2, Name>:
  match P:
    case Nil{}:
      None{}
    case +n <> more:
      res.find.at(n, res.find(more, authors, m, kept), keepable(n, authors, m, kept))

# A resolution in progress: the view as its own inserts grow it, the count
# minted so far, the actions decided, the elements kept, and what the next
# insert follows. `None` once a keep names nothing the view holds.
type Resolving is Data:
  Resolving{view: List<&2, Node>, minted: Nat, acts: List<&2, Action>, kept: List<&2, Name>, left: Maybe<&2, Name>}

def res.took(+v: List<&2, Node>, minted: Nat, acts: List<&2, Action>, kept: List<&2, Name>, found: Maybe<&2, Name>) -> Maybe<&2, Resolving>:
  match found:
    case None{}:
      None{}
    case Some{+nm}:
      Some{Resolving{v, minted, acts, nm <> kept, Some{nm}}}

def res.one(st: Maybe<&2, Resolving>, +authors: List<&2, Nat>, +m: Nat, +P: List<&2, Node>) -> Maybe<&2, Resolving>:
  match st:
    case None{}:
      None{}
    case Some{Resolving{v, minted, acts, +kept, left}}:
      res.took(v, minted, acts, kept, res.find(P, authors, m, kept))

def res.keep(count: Nat, st: Maybe<&2, Resolving>, +authors: List<&2, Nat>, +first: Nat, +P: List<&2, Node>) -> Maybe<&2, Resolving>:
  match count:
    case 0n:
      st
    case 1n+c:
      res.keep(c, res.one(st, authors, first, P), authors, 1n+first, P)

# What follows a run of inserts: its last element, or what it followed.
def res.last(items: List<&2, Ops.Item>, +e: Nat, left: Maybe<&2, Name>, +minted: Nat) -> Maybe<&2, Name>:
  match items:
    case Nil{}:
      left
    case it <> more:
      res.last(more, e, Some{Name{e, minted}}, 1n+minted)

def res.inserted(acts: List<&2, Action>, kept: List<&2, Name>, left: Maybe<&2, Name>, done: Inserted) -> Maybe<&2, Resolving>:
  match done:
    case Inserted{v2, new, m2}:
      Some{Resolving{v2, m2, List.append(&2, Action, acts, new), kept, left}}

def res.step(st: Maybe<&2, Resolving>, p: Part, +e: Nat, +P: List<&2, Node>) -> Maybe<&2, Resolving>:
  match st:
    case None{}:
      None{}
    case Some{Resolving{+v, +minted, acts, kept, +left}}:
      match p:
        case Kept{authors, first, count}:
          res.keep(count, Some{Resolving{v, minted, acts, kept, left}}, authors, first, P)
        case Own{+items}:
          res.inserted(acts, kept, res.last(items, e, left, minted), inserts(items, v, e, left, minted))

def res(parts: List<&2, Part>, st: Maybe<&2, Resolving>, +e: Nat, +P: List<&2, Node>) -> Maybe<&2, Resolving>:
  match parts:
    case Nil{}:
      st
    case p <> rest:
      res(rest, res.step(st, p, e, P), e, P)

def unkept.put(+n: Node, rest: List<&2, Action>, hit: Bool) -> List<&2, Action>:
  match hit:
    case True{}:
      rest
    case False{}:
      Delete{Node.name(n)} <> rest

# Every element of the view no keep took.
def unkept(P: List<&2, Node>, +kept: List<&2, Name>) -> List<&2, Action>:
  match P:
    case Nil{}:
      Nil{}
    case +n <> more:
      unkept.put(n, unkept(more, kept), res.taken(kept, Node.name(n)))

# The resolution done: its inserts, then the removal of what it left out,
# as a run whose last operation deleted them.
def res.done(st: Maybe<&2, Resolving>, +P: List<&2, Node>) -> Maybe<&2, Running>:
  match st:
    case None{}:
      None{}
    case Some{Resolving{v, m, acts, +kept, left}}:
      run.deleted(v, m, acts, Some{unkept(P, kept)})

def resolve(+t: List<&2, Node>, +seen: List<&2, Nat>, +e: Nat, parts: List<&2, Part>) -> Maybe<&2, List<&2, Action>>:
  +v = restrict(t, seen)
  run.acts(res.done(res(parts, Some{Resolving{v, 0n, Nil{}, Nil{}, None{}}}, e, visible(v)), visible(v)))

# What an event does, whichever it stated.
def event_acts(+t: List<&2, Node>, +seen: List<&2, Nat>, +e: Nat, s: Statement) -> Maybe<&2, List<&2, Action>>:
  match s:
    case Edits{ops}:
      actions(t, seen, e, ops)
    case Resolves{parts}:
      resolve(t, seen, e, parts)

# Applying them to the whole tree, as the event's own.
def one(t: List<&2, Node>, +by: Nat, act: Action) -> List<&2, Node>:
  match act:
    case Attach{m, it, pl}:
      attach(t, Node{Name{by, m}, it, pl, Nil{}})
    case Delete{target}:
      mark(t, target, by)

def apply(acts: List<&2, Action>, t: List<&2, Node>, +by: Nat) -> List<&2, Node>:
  match acts:
    case Nil{}:
      t
    case a <> rest:
      apply(rest, one(t, by, a), by)

def step.of(t: List<&2, Node>, e: Nat, acts: Maybe<&2, List<&2, Action>>) -> Maybe<&2, List<&2, Node>>:
  match acts:
    case None{}:
      None{}
    case Some{a}:
      Some{apply(a, t, e)}

# One event replayed: nothing for an event that stated nothing, a refusal
# for an index the graph does not hold.
def step(ev: Maybe<&2, Rev>, +t: List<&2, Node>, +e: Nat) -> Maybe<&2, List<&2, Node>>:
  match ev:
    case None{}:
      None{}
    case Some{Rev{seen, None{}}}:
      Some{t}
    case Some{Rev{seen, Some{s}}}:
      step.of(t, e, event_acts(t, seen, e, s))

def step.m(mt: Maybe<&2, List<&2, Node>>, ev: Maybe<&2, Rev>, e: Nat) -> Maybe<&2, List<&2, Node>>:
  match mt:
    case None{}:
      None{}
    case Some{t}:
      step(ev, t, e)

# The walk
# --------

def walk(o: List<&2, Nat>, +g: List<&2, Rev>, mt: Maybe<&2, List<&2, Node>>) -> Maybe<&2, List<&2, Node>>:
  match o:
    case Nil{}:
      mt
    case +e <> +rest:
      walk(rest, g, step.m(mt, List.get(&2, Rev, g, e), e))

def merged.of(mt: Maybe<&2, List<&2, Node>>) -> Maybe<&2, List<&2, Ops.Item>>:
  match mt:
    case None{}:
      None{}
    case Some{t}:
      Some{file(t)}

def merged(g: List<&2, Rev>, o: List<&2, Nat>) -> Maybe<&2, List<&2, Ops.Item>>:
  merged.of(walk(o, g, Some{Nil{}}))

# The file as an author who had seen the events of `s` reads a walk's tree.
def seen_file(mt: Maybe<&2, List<&2, Node>>, +s: List<&2, Nat>) -> Maybe<&2, List<&2, Ops.Item>>:
  match mt:
    case None{}:
      None{}
    case Some{t}:
      Some{file(restrict(t, s))}

# Causal orders
# -------------
#
# Two orders of one graph: each event once, the same events in both, and
# nothing before what it had seen.
def distinct(o: List<&2, Nat>) -> Bool:
  match o:
    case Nil{}:
      True{}
    case +e <> +rest:
      Bool.and(Bool.not(has(rest, e)), distinct(rest))

def subset(a: List<&2, Nat>, +b: List<&2, Nat>) -> Bool:
  match a:
    case Nil{}:
      True{}
    case x <> rest:
      Bool.and(has(b, x), subset(rest, b))

# Nothing after an event is in its past.
def none_known(+seen: List<&2, Nat>, rest: List<&2, Nat>) -> Bool:
  match rest:
    case Nil{}:
      True{}
    case x <> more:
      Bool.and(Bool.not(has(seen, x)), none_known(seen, more))

def causal(o: List<&2, Nat>, +g: List<&2, Rev>) -> Bool:
  match o:
    case Nil{}:
      True{}
    case e <> +rest:
      Bool.and(none_known(past(g, e), rest), causal(rest, g))

# Every index in an order names an event the graph holds.
def below(o: List<&2, Nat>, +n: Nat) -> Bool:
  match o:
    case Nil{}:
      True{}
    case +e <> rest:
      Bool.and(Nat.is_lt(e, n), below(rest, n))

def orders(+g: List<&2, Rev>, +a: List<&2, Nat>, +b: List<&2, Nat>) -> Bool:
  Bool.and(distinct(a), Bool.and(distinct(b), Bool.and(subset(a, b), Bool.and(subset(b, a), Bool.and(causal(a, g), causal(b, g))))))

# Every event of `xs` had seen only events in `s`. Of `s` itself, a set
# of events that holds the past of each: what an author can have seen.
def closed(xs: List<&2, Nat>, +g: List<&2, Rev>, +s: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case x <> rest:
      Bool.and(subset(past(g, x), s), closed(rest, g, s))

# Reachable states
# ----------------
#
# What holds of a view as its author's run grows it, stated so a proof can
# carry it: the reading of every sibling list finishes within the fuel
# `order` gives it, and no element is read twice. `fits` is the fuel bound
# as a fact about the tree rather than a count of its depth; the invariant
# holds of the empty view and is kept by an anchored attach and by a mark
# (`LAWS.insert_keeps_invariant`, `LAWS.mark_keeps_invariant`).
def is_nil(ns: List<&2, Node>) -> Bool:
  match ns:
    case Nil{}:
      True{}
    case n <> rest:
      False{}

# The reading of `siblings` completes within `fuel`: no branch runs out.
def fits(fuel: Nat, +t: List<&2, Node>, siblings: List<&2, Node>) -> Bool:
  match fuel:
    case 0n:
      is_nil(siblings)
    case 1n++p:
      match siblings:
        case Nil{}:
          True{}
        case +s <> rest:
          Bool.and(fits(p, t, children(t, Some{Node.name(s)}, False{})), Bool.and(fits(p, t, children(t, Some{Node.name(s)}, True{})), fits(p, t, rest)))

def named(ns: List<&2, Node>, +nm: Name) -> Bool:
  match ns:
    case Nil{}:
      False{}
    case n <> rest:
      Bool.or(Name.eq(Node.name(n), nm), named(rest, nm))

def nodup(ns: List<&2, Node>) -> Bool:
  match ns:
    case Nil{}:
      True{}
    case +n <> +rest:
      Bool.and(Bool.not(named(rest, Node.name(n))), nodup(rest))

def Node.under(n: Node, nm: Name) -> Bool:
  match n:
    case Node{x, it, Place{p, r}, d}:
      Name.same(p, Some{nm})

def hangs_under(ns: List<&2, Node>, +nm: Name) -> Bool:
  match ns:
    case Nil{}:
      False{}
    case n <> rest:
      Bool.or(Node.under(n, nm), hangs_under(rest, nm))

# A name no element has and none hangs under: what an event mints.
def fresh(+t: List<&2, Node>, +nm: Name) -> Bool:
  Bool.and(Bool.not(named(t, nm)), Bool.not(hangs_under(t, nm)))

def invariant(+t: List<&2, Node>) -> Bool:
  Bool.and(fits(1n+List.length(&2, Node, t), t, children(t, None{}, True{})), nodup(order(t)))

# The element an insert follows is visible, or there is none.
def in_view(+t: List<&2, Node>, left: Maybe<&2, Name>) -> Bool:
  match left:
    case None{}:
      True{}
    case Some{nm}:
      named(visible(t), nm)

# One line of history
# -------------------
#
# A chain of documents, each an event that has seen every event before
# it — the history recorded when nobody branches — and `replay`, plain
# application along it from the empty file. `LAWS.merge_linear` says the
# walk agrees with the replay wherever the replay succeeds.

# The indices from `k`, `n` of them, in order.
def upto.go(n: Nat, +k: Nat) -> List<&2, Nat>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      k <> upto.go(p, 1n+k)

def upto(n: Nat) -> List<&2, Nat>:
  upto.go(n, 0n)

def chain.go(docs: List<&2, List<&2, Ops.Op>>, +n: Nat) -> List<&2, Rev>:
  match docs:
    case Nil{}:
      Nil{}
    case d <> ds:
      Rev{upto(n), Some{Edits{d}}} <> chain.go(ds, 1n+n)

def chain(docs: List<&2, List<&2, Ops.Op>>) -> List<&2, Rev>:
  chain.go(docs, 0n)

def replay(docs: List<&2, List<&2, Ops.Op>>, r: Result<&2, &2, String, List<&2, Ops.Item>>) -> Result<&2, &2, String, List<&2, Ops.Item>>:
  match docs r:
    case _ Fail{e}:
      Fail{e}
    case Nil{} Done{f}:
      Done{f}
    case d <> ds Done{f}:
      replay(ds, Ops.apply(f, Ops.Doc{None{}, None{}, d}))
