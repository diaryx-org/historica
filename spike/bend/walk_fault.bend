# Why a walk refused, in `merge.rs`'s `MergeError` words: the first event,
# in the order walked, whose document contradicts its author's view — a
# position past what the author saw, an item removed that is not the one
# there, or a `keep` of a name the view does not hold, or holds fewer
# times than the resolution keeps it.
#
# `Merge.walk` answers only that it refused, which is all its laws need.
# This walks again, on the refusing path alone, to find where and why:
# each event's view is the one the walk decides it on, and its document
# is held to that view as `merge.rs` holds it — a delete's whole run in
# range before any of its items is compared, each position against the
# view the event started from.

import Base
import ./ops.bend as Ops
import ./merge.bend as Merge
import ./resolution.bend as Res

def name_at(names: List<&2, String>, n: Nat) -> String:
  match names n:
    case Nil{} _:
      SNil{}
    case x <> rest 0n:
      x
    case x <> rest 1n+k:
      name_at(rest, k)

def item_text(it: Ops.Item) -> String:
  match it:
    case Ops.Item{t, n, f}:
      t

def OUT_OF_RANGE(+rev: String, +position: Nat, +length: Nat) -> String:
  rev ++ " names position " ++ Nat.show(position) ++ " of a file its author saw " ++ Nat.show(length) ++ " items of; the document was recorded against a different history"

def UNKNOWN(+rev: String, +document: String, +item: Nat) -> String:
  rev ++ " keeps item " ++ Nat.show(item) ++ " of " ++ document ++ ", which its author's view of the file does not hold; the resolution names a document outside this merge's past, or a run longer than that document has items"

def DISAGREES(+rev: String, +position: Nat, +recorded: String, +found: String) -> String:
  rev ++ " deletes `" ++ recorded ++ "` at position " ++ Nat.show(position) ++ ", where its author's view held `" ++ found ++ "`; one of the two is corrupt, and the digests say which"

# An operation document
# ---------------------

def deleted.at(+it: Ops.Item, found: Maybe<&2, Merge.Node>, later: Maybe<&2, String>, +at: Nat, +rev: String) -> Maybe<&2, String>:
  match found:
    case None{}:
      later
    case Some{+n}:
      Bool.pick(Maybe<&2, String>, Ops.agrees(it, Merge.Node.item(n)), later, Some{DISAGREES(rev, at, item_text(it), item_text(Merge.Node.item(n)))})

def deleted(items: List<&2, Ops.Item>, +prepare: List<&2, Merge.Node>, +at: Nat, +rev: String) -> Maybe<&2, String>:
  match items:
    case Nil{}:
      None{}
    case +it <> more:
      deleted.at(it, List.get(&2, Merge.Node, prepare, at), deleted(more, prepare, 1n+at, rev), at, rev)

def op.fault(op: Ops.Op, +prepare: List<&2, Merge.Node>, +length: Nat, +rev: String) -> Maybe<&2, String>:
  match op:
    case Ops.Op{Ops.Delete{}, +at, +items}:
      +end = Nat.add(at, List.length(&2, Ops.Item, items))
      Bool.pick(Maybe<&2, String>, Nat.is_gt(end, length), Some{OUT_OF_RANGE(rev, end, length)}, deleted(items, prepare, at, rev))
    case Ops.Op{Ops.Insert{}, +at, items}:
      Bool.pick(Maybe<&2, String>, Nat.is_gt(at, length), Some{OUT_OF_RANGE(rev, at, length)}, None{})

def ops.fault(ops: List<&2, Ops.Op>, +prepare: List<&2, Merge.Node>, +rev: String) -> Maybe<&2, String>:
  match ops:
    case Nil{}:
      None{}
    case op <> rest:
      Maybe.or(&2, String, op.fault(op, prepare, List.length(&2, Merge.Node, prepare), rev), ops.fault(rest, prepare, rev))

# A resolution
# ------------

# Each `keep` a resolution states, one name at a time, beside the events
# that minted under its document: `merge.rs` consumes the next element
# standing under each name, and refuses where none is left.
type One is Data:
  One{document: String, item: Nat, authors: List<&2, Nat>}

def ones.run(count: Nat, +d: String, +first: Nat, +authors: List<&2, Nat>, rest: List<&2, One>) -> List<&2, One>:
  match count:
    case 0n:
      rest
    case 1n+c:
      One{d, first, authors} <> ones.run(c, d, 1n+first, authors, rest)

def ones(ps: List<&2, Res.Piece>, parts: List<&2, Merge.Part>) -> List<&2, One>:
  match ps parts:
    case Res.Piece.Keep{+d, +first, count} <> pr Merge.Kept{+authors, f, c} <> rest:
      ones.run(count, d, first, authors, ones(pr, rest))
    case Res.Piece.Insert{its} <> pr Merge.Own{its2} <> rest:
      ones(pr, rest)
    case _ _:
      Nil{}

def one.missing(found: Maybe<&2, Merge.Name>, o: One, +rev: String) -> Maybe<&2, String>:
  match found o:
    case None{} One{d, item, authors}:
      Some{UNKNOWN(rev, d, item)}
    case Some{nm} o2:
      None{}

def one.kept(found: Maybe<&2, Merge.Name>, kept: List<&2, Merge.Name>) -> List<&2, Merge.Name>:
  match found:
    case None{}:
      kept
    case Some{nm}:
      nm <> kept

def ones.fault(os: List<&2, One>, +P: List<&2, Merge.Node>, +kept: List<&2, Merge.Name>, +rev: String) -> Maybe<&2, String>:
  match os:
    case Nil{}:
      None{}
    case One{+d, +item, +authors} <> rest:
      +found = Merge.res.find(P, authors, item, kept)
      Maybe.or(&2, String, one.missing(found, One{d, item, authors}, rev), ones.fault(rest, P, one.kept(found, kept), rev))

# The walk, again
# ---------------

# What went wrong with one event the walk could not step, on its view.
def event.fault(ev: Maybe<&2, Merge.Rev>, +t: List<&2, Merge.Node>, +rev: String, ps: Maybe<&2, List<&2, Res.Piece>>) -> Maybe<&2, String>:
  match ev:
    case Some{Merge.Rev{+seen, Some{Merge.Edits{ops}}}}:
      ops.fault(ops, Merge.visible(Merge.restrict(t, seen)), rev)
    case Some{Merge.Rev{+seen, Some{Merge.Resolves{parts}}}}:
      ones.fault(ones(Maybe.default(&2, List<&2, Res.Piece>, ps, Nil{}), parts), Merge.visible(Merge.restrict(t, seen)), Nil{}, rev)
    case _:
      None{}

def flat(m: Maybe<&2, Maybe<&2, List<&2, Res.Piece>>>) -> Maybe<&2, List<&2, Res.Piece>>:
  match m:
    case None{}:
      None{}
    case Some{x}:
      x

def fault.at(stepped: Maybe<&2, List<&2, Merge.Node>>, ev: Maybe<&2, Merge.Rev>, +t: List<&2, Merge.Node>, +rev: String, ps: Maybe<&2, List<&2, Res.Piece>>) -> Maybe<&2, String>:
  match stepped:
    case None{}:
      event.fault(ev, t, rev, ps)
    case Some{t2}:
      None{}

def fault.go(o: List<&2, Nat>, +g: List<&2, Merge.Rev>, +names: List<&2, String>, +pieces: List<&2, Maybe<&2, List<&2, Res.Piece>>>, mt: Maybe<&2, List<&2, Merge.Node>>) -> Maybe<&2, String>:
  match o mt:
    case Nil{} _:
      None{}
    case e <> rest None{}:
      None{}
    case +e <> rest Some{+t}:
      +ev = List.get(&2, Merge.Rev, g, e)
      +stepped = Merge.step(ev, t, e)
      Maybe.or(&2, String, fault.at(stepped, ev, t, name_at(names, e), flat(List.get(&2, Maybe<&2, List<&2, Res.Piece>>, pieces, e))), fault.go(rest, g, names, pieces, stepped))

# Why the walk of `g` in order `o` refused: `names` are the events'
# revisions and `pieces` what each resolution among them stated, by the
# digest of the document each `keep` names.
def fault(+o: List<&2, Nat>, +g: List<&2, Merge.Rev>, +names: List<&2, String>, +pieces: List<&2, Maybe<&2, List<&2, Res.Piece>>>) -> Maybe<&2, String>:
  fault.go(o, g, names, pieces, Some{Nil{}})
