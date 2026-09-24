# What stands in for a document whose bytes were destroyed: decisions 0014,
# 0050 and 0066, as a reader meets them.
#
# A revision's `edit`, `text` or `bytes` line still names the digest a
# forgetting destroyed, and what the store holds instead is a document of
# its own, stored under its own digest and saying which one it `forgets`.
# It is written in the grammar of what it stands in for: an operation
# document keeping every operation, position, count and terminator and
# `\ forgotten` where each destroyed item's text was (0014); a resolution
# keeping every `keep` and each `insert` at its own length (0050); or, for a
# payload of bytes, which has no items, two headers — the digest and how
# many bytes it held (0066).
#
# Several may stand for one digest, since replicas redact independently, and
# decision 0014's rule reads them together: an item is forgotten if any of
# them forgets it. The first of a grammar is the shape, and one whose shape
# disagrees with it is set aside rather than merged, as the Rust reader's
# `stand_in` does. `Store.fetch` brings them; this says what they mean.

import Base
import ./text.bend as T
import ./ops.bend as Ops
import ./resolution.bend as Res
import ./store.bend as Store

# A payload forgotten
# -------------------

# Decision 0066's document: the payload whose bytes were destroyed, and how
# many there were, spelled as the format spells a count.
type Payload is Data:
  Payload{forgets: String, length: String}

def payload.write(p: Payload) -> String:
  match p:
    case Payload{f, n}:
      "historica\nforgets " ++ f ++ "\nlength " ++ n ++ "\n"

def payload.fields(pre: Bool, f: Maybe<&2, String>, n: Maybe<&2, String>) -> Maybe<&2, Payload>:
  match pre f n:
    case True{} Some{+d} Some{+k}:
      Bool.pick(Maybe<&2, Payload>, Bool.and(T.is_digest(d), Maybe.is_some(&2, Nat, T.number(k))), Some{Payload{d, k}}, None{})
    case _ _ _:
      None{}

# Read as strictly as the Rust reader reads one: the preamble, `forgets` and
# a digest, `length` and a canonical count, every line terminated, nothing
# else and nothing after — so the one spelling it takes is the one written.
def payload.of(ls: List<&2, T.Line>) -> Maybe<&2, Payload>:
  match ls:
    case T.Line{+p, True{}} <> T.Line{+f, True{}} <> T.Line{+n, True{}} <> Nil{}:
      payload.fields(T.same(p, "historica"), T.strip_prefix(f, "forgets "), T.strip_prefix(n, "length "))
    case _:
      None{}

def payload.parse(s: String) -> Maybe<&2, Payload>:
  payload.of(T.lines(s))

# Shape, and the union of redactions
# ----------------------------------

# Two runs of items have one shape where they are as many, each terminated
# alike: text is the one thing a forgetting may change.
def items.shape(a: List<&2, Ops.Item>, b: List<&2, Ops.Item>) -> Bool:
  match a b:
    case Nil{} Nil{}:
      True{}
    case Ops.Item{t1, n1, f1} <> ra Ops.Item{t2, n2, f2} <> rb:
      Bool.and(Bool.not(Bool.xor(n1, n2)), items.shape(ra, rb))
    case _ _:
      False{}

def ops.shape(a: List<&2, Ops.Op>, b: List<&2, Ops.Op>) -> Bool:
  match a b:
    case Nil{} Nil{}:
      True{}
    case Ops.Op{k1, +at1, i1} <> ra Ops.Op{k2, +at2, i2} <> rb:
      Bool.and(Ops.verb_is(k1, k2), Bool.and(Nat.is_eq(at1, at2), Bool.and(items.shape(i1, i2), ops.shape(ra, rb))))
    case _ _:
      False{}

# An item stays as it is held unless the other says it is forgotten; then
# its text goes and its terminator stays.
def item.union(held: Ops.Item, stated: Ops.Item) -> Ops.Item:
  match held stated:
    case Ops.Item{t, n, f} Ops.Item{t2, n2, True{}}:
      Ops.Item{SNil{}, n, True{}}
    case Ops.Item{t, n, f} Ops.Item{t2, n2, False{}}:
      Ops.Item{t, n, f}

def items.union(held: List<&2, Ops.Item>, stated: List<&2, Ops.Item>) -> List<&2, Ops.Item>:
  match held stated:
    case h <> hs s <> ss:
      item.union(h, s) <> items.union(hs, ss)
    case hs _:
      hs

def ops.union(held: List<&2, Ops.Op>, stated: List<&2, Ops.Op>) -> List<&2, Ops.Op>:
  match held stated:
    case Ops.Op{k, at, hi} <> hs Ops.Op{k2, at2, si} <> ss:
      Ops.Op{k, at, items.union(hi, si)} <> ops.union(hs, ss)
    case hs _:
      hs

def ops.fold.of(+forgets: Maybe<&2, String>, +result: Maybe<&2, String>, +held: List<&2, Ops.Op>, stated: List<&2, Ops.Op>, same: Bool) -> Ops.Doc:
  match same:
    case True{}:
      Ops.Doc{forgets, result, ops.union(held, stated)}
    case False{}:
      Ops.Doc{forgets, result, held}

def ops.fold.one(base: Ops.Doc, d: Ops.Doc) -> Ops.Doc:
  match base d:
    case Ops.Doc{+f, +r, +held} Ops.Doc{f2, r2, +stated}:
      ops.fold.of(f, r, held, stated, ops.shape(held, stated))

# Decision 0014's union rule over one grammar: the first document is the
# shape, and every one of the same shape forgets into it.
def ops.fold(ds: List<&2, Ops.Doc>, base: Ops.Doc) -> Ops.Doc:
  match ds:
    case Nil{}:
      base
    case d <> rest:
      ops.fold(rest, ops.fold.one(base, d))

# A resolution's shape: each `keep` the same reference, each `insert` the
# same run of terminators (decision 0050).
def piece.shape(a: Res.Piece, b: Res.Piece) -> Bool:
  match a b:
    case Res.Piece.Keep{d1, +f1, +c1} Res.Piece.Keep{d2, +f2, +c2}:
      Bool.and(String.eq(d1, d2), Bool.and(Nat.is_eq(f1, f2), Nat.is_eq(c1, c2)))
    case Res.Piece.Insert{i1} Res.Piece.Insert{i2}:
      items.shape(i1, i2)
    case _ _:
      False{}

def pieces.shape(a: List<&2, Res.Piece>, b: List<&2, Res.Piece>) -> Bool:
  match a b:
    case Nil{} Nil{}:
      True{}
    case p <> ra q <> rb:
      Bool.and(piece.shape(p, q), pieces.shape(ra, rb))
    case _ _:
      False{}

def piece.union(held: Res.Piece, stated: Res.Piece) -> Res.Piece:
  match held stated:
    case Res.Piece.Insert{hi} Res.Piece.Insert{si}:
      Res.Piece.Insert{items.union(hi, si)}
    case h _:
      h

def pieces.union(held: List<&2, Res.Piece>, stated: List<&2, Res.Piece>) -> List<&2, Res.Piece>:
  match held stated:
    case h <> hs s <> ss:
      piece.union(h, s) <> pieces.union(hs, ss)
    case hs _:
      hs

def res.fold.of(+forgets: Maybe<&2, String>, +result: Maybe<&2, String>, +held: List<&2, Res.Piece>, stated: List<&2, Res.Piece>, same: Bool) -> Res.Doc:
  match same:
    case True{}:
      Res.Doc{forgets, result, pieces.union(held, stated)}
    case False{}:
      Res.Doc{forgets, result, held}

def res.fold.one(base: Res.Doc, d: Res.Doc) -> Res.Doc:
  match base d:
    case Res.Doc{+f, +r, +held} Res.Doc{f2, r2, +stated}:
      res.fold.of(f, r, held, stated, pieces.shape(held, stated))

def res.fold(ds: List<&2, Res.Doc>, base: Res.Doc) -> Res.Doc:
  match ds:
    case Nil{}:
      base
    case d <> rest:
      res.fold(rest, res.fold.one(base, d))

# Which documents stand in for a digest
# -------------------------------------

def forgets.is(f: Maybe<&2, String>, +d: String) -> Bool:
  match f:
    case None{}:
      False{}
    case Some{x}:
      String.eq(x, d)

def ops.standing.one(+d: String, r: Result<&2, &2, String, Ops.Doc>, rest: List<&2, Ops.Doc>) -> List<&2, Ops.Doc>:
  match r:
    case Fail{e}:
      rest
    case Done{Ops.Doc{+f, r2, ops}}:
      List.filter.put(Ops.Doc, Ops.Doc{f, r2, ops}, rest, forgets.is(f, d))

# The operation documents among these that forget `d`, in the order given.
def ops.standing(ds: List<&2, Store.Doc>, +d: String) -> List<&2, Ops.Doc>:
  match ds:
    case Nil{}:
      Nil{}
    case Store.Doc{p, i, n, t} <> rest:
      ops.standing.one(d, Ops.parse(t), ops.standing(rest, d))

def res.standing.one(+d: String, r: Result<&2, &2, String, Res.Doc>, rest: List<&2, Res.Doc>) -> List<&2, Res.Doc>:
  match r:
    case Fail{e}:
      rest
    case Done{Res.Doc{+f, r2, ps}}:
      List.filter.put(Res.Doc, Res.Doc{f, r2, ps}, rest, forgets.is(f, d))

def res.parsed(+t: String, resolution: Bool) -> Result<&2, &2, String, Res.Doc>:
  match resolution:
    case True{}:
      Res.parse(t)
    case False{}:
      Fail{"not a resolution"}

# The resolutions among these that forget `d`, in the order given.
def res.standing(ds: List<&2, Store.Doc>, +d: String) -> List<&2, Res.Doc>:
  match ds:
    case Nil{}:
      Nil{}
    case Store.Doc{p, i, n, +t} <> rest:
      res.standing.one(d, res.parsed(t, Res.is_resolution(t)), res.standing(rest, d))

# The first payload stand-in for `d`, and its own digest: two replicas that
# forget one payload write one file, so the first says what all of them do.
type Stood is Data:
  Stood{doc: Payload, id: String}

def payload.hit(+d: String, +i: String, m: Maybe<&2, Payload>, rest: Maybe<&2, Stood>) -> Maybe<&2, Stood>:
  match m:
    case None{}:
      rest
    case Some{Payload{+f, n}}:
      Bool.pick(Maybe<&2, Stood>, String.eq(f, d), Some{Stood{Payload{f, n}, i}}, rest)

def payload.standing(ds: List<&2, Store.Doc>, +d: String) -> Maybe<&2, Stood>:
  match ds:
    case Nil{}:
      None{}
    case Store.Doc{p, +i, n, t} <> rest:
      payload.hit(d, i, payload.parse(t), payload.standing(rest, d))

# What a digest names
# -------------------

# What a reader consumes for a digest a revision names: the document the
# store holds under it, or, where there is none, what stands in for it —
# the operation documents first, then the resolutions, then a payload's two
# headers, the order the Rust reader asks in.
type Found is Data:
  Found.Held{text: String}
  Found.Ops{doc: Ops.Doc}
  Found.Res{doc: Res.Doc}
  Found.Payload{stood: Stood}
  Found.Absent{}

def held(ds: List<&2, Store.Doc>, +id: String) -> Maybe<&2, String>:
  match ds:
    case Nil{}:
      None{}
    case Store.Doc{path, +i, size, text} <> rest:
      Bool.pick(Maybe<&2, String>, String.starts_with(i, id), Some{text}, held(rest, id))

def found.payload(m: Maybe<&2, Stood>) -> Found:
  match m:
    case None{}:
      Found.Absent{}
    case Some{s}:
      Found.Payload{s}

def found.res(+ds: List<&2, Store.Doc>, +d: String, rs: List<&2, Res.Doc>) -> Found:
  match rs:
    case Nil{}:
      found.payload(payload.standing(ds, d))
    case +r <> rest:
      Found.Res{res.fold(r <> rest, r)}

def found.ops(+ds: List<&2, Store.Doc>, +d: String, os: List<&2, Ops.Doc>) -> Found:
  match os:
    case Nil{}:
      found.res(ds, d, res.standing(ds, d))
    case +o <> rest:
      Found.Ops{ops.fold(o <> rest, o)}

def found.of(+ds: List<&2, Store.Doc>, +d: String, h: Maybe<&2, String>) -> Found:
  match h:
    case Some{t}:
      Found.Held{t}
    case None{}:
      found.ops(ds, d, ops.standing(ds, d))

def found(+ds: List<&2, Store.Doc>, +d: String) -> Found:
  found.of(ds, d, held(ds, d))

# The text a reader of an `edit` — or of a `keep` — consumes: the held
# document, or the stand-ins' union written in their grammar. Nothing for a
# payload's stand-in, which states no items for either to read.
def text.of(f: Found) -> Maybe<&2, String>:
  match f:
    case Found.Held{t}:
      Some{t}
    case Found.Ops{doc}:
      Some{Ops.write(doc)}
    case Found.Res{doc}:
      Some{Res.write(doc)}
    case _:
      None{}

def text(+ds: List<&2, Store.Doc>, +d: String) -> Maybe<&2, String>:
  text.of(found(ds, d))

def ops.forgets(r: Result<&2, &2, String, Ops.Doc>) -> Maybe<&2, String>:
  match r:
    case Fail{e}:
      None{}
    case Done{Ops.Doc{f, r2, ops}}:
      f

def res.forgets(r: Result<&2, &2, String, Res.Doc>) -> Maybe<&2, String>:
  match r:
    case Fail{e}:
      None{}
    case Done{Res.Doc{f, r2, ps}}:
      f

def payload.forgets(m: Maybe<&2, Payload>) -> Maybe<&2, String>:
  match m:
    case None{}:
      None{}
    case Some{Payload{f, n}}:
      Some{f}

# What one document is to a digest `show` was asked for: nothing, one of the
# operation documents or resolutions standing in for it, or a payload's.
type Taken is Data:
  Taken.Other{}
  Taken.Stands{}
  Taken.Payload{}

def kind.of(says: Bool, stands: Bool, payload: Bool) -> Taken:
  match says stands payload:
    case True{} True{} _:
      Taken.Stands{}
    case True{} False{} True{}:
      Taken.Payload{}
    case _ _ _:
      Taken.Other{}

# Asked of its header first, which is cheap, and then of its grammar.
def kind(+t: String, +d: String) -> Taken:
  kind.of(Store.stands_for(t, [d]), Bool.or(forgets.is(ops.forgets(Ops.parse(t)), d), forgets.is(res.forgets(res.parsed(t, Res.is_resolution(t))), d)), forgets.is(payload.forgets(payload.parse(t)), d))

def kind.taken(k: Taken, seen: Bool) -> Bool:
  match k:
    case Taken.Stands{}:
      True{}
    case Taken.Payload{}:
      Bool.not(seen)
    case Taken.Other{}:
      False{}

def kind.seen(k: Taken, seen: Bool) -> Bool:
  match k:
    case Taken.Payload{}:
      True{}
    case _:
      seen

# Every document standing in for `d`, whole, in the order given; of the
# payload stand-ins only the first, since two replicas that forget one
# payload write one file.
def shown.go(ds: List<&2, Store.Doc>, +d: String, +seen: Bool) -> String:
  match ds:
    case Nil{}:
      SNil{}
    case Store.Doc{p, i, n, +t} <> rest:
      +k = kind(t, d)
      Bool.pick(String, kind.taken(k, seen), t, SNil{}) ++ shown.go(rest, d, kind.seen(k, seen))

def nonempty(s: String) -> Maybe<&2, String>:
  match s:
    case SNil{}:
      None{}
    case SCon{c, rest}:
      Some{SCon{c, rest}}

def shown.of(+ds: List<&2, Store.Doc>, +d: String, h: Maybe<&2, String>) -> Maybe<&2, String>:
  match h:
    case Some{t}:
      Some{t}
    case None{}:
      nonempty(shown.go(ds, d, False{}))

# What `show` prints for a digest: the held document, byte for byte, or
# every document standing in for it — each a real file of the store, so
# each is printed, as the Rust tool prints them. Nothing where there is
# neither.
def shown(+ds: List<&2, Store.Doc>, +d: String) -> Maybe<&2, String>:
  shown.of(ds, d, held(ds, d))

# What that is made of, stated without the grammars: the texts of some of
# these documents, whole and in order, each saying in its first header that
# it `forgets` the digest named. `LAWS.show_prints_what_the_revision_states`
# holds `shown` to it.
def made_of(ds: List<&2, Store.Doc>, +d: String, +text: String) -> Bool:
  match ds:
    case Nil{}:
      String.is_empty(text)
    case Store.Doc{p, i, n, +t} <> +rest:
      Bool.or(Bool.and(Bool.and(Store.stands_for(t, [d]), String.starts_with(text, t)), made_of(rest, d, String.drop(text, String.length(t)))), made_of(rest, d, text))
