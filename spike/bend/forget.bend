# `forget <target> <path> [--lines <first>..<last>] [--dry-run] [--fields]`:
# destroying what a store holds of some of one file, and keeping its shape.
#
# Decision 0014: an operation's arithmetic and its payload are different
# bytes, and only the payload goes. A forgetting document states the same
# operations, at the same positions, with the same counts and terminators,
# and `\ forgotten` where each destroyed item's text was; it is stored under
# its own digest, names in a `forgets` header the digest it stands in for,
# and the original is destroyed. An item forgotten once is forgotten wherever
# it is quoted — the document that wrote it, and every delete that quotes it
# back — so the command is a walk over the file's history: the merge walk,
# read for who wrote each element and which deletes quote it. Decision 0050
# carries that into a merge's resolution, which forgets in its own grammar,
# and makes a line a resolution copied while moving it go with the line.
# Decision 0066 is the other extent: a payload of bytes has no items and no
# shape, so it goes whole, and two headers stand where it was.
#
# What is decided — the span, the items, the documents written, the files
# destroyed and every refusal — is a pure def here; the IO at the bottom
# reads the store, files each document through `Store.once`, destroys each
# original and each copy in `cache/` through `Store.remove`, and says so.

import Base
import ./text.bend as T
import ./ops.bend as Ops
import ./revision.bend as Rev
import ./store.bend as Store
import ./tree.bend as Tree
import ./bookmark.bend as Bm
import ./resolution.bend as Res
import ./merge.bend as Merge
import ./sha256.bend as Sha
import ./utf8.bend as Utf8
import ./standin.bend as Stand
import ./commands.bend as Main

# The command line
# ----------------

# A count, as Rust reads a `usize`, spelled back as Rust prints one: an
# optional `+`, then digits, leading zeros dropped; nothing past a `usize`.
def usize.of(+ds: String) -> Maybe<&2, String>:
  +n = String.length(ds)
  Bool.pick(Maybe<&2, String>, Bool.or(Nat.is_gt(n, 20n), Bool.and(Nat.is_eq(n, 20n), String.is_lt("18446744073709551615", ds))), None{}, Some{ds})

def usize(+v: String) -> Maybe<&2, String>:
  +ds = Maybe.default(&2, String, T.strip_prefix(v, "+"), v)
  Bool.pick(Maybe<&2, String>, Bool.and(Bool.not(String.is_empty(ds)), T.all_chars(~(c => Char.is_digit(c)), ds)), usize.of(Main.count.zeros(ds)), None{})

# Two counts so spelled, compared as numbers: the longer is the greater,
# and one length compares as the digits do.
def usize.lt(+a: String, +b: String) -> Bool:
  Bool.or(Nat.is_lt(String.length(a), String.length(b)), Bool.and(Nat.is_eq(String.length(a), String.length(b)), String.is_lt(a, b)))

# The first and last line a span names, each as a count so spelled.
type FgSpan is Data:
  Fg.Span{first: String, last: String}

# A string cut at its first `..`: what is before it and what is after.
def cut.go(s: String, +acc: String, here: Bool) -> Maybe<&2, T.Split>:
  match s here:
    case +x True{}:
      Some{T.Split{String.reverse(acc), String.drop(x, 2n)}}
    case SNil{} False{}:
      None{}
    case SCon{c, +rest} False{}:
      cut.go(rest, SCon{c, acc}, String.starts_with(rest, ".."))

def span.pair(a: Maybe<&2, String>, b: Maybe<&2, String>) -> Result<&2, &2, Main.Refused, FgSpan>:
  match a b:
    case Some{x} Some{y}:
      Done{Fg.Span{x, y}}
    case _ _:
      Fail{Main.Refused{2, "a span is `<first>..<last>`, or one line number"}}

def span.of(+s: String, cut: Maybe<&2, T.Split>) -> Result<&2, &2, Main.Refused, FgSpan>:
  match cut:
    case Some{T.Split{+a, +b}}:
      span.pair(usize(a), usize(b))
    case None{}:
      span.pair(usize(s), usize(s))

# A span of lines, as `--lines` spells it: `<first>..<last>`, or one line.
def span.r(+s: String) -> Result<&2, &2, Main.Refused, FgSpan>:
  span.of(s, cut.go(s, SNil{}, String.starts_with(s, "..")))

# What the arguments said, read a word at a time: the span's spelling, a
# dry run, `--fields`, the other words in order, and whether the word just
# read was `--lines`, which takes the next one whatever it is.
type FgReading is Data:
  Fg.Reading{lines: Maybe<&2, String>, dry: Bool, fields: Bool, words: List<&2, String>, wants: Bool}

type FgWord is Data:
  Fg.Lines{}
  Fg.Dry{}
  Fg.Fields{}
  Fg.Flag{}
  Fg.Plain{}

def word(+w: String) -> FgWord:
  Bool.pick(FgWord, String.eq(w, "--lines"), Fg.Lines{},
  Bool.pick(FgWord, Bool.or(String.eq(w, "-n"), String.eq(w, "--dry-run")), Fg.Dry{},
  Bool.pick(FgWord, String.eq(w, "--fields"), Fg.Fields{},
  Bool.pick(FgWord, String.starts_with(w, "-"), Fg.Flag{}, Fg.Plain{}))))

def reading.word(r: FgReading, +w: String, k: FgWord) -> Result<&2, &2, Main.Refused, FgReading>:
  match r k:
    case Fg.Reading{l, d, f, ws, x} Fg.Lines{}:
      Done{Fg.Reading{l, d, f, ws, True{}}}
    case Fg.Reading{l, d, f, ws, x} Fg.Dry{}:
      Done{Fg.Reading{l, True{}, f, ws, False{}}}
    case Fg.Reading{l, d, f, ws, x} Fg.Fields{}:
      Done{Fg.Reading{l, d, True{}, ws, False{}}}
    case Fg.Reading{l, d, f, ws, x} Fg.Flag{}:
      Fail{Main.Refused{2, "`" ++ w ++ "` is not an argument `forget` takes"}}
    case Fg.Reading{l, d, f, ws, x} Fg.Plain{}:
      Done{Fg.Reading{l, d, f, List.append(&2, String, ws, [w]), False{}}}

def reading.step(r: FgReading, +w: String) -> Result<&2, &2, Main.Refused, FgReading>:
  match r:
    case Fg.Reading{l, d, f, ws, True{}}:
      Done{Fg.Reading{Some{w}, d, f, ws, False{}}}
    case Fg.Reading{l, d, f, ws, False{}}:
      reading.word(Fg.Reading{l, d, f, ws, False{}}, w, word(w))

def reading.go(ws: List<&2, String>, r: Result<&2, &2, Main.Refused, FgReading>) -> Result<&2, &2, Main.Refused, FgReading>:
  match ws:
    case Nil{}:
      r
    case +w <> rest:
      reading.go(rest, Result.bind(&2, &2, Main.Refused, FgReading, FgReading, r, x => reading.step(x, w)))

# The words of a command line read plainly: every flag `forget` knows set
# aside, and the word after `--lines`, whatever it is, with it; the rest in
# order. `wants` is whether the word before was `--lines`.
# `LAWS.forget_reads_its_words` holds `asked.r` to it.
def plain.pick(wants: Bool, k: FgWord, +w: String, on: List<&2, String>, off: List<&2, String>) -> List<&2, String>:
  match wants k:
    case True{} _:
      off
    case False{} Fg.Lines{}:
      on
    case False{} Fg.Plain{}:
      w <> off
    case False{} _:
      off

def plain(ws: List<&2, String>, wants: Bool) -> List<&2, String>:
  match ws:
    case Nil{}:
      Nil{}
    case +w <> +rest:
      plain.pick(wants, word(w), w, plain(rest, True{}), plain(rest, False{}))

# What `forget` was asked: a revision, a path, the span if one was named,
# a dry run, and `--fields`.
type FgAsked is Data:
  Fg.Asked{target: String, path: String, span: Maybe<&2, FgSpan>, dry: Bool, fields: Bool}

def asked.span(lines: Maybe<&2, String>) -> Result<&2, &2, Main.Refused, Maybe<&2, FgSpan>>:
  match lines:
    case None{}:
      Done{None{}}
    case Some{+s}:
      Result.map(&2, &2, Main.Refused, FgSpan, Maybe<&2, FgSpan>, x => Some{x}, span.r(s))

def asked.words(lines: Maybe<&2, String>, +dry: Bool, +fields: Bool, words: List<&2, String>) -> Result<&2, &2, Main.Refused, FgAsked>:
  match words:
    case Nil{}:
      Fail{Main.Refused{2, "`forget` wants a revision to read the span at"}}
    case t <> Nil{}:
      Fail{Main.Refused{2, "`forget` wants a path"}}
    case t <> p <> extra <> more:
      Fail{Main.Refused{2, "`forget` takes a target and one path, and `" ++ extra ++ "` is a third argument"}}
    case +t <> +p <> Nil{}:
      Result.map(&2, &2, Main.Refused, Maybe<&2, FgSpan>, FgAsked, sp => Fg.Asked{t, p, sp, dry, fields}, asked.span(lines))

def asked.read(r: FgReading) -> Result<&2, &2, Main.Refused, FgAsked>:
  match r:
    case Fg.Reading{l, d, f, ws, True{}}:
      Fail{Main.Refused{2, "`--lines` wants a span, as `<first>..<last>`"}}
    case Fg.Reading{l, True{}, True{}, ws, False{}}:
      Fail{Main.Refused{2, "`forget --dry-run --fields` is refused: `--fields` states what is on disk, and a plan is not on disk. ask for one or the other"}}
    case Fg.Reading{l, +d, +f, ws, False{}}:
      asked.words(l, d, f, ws)

# `forget`'s arguments read as the Rust tool reads them: every flag in
# order, the first that is wrong refusing, `--lines` taking the word after
# it and the last one counting; then a dry run with `--fields` refused, the
# target, the path and nothing more, and the span.
def asked.r(ws: List<&2, String>) -> Result<&2, &2, Main.Refused, FgAsked>:
  do Result<&2, &2, Main.Refused, FgAsked>:
    r : FgReading <- reading.go(ws, Done{Fg.Reading{None{}, False{}, False{}, Nil{}, False{}}})
    asked.read(r)

# The walk, read for what forgetting needs
# ----------------------------------------

# A delete quoting an element: the element, and the event and the item of
# its document that quote it.
type FgMark is Data:
  Fg.Mark{name: Merge.Name, by: Nat, op: Nat, item: Nat}

def marks.at(found: Maybe<&2, Merge.Node>, +e: Nat, +op: Nat, +j: Nat, rest: List<&2, FgMark>) -> List<&2, FgMark>:
  match found:
    case None{}:
      rest
    case Some{n}:
      Fg.Mark{Merge.Node.name(n), e, op, j} <> rest

def marks.items(items: List<&2, Ops.Item>, +P: List<&2, Merge.Node>, +e: Nat, +op: Nat, +at: Nat, +j: Nat) -> List<&2, FgMark>:
  match items:
    case Nil{}:
      Nil{}
    case it <> rest:
      marks.at(List.get(&2, Merge.Node, P, Nat.add(at, j)), e, op, j, marks.items(rest, P, e, op, at, 1n+j))

# Each delete's items, against the view its author counted into: the
# element at its position plus its offset, as `merge.rs` reads `prepare`.
def marks.ops(ops: List<&2, Ops.Op>, +P: List<&2, Merge.Node>, +e: Nat, +op: Nat) -> List<&2, FgMark>:
  match ops:
    case Nil{}:
      Nil{}
    case Ops.Op{Ops.Delete{}, +at, items} <> rest:
      List.append(&2, FgMark, marks.items(items, P, e, op, at, 0n), marks.ops(rest, P, e, 1n+op))
    case Ops.Op{Ops.Insert{}, at, items} <> rest:
      marks.ops(rest, P, e, 1n+op)

def marks.of(ev: Maybe<&2, Merge.Rev>, +t: List<&2, Merge.Node>, +e: Nat) -> List<&2, FgMark>:
  match ev:
    case Some{Merge.Rev{+seen, Some{Merge.Edits{ops}}}}:
      marks.ops(ops, Merge.visible(Merge.restrict(t, seen)), e, 0n)
    case _:
      Nil{}

# The walk `commands.bend` reads a merge by, with each event's delete
# quotes taken from its view before it is applied.
type FgWalking is Data:
  Fg.Walking{tree: Maybe<&2, List<&2, Merge.Node>>, marks: List<&2, FgMark>}

def walking.step(w: FgWalking, +ev: Maybe<&2, Merge.Rev>, +e: Nat) -> FgWalking:
  match w:
    case Fg.Walking{None{}, ms}:
      Fg.Walking{None{}, ms}
    case Fg.Walking{Some{+t}, ms}:
      Fg.Walking{Merge.step(ev, t, e), List.append(&2, FgMark, ms, marks.of(ev, t, e))}

def walking(o: List<&2, Nat>, +g: List<&2, Merge.Rev>, w: FgWalking) -> FgWalking:
  match o:
    case Nil{}:
      w
    case +e <> rest:
      walking(rest, g, walking.step(w, List.get(&2, Merge.Rev, g, e), e))

# One element, as `merge::quotes` reports it: the revision that wrote it and
# the operation and item of its document that did; its text; each delete
# quoting it; each revision that dropped it without quoting — a resolution,
# stating what survives; whether its text is already destroyed; whether it
# still stands.
type FgQuote is Data:
  Fg.Quote{by: String, op: Nat, item: Nat}

type FgQuoted is Data:
  Fg.Quoted{by: String, op: Nat, item: Nat, text: String, deletes: List<&2, FgQuote>, dropped: List<&2, String>, forgotten: Bool, visible: Bool}

# Where in its author's document the element minted `m`-th was written:
# the operation, counting every operation, and the item within it; for a
# resolution, the piece and the item.
def wrote.ops(ops: List<&2, Ops.Op>, +k: Nat, +i: Nat) -> Nat & Nat:
  match ops:
    case Nil{}:
      (i, k)
    case Ops.Op{Ops.Insert{}, at, +items} <> rest:
      Bool.pick(Nat & Nat, Nat.is_lt(k, List.length(&2, Ops.Item, items)), (i, k), wrote.ops(rest, Nat.sub(k, List.length(&2, Ops.Item, items)), 1n+i))
    case Ops.Op{Ops.Delete{}, at, items} <> rest:
      wrote.ops(rest, k, 1n+i)

def wrote.parts(ps: List<&2, Merge.Part>, +k: Nat, +i: Nat) -> Nat & Nat:
  match ps:
    case Nil{}:
      (i, k)
    case Merge.Own{+items} <> rest:
      Bool.pick(Nat & Nat, Nat.is_lt(k, List.length(&2, Ops.Item, items)), (i, k), wrote.parts(rest, Nat.sub(k, List.length(&2, Ops.Item, items)), 1n+i))
    case Merge.Kept{a, f, c} <> rest:
      wrote.parts(rest, k, 1n+i)

def wrote(ev: Maybe<&2, Merge.Rev>, +m: Nat) -> Nat & Nat:
  match ev:
    case Some{Merge.Rev{p, Some{Merge.Edits{ops}}}}:
      wrote.ops(ops, m, 0n)
    case Some{Merge.Rev{p, Some{Merge.Resolves{parts}}}}:
      wrote.parts(parts, m, 0n)
    case _:
      (0n, m)

def resolves(ev: Maybe<&2, Merge.Rev>) -> Bool:
  match ev:
    case Some{Merge.Rev{p, Some{Merge.Resolves{parts}}}}:
      True{}
    case _:
      False{}

def name_of(+names: List<&2, String>, +e: Nat) -> String:
  Maybe.default(&2, String, List.get(&2, String, names, e), SNil{})

def quotes.of(ms: List<&2, FgMark>, +names: List<&2, String>, +nm: Merge.Name) -> List<&2, FgQuote>:
  match ms:
    case Nil{}:
      Nil{}
    case Fg.Mark{n, +e, op, item} <> rest:
      List.filter.put(FgQuote, Fg.Quote{name_of(names, e), op, item}, quotes.of(rest, names, nm), Merge.Name.eq(n, nm))

def dropped.of(ds: List<&2, Nat>, +names: List<&2, String>, +g: List<&2, Merge.Rev>) -> List<&2, String>:
  match ds:
    case Nil{}:
      Nil{}
    case +e <> rest:
      Rev.keep(resolves(List.get(&2, Merge.Rev, g, e)), name_of(names, e), dropped.of(rest, names, g))

def quoted.wrote(+by: String, w: Nat & Nat, it: Ops.Item, deletes: List<&2, FgQuote>, dropped: List<&2, String>, visible: Bool) -> FgQuoted:
  match w it:
    case (op, item) Ops.Item{t, n, f}:
      Fg.Quoted{by, op, item, t, deletes, dropped, f, visible}

def quoted.one(+g: List<&2, Merge.Rev>, +names: List<&2, String>, +ms: List<&2, FgMark>, n: Merge.Node) -> FgQuoted:
  match n:
    case Merge.Node{Merge.Name{+a, +m}, it, pl, +d}:
      quoted.wrote(name_of(names, a), wrote(List.get(&2, Merge.Rev, g, a), m), it, quotes.of(ms, names, Merge.Name{a, m}), dropped.of(d, names, g), List.is_empty(&2, Nat, d))

def quoted.all(ns: List<&2, Merge.Node>, +g: List<&2, Merge.Rev>, +names: List<&2, String>, +ms: List<&2, FgMark>) -> List<&2, FgQuoted>:
  match ns:
    case Nil{}:
      Nil{}
    case n <> rest:
      quoted.one(g, names, ms, n) <> quoted.all(rest, g, names, ms)

def quotes.walked(+g: List<&2, Merge.Rev>, +names: List<&2, String>, +head: String, +file: String, w: FgWalking) -> Result<&2, &2, String, List<&2, FgQuoted>>:
  match w:
    case Fg.Walking{None{}, ms}:
      Fail{head ++ ", file " ++ file ++ ": a revision behind it names a position or an item its author's view of the file does not hold; the document was recorded against a different history"}
    case Fg.Walking{Some{+t}, +ms}:
      Done{quoted.all(Merge.order(t), g, names, ms)}

def quotes.graph(+rs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +head: String, +file: String, seen: Result<&2, &2, Tree.Fault, List<&2, Tree.Seen>>) -> Result<&2, &2, String, List<&2, FgQuoted>>:
  match seen:
    case Fail{e}:
      Fail{head ++ ": " ++ Tree.fault_show(e)}
    case Done{+ss}:
      do Result<&2, &2, String, List<&2, FgQuoted>>:
        +g : List<&2, Merge.Rev> <- Main.walked.revs(rs, Main.ids(rs), Main.minted_digests(rs, file), ss, ds, file)
        quotes.walked(g, Main.ids(rs), head, file, walking(Main.walked.order(g), g, Fg.Walking{Some{Nil{}}, Nil{}}))

# Every element these revisions ever wrote to the file, in reading order,
# tombstones included: `rs` in digest order, the graph `walked` walks.
def quotes(+rs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +head: String, +file: String) -> Result<&2, &2, String, List<&2, FgQuoted>>:
  quotes.graph(rs, ds, head, file, Tree.seen(List.length(&2, Main.Full, rs), Main.events_of(rs), Nil{}))

def quoted.key(q: FgQuoted) -> String:
  match q:
    case Fg.Quoted{by, op, item, t, dl, dr, f, v}:
      by ++ " " ++ T.spell(op) ++ " " ++ T.spell(item)

def quoted.shown(q: FgQuoted) -> Bool:
  match q:
    case Fg.Quoted{by, op, item, t, dl, dr, f, v}:
      v

def quoted.visible(qs: List<&2, FgQuoted>) -> List<&2, FgQuoted>:
  match qs:
    case Nil{}:
      Nil{}
    case +q <> rest:
      List.filter.put(FgQuoted, q, quoted.visible(rest), quoted.shown(q))

def keys(qs: List<&2, FgQuoted>) -> List<&2, String>:
  match qs:
    case Nil{}:
      Nil{}
    case +q <> rest:
      quoted.key(q) <> keys(rest)

# Copies a resolution made
# ------------------------

# Decision 0050: a resolution cannot reorder what it keeps, so a line a
# person moved while resolving is dropped and minted again under the
# resolution's own name — the same text under a new name, which forgetting
# the original alone would leave legible at the head. So an element of the
# span a resolution dropped goes with an element the same resolution minted
# reading the same, and so on to a fixed point, since a later merge can copy
# the copy. Only that resolution's drops against its own mints: a line
# another revision typed again is a different item and stays one.
def copies.text(q: FgQuoted) -> String:
  match q:
    case Fg.Quoted{by, op, item, t, dl, dr, f, v}:
      t

def copies.by(q: FgQuoted) -> String:
  match q:
    case Fg.Quoted{by, op, item, t, dl, dr, f, v}:
      by

def copies.minted(cs: List<&2, FgQuoted>, +by: String, +text: String) -> List<&2, String>:
  match cs:
    case Nil{}:
      Nil{}
    case +c <> rest:
      Rev.keep(Bool.and(String.eq(copies.by(c), by), String.eq(copies.text(c), text)), quoted.key(c), copies.minted(rest, by, text))

def copies.dropped(ds: List<&2, String>, +every: List<&2, FgQuoted>, +text: String) -> List<&2, String>:
  match ds:
    case Nil{}:
      Nil{}
    case +by <> rest:
      List.append(&2, String, copies.minted(every, by, text), copies.dropped(rest, every, text))

def copies.of(+every: List<&2, FgQuoted>, +span: List<&2, String>, q: FgQuoted) -> List<&2, String>:
  match q:
    case Fg.Quoted{+by, +op, +item, +t, dl, +dr, False{}, v}:
      Bool.pick(List<&2, String>, Rev.member(span, quoted.key(Fg.Quoted{by, op, item, t, dl, dr, False{}, v})), copies.dropped(dr, every, t), Nil{})
    case Fg.Quoted{by, op, item, t, dl, dr, True{}, v}:
      Nil{}

def copies.step(qs: List<&2, FgQuoted>, +every: List<&2, FgQuoted>, +span: List<&2, String>) -> List<&2, String>:
  match qs:
    case Nil{}:
      Nil{}
    case q <> rest:
      List.append(&2, String, copies.of(every, span, q), copies.step(rest, every, span))

def copies.grown(more: List<&2, String>, +span: List<&2, String>) -> List<&2, String>:
  match more:
    case Nil{}:
      span
    case +k <> rest:
      copies.grown(rest, Bool.pick(List<&2, String>, Rev.member(span, k), span, List.append(&2, String, span, [k])))

def copies.go(fuel: Nat, +every: List<&2, FgQuoted>, +span: List<&2, String>) -> List<&2, String>:
  match fuel:
    case 0n:
      span
    case 1n+p:
      +next = copies.grown(copies.step(every, every, span), span)
      Bool.pick(List<&2, String>, Nat.is_eq(List.length(&2, String, next), List.length(&2, String, span)), span, copies.go(p, every, next))

def copies(+every: List<&2, FgQuoted>, +span: List<&2, String>) -> List<&2, String>:
  copies.go(1n+List.length(&2, FgQuoted, every), every, span)

# What goes, document by document
# -------------------------------

# One item a forgetting destroys: the document it is in, and the operation
# — or piece — and item there.
type FgPick is Data:
  Fg.Pick{target: String, op: Nat, item: Nat}

# The document each revision names for the file: its `edit`'s, or the
# payload its `text` states, which a quote's indices index into.
type FgNamed is Data:
  Fg.Named{by: String, document: String}

def named.of(+id: String, s: Main.Said, text: Bool, rest: List<&2, FgNamed>) -> List<&2, FgNamed>:
  match s text:
    case Main.Edited{d} _:
      Fg.Named{id, d} <> rest
    case Main.Whole{d} True{}:
      Fg.Named{id, d} <> rest
    case _ _:
      rest

def named(fs: List<&2, Main.Full>, +file: String) -> List<&2, FgNamed>:
  match fs:
    case Nil{}:
      Nil{}
    case +f <> rest:
      named.of(Main.id_of(f), Main.said(Main.facts_of(f), file), Main.is_text(Main.facts_of(f), file), named(rest, file))

# The documents themselves. `LAWS.forget_rewrites_only_the_files_documents`
# holds the plan's targets to them.
def named.docs(ns: List<&2, FgNamed>) -> List<&2, String>:
  match ns:
    case Nil{}:
      Nil{}
    case Fg.Named{b, d} <> rest:
      d <> named.docs(rest)

def named.find(ns: List<&2, FgNamed>, +by: String) -> Maybe<&2, String>:
  match ns:
    case Nil{}:
      None{}
    case Fg.Named{+b, d} <> rest:
      Bool.pick(Maybe<&2, String>, String.eq(b, by), Some{d}, named.find(rest, by))

def pick.if(found: Maybe<&2, String>, +op: Nat, +item: Nat, rest: List<&2, FgPick>) -> List<&2, FgPick>:
  match found:
    case None{}:
      rest
    case Some{d}:
      Fg.Pick{d, op, item} <> rest

def picks.deletes(qs: List<&2, FgQuote>, +ns: List<&2, FgNamed>) -> List<&2, FgPick>:
  match qs:
    case Nil{}:
      Nil{}
    case Fg.Quote{+by, +op, +item} <> rest:
      pick.if(named.find(ns, by), op, item, picks.deletes(rest, ns))

def picks.of(+ns: List<&2, FgNamed>, taken: Bool, q: FgQuoted) -> List<&2, FgPick>:
  match taken q:
    case True{} Fg.Quoted{+by, +op, +item, t, dl, dr, f, v}:
      pick.if(named.find(ns, by), op, item, picks.deletes(dl, ns))
    case False{} q2:
      Nil{}

# Every item of the span, where it was written and wherever a delete quotes
# it, and how many of them were already forgotten where they were written.
type FgPicked is Data:
  Fg.Picked{picks: List<&2, FgPick>, already: Nat}

def picked.join(+taken: Bool, +forgot: Bool, here: List<&2, FgPick>, rest: FgPicked) -> FgPicked:
  match rest:
    case Fg.Picked{ps, +n}:
      Fg.Picked{List.append(&2, FgPick, here, ps), Bool.pick(Nat, Bool.and(taken, forgot), 1n+n, n)}

def quoted.forgot(q: FgQuoted) -> Bool:
  match q:
    case Fg.Quoted{by, op, item, t, dl, dr, f, v}:
      f

def picked(qs: List<&2, FgQuoted>, +span: List<&2, String>, +ns: List<&2, FgNamed>) -> FgPicked:
  match qs:
    case Nil{}:
      Fg.Picked{Nil{}, 0n}
    case +q <> rest:
      +taken = Rev.member(span, quoted.key(q))
      picked.join(taken, quoted.forgot(q), picks.of(ns, taken, q), picked(rest, span, ns))

def targets.of(ps: List<&2, FgPick>) -> List<&2, String>:
  match ps:
    case Nil{}:
      Nil{}
    case Fg.Pick{d, op, item} <> rest:
      d <> targets.of(rest)

def targets(+ps: List<&2, FgPick>) -> List<&2, String>:
  Main.distinct(List.sort(~String, ~(a => b => String.is_le(a, b)), targets.of(ps)))

# Whether item `j` of operation `i` of `target` is one to forget.
def picked.has(ps: List<&2, FgPick>, +target: String, +i: Nat, +j: Nat) -> Bool:
  match ps:
    case Nil{}:
      False{}
    case Fg.Pick{+d, +op, +item} <> rest:
      Bool.or(Bool.and(String.eq(d, target), Bool.and(Nat.is_eq(op, i), Nat.is_eq(item, j))), picked.has(rest, target, i, j))

# The stand-ins
# -------------

# An item forgotten keeps its terminator and loses its text; one already
# forgotten stays as it is.
def forget.item(hit: Bool, it: Ops.Item) -> Ops.Item:
  match hit it:
    case True{} Ops.Item{t, n, f}:
      Ops.Item{SNil{}, n, True{}}
    case False{} it2:
      it2

def forget.items(items: List<&2, Ops.Item>, +ps: List<&2, FgPick>, +target: String, +i: Nat, +j: Nat) -> List<&2, Ops.Item>:
  match items:
    case Nil{}:
      Nil{}
    case it <> rest:
      forget.item(picked.has(ps, target, i, j), it) <> forget.items(rest, ps, target, i, 1n+j)

def forget.ops(ops: List<&2, Ops.Op>, +ps: List<&2, FgPick>, +target: String, +i: Nat) -> List<&2, Ops.Op>:
  match ops:
    case Nil{}:
      Nil{}
    case Ops.Op{k, at, items} <> rest:
      Ops.Op{k, at, forget.items(items, ps, target, i, 0n)} <> forget.ops(rest, ps, target, 1n+i)

# Only an `insert` mints, so only an `insert`'s items are a resolution's own
# to destroy; a `keep` carries a reference and no text.
def forget.pieces(ps: List<&2, Res.Piece>, +picks: List<&2, FgPick>, +target: String, +i: Nat) -> List<&2, Res.Piece>:
  match ps:
    case Nil{}:
      Nil{}
    case Res.Piece.Insert{items} <> rest:
      Res.Piece.Insert{forget.items(items, picks, target, i, 0n)} <> forget.pieces(rest, picks, target, 1n+i)
    case Res.Piece.Keep{d, f, c} <> rest:
      Res.Piece.Keep{d, f, c} <> forget.pieces(rest, picks, target, 1n+i)

# What a document is before this forgetting: its own bytes where the store
# holds them — an operation document, a resolution, or a `text` payload,
# which is the document inserting every line at 0 and states its own digest
# as its result — or the stand-ins already standing for it, read together.
type FgBase is Data:
  Fg.Ops{doc: Ops.Doc}
  Fg.Res{doc: Res.Doc}
  Fg.Absent{}

def base.parsed(r: Result<&2, &2, String, Ops.Doc>) -> FgBase:
  match r:
    case Done{d}:
      Fg.Ops{d}
    case Fail{e}:
      Fg.Absent{}

def base.resolved(r: Result<&2, &2, String, Res.Doc>) -> FgBase:
  match r:
    case Done{d}:
      Fg.Res{d}
    case Fail{e}:
      Fg.Absent{}

def base.created(+text: String, items: List<&2, Ops.Item>) -> FgBase:
  match items:
    case Nil{}:
      Fg.Absent{}
    case +some:
      Fg.Ops{Ops.Doc{None{}, Some{Sha.digest(Utf8.encode(text))}, [Ops.Op{Ops.Insert{}, 0n, some}]}}

def base.held(+path: String, +text: String) -> FgBase:
  Bool.pick(FgBase, String.ends_with(path, ".ops.txt"),
    Bool.pick(FgBase, Res.is_resolution(text), base.resolved(Res.parse(text)), base.parsed(Ops.parse(text))),
    base.created(text, Ops.from_text(text)))

def base.standing(f: Stand.Found) -> FgBase:
  match f:
    case Stand.Found.Ops{d}:
      Fg.Ops{d}
    case Stand.Found.Res{d}:
      Fg.Res{d}
    case _:
      Fg.Absent{}

def base.found(+ds: List<&2, Store.Doc>, +target: String, held: Maybe<&2, Store.Doc>) -> FgBase:
  match held:
    case Some{Store.Doc{+p, i, n, +t}}:
      base.held(p, t)
    case None{}:
      base.standing(Stand.found(ds, target))

def doc.exact(ds: List<&2, Store.Doc>, +id: String) -> Maybe<&2, Store.Doc>:
  match ds:
    case Nil{}:
      None{}
    case +d <> rest:
      Bool.pick(Maybe<&2, Store.Doc>, String.eq(Store.id_of(d), id), Some{d}, doc.exact(rest, id))

def base(+ds: List<&2, Store.Doc>, +target: String) -> FgBase:
  base.found(ds, target, doc.exact(ds, target))

# A document written: the digest it forgets, and its bytes. `beside` is
# where a payload's stand-in asks to be filed: at the payload's own name,
# where that is free.
type FgWrite is Data:
  Fg.Write{forgets: String, text: String, payload: Bool}

def write.of(+target: String, +text: String, +said: String) -> Maybe<&2, FgWrite>:
  Bool.pick(Maybe<&2, FgWrite>, String.eq(text, said), None{}, Some{Fg.Write{target, text, False{}}})

# Decision 0014's stand-in, in the grammar of what it stands in for: the
# same operations — or pieces — with the items picked forgotten, `forgets`
# naming the target, and no result, since the file it makes is the
# destroyed state and a digest of it would confirm a guess. Nothing is
# written where what the store already says of the target says as much.
def standin.of(+target: String, +ps: List<&2, FgPick>, b: FgBase) -> Result<&2, &2, Main.Refused, Maybe<&2, FgWrite>>:
  match b:
    case Fg.Ops{Ops.Doc{f, +r, +ops}}:
      Done{write.of(target, Ops.write(Ops.Doc{Some{target}, None{}, forget.ops(ops, ps, target, 0n)}), Ops.write(Ops.Doc{Some{target}, r, ops}))}
    case Fg.Res{Res.Doc{f, r, +pieces}}:
      Done{write.of(target, Res.write(Res.Doc{Some{target}, None{}, forget.pieces(pieces, ps, target, 0n)}), Res.write(Res.Doc{Some{target}, None{}, pieces}))}
    case Fg.Absent{}:
      Fail{Main.Refused{1, "the span is quoted in " ++ target ++ ", which this store does not hold yet; forgetting preserves a document's shape, and the shape has not arrived"}}

def standins(ts: List<&2, String>, +ps: List<&2, FgPick>, +ds: List<&2, Store.Doc>) -> Result<&2, &2, Main.Refused, List<&2, FgWrite>>:
  match ts:
    case Nil{}:
      Done{Nil{}}
    case +t <> rest:
      do Result<&2, &2, Main.Refused, List<&2, FgWrite>>:
        w : Maybe<&2, FgWrite> <- standin.of(t, ps, base(ds, t))
        more : List<&2, FgWrite> <- standins(rest, ps, ds)
        return List.append(&2, FgWrite, Maybe.default(&2, List<&2, FgWrite>, Maybe.map(&2, FgWrite, List<&2, FgWrite>, x => [x], w), Nil{}), more)

# The plan
# --------

# What forgetting destroys and what stands in for it, decided before any of
# it is done, so that `--dry-run` and the real thing cannot describe
# different bytes: the digests whose bytes go, the documents written, how
# much of what was asked was already forgotten, and how many other versions
# of a file of bytes its history holds.
type FgPlan is Data:
  Fg.Plan{targets: List<&2, String>, writes: List<&2, FgWrite>, already: Nat, elsewhere: Nat}

def refused.of(-A: Data, r: Result<&2, &2, String, A>) -> Result<&2, &2, Main.Refused, A>:
  match r:
    case Fail{e}:
      Fail{Main.Refused{1, e}}
    case Done{x}:
      Done{x}

def span.checked.r(+first: String, +last: String) -> Result<&2, &2, Main.Refused, Unit>:
  Bool.pick(Result<&2, &2, Main.Refused, Unit>, Bool.or(String.eq(first, "0"), usize.lt(last, first)),
    Fail{Main.Refused{1, "lines " ++ first ++ ".." ++ last ++ " name no span: lines count from 1, and the last is not before the first"}},
    Done{Unit{}})

def span.within.r(+last: String, +lines: Nat) -> Result<&2, &2, Main.Refused, Unit>:
  Bool.pick(Result<&2, &2, Main.Refused, Unit>, usize.lt(T.spell(lines), last),
    Fail{Main.Refused{1, "the file has " ++ T.spell(lines) ++ " lines there, and line " ++ last ++ " is past the end of it"}},
    Done{Unit{}})

# The elements a span names: the file's lines at the revision, as the walk
# of its ancestry reads them, from the first to the last.
def span.keys(+visible: List<&2, FgQuoted>, +first: String, +last: String) -> List<&2, String>:
  +f = Maybe.default(&2, Nat, T.number(first), 1n)
  keys(List.take(&2, FgQuoted, List.drop(&2, FgQuoted, visible, Nat.sub(f, 1n)), Nat.sub(Maybe.default(&2, Nat, T.number(last), 0n), Nat.sub(f, 1n))))

def by_digest(+fs: List<&2, Main.Full>) -> List<&2, Main.Full>:
  List.sort(~Main.Full, ~(a => b => String.is_le(Main.id_of(a), Main.id_of(b))), fs)

def lines.picked(+ts: List<&2, String>, +ps: List<&2, FgPick>, +ds: List<&2, Store.Doc>, +already: Nat) -> Result<&2, &2, Main.Refused, FgPlan>:
  Result.map(&2, &2, Main.Refused, List<&2, FgWrite>, FgPlan, ws => Fg.Plan{ts, ws, already, 0n}, standins(ts, ps, ds))

def lines.of(+ds: List<&2, Store.Doc>, p: FgPicked) -> Result<&2, &2, Main.Refused, FgPlan>:
  match p:
    case Fg.Picked{+ps, +already}:
      lines.picked(targets(ps), ps, ds, already)

# `forget --lines` over a file of lines: the span checked; the elements it
# names at the revision; every element the store's whole history wrote to
# the file, to find each delete quoting them and each copy a resolution
# made; and a stand-in for each document holding one. One def per stage,
# each taking the last one's result, so that a proof opens it a stage at a
# time.
def lines.every(+fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +file: String, +span: List<&2, String>, r: Result<&2, &2, Main.Refused, List<&2, FgQuoted>>) -> Result<&2, &2, Main.Refused, FgPlan>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{+every}:
      lines.of(ds, picked(every, copies(every, span), named(fs, file)))

def lines.within(+fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +id: String, +file: String, +first: String, +last: String, +visible: List<&2, FgQuoted>, ok: Result<&2, &2, Main.Refused, Unit>) -> Result<&2, &2, Main.Refused, FgPlan>:
  match ok:
    case Fail{e}:
      Fail{e}
    case Done{u}:
      lines.every(fs, ds, file, span.keys(visible, first, last), refused.of(List<&2, FgQuoted>, quotes(by_digest(fs), ds, id, file)))

def lines.at(+fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +id: String, +file: String, +first: String, +last: String, r: Result<&2, &2, Main.Refused, List<&2, FgQuoted>>) -> Result<&2, &2, Main.Refused, FgPlan>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{at}:
      +visible = quoted.visible(at)
      lines.within(fs, ds, id, file, first, last, visible, span.within.r(last, List.length(&2, FgQuoted, visible)))

def lines.checked(+fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +id: String, +file: String, +first: String, +last: String, ok: Result<&2, &2, Main.Refused, Unit>) -> Result<&2, &2, Main.Refused, FgPlan>:
  match ok:
    case Fail{e}:
      Fail{e}
    case Done{u}:
      lines.at(fs, ds, id, file, first, last, refused.of(List<&2, FgQuoted>, quotes(Main.walked.ancestry(fs, id), ds, id, file)))

def lines.plan.r(+fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +id: String, +file: String, +first: String, +last: String) -> Result<&2, &2, Main.Refused, FgPlan>:
  lines.checked(fs, ds, id, file, first, last, span.checked.r(first, last))

# A file of `operations/`, as the host hashed it: where, its digest, and how
# many bytes.
type FgFiled is Data:
  Fg.Filed{path: String, digest: String, size: String}

def filed.one(+path: String, cut: Maybe<&2, T.Split>) -> FgFiled:
  match cut:
    case Some{T.Split{d, n}}:
      Fg.Filed{path, d, n}
    case None{}:
      Fg.Filed{path, "-", "0"}

def filed(ps: List<&2, String>, stats: List<&2, String>) -> List<&2, FgFiled>:
  match ps stats:
    case +p <> pr +st <> sr:
      filed.one(p, T.split_once(st)) <> filed(pr, sr)
    case _ _:
      Nil{}

def filed.document(+p: String) -> Bool:
  String.ends_with(p, ".ops.txt")

# How many bytes a payload the store holds is: the first file that is not
# a document and hashes to it.
def held.size(fs: List<&2, FgFiled>, +target: String) -> Maybe<&2, String>:
  match fs:
    case Nil{}:
      None{}
    case Fg.Filed{+p, +d, n} <> rest:
      Bool.pick(Maybe<&2, String>, Bool.and(Bool.not(filed.document(p)), String.eq(d, target)), Some{n}, held.size(rest, target))

def stood.text(m: Maybe<&2, Stand.Stood>) -> String:
  match m:
    case None{}:
      SNil{}
    case Some{Stand.Stood{p, i}}:
      Stand.payload.write(p)

# Decision 0066: a payload has no shape to keep, so what stands in for it is
# two headers — the digest destroyed and how many bytes it held — measured
# from the bytes, or, where they are already gone, taken from the stand-in
# that says so. Nothing to destroy and nothing to say how much there was is
# a refusal; bytes already gone are already forgotten, everywhere at once.
def whole.of(+target: String, held: Maybe<&2, String>, +stood: Maybe<&2, Stand.Stood>, +elsewhere: Nat) -> Result<&2, &2, Main.Refused, FgPlan>:
  match held stood:
    case None{} None{}:
      Fail{Main.Refused{1, "this store does not hold the content " ++ target ++ ", and has no record of destroying it; there is nothing here to forget"}}
    case None{} Some{s}:
      Done{Fg.Plan{Nil{}, Nil{}, 1n, elsewhere}}
    case Some{+n} _:
      +text = Stand.payload.write(Stand.Payload{target, n})
      Done{Fg.Plan{[target], Bool.pick(List<&2, FgWrite>, String.eq(stood.text(stood), text), Nil{}, [Fg.Write{target, text, True{}}]), 0n, elsewhere}}

# The payload the tree holds, as a list of none or one.
# `LAWS.forget_whole_takes_one_payload` holds the plan's targets to it.
def payload.list(m: Maybe<&2, String>) -> List<&2, String>:
  match m:
    case None{}:
      Nil{}
    case Some{d}:
      [d]

# `forget` of a file of bytes: the payload the tree holds for it at the
# revision, which concurrent revisions stating it two ways leave none of.
def whole.plan.r(+file: String, payload: Maybe<&2, String>, +files: List<&2, FgFiled>, +stood: List<&2, Store.Doc>, +elsewhere: Nat) -> Result<&2, &2, Main.Refused, FgPlan>:
  match payload:
    case None{}:
      Fail{Main.Refused{1, "concurrent revisions each state the whole content of the file " ++ file ++ ", and bytes do not merge; record the version you mean, which is the only thing that can decide it"}}
    case Some{+target}:
      whole.of(target, held.size(files, target), Stand.payload.standing(stood, target), elsewhere)

# Every other version of a file of bytes its history states, each its own
# payload: decision 0066 counts them, and says so, rather than reaching
# revisions nobody named.
def bytes.fact(+file: String, +k: String, cut: Maybe<&2, T.Split>) -> List<&2, String>:
  match cut:
    case Some{T.Split{+f, d}}:
      Bool.pick(List<&2, String>, Bool.and(String.eq(k, "bytes"), String.eq(f, file)), [d], Nil{})
    case None{}:
      Nil{}

def bytes.facts(hs: List<&2, Rev.Header>, +file: String) -> List<&2, String>:
  match hs:
    case Nil{}:
      Nil{}
    case Rev.Header{+k, +v} <> rest:
      List.append(&2, String, bytes.fact(file, k, T.split_once(v)), bytes.facts(rest, file))

def bytes.of(fs: List<&2, Main.Full>, +file: String) -> List<&2, String>:
  match fs:
    case Nil{}:
      Nil{}
    case +f <> rest:
      List.append(&2, String, bytes.facts(Main.facts_of(f), file), bytes.of(rest, file))

def others.of(ds: List<&2, String>, +target: String) -> List<&2, String>:
  match ds:
    case Nil{}:
      Nil{}
    case +d <> rest:
      Rev.keep(Bool.not(String.eq(d, target)), d, others.of(rest, target))

def others(+fs: List<&2, Main.Full>, +file: String, +target: String) -> List<&2, String>:
  Main.distinct(List.sort(~String, ~(a => b => String.is_le(a, b)), others.of(bytes.of(fs, file), target)))

# Those not already forgotten: no payload stand-in forgets them.
def elsewhere(ds: List<&2, String>, +stood: List<&2, Store.Doc>) -> Nat:
  match ds:
    case Nil{}:
      0n
    case +d <> +rest:
      Bool.pick(Nat, Maybe.is_none(&2, Stand.Stood, Stand.payload.standing(stood, d)), 1n+elsewhere(rest, stood), elsewhere(rest, stood))

# What is destroyed
# -----------------

# A path's components compared in order, as Rust orders a `PathBuf`: a
# directory's files come before a sibling whose name continues it.
def parts.le(xs: List<&2, String>, ys: List<&2, String>) -> Bool:
  match xs ys:
    case Nil{} _:
      True{}
    case x <> xr Nil{}:
      False{}
    case +x <> xr +y <> yr:
      Bool.pick(Bool, String.eq(x, y), parts.le(xr, yr), String.is_lt(x, y))

def path.le(+a: String, +b: String) -> Bool:
  parts.le(String.split(a, '/'), String.split(b, '/'))

def destroyed.of(fs: List<&2, FgFiled>, +targets: List<&2, String>, +documents: Bool) -> List<&2, String>:
  match fs:
    case Nil{}:
      Nil{}
    case Fg.Filed{+p, +d, n} <> rest:
      Rev.keep(Bool.and(Rev.member(targets, d), Bool.not(Bool.xor(filed.document(p), documents))), p, destroyed.of(rest, targets, documents))

# The files of `operations/` whose bytes are one of these digests.
# `LAWS.forget_destroys_only_what_it_forgets` holds `destroyed` to it.
def holding(fs: List<&2, FgFiled>, +ts: List<&2, String>) -> List<&2, String>:
  match fs:
    case Nil{}:
      Nil{}
    case Fg.Filed{+p, +d, n} <> rest:
      Rev.keep(Rev.member(ts, d), p, holding(rest, ts))

# Every file whose bytes are a destroyed digest, found by content as
# everything in a store is: the documents first, then the payloads, each in
# path order.
def destroyed(+fs: List<&2, FgFiled>, +targets: List<&2, String>) -> List<&2, String>:
  List.append(&2, String, List.sort(~String, ~(a => b => path.le(a, b)), destroyed.of(fs, targets, True{})), List.sort(~String, ~(a => b => path.le(a, b)), destroyed.of(fs, targets, False{})))

def filed.taken(fs: List<&2, FgFiled>, +p: String) -> Bool:
  match fs:
    case Nil{}:
      False{}
    case Fg.Filed{+q, d, n} <> rest:
      Bool.or(String.eq(q, p), filed.taken(rest, p))

def filed.beside(+fs: List<&2, FgFiled>, ds: List<&2, String>, +named: String) -> String:
  match ds:
    case Nil{}:
      named
    case +d <> rest:
      Bool.pick(String, filed.taken(fs, d ++ ".ops.txt"), named, d ++ ".ops.txt")

# Where a document is filed, relative to the root. Decision 0066 files a
# payload's stand-in where the payload was, at its name with the suffix
# that says it is a document, where that name is free; every other
# document goes under its own digest.
def filed.as(+fs: List<&2, FgFiled>, +destroys: List<&2, String>, w: FgWrite) -> String:
  match w:
    case Fg.Write{f, +text, +payload}:
      +named = "operations/" ++ Sha.digest(Utf8.encode(text)) ++ ".ops.txt"
      Bool.pick(String, payload, filed.beside(fs, destroys, named), named)

# What `cache/` holds that `forget` destroys: every entry named by a digest,
# since an entry is a file's content at some revision and may be a copy of
# what went. The note `init` writes and the catalogues are not entries.
def cached(ps: List<&2, String>) -> List<&2, String>:
  match ps:
    case Nil{}:
      Nil{}
    case +p <> rest:
      Rev.keep(T.is_digest(String.drop(p, 6n)), p, cached(rest))

# What is said
# ------------

def said.writes(ws: List<&2, FgWrite>, +wrote: String) -> List<&2, String>:
  match ws:
    case Nil{}:
      Nil{}
    case Fg.Write{f, t, p} <> rest:
      (wrote ++ " a forgetting document for " ++ String.take(f, 12n)) <> said.writes(rest, wrote)

def said.destroys(ds: List<&2, String>, +destroyed: String) -> List<&2, String>:
  match ds:
    case Nil{}:
      Nil{}
    case d <> rest:
      (destroyed ++ " history/" ++ d) <> said.destroys(rest, destroyed)

def said.elsewhere(+n: Nat) -> List<&2, String>:
  Bool.pick(List<&2, String>, Nat.is_eq(n, 0n), Nil{}, ["this file holds " ++ Nat.show(n) ++ " other version" ++ Bool.pick(String, Nat.is_eq(n, 1n), SNil{}, "s") ++ " elsewhere in its history, each forgotten on its own"])

def said.cannot(lines: Bool) -> String:
  Bool.pick(String, lines,
    "the shape and place of those lines, and the revisions around them, are still recorded; only the text is destroyed — and only on this replica until the forgetting documents sync",
    "the file's name, its length, and the revisions around it are still recorded; only the content is destroyed — and only on this replica until the forgetting document syncs")

def said.gone(ts: List<&2, String>) -> List<&2, String>:
  match ts:
    case Nil{}:
      Nil{}
    case t <> rest:
      ("gone " ++ t) <> said.gone(rest)

# What `forget` prints: with `--fields`, decision 0074's statement — which
# digests stopped being readable; otherwise each document written, each
# file destroyed, the other versions a file of bytes still has, and decision
# 0014's "what forgetting cannot hide", said where the person is. Where
# nothing is written or destroyed, that it was already forgotten.
def said.done(ws: List<&2, FgWrite>, destroys: List<&2, String>, +n: Nat, +lines: Bool, +dry: Bool) -> List<&2, String>:
  match ws destroys:
    case Nil{} Nil{}:
      [Bool.pick(String, lines, "those lines are already forgotten everywhere they are quoted", "those bytes are already forgotten")]
    case +w +ds:
      List.append(&2, String, said.writes(w, Bool.pick(String, dry, "would write", "wrote")), List.append(&2, String, said.destroys(ds, Bool.pick(String, dry, "would destroy", "destroyed")), List.append(&2, String, said.elsewhere(n), [said.cannot(lines)])))

def said(p: FgPlan, +fields: Bool, destroys: List<&2, String>, +lines: Bool, +dry: Bool) -> List<&2, String>:
  match p fields:
    case Fg.Plan{ts, ws, a, n} True{}:
      said.gone(ts)
    case Fg.Plan{ts, ws, a, +n} False{}:
      said.done(ws, destroys, n, lines, dry)

# The command
# -----------

def write.text(w: FgWrite) -> String:
  match w:
    case Fg.Write{f, t, p}:
      t

def io.answer(r: Result<&1, &1, U32 & String, String>) -> IO(String):
  match r:
    case Fail{Tuple{code, msg}}:
      Main.die(String, 1, msg)
    case Done{answer}:
      IO.pure(String, answer)

def io.file(+path: String, +text: String, missing: Bool) -> IO(Unit):
  match missing:
    case False{}:
      IO.pure(Unit, Unit{})
    case True{}:
      do IO<Unit>:
        r : Result<&1, &1, U32 & String, String> <- Store.filed(path ++ "\n" ++ text)
        done : String <- io.answer(r)
        IO.pure(Unit, Unit{})

# The documents written, each where it is filed and unless the store
# already holds its bytes; then each original destroyed, and each copy in
# `cache/` — the stand-ins first, so that an interruption leaves both a
# document and one naming it rather than bytes gone with nothing said.
def io.write(+root: String, +files: List<&2, FgFiled>, +destroys: List<&2, String>, ws: List<&2, FgWrite>) -> IO(Unit):
  match ws:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case +w <> rest:
      do IO<Unit>:
        +text : String = write.text(w)
        at : List<&2, String> <- Store.located(root, [Sha.digest(Utf8.encode(text))])
        io.file(root ++ "/" ++ filed.as(files, destroys, w), text, Rev.member(at, "-"))
        io.write(root, files, destroys, rest)

def io.remove(+boundary: String, +root: String, ps: List<&2, String>) -> IO(Unit):
  match ps:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case +p <> rest:
      do IO<Unit>:
        r : Result<&1, &1, U32 & String, String> <- Store.removed(boundary ++ "\n" ++ root ++ "/" ++ p)
        done : String <- io.answer(r)
        io.remove(boundary, root, rest)

def io.said(ls: List<&2, String>) -> IO(Unit):
  match ls:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case l <> rest:
      do IO<Unit>:
        IO.print(l)
        io.said(rest)

def io.act(+root: String, +files: List<&2, FgFiled>, +destroys: List<&2, String>, ws: List<&2, FgWrite>, dry: Bool) -> IO(Unit):
  match dry:
    case True{}:
      IO.pure(Unit, Unit{})
    case False{}:
      do IO<Unit>:
        io.write(root, files, destroys, ws)
        io.remove(root ++ "/operations", root, destroys)
        listed : List<&2, String> <- Store.cached(root)
        io.remove(root ++ "/cache", root, cached(listed))

# Every file of `operations/`, with the digest and size the host found.
def io.files(+root: String) -> IO(List<&2, FgFiled>):
  do IO<List<&2, FgFiled>>:
    listed : List<&2, String> <- Store.operations(root)
    +ps : List<&2, String> = listed
    stats : List<&2, String> <- Store.stats(root, ps)
    return filed(ps, stats)

def io.done(+root: String, +files: List<&2, FgFiled>, p: FgPlan, +lines: Bool, +dry: Bool, +fields: Bool, +early: Bool) -> IO(Unit):
  match p:
    case Fg.Plan{+ts, +ws, +a, +n}:
      +destroys = destroyed(files, ts)
      do IO<Unit>:
        io.act(root, files, destroys, ws, dry)
        Main.name.header(Bool.and(fields, Bool.not(early)))
        io.said(said(Fg.Plan{ts, ws, a, n}, fields, destroys, lines, dry))

def lines.whole.r(+file: String, r: Result<&2, &2, String, List<&2, Ops.Item>>) -> Result<&2, &2, Main.Refused, FgPlan>:
  match r:
    case Fail{e}:
      Fail{Main.Refused{1, e}}
    case Done{items}:
      +n = T.spell(List.length(&2, Ops.Item, items))
      Fail{Main.Refused{1, "the file " ++ file ++ " is lines rather than bytes, and a redaction is exact: name the span, as `--lines <first>..<last>`. It has " ++ n ++ " lines there, so `--lines 1.." ++ n ++ "` is all of them"}}

def io.lines.plan.r(+fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +id: String, +file: String, sp: Maybe<&2, FgSpan>) -> Result<&2, &2, Main.Refused, FgPlan>:
  match sp:
    case Some{Fg.Span{+first, +last}}:
      lines.plan.r(fs, ds, id, file, first, last)
    case None{}:
      lines.whole.r(file, Main.content(fs, ds, id, file))

# A file of lines: `--lines` over it, or the refusal that names the span
# covering all of it — which is the one place the file is materialised.
def io.lines(+root: String, +fs: List<&2, Main.Full>, +id: String, +file: String, sp: Maybe<&2, FgSpan>, +dry: Bool, +fields: Bool, +early: Bool) -> IO(Unit):
  +late = Bool.and(fields, Bool.not(early))
  do IO<Unit>:
    ds : List<&2, Store.Doc> <- Store.fetch(root, Main.wanted(fs, file))
    +ds2 : List<&2, Store.Doc> = ds
    more : List<&2, Store.Doc> <- Store.fetch(root, Main.kept_digests(ds2))
    +all : List<&2, Store.Doc> = List.append(&2, Store.Doc, ds2, more)
    p : FgPlan <- Main.stated.io(FgPlan, late, io.lines.plan.r(fs, all, id, file, sp))
    listed : List<&2, FgFiled> <- io.files(root)
    io.done(root, listed, p, True{}, dry, fields, early)

# A file of bytes: forgotten whole, or refused a span.
def io.whole(+root: String, +fs: List<&2, Main.Full>, +file: String, payload: Maybe<&2, String>, +dry: Bool, +fields: Bool, +early: Bool) -> IO(Unit):
  +late = Bool.and(fields, Bool.not(early))
  +y = payload
  +target = Maybe.default(&2, String, y, SNil{})
  +others = others(fs, file, target)
  do IO<Unit>:
    listed : List<&2, FgFiled> <- io.files(root)
    +files : List<&2, FgFiled> = listed
    at : List<&2, String> <- Store.located(root, others)
    stood : List<&2, Store.Doc> <- Store.standing(root, target <> Store.missing(others, at))
    +stood2 : List<&2, Store.Doc> = stood
    p : FgPlan <- Main.stated.io(FgPlan, late, whole.plan.r(file, y, files, stood2, elsewhere(others, stood2)))
    io.done(root, files, p, False{}, dry, fields, early)

# What the file is decides which forgetting is even askable (decision
# 0017 fixed it when the file was added): a span of a file of lines, the
# whole of a file of bytes, and nothing of a link, whose target is a fact of
# the revision document.
def io.kind(+root: String, +fs: List<&2, Main.Full>, +id: String, +file: String, +dry: Bool, +fields: Bool, +early: Bool, e: Maybe<&2, Tree.Entry>, sp: Maybe<&2, FgSpan>) -> IO(Unit):
  match e sp:
    case Some{Tree.Entry{f, p, Tree.Lines{}, y, g, m}} sp2:
      io.lines(root, fs, id, file, sp2, dry, fields, early)
    case Some{Tree.Entry{f, p, Tree.Whole{}, y, g, m}} None{}:
      io.whole(root, fs, file, y, dry, fields, early)
    case Some{Tree.Entry{f, p, Tree.Whole{}, y, g, m}} Some{s}:
      Main.stated.io(Unit, Bool.and(fields, Bool.not(early)), Fail{Main.Refused{1, "the file " ++ file ++ " is bytes rather than lines, so a span names nothing in it; forgetting it without a span destroys the whole of what it holds there, which is all a file of bytes has"}})
    case Some{Tree.Entry{f, p, Tree.Link{}, y, g, m}} s:
      Main.stated.io(Unit, Bool.and(fields, Bool.not(early)), Fail{Main.Refused{1, "the file " ++ file ++ " is a link, and holds no content to destroy: where it points is stated in the revision document, which is the one thing an append-only store cannot rewrite"}})
    case None{} s:
      Main.stated.io(Unit, Bool.and(fields, Bool.not(early)), Fail{Main.Refused{1, "no file " ++ file ++ " exists here"}})

def forget.asked(a: FgAsked) -> IO(Unit):
  match a:
    case Fg.Asked{+t, +path, sp, +dry, +fields}:
      # Decision 0074: asked for a statement, `forget` leaves one behind
      # wherever it stops but at a command line that was wrong — printed
      # before the store is opened where nothing left can prove the line
      # wrong, and otherwise before the refusal the Bend side decides.
      +early = Bool.and(fields, Bool.and(Bool.not(String.is_empty(t)), Bool.not(String.eq(path, "file:"))))
      +late = Bool.and(fields, Bool.not(early))
      do IO<Unit>:
        Main.name.header(early)
        root : String <- Store.root()
        +r : String = root
        rs : List<&2, Store.Doc> <- Store.revisions(r)
        bs : List<&2, Bm.Bookmark> <- Main.bookmarks(r)
        +bs2 : List<&2, Bm.Bookmark> = bs
        +fs : List<&2, Main.Full> = Main.fulls(r, rs)
        f : Main.Full <- Main.stated.io(Main.Full, late, Main.name.resolved.r(fs, bs2, t))
        +id : String = Main.id_of(f)
        tr : Tree.Tree() <- Main.stated.io(Tree.Tree(), late, Main.tree.r(fs, id))
        +tr2 : Tree.Tree() = tr
        file : String <- Main.stated.io(String, late, Main.file_in.r(id, bs2, path, tr2))
        +file2 : String = file
        io.kind(r, fs, id, file2, dry, fields, early, Tree.lookup(tr2, file2), sp)

# `forget <target> <path> [--lines <first>..<last>] [--dry-run] [--fields]`.
def forget(+args: List<&2, String>) -> IO(Unit):
  do IO<Unit>:
    a : FgAsked <- Main.stated.io(FgAsked, False{}, asked.r(args))
    forget.asked(a)
