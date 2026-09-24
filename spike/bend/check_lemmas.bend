# `check` reports each payload with the digest asked for it. The digests
# are asked for in the listing's own order, one per payload, and taken back
# one at each payload and none elsewhere.
import Base
import ./commands.bend as Main
import ./text.bend as T
import ./revision.bend as Rev
import ./ops.bend as Ops
import ./store.bend as Store

def ndisc(n: Nat) -> Type:
  match n:
    case 0n:
      Unit
    case 1n+k:
      Empty

def zero_succ(-k: Nat, e: {0n == 1n+k : Nat}) -> Empty:
  %e : {ndisc(_) : Type}
  Unit{}

def pred(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+k:
      k

def succ_inj(-a: Nat, -b: Nat, e: {1n+a == 1n+b : Nat}) -> {a == b : Nat}:
  Equal.cong(Nat, Nat, n => pred(n), 1n+a, 1n+b, e)

def att_step(d: Bool, +l: String, +rv: Bool, +rest: List<&2, String>, stats: List<&2, String>, h: {List.length(&2, String, stats) == List.length(&2, String, Rev.keep(Bool.not(d), l, Main.payloads(rest))) : Nat}, ih: @st: List<&2, String> -> {List.length(&2, String, st) == List.length(&2, String, Main.payloads(rest)) : Nat} -> {Main.payload.pairs(Main.attach(Main.filed(rest), st)) == Main.zip.pairs(Main.payloads(rest), st) : List<&2, T.Split>}) -> {Main.payload.pairs(Main.attach(Main.Filed{l, d, rv, SNil{}} <> Main.filed(rest), stats)) == Main.zip.pairs(Rev.keep(Bool.not(d), l, Main.payloads(rest)), stats) : List<&2, T.Split>}:
  match d:
    case True{}:
      ih(stats, h)
    case False{}:
      match stats:
        case Nil{}:
          Empty.absurd({Main.payload.pairs(Main.attach(Main.Filed{l, False{}, rv, SNil{}} <> Main.filed(rest), Nil{})) == Main.zip.pairs(l <> Main.payloads(rest), Nil{}) : List<&2, T.Split>}, zero_succ(List.length(&2, String, Main.payloads(rest)), h))
        case +s <> more:
          Equal.cong(List<&2, T.Split>, List<&2, T.Split>, xs => T.Split{l, s} <> xs, Main.payload.pairs(Main.attach(Main.filed(rest), more)), Main.zip.pairs(Main.payloads(rest), more), ih(more, succ_inj(List.length(&2, String, more), List.length(&2, String, Main.payloads(rest)), h)))

# Each payload is paired with the digest asked for it, in order.
def pairs_ok(ls: List<&2, String>, stats: List<&2, String>, h: {List.length(&2, String, stats) == List.length(&2, String, Main.payloads(ls)) : Nat}) -> {Main.payload.pairs(Main.attach(Main.filed(ls), stats)) == Main.zip.pairs(Main.payloads(ls), stats) : List<&2, T.Split>}:
  match ls:
    case Nil{}:
      {==}
    case +l <> +rest:
      att_step(Bool.or(String.starts_with(l, "revisions/"), String.ends_with(l, ".ops.txt")), l, String.starts_with(l, "revisions/"), rest, stats, h, st => hs => pairs_ok(rest, st, hs))

# Refusals
# --------

def rev_line(+id: String, r: Result<&2, &2, String, Rev.Rev>) -> {Main.check.refuses(Main.check_rev(id, r)) == Main.rev.fails(r) : Bool}:
  match r:
    case Fail{e}:
      {==}
    case Done{x}:
      {==}

def ops_line(+id: String, r: Result<&2, &2, String, Ops.Doc>) -> {Main.check.refuses(Main.check_ops.of(id, r)) == Main.ops.fails(r) : Bool}:
  match r:
    case Fail{e}:
      {==}
    case Done{x}:
      match x:
        case Ops.Doc{f, res, ops}:
          {==}

# `check` calls a document refused exactly where it does not parse.
def doc_line(+d: Store.Doc, rev: Bool) -> {Main.check.refuses(Main.check_doc.of(d, rev)) == Main.doc.fails(d, rev) : Bool}:
  match rev:
    case True{}:
      rev_line(Store.id_of(d), Rev.parse(Store.text_of(d)))
    case False{}:
      ops_line(Store.id_of(d), Ops.parse(Store.text_of(d)))
