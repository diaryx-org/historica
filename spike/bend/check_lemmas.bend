# `check` asks the host for each payload's digest in the order it found the
# payloads, and pairs each with its own answer: given one answer per
# payload, every payload is paired with its own, in order, and no document
# takes one. And the walk it reads a merged file by places every event
# after all it had seen, which is what makes it a walk of the history.
import Base
import ./check.bend as Check
import ./merge.bend as Merge
import ./text.bend as T
import ./composition_lemmas.bend as Comp
import ./notes.bend as Notes

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

# Pairing
# -------

def pairs_ok(fs: List<&2, Check.OpFiled>, stats: List<&2, String>, h: {List.length(&2, String, stats) == List.length(&2, String, Check.payload.paths(fs)) : Nat}) -> {Check.payload.pairs(Check.attach(fs, stats)) == Check.zip.pairs(Check.payload.paths(fs), stats) : List<&2, T.Split>}:
  match fs:
    case Nil{}:
      {==}
    case Check.OpFiled.Doc{r} <> rest:
      match stats:
        case Nil{}:
          pairs_ok(rest, Nil{}, h)
        case +s <> +more:
          pairs_ok(rest, s <> more, h)
    case Check.OpFiled.Payload{+p, x} <> rest:
      match stats:
        case Nil{}:
          Empty.absurd({Check.payload.pairs(Check.attach(Check.OpFiled.Payload{p, x} <> rest, Nil{})) == Check.zip.pairs(p <> Check.payload.paths(rest), Nil{}) : List<&2, T.Split>}, zero_succ(List.length(&2, String, Check.payload.paths(rest)), h))
        case +s <> +more:
          %Equal.sym(List<&2, T.Split>, Check.payload.pairs(Check.attach(rest, more)), Check.zip.pairs(Check.payload.paths(rest), more), pairs_ok(rest, more, succ_inj(List.length(&2, String, more), List.length(&2, String, Check.payload.paths(rest)), h))) : {T.Split{p, s} <> _ == Check.zip.pairs(p <> Check.payload.paths(rest), s <> more) : List<&2, T.Split>}
          {==}

# The walk's order
# ----------------

def app_nil(xs: List<&2, Nat>) -> {List.append(&2, Nat, xs, Nil{}) == xs : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> rest:
      %Equal.sym(List<&2, Nat>, List.append(&2, Nat, rest, Nil{}), rest, app_nil(rest)) : {x <> _ == x <> rest : List<&2, Nat>}
      {==}

def app_assoc(xs: List<&2, Nat>, +ys: List<&2, Nat>, +zs: List<&2, Nat>) -> {List.append(&2, Nat, List.append(&2, Nat, xs, ys), zs) == List.append(&2, Nat, xs, List.append(&2, Nat, ys, zs)) : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> rest:
      %Equal.sym(List<&2, Nat>, List.append(&2, Nat, List.append(&2, Nat, rest, ys), zs), List.append(&2, Nat, rest, List.append(&2, Nat, ys, zs)), app_assoc(rest, ys, zs)) : {x <> _ == x <> List.append(&2, Nat, rest, List.append(&2, Nat, ys, zs)) : List<&2, Nat>}
      {==}

# An order stays causal when what follows it is causal after it.
def app_causal(placed: List<&2, Nat>, +r: List<&2, Nat>, +g: List<&2, Merge.Rev>, +before: List<&2, Nat>, +hp: {Check.causal.go(placed, g, before) == True{} : Bool}, hr: {Check.causal.go(r, g, List.append(&2, Nat, before, placed)) == True{} : Bool}) -> {Check.causal.go(List.append(&2, Nat, placed, r), g, before) == True{} : Bool}:
  match placed:
    case Nil{}:
      Equal.trans(Bool, Check.causal.go(r, g, before), Check.causal.go(r, g, List.append(&2, Nat, before, Nil{})), True{},
        Equal.cong(List<&2, Nat>, Bool, x => Check.causal.go(r, g, x), before, List.append(&2, Nat, before, Nil{}), Equal.sym(List<&2, Nat>, List.append(&2, Nat, before, Nil{}), before, app_nil(before))), hr)
    case +x <> +rest:
      +seen = Comp.and_left(Check.all.in(Merge.past(g, x), before), Check.causal.go(rest, g, List.append(&2, Nat, before, [x])), hp)
      +after = app_causal(rest, r, g, List.append(&2, Nat, before, [x]), Comp.and_right(Check.all.in(Merge.past(g, x), before), Check.causal.go(rest, g, List.append(&2, Nat, before, [x])), hp),
        Equal.trans(Bool, Check.causal.go(r, g, List.append(&2, Nat, List.append(&2, Nat, before, [x]), rest)), Check.causal.go(r, g, List.append(&2, Nat, before, x <> rest)), True{},
          Equal.cong(List<&2, Nat>, Bool, y => Check.causal.go(r, g, y), List.append(&2, Nat, List.append(&2, Nat, before, [x]), rest), List.append(&2, Nat, before, x <> rest), app_assoc(before, [x], rest)), hr))
      %Equal.sym(Bool, Check.all.in(Merge.past(g, x), before), True{}, seen) : {Bool.and(_, Check.causal.go(List.append(&2, Nat, rest, r), g, List.append(&2, Nat, before, [x]))) == True{} : Bool}
      %Equal.sym(Bool, Check.causal.go(List.append(&2, Nat, rest, r), g, List.append(&2, Nat, before, [x])), True{}, after) : {Bool.and(True{}, _) == True{} : Bool}
      {==}

# What `ready` places has its whole past placed already.
def ready.at(+i: Nat, rest: List<&2, Nat>, +g: List<&2, Merge.Rev>, +placed: List<&2, Nat>, b: Bool, eb: {Bool.and(Bool.not(Merge.has(placed, i)), Check.all.in(Merge.past(g, i), placed)) == b : Bool}, ih: {Check.causal.go(Check.ready(g, placed, rest), g, placed) == True{} : Bool}) -> {Check.causal.go(Bool.pick(List<&2, Nat>, b, [i], Check.ready(g, placed, rest)), g, placed) == True{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(Bool, Check.all.in(Merge.past(g, i), placed), True{}, Comp.and_right(Bool.not(Merge.has(placed, i)), Check.all.in(Merge.past(g, i), placed), eb)) : {Bool.and(_, True{}) == True{} : Bool}
      {==}
    case False{}:
      ih

def ready_causal(ixs: List<&2, Nat>, +g: List<&2, Merge.Rev>, +placed: List<&2, Nat>) -> {Check.causal.go(Check.ready(g, placed, ixs), g, placed) == True{} : Bool}:
  match ixs:
    case Nil{}:
      {==}
    case +i <> +rest:
      ready.at(i, rest, g, placed, Bool.and(Bool.not(Merge.has(placed, i)), Check.all.in(Merge.past(g, i), placed)), {==}, ready_causal(rest, g, placed))

def kahn_causal(fuel: Nat, +g: List<&2, Merge.Rev>, +ixs: List<&2, Nat>, +placed: List<&2, Nat>, h: {Check.causal.go(placed, g, Nil{}) == True{} : Bool}) -> {Check.causal(g, Check.kahn(fuel, g, ixs, placed)) == True{} : Bool}:
  match fuel:
    case 0n:
      h
    case 1n+p:
      kahn_causal(p, g, ixs, List.append(&2, Nat, placed, Check.ready(g, placed, ixs)), app_causal(placed, Check.ready(g, placed, ixs), g, Nil{}, h, ready_causal(ixs, g, placed)))

# A new store
# -----------

# What the pass reads of a store `init` has just made — its header, and
# `skipped/`'s note, and nothing else anywhere — is nothing to report.
def fresh(+root: String) -> {Check.found(Check.Gathered{root, Some{Notes.HEADER_NOTE()}, Check.Walked{Nil{}, Nil{}}, Nil{}, Check.Walked{Nil{}, Nil{}}, Nil{}, Check.Texts{Nil{}, Nil{}}, False{}, Check.skipped.read(root ++ "/skipped/README.txt", Done{Notes.SKIPPED_NOTE()}), Check.Walked{Nil{}, Nil{}}, Nil{}}) == Nil{} : List<&2, Check.Finding>}:
  {==}
