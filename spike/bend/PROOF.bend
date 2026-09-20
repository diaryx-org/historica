# The proofs. Most of the laws hold by computation once the one opaque
# value in them is opened by a case, which is what each def does.

import Base
import ./sha256.bend as Sha
import ./ops.bend as Ops
import ./revision.bend as Rev
import ./LAWS.bend as Laws
import ./replay_spec.bend as Spec

# show_hash builds its string from eight words of eight digits, so its
# length is 64 whatever the words are; digest is show_hash of something.
def show_length(h: Sha.Hash) -> {String.length(Sha.show_hash(h)) == 64n : Nat}:
  match h:
    case Sha.H{a, b, c, d, e, f, g, i}:
      {==}

def Laws.digest_length(bs):
  show_length(Sha.digest_words(bs))

def Laws.insert_removes_nothing(at, items):
  {==}

def Laws.delete_end(at, items):
  {==}

def Laws.forgotten_agrees(text, terminated, forgotten):
  match terminated:
    case False{}:
      {==}
    case True{}:
      {==}

def Laws.forgotten_is_nobodys(b):
  match b:
    case Ops.Item{t, n, f}:
      {==}

def Laws.verb_refl(v):
  match v:
    case Ops.Delete{}:
      {==}
    case Ops.Insert{}:
      {==}

def Laws.ordered_first(op):
  match op:
    case Ops.Op{v, at, items}:
      {==}

def Laws.advance_nothing(state, acc):
  {==}

def Laws.drop_nothing(state, ok):
  {==}

def Laws.text_of_line(s):
  {==}

def Laws.empty_history_heads():
  {==}

def Laws.root_is_head(id, change, message):
  {==}

def Laws.no_revisions_unknown(any):
  {==}

# a + (1 + b) is 1 + (a + b): the step a moved item makes on either side.
def add_succ(a: Nat, -b: Nat) -> {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add_succ(p, b) : {1n+Nat.add(p, 1n+b) == 1n+_ : Nat}
      {==}

def Laws.advance_exact(n, state, acc):
  match n state:
    case 0n Nil{}:
      {==}
    case 0n it <> rest:
      {==}
    case 1n+p Nil{}:
      {==}
    case 1n+p it <> rest:
      Laws.advance_exact(p, rest, it <> acc)

# advance moves one item per step: the widths on both sides move together.
def Laws.advance_keeps_everything(n, state, acc):
  match n state:
    case 0n _:
      {==}
    case 1n+p Nil{}:
      {==}
    case 1n+p it <> rest:
      %Equal.sym(Nat, Ops.advance_width(Ops.advance(p, rest, it <> acc)), 1n+Nat.add(List.length(&2, Ops.Item, acc), List.length(&2, Ops.Item, rest)), Laws.advance_keeps_everything(p, rest, it <> acc)) : {_ == Nat.add(List.length(&2, Ops.Item, acc), 1n+List.length(&2, Ops.Item, rest)) : Nat}
      %add_succ(List.length(&2, Ops.Item, acc), List.length(&2, Ops.Item, rest)) : {_ == Nat.add(List.length(&2, Ops.Item, acc), 1n+List.length(&2, Ops.Item, rest)) : Nat}
      {==}

def Laws.agreement_matches_spec(a, b):
  match a b:
    case Ops.Item{a, False{}, f} Ops.Item{b, True{}, g}:
      {==}
    case Ops.Item{a, True{}, f} Ops.Item{b, False{}, g}:
      {==}
    case Ops.Item{a, False{}, True{}} Ops.Item{b, False{}, g}:
      {==}
    case Ops.Item{a, True{}, True{}} Ops.Item{b, True{}, g}:
      {==}
    case Ops.Item{a, False{}, False{}} Ops.Item{b, False{}, True{}}:
      {==}
    case Ops.Item{a, True{}, False{}} Ops.Item{b, True{}, True{}}:
      {==}
    case Ops.Item{a, False{}, False{}} Ops.Item{b, False{}, False{}}:
      {==}
    case Ops.Item{a, True{}, False{}} Ops.Item{b, True{}, False{}}:
      {==}

def and_assoc(a: Bool, -b: Bool, -c: Bool) -> {Bool.and(Bool.and(a, b), c) == Bool.and(a, Bool.and(b, c)) : Bool}:
  match a:
    case False{}:
      {==}
    case True{}:
      {==}

def and_true(a: Bool) -> {a == Bool.and(a, True{}) : Bool}:
  match a:
    case False{}:
      {==}
    case True{}:
      {==}

def and_false(a: Bool) -> {False{} == Bool.and(a, False{}) : Bool}:
  match a:
    case False{}:
      {==}
    case True{}:
      {==}

def Laws.drop_checked_exact(recorded, state, ok):
  match recorded state:
    case Nil{} Nil{}:
      %and_true(ok) : {Ops.Dropped{Nil{}, ok} == Ops.Dropped{Nil{}, _} : Ops.Dropped}
      {==}
    case Nil{} s <> ss:
      %and_true(ok) : {Ops.Dropped{s <> ss, ok} == Ops.Dropped{s <> ss, _} : Ops.Dropped}
      {==}
    case r <> rs Nil{}:
      %and_false(ok) : {Ops.Dropped{Nil{}, False{}} == Ops.Dropped{Nil{}, _} : Ops.Dropped}
      {==}
    case r <> rs s <> ss:
      %Laws.agreement_matches_spec(r, s) : {Ops.drop_checked(rs, ss, Bool.and(ok, Ops.agrees(r, s))) == Ops.Dropped{List.drop(&2, Ops.Item, ss, List.length(&2, Ops.Item, rs)), Bool.and(ok, Bool.and(_, Spec.prefix_matches(rs, ss)))} : Ops.Dropped}
      %and_assoc(ok, Ops.agrees(r, s), Spec.prefix_matches(rs, ss)) : {Ops.drop_checked(rs, ss, Bool.and(ok, Ops.agrees(r, s))) == Ops.Dropped{List.drop(&2, Ops.Item, ss, List.length(&2, Ops.Item, rs)), _} : Ops.Dropped}
      Laws.drop_checked_exact(rs, ss, Bool.and(ok, Ops.agrees(r, s)))

def Laws.result_no_operations(parent, p):
  match parent:
    case Nil{}:
      {==}
    case it <> rest:
      %Laws.result_no_operations(rest, 1n+p) : {it <> Spec.result_from(rest, Nil{}, 1n+p) == it <> _ : List<&2, Ops.Item>}
      {==}
