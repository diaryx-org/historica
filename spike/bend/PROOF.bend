# The proofs. Most of the laws hold by computation once the one opaque
# value in them is opened by a case, which is what each def does.

import Base
import ./sha256.bend as Sha
import ./ops.bend as Ops
import ./revision.bend as Rev
import ./LAWS.bend as Laws

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

def Laws.forgotten_agrees(b):
  match b:
    case Ops.Item{t, n, f}:
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
