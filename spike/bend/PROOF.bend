# The proofs. Most of the laws hold by computation once the one opaque
# value in them is opened by a case, which is what each def does.

import Base
import ./sha256.bend as Sha
import ./ops.bend as Ops
import ./revision.bend as Rev
import ./LAWS.bend as Laws
import ./replay_spec.bend as Spec
import ./cursor_spec.bend as Cursor
import ./replay_lemmas.bend as L
import ./position_lemmas.bend as Pos
import ./semantic_replay.bend as Block
import ./composition_lemmas.bend as Comp
import ./parser_lemmas.bend as Parse
import ./decimal_lemmas.bend as Dec
import ./spelling_lemmas.bend as Spell
import ./diff_lemmas.bend as Diff
import ./refusal_lemmas.bend as Refuse

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

def land_insert(+at: Nat, +pos: Nat, +state: List<&2, Ops.Item>, +acc: List<&2, Ops.Item>, -items: List<&2, Ops.Item>, -rest: List<&2, Ops.Op>) -> {Ops.land(Ops.Op{Ops.Insert{}, at, items} <> rest, pos, state, acc) == Ops.Landed{List.reverse.go(&2, Ops.Item, Cursor.prefix(state, at, pos), acc), Cursor.suffix(state, at, pos), True{}} : Ops.Landed}:
  %Laws.advance_exact(Nat.sub(at, pos), state, acc) : {Ops.land.insert(Ops.advance(Nat.sub(at, pos), state, acc)) == Ops.land.insert(_) : Ops.Landed}
  {==}

def land_delete(+at: Nat, +pos: Nat, +state: List<&2, Ops.Item>, +acc: List<&2, Ops.Item>, +items: List<&2, Ops.Item>, -rest: List<&2, Ops.Op>) -> {Ops.land(Ops.Op{Ops.Delete{}, at, items} <> rest, pos, state, acc) == Ops.Landed{List.reverse.go(&2, Ops.Item, Cursor.prefix(state, at, pos), acc), List.drop(&2, Ops.Item, Cursor.suffix(state, at, pos), List.length(&2, Ops.Item, items)), Spec.prefix_matches(items, Cursor.suffix(state, at, pos))} : Ops.Landed}:
  %Laws.drop_checked_exact(items, Cursor.suffix(state, at, pos), True{}) : {Ops.land.delete(items, Ops.advance(Nat.sub(at, pos), state, acc)) == Ops.land.dropped(List.reverse.go(&2, Ops.Item, Cursor.prefix(state, at, pos), acc), _) : Ops.Landed}
  %Laws.advance_exact(Nat.sub(at, pos), state, acc) : {Ops.land.delete(items, Ops.advance(Nat.sub(at, pos), state, acc)) == Ops.land.delete(items, _) : Ops.Landed}
  {==}

# Induction on every operation, with arbitrary position, suffix, reversed
# prefix and prior error. The insert case needs associativity; the delete
# case uses exact quote agreement and preserves the earliest error.
def Laws.cursor_walk_equivalent(ops, pos, state, acc, error):
  match ops:
    case Nil{}:
      match error:
        case None{}:
          {==}
        case Some{e}:
          {==}
    case Ops.Op{Ops.Insert{}, at, items} <> rest:
      +front = Cursor.prefix(state, at, pos)
      +left = Cursor.suffix(state, at, pos)
      +moved = List.reverse.go(&2, Ops.Item, front, acc)
      +next_acc = List.append(&2, Ops.Item, List.reverse(&2, Ops.Item, items), moved)
      +next_pos = Nat.max(pos, at)
      %Equal.sym(Ops.Landed, Ops.land(Ops.Op{Ops.Insert{}, at, items} <> rest, pos, state, acc), Ops.Landed{moved, left, True{}}, land_insert(at, pos, state, acc, items, rest)) : {Ops.apply.go(Ops.Op{Ops.Insert{}, at, items} <> rest, _, pos, error) == Cursor.combine(error, List.reverse(&2, Ops.Item, acc), Cursor.walk(Ops.Op{Ops.Insert{}, at, items} <> rest, pos, state)) : Result<&2, &2, String, List<&2, Ops.Item>>}
      %L.combine_split(error, None{}, List.reverse(&2, Ops.Item, acc), List.append(&2, Ops.Item, front, items), Cursor.walk(rest, next_pos, left)) : {Ops.apply.go(rest, Ops.land(rest, next_pos, left, next_acc), next_pos, error) == _ : Result<&2, &2, String, List<&2, Ops.Item>>}
      %Equal.sym(Maybe<&2, String>, Maybe.or(&2, String, error, None{}), error, L.or_none(error)) : {Ops.apply.go(rest, Ops.land(rest, next_pos, left, next_acc), next_pos, error) == Cursor.combine(_, List.append(&2, Ops.Item, List.reverse(&2, Ops.Item, acc), List.append(&2, Ops.Item, front, items)), Cursor.walk(rest, next_pos, left)) : Result<&2, &2, String, List<&2, Ops.Item>>}
      %L.insert_acc(items, front, acc) : {Ops.apply.go(rest, Ops.land(rest, next_pos, left, next_acc), next_pos, error) == Cursor.combine(error, _, Cursor.walk(rest, next_pos, left)) : Result<&2, &2, String, List<&2, Ops.Item>>}
      Laws.cursor_walk_equivalent(rest, next_pos, left, next_acc, error)
    case Ops.Op{Ops.Delete{}, at, items} <> rest:
      +front = Cursor.prefix(state, at, pos)
      +left = Cursor.suffix(state, at, pos)
      +moved = List.reverse.go(&2, Ops.Item, front, acc)
      +remaining = List.drop(&2, Ops.Item, left, List.length(&2, Ops.Item, items))
      +agreed = Spec.prefix_matches(items, left)
      +next_pos = Nat.add(at, List.length(&2, Ops.Item, items))
      +failure = Cursor.disagreement(at, agreed)
      +next_error = Maybe.or(&2, String, error, failure)
      %Equal.sym(Ops.Landed, Ops.land(Ops.Op{Ops.Delete{}, at, items} <> rest, pos, state, acc), Ops.Landed{moved, remaining, agreed}, land_delete(at, pos, state, acc, items, rest)) : {Ops.apply.go(Ops.Op{Ops.Delete{}, at, items} <> rest, _, pos, error) == Cursor.combine(error, List.reverse(&2, Ops.Item, acc), Cursor.walk(Ops.Op{Ops.Delete{}, at, items} <> rest, pos, state)) : Result<&2, &2, String, List<&2, Ops.Item>>}
      %L.combine_split(error, failure, List.reverse(&2, Ops.Item, acc), front, Cursor.walk(rest, next_pos, remaining)) : {Ops.apply.go(rest, Ops.land(rest, next_pos, remaining, moved), next_pos, next_error) == _ : Result<&2, &2, String, List<&2, Ops.Item>>}
      %L.reverse_move(front, acc) : {Ops.apply.go(rest, Ops.land(rest, next_pos, remaining, moved), next_pos, next_error) == Cursor.combine(next_error, _, Cursor.walk(rest, next_pos, remaining)) : Result<&2, &2, String, List<&2, Ops.Item>>}
      Laws.cursor_walk_equivalent(rest, next_pos, remaining, moved, next_error)

def Laws.cursor_apply_equivalent(state, doc):
  match doc:
    case Ops.Doc{forgets, result, ops}:
      +actual = Ops.apply.go(ops, Ops.land(ops, 0n, state, Nil{}), 0n, None{})
      +specified = Cursor.walk(ops, 0n, state)
      Equal.cong(Result<&2, &2, String, List<&2, Ops.Item>>, Result<&2, &2, String, List<&2, Ops.Item>>,
        r => Cursor.checked(Ops.in_range(ops, List.length(&2, Ops.Item, state)), result, r),
        actual, specified,
        Equal.trans(Result<&2, &2, String, List<&2, Ops.Item>>, actual, Cursor.combine(None{}, Nil{}, specified), specified,
          Laws.cursor_walk_equivalent(ops, 0n, state, Nil{}, None{}), L.combine_nil(specified)))


def Laws.positional_translation(parent, ops, offset, position):
  Pos.result_shift(parent, ops, offset, position)

def Laws.edit_block_semantics(before, after, stated, edit):
  +parent = List.append(&2, Ops.Item, before, after)
  +ops = Ops.operations(List.length(&2, Ops.Item, before), edit)
  +doc = {Ops.Doc{None{}, stated, ops} : Ops.Doc}
  Equal.trans(Result<&2, &2, String, List<&2, Ops.Item>>, Ops.apply(parent, doc), Cursor.apply(parent, doc), Block.apply(before, after, stated, edit),
    Laws.cursor_apply_equivalent(parent, doc),
    Equal.cong(Result<&2, &2, String, List<&2, Ops.Item>>, Result<&2, &2, String, List<&2, Ops.Item>>,
      r => Cursor.checked(Ops.in_range(ops, List.length(&2, Ops.Item, parent)), stated, r),
      Cursor.walk(ops, 0n, parent), Block.raw(before, after, edit), Pos.cursor_block(before, after, edit)))

def script_semantics.walk(+steps: List<&2, Ops.Step>, +parent: List<&2, Ops.Item>, e: {Ops.in_range(Ops.script(steps, 0n), List.length(&2, Ops.Item, parent)) == True{} : Bool}) -> {Cursor.walk(Ops.script(steps, 0n), 0n, parent) == Cursor.combine(Block.quote_error(parent, Ops.script(steps, 0n)), Nil{}, Done{Spec.result(parent, Ops.script(steps, 0n))}) : Result<&2, &2, String, List<&2, Ops.Item>>}:
  +ops = Ops.script(steps, 0n)
  %Pos.drop_zero(parent) : {Cursor.walk(ops, 0n, _) == Cursor.combine(Block.quote_error(parent, ops), Nil{}, Done{Spec.result_from(_, ops, 0n)}) : Result<&2, &2, String, List<&2, Ops.Item>>}
  Comp.walk_script(steps, 0n, parent, e)

# The range check is shared, so split on it: out of range both sides are
# that refusal; in range the cursor walk is the positional result by the
# induction over the script's blocks.
def script_semantics.checked(+steps: List<&2, Ops.Step>, +parent: List<&2, Ops.Item>, +stated: Maybe<&2, String>, fits: Bool, +e: {Ops.in_range(Ops.script(steps, 0n), List.length(&2, Ops.Item, parent)) == fits : Bool}) -> {Cursor.checked(Ops.in_range(Ops.script(steps, 0n), List.length(&2, Ops.Item, parent)), stated, Cursor.walk(Ops.script(steps, 0n), 0n, parent)) == Cursor.checked(Ops.in_range(Ops.script(steps, 0n), List.length(&2, Ops.Item, parent)), stated, Cursor.combine(Block.quote_error(parent, Ops.script(steps, 0n)), Nil{}, Done{Spec.result(parent, Ops.script(steps, 0n))})) : Result<&2, &2, String, List<&2, Ops.Item>>}:
  match fits:
    case False{}:
      +ops = Ops.script(steps, 0n)
      +len = List.length(&2, Ops.Item, parent)
      +specified = Cursor.combine(Block.quote_error(parent, ops), Nil{}, Done{Spec.result(parent, ops)})
      %Equal.sym(Bool, Ops.in_range(ops, len), False{}, e) : {Cursor.checked(_, stated, Cursor.walk(ops, 0n, parent)) == Cursor.checked(_, stated, specified) : Result<&2, &2, String, List<&2, Ops.Item>>}
      {==}
    case True{}:
      +ops = Ops.script(steps, 0n)
      +len = List.length(&2, Ops.Item, parent)
      +specified = Cursor.combine(Block.quote_error(parent, ops), Nil{}, Done{Spec.result(parent, ops)})
      %Equal.sym(Bool, Ops.in_range(ops, len), True{}, e) : {Cursor.checked(_, stated, Cursor.walk(ops, 0n, parent)) == Cursor.checked(_, stated, specified) : Result<&2, &2, String, List<&2, Ops.Item>>}
      Equal.cong(Result<&2, &2, String, List<&2, Ops.Item>>, Result<&2, &2, String, List<&2, Ops.Item>>,
        r => Cursor.checked(True{}, stated, r),
        Cursor.walk(ops, 0n, parent), specified,
        script_semantics.walk(steps, parent, e))

def Laws.script_semantics(parent, stated, steps):
  +ops = Ops.script(steps, 0n)
  +doc = {Ops.Doc{None{}, stated, ops} : Ops.Doc}
  Equal.trans(Result<&2, &2, String, List<&2, Ops.Item>>, Ops.apply(parent, doc), Cursor.apply(parent, doc), Block.replay(parent, stated, steps),
    Laws.cursor_apply_equivalent(parent, doc),
    script_semantics.checked(steps, parent, stated, Ops.in_range(ops, List.length(&2, Ops.Item, parent)), {==}))

def Laws.ordered_operations_are_scripts(ops, pos, e):
  Comp.is_script(ops, pos, e)

def Laws.ordered_document_semantics(parent, stated, ops, e):
  %Comp.is_script(ops, 0n, e) : {Ops.apply(parent, Ops.Doc{None{}, stated, _}) == Block.replay_ops(parent, stated, _) : Result<&2, &2, String, List<&2, Ops.Item>>}
  Laws.script_semantics(parent, stated, Block.steps_of(ops, 0n))

def Laws.parser_accepts_ordered(s, forgets, result, ops, e):
  Parse.parse_ordered(s, forgets, result, ops, e)

def Laws.parsed_document_semantics(parent, stated, s, forgets, ops, e):
  Laws.ordered_document_semantics(parent, stated, ops, Parse.parse_ordered(s, forgets, stated, ops, e))

def Laws.spell_number(s, n, e):
  Dec.spell_number(s, n, e)

def Laws.write_parse(s, doc, e):
  Spell.write_parse(s, doc, e)

def Laws.diff_applies(parent, child, tbl, doc, e):
  Equal.trans(Result<&2, &2, String, List<&2, Ops.Item>>, Ops.apply(parent, doc), Cursor.apply(parent, doc), Done{child},
    Laws.cursor_apply_equivalent(parent, doc),
    Diff.diff_applies(parent, child, tbl, doc, e))

def Laws.refusal_has_cause(parent, stated, ops, e, msg, r):
  Refuse.refused.of(Ops.in_range(ops, List.length(&2, Ops.Item, parent)), Block.quote_error(parent, ops), Spec.result(parent, ops), stated, msg,
    Equal.trans(Result<&2, &2, String, List<&2, Ops.Item>>, Block.replay_ops(parent, stated, ops), Ops.apply(parent, Ops.Doc{None{}, stated, ops}), Fail{msg},
      Equal.sym(Result<&2, &2, String, List<&2, Ops.Item>>, Ops.apply(parent, Ops.Doc{None{}, stated, ops}), Block.replay_ops(parent, stated, ops), Laws.ordered_document_semantics(parent, stated, ops, e)),
      r))

def Laws.no_cause_replays(parent, stated, ops, e, c):
  Equal.trans(Result<&2, &2, String, List<&2, Ops.Item>>, Ops.apply(parent, Ops.Doc{None{}, stated, ops}), Block.replay_ops(parent, stated, ops), Done{Spec.result(parent, ops)},
    Laws.ordered_document_semantics(parent, stated, ops, e),
    Refuse.accepted.of(Ops.in_range(ops, List.length(&2, Ops.Item, parent)), Block.quote_error(parent, ops), Spec.result(parent, ops), stated, c))
