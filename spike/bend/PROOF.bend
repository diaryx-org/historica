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
import ./revision_lemmas.bend as RevL
import ./diff_lemmas.bend as Diff
import ./refusal_lemmas.bend as Refuse
import ./merge_lemmas.bend as Conv
import ./tree.bend as Tree
import ./tree_lemmas.bend as TL
import ./graph_lemmas.bend as GL
import ./anchor_lemmas.bend as AL
import ./merge.bend as Merge
import ./linear_lemmas.bend as Lin
import ./walk_lemmas.bend as Walk
import ./view_lemmas.bend as View
import ./order_lemmas.bend as Order
import ./similar_lemmas.bend as SimL
import ./emphasis_lemmas.bend as Emph
import ./folder_lemmas.bend as FolderL
import ./target_lemmas.bend as Target
import ./log_lemmas.bend as LogL
import ./fileat_lemmas.bend as FileAt
import ./laid_lemmas.bend as LaidL
import ./blame_lemmas.bend as BlameL
import ./bookmark_lemmas.bend as BmL
import ./abbrev_lemmas.bend as Abbrev
import ./blamed_lemmas.bend as Blamed
import ./diffcmd_lemmas.bend as DiffCmd
import ./logargs_lemmas.bend as LogArgs
import ./check_lemmas.bend as CheckL
import ./show_lemmas.bend as ShowL
import ./hunk_lemmas.bend as HunkL
import ./mark_lemmas.bend as MarkL
import ./sort_lemmas.bend as SortL
import ./pair_lemmas.bend as PairL
import ./survey_lemmas.bend as SurveyL
import ./status_lemmas.bend as StatusL
import ./name_lemmas.bend as NameL
import ./listing_lemmas.bend as ListL
import ./naming_lemmas.bend as NamingL
import ./colour_lemmas.bend as Colour
import ./plan_lemmas.bend as PlanL
import ./chain_lemmas.bend as ChainL
import ./fulls_lemmas.bend as FullsL
import ./sizes_lemmas.bend as SizesL
import ./fetch_lemmas.bend as FetchL
import ./span_lemmas.bend as SpanL
import ./survey.bend as Sv
import ./naming.bend as Naming
import ./store.bend as Store
import ./commands.bend as Main
import ./forget_lemmas.bend as ForgetL
import ./forget.bend as Fg
import ./record_lemmas.bend as RecordL
import ./rewrite_lemmas.bend as RewriteL
import ./update_lemmas.bend as UpdL
import ./conflict_lemmas.bend as ConflictL
import ./merging_lemmas.bend as MergingL
import ./skip_lemmas.bend as SkipL
import ./argv_lemmas.bend as ArgvL
import ./shell_lemmas.bend as ShellL
import ./opening_lemmas.bend as OpeningL
import ./identity_lemmas.bend as IdentityL
import ./arrange_lemmas.bend as ArrangeL
import ./prune_lemmas.bend as PruneL
import ./prune.bend as Prune
import ./receive_lemmas.bend as ReceiveL
import ./offer_lemmas.bend as OfferL
import ./export_lemmas.bend as ExportL
import ./words_lemmas.bend as WordsL
import ./nfc_lemmas.bend as NfcL
import ./fetching_lemmas.bend as FetchingL
import ./manifest_lemmas.bend as ManL
import ./fetchplan_lemmas.bend as FPlanL
import ./escape_lemmas.bend as EscL

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

def Laws.revision_write_parse(s, r, e):
  RevL.write_parse(s, r, e)

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

def Laws.merge_converges(g, a, b, e):
  Conv.merge_converges(g, a, b, e)

def Laws.merge_records_nothing(g, o, past, b):
  Conv.merge_records_nothing(g, o, past, b)

# Plain replay is replay by the cursor specification, one document at a time.
def replay_creplay(docs: List<&2, List<&2, Ops.Op>>, r: Result<&2, &2, String, List<&2, Ops.Item>>) -> {Merge.replay(docs, r) == Lin.creplay(docs, r) : Result<&2, &2, String, List<&2, Ops.Item>>}:
  match docs r:
    case Nil{} Fail{m}:
      {==}
    case Nil{} Done{f}:
      {==}
    case d <> ds Fail{m}:
      {==}
    case +d <> +ds Done{+f}:
      Equal.trans(Result<&2, &2, String, List<&2, Ops.Item>>, Merge.replay(ds, Ops.apply(f, Ops.Doc{None{}, None{}, d})), Merge.replay(ds, Cursor.apply(f, Ops.Doc{None{}, None{}, d})), Lin.creplay(ds, Cursor.apply(f, Ops.Doc{None{}, None{}, d})),
        Equal.cong(Result<&2, &2, String, List<&2, Ops.Item>>, Result<&2, &2, String, List<&2, Ops.Item>>, x => Merge.replay(ds, x), Ops.apply(f, Ops.Doc{None{}, None{}, d}), Cursor.apply(f, Ops.Doc{None{}, None{}, d}), Laws.cursor_apply_equivalent(f, Ops.Doc{None{}, None{}, d})),
        replay_creplay(ds, Cursor.apply(f, Ops.Doc{None{}, None{}, d})))

def Laws.merge_linear(docs, f, o, e):
  Lin.merge_linear_c(docs, f, Lin.all_strict_of(docs, o),
    Equal.trans(Result<&2, &2, String, List<&2, Ops.Item>>, Lin.creplay(docs, Done{Nil{}}), Merge.replay(docs, Done{Nil{}}), Done{f},
      Equal.sym(Result<&2, &2, String, List<&2, Ops.Item>>, Merge.replay(docs, Done{Nil{}}), Lin.creplay(docs, Done{Nil{}}), replay_creplay(docs, Done{Nil{}})), e))

def Laws.merge_walk_invariant(g, o, t, d, e):
  Walk.walk_invariant_c(g, o, t, d, e)

def Laws.view_keeps_invariant(g, o, t, s, d, c, e):
  View.view_invariant(g, o, t, s, d, c, e)

def Laws.merge_extends(g, p, e, past, d, f0, f1, hd, he, hs, hg, ho, hm, ha):
  Walk.merge_extends_c(g, p, e, past, d, f0, f1, hd, he, hs, hg, ho, hm,
    Equal.trans(Result<&2, &2, String, List<&2, Ops.Item>>, Cursor.apply(f0, Ops.Doc{None{}, None{}, d}), Ops.apply(f0, Ops.Doc{None{}, None{}, d}), Done{f1},
      Equal.sym(Result<&2, &2, String, List<&2, Ops.Item>>, Ops.apply(f0, Ops.Doc{None{}, None{}, d}), Cursor.apply(f0, Ops.Doc{None{}, None{}, d}), Laws.cursor_apply_equivalent(f0, Ops.Doc{None{}, None{}, d})),
      ha))

def Laws.merge_intent(g, p, e, past, d, t, f1, hd, he, hc, hg, ho, hw, ha):
  View.merge_intent_c(g, p, e, past, d, t, f1, hd, he, hc, hg, ho, hw,
    Equal.trans(Result<&2, &2, String, List<&2, Ops.Item>>, Cursor.apply(Merge.file(Merge.restrict(t, past)), Ops.Doc{None{}, None{}, d}), Ops.apply(Merge.file(Merge.restrict(t, past)), Ops.Doc{None{}, None{}, d}), Done{f1},
      Equal.sym(Result<&2, &2, String, List<&2, Ops.Item>>, Ops.apply(Merge.file(Merge.restrict(t, past)), Ops.Doc{None{}, None{}, d}), Cursor.apply(Merge.file(Merge.restrict(t, past)), Ops.Doc{None{}, None{}, d}), Laws.cursor_apply_equivalent(Merge.file(Merge.restrict(t, past)), Ops.Doc{None{}, None{}, d})),
      ha))

def Laws.insert_at_gap(t, at, nm, it, left, inv, fr, lo):
  AL.insert_at(t, at, nm, it, left, inv, fr, lo)

def Laws.invariant_empty():
  AL.invariant_nil()

def Laws.insert_keeps_invariant(t, nm, it, left, inv, fr, lo):
  AL.invariant_attach(t, Merge.Node{nm, it, Merge.anchor(t, left), Nil{}}, left, inv, fr, {==}, lo)

def Laws.mark_keeps_invariant(t, target, by, inv):
  AL.invariant_mark(t, target, by, inv)

def Laws.one_file_per_path(t, r, t2, q, e):
  TL.fits_alone(Tree.at(t2, q), TL.path_fits(t2, q, Nil{}, TL.wf_paths(t2, TL.apply_wf(t, r, t2, e))))

def Laws.no_link_dangles(t, r, t2, e):
  TL.wf_dangling(t2, TL.apply_wf(t, r, t2, e))

def Laws.kind_fixed(t, r, t2, x, k, e, h):
  TL.apply_kinds(t, r, t2, x, k, e, h)

def Laws.replay_one_file_per_path(rs, t, q, e):
  TL.fits_alone(Tree.at(t, q), TL.path_fits(t, q, Nil{}, TL.wf_paths(t, TL.replay_wf(rs, t, e))))

def Laws.replay_no_link_dangles(rs, t, e):
  TL.wf_dangling(t, TL.replay_wf(rs, t, e))

def Laws.move_then_drop(t, e, p):
  match e:
    case Tree.Entry{+f, old, k, y, g, m}:
      TL.remove_insert(t, Tree.Entry{f, p, k, y, g, m})

def Laws.merge_parents_unordered(es, es2, m, a, e):
  GL.merge_alike(es, es2, m, a, e)

def Laws.walked_order_causal(g, h):
  Order.order_causal(g, h)

def Laws.walked_reads_every_order(head, file, names, g, b, w, hb, hc, hs, ht, e):
  Order.reads_every_order(head, file, names, g, b, w, hb, hc, hs, ht, e)

def Laws.walked_file_every_order(fs, ds, head, file, ss, g, b, w, hs, hg, hb, hc, hu, ht, e):
  Order.file_every_order(fs, ds, head, file, ss, g, b, w, hs, hg, hb, hc, hu, ht, e)

def Laws.similar_diff_applies(parent, child, tbl, doc, e):
  Equal.trans(Result<&2, &2, String, List<&2, Ops.Item>>, Ops.apply(parent, doc), Cursor.apply(parent, doc), Done{child},
    Laws.cursor_apply_equivalent(parent, doc),
    SimL.similar_applies(parent, child, tbl, doc, e))

def Laws.emphasis_keeps_was(was, now, w, n, e):
  Emph.apart_was(was, now, w, n, e)

def Laws.emphasis_keeps_now(was, now, w, n, e):
  Emph.apart_now(was, now, w, n, e)

def Laws.emphasis_marks_its_own_line(ns, paint):
  MarkL.emph_fit(ns, paint)

def Laws.listing_skips_nothing(ls, prefix, rules, l, h):
  FolderL.listing_ok(ls, prefix, rules, l, h)

def Laws.target_is_held(fs, bs, spelling, id, e):
  Target.resolve_mem(fs, bs, spelling, id, e)

def Laws.log_lists_what_it_asks(fl, fs, limit):
  LogL.listed_ok(fl, fs, limit)

def Laws.file_is_held(id, bs, path, t, f, e):
  FileAt.file_ok(id, bs, path, t, f, e)

def Laws.laid_keeps_parent(parent, doc):
  LaidL.laid_keeps_parent(parent, doc)

def Laws.laid_reads_child(parent, doc, child, e):
  LaidL.laid_reads_child(parent, doc, child, Equal.trans(Result<&2, &2, String, List<&2, Ops.Item>>, Cursor.apply(parent, doc), Ops.apply(parent, doc), Done{child}, Equal.sym(Result<&2, &2, String, List<&2, Ops.Item>>, Ops.apply(parent, doc), Cursor.apply(parent, doc), Laws.cursor_apply_equivalent(parent, doc)), e))

def Laws.diff_hunks_apply(parent, doc, child, e):
  HunkL.hunks_patch(parent, doc, child, Laws.laid_keeps_parent(parent, doc), Laws.laid_reads_child(parent, doc, child, e))

def Laws.blame_shows_the_folder(rows, text):
  BlameL.folder_lines(rows, text)

def Laws.rules_are_well_formed(text):
  FolderL.rules_ok(text)

def Laws.bookmark_reads_back(t, p, h):
  BmL.reads_back(t, p, h)

def Laws.abbreviation_is_a_prefix(id, among):
  Abbrev.prefix_ok(id, among)

def Laws.abbreviation_names_one(id, among, other, m, ne, len):
  Abbrev.unique(id, among, other, m, ne, len)

def Laws.blame_reads_the_walk(oldest, ds, id, file, rs, e):
  Blamed.rows_walked(oldest, ds, id, file, rs, e)

def Laws.blame_numbers_its_lines(rs, span, bl, e):
  Blamed.span_lines(rs, span, bl, e)

def Laws.blame_prints_each_line(fs, cs, rs, span, out, e):
  Blamed.printed_lines(fs, cs, rs, span, out, e)

def Laws.blame_reads_the_position(fs, bs, sp, p, e):
  Blamed.position_ok(fs, bs, sp, p, e)

def Laws.blame_reads_a_held_file(fs, bs, target, sp, p, e):
  Blamed.picked_ok(fs, bs, target, sp, p, e)

def Laws.blame_prints_the_walk(fs, all, id, file, span, out, e, w, ew):
  Blamed.recorded_printed(fs, all, id, file, span, out, e, w, ew)

def Laws.blame_prints_the_folder(fs, path, k, bs, rows, span, out, e):
  Blamed.folder_printed(fs, path, k, bs, rows, span, out, e)

def Laws.blame_reads_its_words(bs, args, b, e):
  Blamed.args_said(bs, args, b, e)

def Laws.blame_reads_a_folder_file(path, t, file, found, k, e):
  Blamed.checked_ok(path, t, file, found, k, e)

def Laws.diff_reads_its_words(bs, args, cmd, e):
  DiffCmd.args_said(bs, args, cmd, e)

def Laws.diff_compares_with_the_parent(fs, bs, right, onto, l, e):
  DiffCmd.left_ok(fs, bs, right, onto, l, e)

def Laws.diff_folder_compares_with_a_held_revision(fs, bs, onto, l, e):
  DiffCmd.wc_left_ok(fs, bs, onto, l, e)

def Laws.diff_limits_to_a_held_file(fs, bs, right, only, lim, e):
  DiffCmd.limit_ok(fs, bs, right, only, lim, e)

def Laws.diff_folder_limits_to_a_held_file(fs, bs, left, only, lim, e):
  DiffCmd.wc_limit_ok(fs, bs, left, only, lim, e)

def Laws.diff_shows_what_differs(sd, l, files, cs, e):
  DiffCmd.compare_ok(sd, l, files, cs, e)

def Laws.diff_folder_keeps_what_the_limit_wants(t, found, l):
  DiffCmd.heres_ok(t, found, l)

def Laws.diff_folder_shows_what_differs(t, older, ds, left, reads, ps, cs, e):
  DiffCmd.wc_compare_ok(t, older, ds, left, reads, ps, cs, e)

def Laws.diff_colour_changes_no_character(cs):
  Colour.colour_fit(cs)

def Laws.diff_folder_plans_by_the_edits_it_fetches(dg, os, eds, all, hs, h):
  FetchL.plans_fetched(dg, os, eds, all, hs, h)

def Laws.diff_asks_every_payload_it_shows(cs, d):
  FetchL.payloads_shown(cs, d)

def Laws.diff_asks_each_payload_once(cs):
  FetchL.payloads_once(cs)

def Laws.diff_stats_where_each_payload_was_found(root, ds, at):
  FetchL.sizes_located(root, ds, at)

def Laws.reading_finds_what_resolutions_keep(ds, more, h):
  FetchL.kept_found(ds, more, h)

def Laws.chain_follows_first_parents(fs, id):
  ChainL.chain_whole(fs, id)

def Laws.revisions_read_are_their_documents(root, ds):
  FullsL.fulls_filed(root, ds)

def Laws.log_reads_its_words(args, a, e):
  LogArgs.args_said(args, a, e)

def Laws.cat_reads_a_held_file(fs, bs, target, path, p, e):
  ShowL.cat_ok(fs, bs, target, path, p, e)

def Laws.show_names_a_held_file(fs, bs, id, p, file, e):
  ShowL.file_ok(fs, bs, id, p, file, e)

def Laws.show_prints_a_held_document(id, d, ds, text, e):
  ShowL.doc_ok(id, d, ds, text, e)

def Laws.show_prints_what_the_revision_states(id, file, ds, s, text, e):
  ShowL.said_ok(id, file, ds, s, text, e)

def Laws.diff_pairs_each_file(xs, ys, f):
  PairL.pairs_by_file(xs, ys, f)

def Laws.walk_refuses_nothing_skipped(ls, prefix, rules, after, acc, h):
  SurveyL.refusals_ok(ls, prefix, rules, after, acc, h)

def Laws.status_says_an_arrival_once(os, links):
  Equal.trans(Bool, Sv.arrives_once.list(Sv.added(os), Sv.facts(os, links)), Sv.arrives_once(Set.from_list(Sv.added(os)), Sv.facts(os, links)), True{}, Equal.sym(Bool, Sv.arrives_once(Set.from_list(Sv.added(os)), Sv.facts(os, links)), Sv.arrives_once.list(Sv.added(os), Sv.facts(os, links)), SurveyL.arrives_list(Sv.added(os), Sv.facts(os, links))), SurveyL.facts_ok(Set.from_list(Sv.added(os)), os, links))

def replay_doc_fail(+e: String, text: String, is_ops: Bool) -> {Main.replay.doc(Fail{e}, text, is_ops) == Fail{e} : Result<&2, &2, String, List<&2, Ops.Item>>}:
  match is_ops:
    case True{}:
      {==}
    case False{}:
      {==}

def Laws.replay_keeps_a_refusal(ds, e):
  match ds:
    case Nil{}:
      {==}
    case Store.Doc{+path, id, size, +text} <> rest:
      %Equal.sym(Result<&2, &2, String, List<&2, Ops.Item>>, Main.replay.doc(Fail{e}, text, String.ends_with(path, ".ops.txt")), Fail{e}, replay_doc_fail(e, text, String.ends_with(path, ".ops.txt"))) : {Main.replay.go(rest, _) == Fail{e} : Result<&2, &2, String, List<&2, Ops.Item>>}
      Laws.replay_keeps_a_refusal(rest, e)

def Laws.opdiff_replays_to_the_child(parent, child, doc, e):
  Laws.diff_applies(Ops.from_text(parent), Ops.from_text(child), BlameL.tbl_text(child), doc, e)

def Laws.status_reads_its_words(args, cmd, e):
  StatusL.args_said(args, cmd, e)

def Laws.status_joins_held_revisions(fs, bs, onto, ms, ps, e):
  StatusL.parents_held(fs, bs, onto, ms, ps, e)

def Laws.name_stays_in_names(n, e):
  NameL.stays(n, e)

def Laws.forgetting_keeps_shape(ops, ps, t, i):
  ForgetL.ops_shape(ops, ps, t, i)

def Laws.forgetting_a_resolution_keeps_shape(pieces, ps, t, i):
  ForgetL.pieces_shape(pieces, ps, t, i)

def Laws.forget_rewrites_only_the_files_documents(fs, ds, id, file, first, last, ts, ws, a, n, e):
  ForgetL.rewrites(fs, ds, id, file, first, last, ts, ws, a, n, e)

def Laws.forget_whole_takes_one_payload(file, payload, files, stood, n, ts, ws, a, m, e):
  ForgetL.takes_one(file, payload, files, stood, n, Fg.Fg.Plan{ts, ws, a, m}, e)

def Laws.forget_counts_only_other_versions(fs, file, t):
  ForgetL.others_exclude(fs, file, t)

def Laws.forget_destroys_only_what_it_forgets(fs, ts, p, e):
  ForgetL.destroys(fs, ts, p, e)

def Laws.forget_reads_its_words(ws, t, p, sp, d, f, e):
  ForgetL.reads_words(ws, t, p, sp, d, f, e)

def Laws.forget_clears_only_copies(ps, p, e):
  ForgetL.clears(ps, p, e)

def Laws.standin_replays_like_what_it_stands_in_for(st1, st2, f, r, ops1, f2, ops2, hs, hops):
  ForgetL.replays_like(st1, st2, f, r, ops1, f2, ops2, hs, hops)

def Laws.chain_replays_like_through_standins(ds1, ds2, r1, r2, hd, hr):
  ForgetL.chain_like(ds1, ds2, r1, r2, hd, hr)

def Laws.forgetting_destroys_only_text(ops, ps, t, i):
  ForgetL.ops_forgot(ops, ps, t, i)

def Laws.standins_beside_only_forget(ds, ops):
  ForgetL.only_forget(ds, ops)

def Laws.standins_beside_forget_all_they_say(f, r, stated, rest, held, e):
  ForgetL.forgets_all(f, r, stated, rest, held, e)

def Laws.standins_fold_in_any_order(a, b, rest, held):
  ForgetL.folded_swap(a, b, rest, held)

def Laws.name_reads_its_words(ws):
  NameL.args_said(ws)

def Laws.name_does_what_it_reads(c, p, e):
  NameL.plan_meant(c, p, e)

def Laws.name_deletes_the_bookmark_named(bs, n):
  NameL.found_gone(bs, n)

def Laws.name_states_what_it_set(n, b, early, shared):
  NameL.said_fields(n, b, early, shared)

def Laws.files_lists_in_path_order(t):
  Blamed.and_tt(SortL.sorted(~Tree.Entry, ~(e => Main.files.key(e)), Main.files.listed(t)), Main.ends_all(Main.files.said(t), Main.files.ends(t)), ListL.files_sorted(t), ListL.said_ends(t))

def Laws.files_lists_the_tree(t, k):
  ListL.files_keyed(t, k)

def Laws.bookmark_file_reads_back(n, ok):
  ListL.name_back(n, ok)

def Laws.bookmarks_read_in_name_order(ps):
  ListL.order_sorted(ps)

def Laws.bookmarks_read_each_once(ps, k):
  ListL.order_keyed(ps, k)

def Laws.names_lists_each_bookmark(fs, bs):
  ListL.said_begun(fs, bs)

def Laws.names_resolves_to_held(fs, here, t):
  ListL.resolution_ok(fs, here, t)

def Laws.log_fields_lists_what_it_keeps(fs, bs, sp, shown, fl, limit):
  ListL.fields_listed(fs, bs, sp, shown, fl, limit)

def Laws.log_counts_each_fact(sets, facts):
  ListL.figures_counted(~sets, facts)

def Laws.log_follows_a_held_file(fs, bs, sp, path, at, file, ea, e):
  ListL.followed_held(fs, bs, sp, path, at, file, ea, e)

def Laws.status_says_what_it_found(fs, bs, ps, cs, sv):
  StatusL.report_says(fs, bs, ps, cs, sv)

def Laws.status_says_each_contest(ps, cs):
  StatusL.contests_said(ps, cs)

def Laws.status_compares_with_the_revisions_tree(fs, p):
  StatusL.one_tree(fs, p)

def Laws.status_reads_only_lines(dg, bf, eds, os, hs):
  StatusL.reads_only_lines(dg, bf, eds, os, hs)

def Laws.status_believes_what_is_stated(older, ds, left, eds, os, hs, m, e, h):
  StatusL.believes(older, ds, left, eds, os, hs, m, e, h)


def Laws.status_refuses_what_the_folder_holds(t, held, walked, ss):
  SurveyL.refused_ok(t, held, walked, ss)

def Laws.a_revision_is_filed_under_its_month(when, message, change, id, ns, hw, hc, hi):
  NamingL.stem_ok(when, message, change, id, ns, hw, hc, hi)

def Laws.content_is_filed_under_a_name_a_filesystem_holds(fs, held, hf, hh):
  NamingL.filed_as_ok(Naming.filed(fs), held, NamingL.filed_ok(fs, hf), hh)

def reason_pick(b: Bool, -r: Main.Refused) -> {Result.is_done(&2, &2, Main.Refused, Unit, Bool.pick(Result<&2, &2, Main.Refused, Unit>, b, Fail{r}, Done{Unit{}})) == Bool.not(b) : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def Laws.abandon_takes_a_reason_that_says_something(m):
  %NamingL.blank(m) : {Result.is_done(&2, &2, Main.Refused, Unit, Main.reason.r(m)) == Bool.not(_) : Bool}
  reason_pick(String.is_empty(Naming.trim_space(m)), Main.Refused{1, "abandoning removes this work from what the history means, and the reason is the only thing the tombstone carries; say why with -m"})

def Laws.a_rename_keeps_each_file_once(t, ats, ms, t2, moved, e):
  %Equal.sym(Tree.Tree(), t2, Sv.moved_all(moved, t), SurveyL.placed_moved(t, ats, ms, t2, moved, e)) : {Sv.files(_) == Sv.files(t) : List<&2, String>}
  SurveyL.files_moved(moved, t)

def Laws.a_summary_fits_its_limit(message, change):
  NamingL.summary_fits(message, change)

def Laws.a_summary_gives_up_its_ends(message, change, hc):
  NamingL.summary_trimmed(message, change, hc)

def Laws.status_offers_a_rename_the_bytes_make(t, held, walked, ss):
  SurveyL.renames_good(List.append(&2, Sv.Obs, Sv.seens(ss), Sv.claimed_drops(t, Sv.claims(t), held)))

def Laws.record_plans_in_file_order(t):
  SurveyL.by_file_ordered(t)

def Laws.record_plans_every_file(t, f):
  SurveyL.by_file_keeps(t, f)

def Laws.record_goes_on_where_each_path_holds_one_file(t, looked, held, walked, ss, moves, accepted, done, e, p):
  SurveyL.path_once(looked, p, SurveyL.planned_claims(looked, Sv.planned(t, looked, held, walked, ss, moves), accepted, done, e))

def Laws.a_link_resolves_inside_the_folder(link, target, p, h, e):
  SurveyL.link_inside(link, target, p, h, e)

def Laws.abandon_takes_a_line(fs, id, only, run, e):
  RewriteL.plan_line(fs, id, only, run, e)

def Laws.reword_changes_only_the_message(fs, prev, standing, m, reviser, revised, doc, e):
  RewriteL.reword_ok(fs, prev, standing, m, reviser, revised, doc, e)

def Laws.carry_carries_a_held_revision(fs, bs, named, id, e):
  RewriteL.carry_held(fs, bs, named, id, e)

def Laws.record_moves_only_held_files(t, ats, ms, p, e):
  RecordL.placed_held(t, ats, ms, p, e)

def Laws.record_says_an_arrival_once(t, looked, held, walked, ss, moves):
  RecordL.planned_once_list(t, looked, held, walked, ss, moves)

def Laws.writes_say_what_they_wrote(a, when, m, facts, change, id, names, ps, prev, carrying, steps, run, dry):
  RewriteL.writes_fields(a, when, m, facts, change, id, names, ps, prev, carrying, steps, run, dry)

def Laws.amend_keeps_what_it_added(arriving, kept, hex):
  RewriteL.amend_minted_ok(arriving, kept, hex)

def Laws.abandon_dry_run_names_the_run(fs, bs, id, only, run):
  RewriteL.dry_names(fs, bs, id, only, run)

def Laws.update_reads_its_words(ws, c, e):
  UpdL.args_said(ws, c, e)

def Laws.merge_resolution_reads_back(ds, j, s, hm, doc, e):
  ConflictL.resolved(ds, j, s, hm, doc, e)

def Laws.merge_renders_the_uncontested_as_itself(j, e):
  ConflictL.render_plain(j, e)

def Laws.status_surveys_each_path(t, stats, bf, reads, props, hs):
  StatusL.seens_ok(t, Main.regular_paths(hs), stats, bf, reads, props, hs)

def Laws.record_refuses_only_what_it_looks_at(only, t, t0, found, walked, held, dg, bf, reads, props, moves):
  SurveyL.restricted_ok(only, t, t0, found, walked, held, dg, bf, reads, props, moves)

def Laws.merge_joins_held_revisions(fs, bs, ss, xs, e):
  MergingL.joined_held(fs, bs, ss, xs, e)

def Laws.merge_joins_every_head(fs, bs, ss, xs, e):
  MergingL.joined_all(fs, bs, ss, xs, e)

def Laws.check_pairs_each_payload(fs, stats, h):
  CheckL.pairs_ok(fs, stats, h)

def Laws.check_walks_causally(fuel, g, ixs):
  CheckL.kahn_causal(fuel, g, ixs, Nil{}, {==})

def Laws.argv_reads_its_words(ds, w, rest, e):
  ArgvL.reads(ds, w, rest, e)

def Laws.argv_reads_the_version(ds, v, rest, h):
  ArgvL.reads_version(ds, v, rest, h)

def Laws.argv_reads_help(ds, v, rest, h):
  ArgvL.reads_help(ds, v, rest, h)

def Laws.dispatch_runs_no_path(base, w, args, d, p, as, e):
  ShellL.runs(base, w, args, d, p, as, e)

def Laws.header_opens_under_a_note(note):
  OpeningL.noted(note)

def Laws.identity_reads_back(file, a, directory, home, h):
  IdentityL.reads_back(file, a, directory, home, h)

def Laws.check_reads_its_words(ws):
  CheckL.reads_words(ws)

def Laws.check_finds_nothing_in_a_new_store(root):
  CheckL.fresh(root)

def Laws.skip_rules_equal_only_when_equal(a, b, e):
  SkipL.rule_eq_sound(a, b, e)

def Laws.skip_rule_equals_itself(a):
  SkipL.rule_eq_refl(a)

def Laws.skip_path_rule_reads_back(file, v, directory, private, sc, e, h):
  SkipL.scoped_reads(file, v, directory, private, sc, e, h)

def Laws.skip_name_rule_reads_back(file, n, private, sc, e):
  SkipL.named_reads(file, n, private, sc, e)

def Laws.skip_path_rule_skips_under_its_path(v, directory, sc, e, x, q):
  SkipL.scoped_skips(v, directory, sc, e, x, q)

def Laws.skip_lists_each_rule_once(ss):
  SkipL.lists_once(ss)

def Laws.skip_writes_what_is_new(rs, had):
  SkipL.writes_new(rs, had)

def Laws.update_lands(fs, id, t, rs, walked, found, dg, ls, located, ds, more, p, e):
  UpdL.plan_holds(fs, id, t, rs, walked, found, dg, ls, located, ds, more, p, e)

def Laws.update_spares_the_unrecorded(fs, id, t, rs, walked, found, dg, ls, located, ds, more, p, e):
  UpdL.plan_touches(fs, id, t, rs, walked, found, dg, ls, located, ds, more, p, e)

def Laws.update_again_keeps(w, h, rs, rs2, e):
  UpdL.again_keeps(w, h, rs, rs2, e)

def Laws.update_settles_only_what_stays(p, e):
  UpdL.settled_same(p, e)

def Laws.merge_spares_the_unrecorded(fs, ds, heads, bs, t, dg, texts, ls, cs, located, es):
  MergingL.spares(fs, ds, heads, bs, t, dg, texts, ls, cs, located, es)

def Laws.merge_sets_aside_the_claims(cs):
  MergingL.aside(cs)

def Laws.arrange_reads_its_words(ws):
  WordsL.arrange_words(ws)

def Laws.arrange_plans_no_overwrite(refile, fs, revs, ops, ls, a, e, from, to, h):
  ArrangeL.no_overwrite(refile, fs, revs, ops, ls, a, e, from, to, h)

def Laws.arrange_keeps_a_revision_where_it_sits(fs, revs, ops, ls, a, e):
  ArrangeL.kept(fs, revs, ops, ls, a, e)

def Laws.arrange_opens_what_parses(pre, path, id, size, text, post, msg, hp, hf):
  ArrangeL.opens(pre, path, id, size, text, post, msg, hp, hf)

def Laws.arrange_counts_every_file(refile, fs, revs, ops, ls, a, e):
  ArrangeL.counts(refile, fs, revs, ops, ls, a, e)

def Laws.arrange_moves_each_file_once(refile, fs, revs, ops, ls, a, e, x):
  ArrangeL.once(refile, fs, revs, ops, ls, a, e, x)

def Laws.prune_reads_its_words(ws):
  WordsL.prune_words(ws)

def Laws.prune_keeps_what_work_stands_on(fs, id, hf, hk):
  PruneL.stands(fs, id, hf, hk)

def Laws.prune_lets_go_only_what_is_superseded(fs, id, hf, hk):
  PruneL.superseded_gone(fs, id, hf, hk)

def Laws.prune_dry_run_names_what_prune_removes(s):
  PruneL.dry_run(Prune.stored.plan(s))

def Laws.prune_clears_only_derived_files(ls, x, h):
  PruneL.cached(ls, x, h)

def Laws.prune_removes_only_unneeded_content(fs, revs, bs, ps, d, h):
  PruneL.removes(fs, revs, bs, ps, d, h)

def Laws.receive_takes_only_revisions_it_lacks(here, there, join, p, e, id, text, h):
  ReceiveL.revisions(here, there, join, p, e, id, text, h)

def Laws.receive_takes_only_documents_it_lacks(here, there, id, text, h):
  ReceiveL.documents(here, there, id, text, h)

def Laws.receive_takes_only_payloads_it_lacks(here, there, path, d, h):
  ReceiveL.payloads(here, there, path, d, h)

def Laws.receive_joins_only_related_histories(here, there, join, hh, ht):
  ReceiveL.joins(here, there, join, hh, ht)

def Laws.receive_moves_no_bookmark(here, there, n, at, h):
  ReceiveL.moves_none(here, there, n, at, h)

def Laws.receive_destroys_only_what_is_forgotten(here, there, d, h):
  ReceiveL.destroyed(here, there, d, h)

def Laws.offer_lines_read_back(k, d, g, p, rest, nh, hk, hd, hg):
  OfferL.line_back(k, d, g, p, rest, nh, hk, hd, hg)

def Laws.offer_lists_forgetting_as_prune_reads_it(path, id, text):
  OfferL.catalogue(path, id, text)

def Laws.offer_names_no_private_bookmark(prefix, s, bs, claims, rids, nids):
  OfferL.bookmarks(prefix, s, bs, claims, rids, nids)

def Laws.offer_names_no_private_rule(prefix, s, bs, claims, rids, nids):
  OfferL.rules(prefix, s, bs, claims, rids, nids)

def Laws.export_lays_out_every_path(ps, t, fs, ds, id, pays, bs):
  ExportL.laid(ps, t, fs, ds, id, pays, bs)

def Laws.export_names_only_what_travels(bs, pt):
  ExportL.names(bs, pt)

def Laws.export_states_no_private_rule(rs):
  ExportL.rules(rs)

def Laws.export_writes_over_no_unrecorded_work(os, ss, dirs, others, whole, rs):
  ExportL.steps_safe(os, ss, dirs, others, whole, rs)

def Laws.export_removes_only_recorded_files(ss, placed, whole, rs):
  ExportL.removes_safe(ss, placed, whole, rs)

def Laws.export_reads_its_words(ws):
  WordsL.export_words(ws)

def Laws.export_writes_only_where_a_copy_may_go(into, l, store):
  ExportL.dest(into, l, store)

def Laws.export_lays_each_file_as_the_tree_has_it(ps, t, fs, ds, id, pays, bs):
  ExportL.laid_all(ps, t, fs, ds, id, pays, bs)

def Laws.export_carries_only_this_stores_files(held, t, ds, ps, bodies, rs, bs, claims):
  ExportL.plan_from(held, t, ds, ps, bodies, rs, bs, claims)

def Laws.export_renames_nothing_a_copy_holds(fs, held, ex, id, s, e, m):
  ExportL.stems_kept(fs, held, ex, id, s, e, m)

def Laws.receive_removes_only_the_originals(bs, ps, des, x, h):
  ReceiveL.removes_only(bs, ps, des, x, h)

def Laws.receive_trusts_what_it_plans_from(other, root, pre, path, id, size, text, post, revs, od, bs, ps, names, rules, marks, claims, join, msg, hp, hf):
  ReceiveL.trusts(other, root, pre, path, id, size, text, post, revs, od, bs, ps, names, rules, marks, claims, join, msg, hp, hf)

def Laws.receive_reads_its_words(ws):
  WordsL.receive_words(ws)

def Laws.offer_reads_its_words(ws):
  WordsL.offer_words(ws)

def Laws.export_lays_out_only_what_the_walk_offers_back(t, fs, ds, id, pays, bs, rules):
  ExportL.folder_clear(t, fs, ds, id, pays, bs, rules)

def Laws.export_destroys_only_what_is_forgotten(p, here, cst, marks, d, h):
  ExportL.destroyed(p, here, cst, marks, d, h)

def Laws.offer_names_each_file_by_its_digest(prefix, s, marks, claims, rids, nids):
  OfferL.digests(prefix, s, marks, claims, rids, nids)

def Laws.nfc_leaves_ascii(s, h):
  NfcL.leaves_ascii(s, h)

def Laws.nfc_orders_marks_by_class(ms):
  NfcL.orders_by_class(ms)

def Laws.nfc_ordering_keeps_every_mark(ms, k):
  NfcL.keeps_each_class(ms, k)

def Laws.nfc_class_misses_nothing(c):
  NfcL.class_misses_nothing(c)

def Laws.nfc_leaves_separators_alone():
  NfcL.separators_inert()

def Laws.the_walk_yields_a_path_once(fs):
  NfcL.walk_once(fs)

def Laws.the_folder_spells_what_is_opened(ls, want):
  NfcL.spelled_there(ls, want)

def Laws.a_name_that_cannot_be_spelled_is_refused(es, prefix, dir):
  NfcL.all_refused(es, prefix, dir)

def Laws.fetch_reads_its_words(ws):
  WordsL.fetch_words(ws)

def Laws.fetch_asks_under_the_manifests_directory(url, r, m, e):
  FetchingL.addressed_ok(url, r, m, e)

def Laws.fetch_asks_only_for_what_the_manifest_names(h, os):
  FetchingL.asks_what_is_named(h, os)

def Laws.fetch_files_only_text_that_hashes_to_its_line(root, held, o, g, at, t, e):
  FetchingL.filed_is_its_digest(root, held, o, g, at, t, e)

def Laws.fetch_lands_a_file_only_where_it_hashes_to_its_line(folder, name, o, g, f, a, b, e):
  FetchingL.moved_is_its_digest(folder, name, o, g, f, a, b, e)

def Laws.fetch_files_a_payload_under_what_it_hashes_to(root, o, g, f, a, b, e):
  FetchingL.payload_lands_under_its_digest(root, o, g, f, a, b, e)

def Laws.record_reads_its_words(args, o, ms, ac, at, mv, ks, ns, d, f, mg, e, v):
  RecordL.words_read(args, o, ms, ac, at, mv, ks, ns, d, f, mg, e, v)

def Laws.record_reads_renames_and_paths(args, o, ms, ac, at, mv, ks, ns, d, f, mg, e, a, b, ha, p, hp, hn, hs):
  RecordL.renames_read(args, o, ms, ac, at, mv, ks, ns, d, f, mg, e, a, b, ha, p, hp, hn, hs)

def Laws.amend_reads_its_words(args, m, mv, o, n, d, f, y, e, v, a, b, ha, w, hw):
  RecordL.amend_reads_its_words_ok(args, m, mv, o, n, d, f, y, e, v, a, b, ha, w, hw)

def Laws.abandon_reads_its_words(args, m, mv, o, n, d, f, y, e, v, a, b, ha, w, hw):
  RecordL.abandon_reads_its_words_ok(args, m, mv, o, n, d, f, y, e, v, a, b, ha, w, hw)

def Laws.carry_reads_its_words(args, m, mv, o, n, d, f, y, e, v, a, b, ha, w, hw):
  RecordL.carry_reads_its_words_ok(args, m, mv, o, n, d, f, y, e, v, a, b, ha, w, hw)

def Laws.record_states_the_folder(older, ds, left, dg, reads, t, hs, ks, moves, obs, ls, mint, bs, e):
  RecordL.drafted_state(~(p => c => tbl => d => e2 => Laws.diff_applies(p, c, tbl, d, e2)), older, ds, left, dg, reads, t, hs, ks, moves, obs, ls, mint, bs, e)

def Laws.record_resolves_as_the_walk_proposes(fs, ds, ps, reads, dg, t, hs, ks, moves, obs, ls, mint, bs, e):
  RecordL.drafted_resolves(fs, ds, ps, reads, dg, t, hs, ks, moves, obs, ls, mint, bs, e)

def Laws.record_names_what_it_writes(a, when, message, fl, hex, befores, fs, bs, ps, t, hs, dg, reads, ks, moves, obs, ls):
  RecordL.names_ok(a, when, message, fl, hex, befores, fs, bs, ps, t, hs, dg, reads, ks, moves, obs, ls)

def Laws.record_moves_the_bookmarks_on_its_parents(a, when, message, fl, hex, befores, fs, bs, ps, t, hs, dg, reads, ks, moves, obs, ls, k, p, hp, m, f, hf, hid, hfirst, i, n, pr, hi):
  RecordL.parents.move(fs, ps, bs, k, p, hp, m, f, hf, hid, hfirst, i, n, pr, hi)

def Laws.record_moves_only_the_bookmarks_on_its_parents(a, when, message, fl, hex, befores, fs, bs, ps, t, hs, dg, reads, ks, moves, obs, ls, j, b, hj):
  RecordL.parents.moved(fs, ps, bs, j, b, hj)

def Laws.record_writes_only_what_is_settled(t, looked, held, walked, ss, moves, accepted, pl2, e, x):
  RecordL.settled_read(t, looked, held, walked, ss, moves, accepted, pl2, e, x)

def Laws.record_restricts_no_merge_and_no_half_rename(named, ps, moves):
  RecordL.restriction_iff(named, ps, moves)

def Laws.record_reads_lines_as_text(ks, reads, hs, e, i, p, q, r, n, hi, j, hj):
  RecordL.lines_read(ks, reads, hs, e, i, p, q, r, n, hi, j, hj)

def Laws.record_gives_kinds_only_to_files(ks, found, u, e, j, p, k, hj):
  RecordL.kinds_held(ks, found, u, e, j, p, k, hj)

def Laws.record_refuses_a_dangling_link(t, looked, held, walked, ss, moves, hd, pre, post, f, p, k, y, named, m, ht, hn, hf):
  SurveyL.dangle_found(t, looked, held, walked, ss, moves, hd, pre, post, f, p, k, y, named, m, ht, hn, hf)

def Laws.record_states_a_kind_only_for_an_arrival(only, t, pre, p, k, post, e, g):
  SurveyL.kind_arrival(only, t, pre, p, k, post, e, g)

def Laws.record_moves_each_file_once(ms, gone, f):
  SurveyL.final_moves(ms, gone, f)

def Laws.record_names_only_what_is_there(rules, named, folder, was, placed):
  SurveyL.named_done(rules, named, folder, was, placed)

def Laws.a_rename_puts_each_file_where_it_was_said(t, ats, t2, moved, e, g, hg):
  SurveyL.at_placed(t, ats, t2, moved, e, g, hg)

def Laws.a_link_refers_only_to_what_the_revision_states(mint, t, gone, arriving, path, target, at, f, hr, hl, ho, hm, e):
  SurveyL.ref_held(mint, t, gone, arriving, path, target, at, f, hr, hl, ho, hm, e)

def Laws.carry_says_what_it_files(fs, ds, c, steps, e, path):
  RewriteL.carry_fields(path, fs, ds, c, steps, e)

def Laws.amend_rewrites_the_revision_named(fs, bs, s, f, e):
  RewriteL.amend_named(fs, bs, s, f, e)

def Laws.amend_rewrites_the_one_head(fs, bs, f, e):
  RewriteL.amend_head(fs, bs, f, e)

def Laws.abandon_abandons_only_a_word_it_was_given(args, c, e):
  RewriteL.target_words(args, c, e)

def Laws.abandon_refuses_a_dry_run_with_fields(args, c, e):
  RewriteL.dry_fields(args, c, e)

def Laws.log_lists_its_span(fs, a, b):
  SpanL.span_listed(fs, a, b)

def Laws.status_leaves_a_disputed_file_unsettled(t, dg, bf, bf2, reads, props, path, f, q, y, g, m, found, h):
  StatusL.disputed(t, dg, bf, bf2, reads, props, path, f, q, y, g, m, found, h)

def Laws.status_joins_what_it_reads(hs, fs, ds, ps, xs, h):
  StatusL.pairs_files(hs, fs, ds, ps, xs, h)

def Laws.diff_folder_compares_like_with_like(dg, os, eds, hs):
  PlanL.plans_like(dg, os, eds, hs)

def Laws.diff_folder_believes_a_stated_digest(dg, os, eds, path, file, at, y, g, m, fp, runs, size, d, os2, ho, w, hw, more, dg2, hd):
  PlanL.believed(dg, os, eds, path, file, at, y, g, m, fp, runs, size, d, os2, ho, w, hw, more, dg2, hd)

def Laws.diff_sizes_only_what_the_host_stated(found, stats, cs):
  SizesL.sized_told(found, stats, cs)

def Laws.diff_sizes_what_the_host_stated(f1, s1, hl, d, hn, hd, hs, p, f2, size, n, hz, s2, from, to, modes, targets):
  SizesL.sized_given(f1, s1, hl, d, hn, hd, hs, p, f2, size, n, hz, s2, from, to, modes, targets)

def Laws.name_points_where_asked(fs, bs, n, spelling, path, pin, axis, b, e, id, ei):
  NameL.points_ok(fs, bs, n, spelling, path, pin, axis, b, e, id, ei)

def Laws.record_compares_with_the_latest(now, ws):
  NamingL.warns(now, ws)

def Laws.record_names_the_latest_work(ws, w, e):
  NamingL.latest_ok(ws, w, e)

def Laws.a_timestamp_is_read_at_its_offset(base, hb, hh, hh2, h, eh, mm, hm2, m, em, hd):
  NamingL.two.hh(hh, hh2, base, hb, h, eh, mm, hm2, m, em, hd)

def Laws.fetch_reads_the_manifest_offer_writes(url, hs, os, hh, ho):
  ManL.reads_back(url, hs, os, hh, ho)

def Laws.fetch_refuses_only_what_shares_no_revision(h, os, join, x, r, e):
  FPlanL.refused_only(h, os, join, x, r, e)

def Laws.fetch_refuses_what_shares_no_revision(h, os, hr, ht, hn):
  FPlanL.refuses(h, os, hr, ht, hn)

def Laws.fetch_destroys_only_what_is_forgotten(s, os, d, h):
  FPlanL.destroyed(s, os, d, h)

def Laws.fetch_writes_a_bookmark_once_a_pass(o, n, at, text, t, rules, held, moved, landed, root, o2, g, h):
  FetchingL.once_a_pass(o, n, at, text, t, rules, held, moved, landed, root, o2, g, h)

def Laws.fetch_asks_for_no_payload_held_or_forgotten(s, os, d, m):
  FPlanL.payload_lacks(s, os, d, m)

def Laws.fetch_asks_for_no_document_held_or_forgotten(s, os, d, m):
  FPlanL.document_lacks(s, os, d, m)

def Laws.fetch_asks_for_no_revision_it_holds(s, os, d, m):
  FPlanL.revision_lacks(s, os, d, m)

def Laws.fetch_says_what_it_took(rs, ds, ps, rus, res, ns, k, dec, des, re):
  FPlanL.says_what_it_took(rs, ds, ps, rus, res, ns, k, dec, des, re)

def Laws.fetch_asks_for_a_path_by_its_bytes(bs, h):
  EscL.dec_bytes(bs, h)

def Laws.fetch_asks_in_characters_a_url_may_hold(bs, h):
  EscL.url_bytes(bs, h)

def Laws.fetch_asks_for_what_is_unreserved_as_itself():
  EscL.kept_as_itself()
