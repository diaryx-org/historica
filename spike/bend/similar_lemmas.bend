# The diff the commands draw takes one side to the other. `similar.bend` is
# `similar`'s Histogram search, held to the crate on two thousand cases;
# what it returns is checked in one pass (`Sim.fit`) before a document is
# written from it, and moves that pass are an edit script `diff_lemmas.bend`
# already proves: the runs of any such script are blocks the cursor walks
# to the child. Moves that did not pass would be answered by `Ops.diff`,
# which is proven the same way.
import Base
import ./ops.bend as Ops
import ./similar.bend as Sim
import ./cursor_spec.bend as Cursor
import ./composition_lemmas.bend as Comp
import ./diff_lemmas.bend as Diff
import ./linear_lemmas.bend as Lin

def item_is_equal(x: Ops.Item, y: Ops.Item, +h: {Sim.fit.item(x, y) == True{} : Bool}) -> {x == y : Ops.Item}:
  match x y:
    case Ops.Item{+s, +n, +f} Ops.Item{+t, +m, +g}:
      Lin.item_eq_equal(Ops.Item{s, n, f}, Ops.Item{t, m, g}, h)

# Moves that pass the check take the parent to the child.
def fit_apply(es: List<&2, Ops.Move>, +old: List<&2, Ops.Item>, +new: List<&2, Ops.Item>, +h: {Sim.fit(es, old, new) == True{} : Bool}) -> {Diff.edits_apply(es, old) == Some{new} : Maybe<&2, List<&2, Ops.Item>>}:
  match es old new:
    case Nil{} Nil{} Nil{}:
      {==}
    case Nil{} Nil{} +z <> +zs:
      Empty.absurd({Diff.edits_apply(Nil{}, Nil{}) == Some{z <> zs} : Maybe<&2, List<&2, Ops.Item>>}, Comp.false_true(h))
    case Nil{} +x <> +xs Nil{}:
      Empty.absurd({Diff.edits_apply(Nil{}, x <> xs) == Some{Nil{}} : Maybe<&2, List<&2, Ops.Item>>}, Comp.false_true(h))
    case Nil{} +x <> +xs +z <> +zs:
      Empty.absurd({Diff.edits_apply(Nil{}, x <> xs) == Some{z <> zs} : Maybe<&2, List<&2, Ops.Item>>}, Comp.false_true(h))
    case Ops.Keep{} <> +r Nil{} Nil{}:
      Empty.absurd({Diff.edits_apply(Ops.Keep{} <> r, Nil{}) == Some{Nil{}} : Maybe<&2, List<&2, Ops.Item>>}, Comp.false_true(h))
    case Ops.Keep{} <> +r Nil{} +z <> +zs:
      Empty.absurd({Diff.edits_apply(Ops.Keep{} <> r, Nil{}) == Some{z <> zs} : Maybe<&2, List<&2, Ops.Item>>}, Comp.false_true(h))
    case Ops.Keep{} <> +r +x <> +xs Nil{}:
      Empty.absurd({Diff.edits_apply(Ops.Keep{} <> r, x <> xs) == Some{Nil{}} : Maybe<&2, List<&2, Ops.Item>>}, Comp.false_true(h))
    case Ops.Keep{} <> +r +x <> +xs +z <> +zs:
      (%Equal.sym(Maybe<&2, List<&2, Ops.Item>>, Diff.edits_apply(r, xs), Some{zs}, fit_apply(r, xs, zs, Comp.and_right(Sim.fit.item(x, z), Sim.fit(r, xs, zs), h))) : {Diff.map_cons(x, _) == Some{z <> zs} : Maybe<&2, List<&2, Ops.Item>>}
        (%item_is_equal(x, z, Comp.and_left(Sim.fit.item(x, z), Sim.fit(r, xs, zs), h)) : {Some{x <> zs} == Some{_ <> zs} : Maybe<&2, List<&2, Ops.Item>>}
          {==}))
    case Ops.Del{+d} <> +r Nil{} Nil{}:
      Empty.absurd({Diff.edits_apply(Ops.Del{d} <> r, Nil{}) == Some{Nil{}} : Maybe<&2, List<&2, Ops.Item>>}, Comp.false_true(h))
    case Ops.Del{+d} <> +r Nil{} +z <> +zs:
      Empty.absurd({Diff.edits_apply(Ops.Del{d} <> r, Nil{}) == Some{z <> zs} : Maybe<&2, List<&2, Ops.Item>>}, Comp.false_true(h))
    case Ops.Del{+d} <> +r +x <> +xs Nil{}:
      (%Equal.sym(Bool, Ops.agrees(d, x), True{}, Comp.and_left(Ops.agrees(d, x), Sim.fit(r, xs, Nil{}), h)) : {Bool.pick(Maybe<&2, List<&2, Ops.Item>>, _, Diff.edits_apply(r, xs), None{}) == Some{Nil{}} : Maybe<&2, List<&2, Ops.Item>>}
        fit_apply(r, xs, Nil{}, Comp.and_right(Ops.agrees(d, x), Sim.fit(r, xs, Nil{}), h)))
    case Ops.Del{+d} <> +r +x <> +xs +z <> +zs:
      (%Equal.sym(Bool, Ops.agrees(d, x), True{}, Comp.and_left(Ops.agrees(d, x), Sim.fit(r, xs, z <> zs), h)) : {Bool.pick(Maybe<&2, List<&2, Ops.Item>>, _, Diff.edits_apply(r, xs), None{}) == Some{z <> zs} : Maybe<&2, List<&2, Ops.Item>>}
        fit_apply(r, xs, z <> zs, Comp.and_right(Ops.agrees(d, x), Sim.fit(r, xs, z <> zs), h)))
    case Ops.Ins{+y} <> +r Nil{} Nil{}:
      Empty.absurd({Diff.edits_apply(Ops.Ins{y} <> r, Nil{}) == Some{Nil{}} : Maybe<&2, List<&2, Ops.Item>>}, Comp.false_true(h))
    case Ops.Ins{+y} <> +r Nil{} +z <> +zs:
      (%Equal.sym(Maybe<&2, List<&2, Ops.Item>>, Diff.edits_apply(r, Nil{}), Some{zs}, fit_apply(r, Nil{}, zs, Comp.and_right(Sim.fit.item(y, z), Sim.fit(r, Nil{}, zs), h))) : {Diff.map_cons(y, _) == Some{z <> zs} : Maybe<&2, List<&2, Ops.Item>>}
        (%item_is_equal(y, z, Comp.and_left(Sim.fit.item(y, z), Sim.fit(r, Nil{}, zs), h)) : {Some{y <> zs} == Some{_ <> zs} : Maybe<&2, List<&2, Ops.Item>>}
          {==}))
    case Ops.Ins{+y} <> +r +x <> +xs Nil{}:
      Empty.absurd({Diff.edits_apply(Ops.Ins{y} <> r, x <> xs) == Some{Nil{}} : Maybe<&2, List<&2, Ops.Item>>}, Comp.false_true(h))
    case Ops.Ins{+y} <> +r +x <> +xs +z <> +zs:
      (%Equal.sym(Maybe<&2, List<&2, Ops.Item>>, Diff.edits_apply(r, x <> xs), Some{zs}, fit_apply(r, x <> xs, zs, Comp.and_right(Sim.fit.item(y, z), Sim.fit(r, x <> xs, zs), h))) : {Diff.map_cons(y, _) == Some{z <> zs} : Maybe<&2, List<&2, Ops.Item>>}
        (%item_is_equal(y, z, Comp.and_left(Sim.fit.item(y, z), Sim.fit(r, x <> xs, zs), h)) : {Some{y <> zs} == Some{_ <> zs} : Maybe<&2, List<&2, Ops.Item>>}
          {==}))

# `diff_lemmas.diff_walks`, for any moves that take the parent to the child.
def moves_walk(+parent: List<&2, Ops.Item>, +child: List<&2, Ops.Item>, +es: List<&2, Ops.Move>, +ops: List<&2, Ops.Op>, eq: {Ops.script(Ops.runs(es, 0n, Nil{}, Nil{}), 0n) == ops : List<&2, Ops.Op>}, +ea: {Diff.edits_apply(es, parent) == Some{child} : Maybe<&2, List<&2, Ops.Item>>}, tbl: {Ops.terminated_but_last(child) == True{} : Bool}) -> {Cursor.apply(parent, Ops.Doc{None{}, Some{Ops.state_digest(child)}, ops}) == Done{child} : Result<&2, &2, String, List<&2, Ops.Item>>}:
  +steps = Ops.runs(es, 0n, Nil{}, Nil{})
  +applied = Diff.runs_apply(es, 0n, Nil{}, Nil{}, Nil{}, Nil{}, parent, child, {==}, {==}, ea)
  %eq : {Cursor.apply(parent, Ops.Doc{None{}, Some{Ops.state_digest(child)}, _}) == Done{child} : Result<&2, &2, String, List<&2, Ops.Item>>}
  %Equal.sym(Bool, Ops.in_range(Ops.script(steps, 0n), List.length(&2, Ops.Item, parent)), True{}, Diff.steps_range(steps, 0n, parent, child, applied)) : {Cursor.checked(_, Some{Ops.state_digest(child)}, Cursor.walk(Ops.script(steps, 0n), 0n, parent)) == Done{child} : Result<&2, &2, String, List<&2, Ops.Item>>}
  %Equal.sym(Result<&2, &2, String, List<&2, Ops.Item>>, Cursor.walk(Ops.script(steps, 0n), 0n, parent), Done{child}, Diff.steps_walk(steps, 0n, parent, child, applied)) : {Cursor.checked(True{}, Some{Ops.state_digest(child)}, _) == Done{child} : Result<&2, &2, String, List<&2, Ops.Item>>}
  Diff.checked_child(child, tbl)

def moves_applies(+parent: List<&2, Ops.Item>, +child: List<&2, Ops.Item>, +es: List<&2, Ops.Move>, ops: List<&2, Ops.Op>, +eq: {Ops.script(Ops.runs(es, 0n, Nil{}, Nil{}), 0n) == ops : List<&2, Ops.Op>}, +ea: {Diff.edits_apply(es, parent) == Some{child} : Maybe<&2, List<&2, Ops.Item>>}, tbl: {Ops.terminated_but_last(child) == True{} : Bool}, -doc: Ops.Doc, e: {Ops.diff.of(ops, Ops.state_digest(child)) == Some{doc} : Maybe<&2, Ops.Doc>}) -> {Cursor.apply(parent, doc) == Done{child} : Result<&2, &2, String, List<&2, Ops.Item>>}:
  match ops:
    case Nil{}:
      Empty.absurd({Cursor.apply(parent, doc) == Done{child} : Result<&2, &2, String, List<&2, Ops.Item>>}, Diff.none_doc(doc, e))
    case +op <> +rest:
      %Equal.cong(Maybe<&2, Ops.Doc>, Ops.Doc, Diff.maybe_doc, Some{Ops.Doc{None{}, Some{Ops.state_digest(child)}, op <> rest}}, Some{doc}, e) : {Cursor.apply(parent, _) == Done{child} : Result<&2, &2, String, List<&2, Ops.Item>>}
      moves_walk(parent, child, es, op <> rest, eq, ea, tbl)

def checked_applies(+parent: List<&2, Ops.Item>, +child: List<&2, Ops.Item>, +moves: List<&2, Ops.Move>, ok: Bool, +eo: {Sim.fit(moves, parent, child) == ok : Bool}, tbl: {Ops.terminated_but_last(child) == True{} : Bool}, -doc: Ops.Doc, e: {Sim.diff.checked(parent, child, moves, ok) == Some{doc} : Maybe<&2, Ops.Doc>}) -> {Cursor.apply(parent, doc) == Done{child} : Result<&2, &2, String, List<&2, Ops.Item>>}:
  match ok:
    case True{}:
      moves_applies(parent, child, moves, Ops.script(Ops.runs(moves, 0n, Nil{}, Nil{}), 0n), {==}, fit_apply(moves, parent, child, eo), tbl, doc, e)
    case False{}:
      Diff.diff_applies(parent, child, tbl, doc, e)

# The theorem, over the cursor specification, as `diff_applies` is.
def similar_applies(+parent: List<&2, Ops.Item>, +child: List<&2, Ops.Item>, tbl: {Ops.terminated_but_last(child) == True{} : Bool}, -doc: Ops.Doc, e: {Sim.diff(parent, child) == Some{doc} : Maybe<&2, Ops.Doc>}) -> {Cursor.apply(parent, doc) == Done{child} : Result<&2, &2, String, List<&2, Ops.Item>>}:
  checked_applies(parent, child, Sim.walked.moves(Sim.walked.go(Sim.ops(parent, child), Sim.Walked{parent, child, Nil{}})), Sim.fit(Sim.walked.moves(Sim.walked.go(Sim.ops(parent, child), Sim.Walked{parent, child, Nil{}})), parent, child), {==}, tbl, doc, e)
