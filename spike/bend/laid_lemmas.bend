# What `diff` and `blame` lay out is both sides. A comparison is laid over
# the parent a line at a time — context, removals and arrivals — by walking
# the document's operations as the cursor walks them. The lines that are
# not arrivals are the parent, whatever the document says; and where the
# cursor reads the child, the lines that are not removals are the child.
import Base
import ./ops.bend as Ops
import ./cursor_spec.bend as Cursor
import ./replay_spec.bend as Spec
import ./commands.bend as Main
import ./composition_lemmas.bend as Comp
import ./diff_lemmas.bend as Diff
import ./refusal_lemmas.bend as Refuse

# Lists
# -----

def app_assoc(xs: List<&2, Ops.Item>, -ys: List<&2, Ops.Item>, -zs: List<&2, Ops.Item>) -> {List.append(&2, Ops.Item, List.append(&2, Ops.Item, xs, ys), zs) == List.append(&2, Ops.Item, xs, List.append(&2, Ops.Item, ys, zs)) : List<&2, Ops.Item>}:
  match xs:
    case Nil{}:
      {==}
    case x <> rest:
      Equal.cong(List<&2, Ops.Item>, List<&2, Ops.Item>, l => x <> l, List.append(&2, Ops.Item, List.append(&2, Ops.Item, rest, ys), zs), List.append(&2, Ops.Item, rest, List.append(&2, Ops.Item, ys, zs)), app_assoc(rest, ys, zs))

def take_drop(xs: List<&2, Ops.Item>, n: Nat) -> {List.append(&2, Ops.Item, List.take(&2, Ops.Item, xs, n), List.drop(&2, Ops.Item, xs, n)) == xs : List<&2, Ops.Item>}:
  match xs n:
    case Nil{} _:
      {==}
    case x <> rest 0n:
      {==}
    case x <> rest 1n+p:
      Equal.cong(List<&2, Ops.Item>, List<&2, Ops.Item>, l => x <> l, List.append(&2, Ops.Item, List.take(&2, Ops.Item, rest, p), List.drop(&2, Ops.Item, rest, p)), rest, take_drop(rest, p))

# The two sides of laid lines
# ---------------------------

def side_app(b: Bool, -it: Ops.Item, -a: List<&2, Ops.Item>, -c: List<&2, Ops.Item>) -> {Main.laid.side(b, it, List.append(&2, Ops.Item, a, c)) == List.append(&2, Ops.Item, Main.laid.side(b, it, a), c) : List<&2, Ops.Item>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def old_app(xs: List<&2, Main.Laid>, -ys: List<&2, Main.Laid>) -> {Main.laid.old(List.append(&2, Main.Laid, xs, ys)) == List.append(&2, Ops.Item, Main.laid.old(xs), Main.laid.old(ys)) : List<&2, Ops.Item>}:
  match xs:
    case Nil{}:
      {==}
    case Main.Laid{+sign, +it} <> rest:
      Equal.trans(List<&2, Ops.Item>, Main.laid.side(String.eq(sign, "+"), it, Main.laid.old(List.append(&2, Main.Laid, rest, ys))), Main.laid.side(String.eq(sign, "+"), it, List.append(&2, Ops.Item, Main.laid.old(rest), Main.laid.old(ys))), List.append(&2, Ops.Item, Main.laid.side(String.eq(sign, "+"), it, Main.laid.old(rest)), Main.laid.old(ys)),
        Equal.cong(List<&2, Ops.Item>, List<&2, Ops.Item>, l => Main.laid.side(String.eq(sign, "+"), it, l), Main.laid.old(List.append(&2, Main.Laid, rest, ys)), List.append(&2, Ops.Item, Main.laid.old(rest), Main.laid.old(ys)), old_app(rest, ys)),
        side_app(String.eq(sign, "+"), it, Main.laid.old(rest), Main.laid.old(ys)))

def new_app(xs: List<&2, Main.Laid>, -ys: List<&2, Main.Laid>) -> {Main.laid.new(List.append(&2, Main.Laid, xs, ys)) == List.append(&2, Ops.Item, Main.laid.new(xs), Main.laid.new(ys)) : List<&2, Ops.Item>}:
  match xs:
    case Nil{}:
      {==}
    case Main.Laid{+sign, +it} <> rest:
      Equal.trans(List<&2, Ops.Item>, Main.laid.side(String.eq(sign, "-"), it, Main.laid.new(List.append(&2, Main.Laid, rest, ys))), Main.laid.side(String.eq(sign, "-"), it, List.append(&2, Ops.Item, Main.laid.new(rest), Main.laid.new(ys))), List.append(&2, Ops.Item, Main.laid.side(String.eq(sign, "-"), it, Main.laid.new(rest)), Main.laid.new(ys)),
        Equal.cong(List<&2, Ops.Item>, List<&2, Ops.Item>, l => Main.laid.side(String.eq(sign, "-"), it, l), Main.laid.new(List.append(&2, Main.Laid, rest, ys)), List.append(&2, Ops.Item, Main.laid.new(rest), Main.laid.new(ys)), new_app(rest, ys)),
        side_app(String.eq(sign, "-"), it, Main.laid.new(rest), Main.laid.new(ys)))

def old_ctx(xs: List<&2, Ops.Item>) -> {Main.laid.old(Main.laid.all(" ", xs)) == xs : List<&2, Ops.Item>}:
  match xs:
    case Nil{}:
      {==}
    case x <> rest:
      Equal.cong(List<&2, Ops.Item>, List<&2, Ops.Item>, l => x <> l, Main.laid.old(Main.laid.all(" ", rest)), rest, old_ctx(rest))

def old_minus(xs: List<&2, Ops.Item>) -> {Main.laid.old(Main.laid.all("-", xs)) == xs : List<&2, Ops.Item>}:
  match xs:
    case Nil{}:
      {==}
    case x <> rest:
      Equal.cong(List<&2, Ops.Item>, List<&2, Ops.Item>, l => x <> l, Main.laid.old(Main.laid.all("-", rest)), rest, old_minus(rest))

def old_plus(xs: List<&2, Ops.Item>) -> {Main.laid.old(Main.laid.all("+", xs)) == Nil{} : List<&2, Ops.Item>}:
  match xs:
    case Nil{}:
      {==}
    case x <> rest:
      old_plus(rest)

def new_ctx(xs: List<&2, Ops.Item>) -> {Main.laid.new(Main.laid.all(" ", xs)) == xs : List<&2, Ops.Item>}:
  match xs:
    case Nil{}:
      {==}
    case x <> rest:
      Equal.cong(List<&2, Ops.Item>, List<&2, Ops.Item>, l => x <> l, Main.laid.new(Main.laid.all(" ", rest)), rest, new_ctx(rest))

def new_plus(xs: List<&2, Ops.Item>) -> {Main.laid.new(Main.laid.all("+", xs)) == xs : List<&2, Ops.Item>}:
  match xs:
    case Nil{}:
      {==}
    case x <> rest:
      Equal.cong(List<&2, Ops.Item>, List<&2, Ops.Item>, l => x <> l, Main.laid.new(Main.laid.all("+", rest)), rest, new_plus(rest))

def new_minus(xs: List<&2, Ops.Item>) -> {Main.laid.new(Main.laid.all("-", xs)) == Nil{} : List<&2, Ops.Item>}:
  match xs:
    case Nil{}:
      {==}
    case x <> rest:
      new_minus(rest)

# The parent side
# ---------------

# Whatever the operations, the lines that are not arrivals are the parent.
def old_walk(ops: List<&2, Ops.Op>, +pos: Nat, +state: List<&2, Ops.Item>) -> {Main.laid.old(Main.laid.walk(ops, pos, state)) == state : List<&2, Ops.Item>}:
  match ops:
    case Nil{}:
      old_ctx(state)
    case Ops.Op{Ops.Insert{}, +at, +items} <> +rest:
      Equal.trans(List<&2, Ops.Item>, Main.laid.old(List.append(&2, Main.Laid, Main.laid.all(" ", List.take(&2, Ops.Item, state, Nat.sub(at, pos))), List.append(&2, Main.Laid, Main.laid.all("+", items), Main.laid.walk(rest, Nat.max(pos, at), List.drop(&2, Ops.Item, state, Nat.sub(at, pos)))))), List.append(&2, Ops.Item, Main.laid.old(Main.laid.all(" ", List.take(&2, Ops.Item, state, Nat.sub(at, pos)))), Main.laid.old(List.append(&2, Main.Laid, Main.laid.all("+", items), Main.laid.walk(rest, Nat.max(pos, at), List.drop(&2, Ops.Item, state, Nat.sub(at, pos)))))), state,
        old_app(Main.laid.all(" ", List.take(&2, Ops.Item, state, Nat.sub(at, pos))), List.append(&2, Main.Laid, Main.laid.all("+", items), Main.laid.walk(rest, Nat.max(pos, at), List.drop(&2, Ops.Item, state, Nat.sub(at, pos))))),
        Equal.trans(List<&2, Ops.Item>, List.append(&2, Ops.Item, Main.laid.old(Main.laid.all(" ", List.take(&2, Ops.Item, state, Nat.sub(at, pos)))), Main.laid.old(List.append(&2, Main.Laid, Main.laid.all("+", items), Main.laid.walk(rest, Nat.max(pos, at), List.drop(&2, Ops.Item, state, Nat.sub(at, pos)))))), List.append(&2, Ops.Item, List.take(&2, Ops.Item, state, Nat.sub(at, pos)), Main.laid.old(List.append(&2, Main.Laid, Main.laid.all("+", items), Main.laid.walk(rest, Nat.max(pos, at), List.drop(&2, Ops.Item, state, Nat.sub(at, pos)))))), state,
        Equal.cong(List<&2, Ops.Item>, List<&2, Ops.Item>, l => List.append(&2, Ops.Item, l, Main.laid.old(List.append(&2, Main.Laid, Main.laid.all("+", items), Main.laid.walk(rest, Nat.max(pos, at), List.drop(&2, Ops.Item, state, Nat.sub(at, pos)))))), Main.laid.old(Main.laid.all(" ", List.take(&2, Ops.Item, state, Nat.sub(at, pos)))), List.take(&2, Ops.Item, state, Nat.sub(at, pos)), old_ctx(List.take(&2, Ops.Item, state, Nat.sub(at, pos)))),
        Equal.trans(List<&2, Ops.Item>, List.append(&2, Ops.Item, List.take(&2, Ops.Item, state, Nat.sub(at, pos)), Main.laid.old(List.append(&2, Main.Laid, Main.laid.all("+", items), Main.laid.walk(rest, Nat.max(pos, at), List.drop(&2, Ops.Item, state, Nat.sub(at, pos)))))), List.append(&2, Ops.Item, List.take(&2, Ops.Item, state, Nat.sub(at, pos)), List.append(&2, Ops.Item, Main.laid.old(Main.laid.all("+", items)), Main.laid.old(Main.laid.walk(rest, Nat.max(pos, at), List.drop(&2, Ops.Item, state, Nat.sub(at, pos)))))), state,
        Equal.cong(List<&2, Ops.Item>, List<&2, Ops.Item>, l => List.append(&2, Ops.Item, List.take(&2, Ops.Item, state, Nat.sub(at, pos)), l), Main.laid.old(List.append(&2, Main.Laid, Main.laid.all("+", items), Main.laid.walk(rest, Nat.max(pos, at), List.drop(&2, Ops.Item, state, Nat.sub(at, pos))))), List.append(&2, Ops.Item, Main.laid.old(Main.laid.all("+", items)), Main.laid.old(Main.laid.walk(rest, Nat.max(pos, at), List.drop(&2, Ops.Item, state, Nat.sub(at, pos))))), old_app(Main.laid.all("+", items), Main.laid.walk(rest, Nat.max(pos, at), List.drop(&2, Ops.Item, state, Nat.sub(at, pos))))),
        Equal.trans(List<&2, Ops.Item>, List.append(&2, Ops.Item, List.take(&2, Ops.Item, state, Nat.sub(at, pos)), List.append(&2, Ops.Item, Main.laid.old(Main.laid.all("+", items)), Main.laid.old(Main.laid.walk(rest, Nat.max(pos, at), List.drop(&2, Ops.Item, state, Nat.sub(at, pos)))))), List.append(&2, Ops.Item, List.take(&2, Ops.Item, state, Nat.sub(at, pos)), Main.laid.old(Main.laid.walk(rest, Nat.max(pos, at), List.drop(&2, Ops.Item, state, Nat.sub(at, pos))))), state,
        Equal.cong(List<&2, Ops.Item>, List<&2, Ops.Item>, l => List.append(&2, Ops.Item, List.take(&2, Ops.Item, state, Nat.sub(at, pos)), List.append(&2, Ops.Item, l, Main.laid.old(Main.laid.walk(rest, Nat.max(pos, at), List.drop(&2, Ops.Item, state, Nat.sub(at, pos)))))), Main.laid.old(Main.laid.all("+", items)), Nil{}, old_plus(items)),
        Equal.trans(List<&2, Ops.Item>, List.append(&2, Ops.Item, List.take(&2, Ops.Item, state, Nat.sub(at, pos)), Main.laid.old(Main.laid.walk(rest, Nat.max(pos, at), List.drop(&2, Ops.Item, state, Nat.sub(at, pos))))), List.append(&2, Ops.Item, List.take(&2, Ops.Item, state, Nat.sub(at, pos)), List.drop(&2, Ops.Item, state, Nat.sub(at, pos))), state,
        Equal.cong(List<&2, Ops.Item>, List<&2, Ops.Item>, l => List.append(&2, Ops.Item, List.take(&2, Ops.Item, state, Nat.sub(at, pos)), l), Main.laid.old(Main.laid.walk(rest, Nat.max(pos, at), List.drop(&2, Ops.Item, state, Nat.sub(at, pos)))), List.drop(&2, Ops.Item, state, Nat.sub(at, pos)), old_walk(rest, Nat.max(pos, at), List.drop(&2, Ops.Item, state, Nat.sub(at, pos)))),
        take_drop(state, Nat.sub(at, pos)))))))
    case Ops.Op{Ops.Delete{}, +at, +items} <> +rest:
      Equal.trans(List<&2, Ops.Item>, Main.laid.old(List.append(&2, Main.Laid, Main.laid.all(" ", List.take(&2, Ops.Item, state, Nat.sub(at, pos))), List.append(&2, Main.Laid, Main.laid.all("-", List.take(&2, Ops.Item, List.drop(&2, Ops.Item, state, Nat.sub(at, pos)), List.length(&2, Ops.Item, items))), Main.laid.walk(rest, Nat.add(at, List.length(&2, Ops.Item, items)), List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, state, Nat.sub(at, pos)), List.length(&2, Ops.Item, items)))))), List.append(&2, Ops.Item, Main.laid.old(Main.laid.all(" ", List.take(&2, Ops.Item, state, Nat.sub(at, pos)))), Main.laid.old(List.append(&2, Main.Laid, Main.laid.all("-", List.take(&2, Ops.Item, List.drop(&2, Ops.Item, state, Nat.sub(at, pos)), List.length(&2, Ops.Item, items))), Main.laid.walk(rest, Nat.add(at, List.length(&2, Ops.Item, items)), List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, state, Nat.sub(at, pos)), List.length(&2, Ops.Item, items)))))), state,
        old_app(Main.laid.all(" ", List.take(&2, Ops.Item, state, Nat.sub(at, pos))), List.append(&2, Main.Laid, Main.laid.all("-", List.take(&2, Ops.Item, List.drop(&2, Ops.Item, state, Nat.sub(at, pos)), List.length(&2, Ops.Item, items))), Main.laid.walk(rest, Nat.add(at, List.length(&2, Ops.Item, items)), List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, state, Nat.sub(at, pos)), List.length(&2, Ops.Item, items))))),
        Equal.trans(List<&2, Ops.Item>, List.append(&2, Ops.Item, Main.laid.old(Main.laid.all(" ", List.take(&2, Ops.Item, state, Nat.sub(at, pos)))), Main.laid.old(List.append(&2, Main.Laid, Main.laid.all("-", List.take(&2, Ops.Item, List.drop(&2, Ops.Item, state, Nat.sub(at, pos)), List.length(&2, Ops.Item, items))), Main.laid.walk(rest, Nat.add(at, List.length(&2, Ops.Item, items)), List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, state, Nat.sub(at, pos)), List.length(&2, Ops.Item, items)))))), List.append(&2, Ops.Item, List.take(&2, Ops.Item, state, Nat.sub(at, pos)), Main.laid.old(List.append(&2, Main.Laid, Main.laid.all("-", List.take(&2, Ops.Item, List.drop(&2, Ops.Item, state, Nat.sub(at, pos)), List.length(&2, Ops.Item, items))), Main.laid.walk(rest, Nat.add(at, List.length(&2, Ops.Item, items)), List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, state, Nat.sub(at, pos)), List.length(&2, Ops.Item, items)))))), state,
        Equal.cong(List<&2, Ops.Item>, List<&2, Ops.Item>, l => List.append(&2, Ops.Item, l, Main.laid.old(List.append(&2, Main.Laid, Main.laid.all("-", List.take(&2, Ops.Item, List.drop(&2, Ops.Item, state, Nat.sub(at, pos)), List.length(&2, Ops.Item, items))), Main.laid.walk(rest, Nat.add(at, List.length(&2, Ops.Item, items)), List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, state, Nat.sub(at, pos)), List.length(&2, Ops.Item, items)))))), Main.laid.old(Main.laid.all(" ", List.take(&2, Ops.Item, state, Nat.sub(at, pos)))), List.take(&2, Ops.Item, state, Nat.sub(at, pos)), old_ctx(List.take(&2, Ops.Item, state, Nat.sub(at, pos)))),
        Equal.trans(List<&2, Ops.Item>, List.append(&2, Ops.Item, List.take(&2, Ops.Item, state, Nat.sub(at, pos)), Main.laid.old(List.append(&2, Main.Laid, Main.laid.all("-", List.take(&2, Ops.Item, List.drop(&2, Ops.Item, state, Nat.sub(at, pos)), List.length(&2, Ops.Item, items))), Main.laid.walk(rest, Nat.add(at, List.length(&2, Ops.Item, items)), List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, state, Nat.sub(at, pos)), List.length(&2, Ops.Item, items)))))), List.append(&2, Ops.Item, List.take(&2, Ops.Item, state, Nat.sub(at, pos)), List.append(&2, Ops.Item, Main.laid.old(Main.laid.all("-", List.take(&2, Ops.Item, List.drop(&2, Ops.Item, state, Nat.sub(at, pos)), List.length(&2, Ops.Item, items)))), Main.laid.old(Main.laid.walk(rest, Nat.add(at, List.length(&2, Ops.Item, items)), List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, state, Nat.sub(at, pos)), List.length(&2, Ops.Item, items)))))), state,
        Equal.cong(List<&2, Ops.Item>, List<&2, Ops.Item>, l => List.append(&2, Ops.Item, List.take(&2, Ops.Item, state, Nat.sub(at, pos)), l), Main.laid.old(List.append(&2, Main.Laid, Main.laid.all("-", List.take(&2, Ops.Item, List.drop(&2, Ops.Item, state, Nat.sub(at, pos)), List.length(&2, Ops.Item, items))), Main.laid.walk(rest, Nat.add(at, List.length(&2, Ops.Item, items)), List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, state, Nat.sub(at, pos)), List.length(&2, Ops.Item, items))))), List.append(&2, Ops.Item, Main.laid.old(Main.laid.all("-", List.take(&2, Ops.Item, List.drop(&2, Ops.Item, state, Nat.sub(at, pos)), List.length(&2, Ops.Item, items)))), Main.laid.old(Main.laid.walk(rest, Nat.add(at, List.length(&2, Ops.Item, items)), List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, state, Nat.sub(at, pos)), List.length(&2, Ops.Item, items))))), old_app(Main.laid.all("-", List.take(&2, Ops.Item, List.drop(&2, Ops.Item, state, Nat.sub(at, pos)), List.length(&2, Ops.Item, items))), Main.laid.walk(rest, Nat.add(at, List.length(&2, Ops.Item, items)), List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, state, Nat.sub(at, pos)), List.length(&2, Ops.Item, items))))),
        Equal.trans(List<&2, Ops.Item>, List.append(&2, Ops.Item, List.take(&2, Ops.Item, state, Nat.sub(at, pos)), List.append(&2, Ops.Item, Main.laid.old(Main.laid.all("-", List.take(&2, Ops.Item, List.drop(&2, Ops.Item, state, Nat.sub(at, pos)), List.length(&2, Ops.Item, items)))), Main.laid.old(Main.laid.walk(rest, Nat.add(at, List.length(&2, Ops.Item, items)), List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, state, Nat.sub(at, pos)), List.length(&2, Ops.Item, items)))))), List.append(&2, Ops.Item, List.take(&2, Ops.Item, state, Nat.sub(at, pos)), List.append(&2, Ops.Item, List.take(&2, Ops.Item, List.drop(&2, Ops.Item, state, Nat.sub(at, pos)), List.length(&2, Ops.Item, items)), Main.laid.old(Main.laid.walk(rest, Nat.add(at, List.length(&2, Ops.Item, items)), List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, state, Nat.sub(at, pos)), List.length(&2, Ops.Item, items)))))), state,
        Equal.cong(List<&2, Ops.Item>, List<&2, Ops.Item>, l => List.append(&2, Ops.Item, List.take(&2, Ops.Item, state, Nat.sub(at, pos)), List.append(&2, Ops.Item, l, Main.laid.old(Main.laid.walk(rest, Nat.add(at, List.length(&2, Ops.Item, items)), List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, state, Nat.sub(at, pos)), List.length(&2, Ops.Item, items)))))), Main.laid.old(Main.laid.all("-", List.take(&2, Ops.Item, List.drop(&2, Ops.Item, state, Nat.sub(at, pos)), List.length(&2, Ops.Item, items)))), List.take(&2, Ops.Item, List.drop(&2, Ops.Item, state, Nat.sub(at, pos)), List.length(&2, Ops.Item, items)), old_minus(List.take(&2, Ops.Item, List.drop(&2, Ops.Item, state, Nat.sub(at, pos)), List.length(&2, Ops.Item, items)))),
        Equal.trans(List<&2, Ops.Item>, List.append(&2, Ops.Item, List.take(&2, Ops.Item, state, Nat.sub(at, pos)), List.append(&2, Ops.Item, List.take(&2, Ops.Item, List.drop(&2, Ops.Item, state, Nat.sub(at, pos)), List.length(&2, Ops.Item, items)), Main.laid.old(Main.laid.walk(rest, Nat.add(at, List.length(&2, Ops.Item, items)), List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, state, Nat.sub(at, pos)), List.length(&2, Ops.Item, items)))))), List.append(&2, Ops.Item, List.take(&2, Ops.Item, state, Nat.sub(at, pos)), List.append(&2, Ops.Item, List.take(&2, Ops.Item, List.drop(&2, Ops.Item, state, Nat.sub(at, pos)), List.length(&2, Ops.Item, items)), List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, state, Nat.sub(at, pos)), List.length(&2, Ops.Item, items)))), state,
        Equal.cong(List<&2, Ops.Item>, List<&2, Ops.Item>, l => List.append(&2, Ops.Item, List.take(&2, Ops.Item, state, Nat.sub(at, pos)), List.append(&2, Ops.Item, List.take(&2, Ops.Item, List.drop(&2, Ops.Item, state, Nat.sub(at, pos)), List.length(&2, Ops.Item, items)), l)), Main.laid.old(Main.laid.walk(rest, Nat.add(at, List.length(&2, Ops.Item, items)), List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, state, Nat.sub(at, pos)), List.length(&2, Ops.Item, items)))), List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, state, Nat.sub(at, pos)), List.length(&2, Ops.Item, items)), old_walk(rest, Nat.add(at, List.length(&2, Ops.Item, items)), List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, state, Nat.sub(at, pos)), List.length(&2, Ops.Item, items)))),
        Equal.trans(List<&2, Ops.Item>, List.append(&2, Ops.Item, List.take(&2, Ops.Item, state, Nat.sub(at, pos)), List.append(&2, Ops.Item, List.take(&2, Ops.Item, List.drop(&2, Ops.Item, state, Nat.sub(at, pos)), List.length(&2, Ops.Item, items)), List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, state, Nat.sub(at, pos)), List.length(&2, Ops.Item, items)))), List.append(&2, Ops.Item, List.take(&2, Ops.Item, state, Nat.sub(at, pos)), List.drop(&2, Ops.Item, state, Nat.sub(at, pos))), state,
        Equal.cong(List<&2, Ops.Item>, List<&2, Ops.Item>, l => List.append(&2, Ops.Item, List.take(&2, Ops.Item, state, Nat.sub(at, pos)), l), List.append(&2, Ops.Item, List.take(&2, Ops.Item, List.drop(&2, Ops.Item, state, Nat.sub(at, pos)), List.length(&2, Ops.Item, items)), List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, state, Nat.sub(at, pos)), List.length(&2, Ops.Item, items))), List.drop(&2, Ops.Item, state, Nat.sub(at, pos)), take_drop(List.drop(&2, Ops.Item, state, Nat.sub(at, pos)), List.length(&2, Ops.Item, items))),
        take_drop(state, Nat.sub(at, pos))))))))

# The child side
# --------------

def is_done(r: Result<&2, &2, String, List<&2, Ops.Item>>) -> Bool:
  match r:
    case Done{x}:
      True{}
    case Fail{e}:
      False{}

def comb_w(err: Maybe<&2, String>, -front: List<&2, Ops.Item>, later: Result<&2, &2, String, List<&2, Ops.Item>>, h: {is_done(Cursor.combine(err, front, later)) == True{} : Bool}) -> {is_done(later) == True{} : Bool}:
  match err later:
    case Some{e} Fail{x}:
      Empty.absurd({False{} == True{} : Bool}, Comp.false_true(h))
    case Some{e} Done{x}:
      {==}
    case None{} Fail{x}:
      Empty.absurd({False{} == True{} : Bool}, Comp.false_true(h))
    case None{} Done{x}:
      {==}

def comb_e(err: Maybe<&2, String>, -front: List<&2, Ops.Item>, later: Result<&2, &2, String, List<&2, Ops.Item>>, h: {is_done(Cursor.combine(err, front, later)) == True{} : Bool}) -> {err == None{} : Maybe<&2, String>}:
  match err later:
    case Some{e} Fail{x}:
      Empty.absurd({Some{e} == None{} : Maybe<&2, String>}, Comp.false_true(h))
    case Some{e} Done{x}:
      Empty.absurd({Some{e} == None{} : Maybe<&2, String>}, Comp.false_true(h))
    case None{} Fail{x}:
      {==}
    case None{} Done{x}:
      {==}

# Where the cursor reads the child, the lines that are not removals are it.
def new_walk(ops: List<&2, Ops.Op>, +pos: Nat, +state: List<&2, Ops.Item>, +h: {is_done(Cursor.walk(ops, pos, state)) == True{} : Bool}) -> {Cursor.walk(ops, pos, state) == Done{Main.laid.new(Main.laid.walk(ops, pos, state))} : Result<&2, &2, String, List<&2, Ops.Item>>}:
  match ops:
    case Nil{}:
      Equal.cong(List<&2, Ops.Item>, Result<&2, &2, String, List<&2, Ops.Item>>, l => Done{l}, state, Main.laid.new(Main.laid.all(" ", state)), Equal.sym(List<&2, Ops.Item>, Main.laid.new(Main.laid.all(" ", state)), state, new_ctx(state)))
    case Ops.Op{Ops.Insert{}, +at, +items} <> +rest:
      Equal.trans(Result<&2, &2, String, List<&2, Ops.Item>>, Cursor.combine(None{}, List.append(&2, Ops.Item, List.take(&2, Ops.Item, state, Nat.sub(at, pos)), items), Cursor.walk(rest, Nat.max(pos, at), List.drop(&2, Ops.Item, state, Nat.sub(at, pos)))), Cursor.combine(None{}, List.append(&2, Ops.Item, List.take(&2, Ops.Item, state, Nat.sub(at, pos)), items), Done{Main.laid.new(Main.laid.walk(rest, Nat.max(pos, at), List.drop(&2, Ops.Item, state, Nat.sub(at, pos))))}), Done{Main.laid.new(List.append(&2, Main.Laid, Main.laid.all(" ", List.take(&2, Ops.Item, state, Nat.sub(at, pos))), List.append(&2, Main.Laid, Main.laid.all("+", items), Main.laid.walk(rest, Nat.max(pos, at), List.drop(&2, Ops.Item, state, Nat.sub(at, pos))))))},
        Equal.cong(Result<&2, &2, String, List<&2, Ops.Item>>, Result<&2, &2, String, List<&2, Ops.Item>>, w => Cursor.combine(None{}, List.append(&2, Ops.Item, List.take(&2, Ops.Item, state, Nat.sub(at, pos)), items), w), Cursor.walk(rest, Nat.max(pos, at), List.drop(&2, Ops.Item, state, Nat.sub(at, pos))), Done{Main.laid.new(Main.laid.walk(rest, Nat.max(pos, at), List.drop(&2, Ops.Item, state, Nat.sub(at, pos))))}, new_walk(rest, Nat.max(pos, at), List.drop(&2, Ops.Item, state, Nat.sub(at, pos)), comb_w(None{}, List.append(&2, Ops.Item, List.take(&2, Ops.Item, state, Nat.sub(at, pos)), items), Cursor.walk(rest, Nat.max(pos, at), List.drop(&2, Ops.Item, state, Nat.sub(at, pos))), h))),
        Equal.cong(List<&2, Ops.Item>, Result<&2, &2, String, List<&2, Ops.Item>>, l => Done{l}, List.append(&2, Ops.Item, List.append(&2, Ops.Item, List.take(&2, Ops.Item, state, Nat.sub(at, pos)), items), Main.laid.new(Main.laid.walk(rest, Nat.max(pos, at), List.drop(&2, Ops.Item, state, Nat.sub(at, pos))))), Main.laid.new(List.append(&2, Main.Laid, Main.laid.all(" ", List.take(&2, Ops.Item, state, Nat.sub(at, pos))), List.append(&2, Main.Laid, Main.laid.all("+", items), Main.laid.walk(rest, Nat.max(pos, at), List.drop(&2, Ops.Item, state, Nat.sub(at, pos)))))),
          Equal.trans(List<&2, Ops.Item>, List.append(&2, Ops.Item, List.append(&2, Ops.Item, List.take(&2, Ops.Item, state, Nat.sub(at, pos)), items), Main.laid.new(Main.laid.walk(rest, Nat.max(pos, at), List.drop(&2, Ops.Item, state, Nat.sub(at, pos))))), List.append(&2, Ops.Item, List.take(&2, Ops.Item, state, Nat.sub(at, pos)), List.append(&2, Ops.Item, items, Main.laid.new(Main.laid.walk(rest, Nat.max(pos, at), List.drop(&2, Ops.Item, state, Nat.sub(at, pos)))))), Main.laid.new(List.append(&2, Main.Laid, Main.laid.all(" ", List.take(&2, Ops.Item, state, Nat.sub(at, pos))), List.append(&2, Main.Laid, Main.laid.all("+", items), Main.laid.walk(rest, Nat.max(pos, at), List.drop(&2, Ops.Item, state, Nat.sub(at, pos)))))),
        app_assoc(List.take(&2, Ops.Item, state, Nat.sub(at, pos)), items, Main.laid.new(Main.laid.walk(rest, Nat.max(pos, at), List.drop(&2, Ops.Item, state, Nat.sub(at, pos))))),
        Equal.trans(List<&2, Ops.Item>, List.append(&2, Ops.Item, List.take(&2, Ops.Item, state, Nat.sub(at, pos)), List.append(&2, Ops.Item, items, Main.laid.new(Main.laid.walk(rest, Nat.max(pos, at), List.drop(&2, Ops.Item, state, Nat.sub(at, pos)))))), List.append(&2, Ops.Item, Main.laid.new(Main.laid.all(" ", List.take(&2, Ops.Item, state, Nat.sub(at, pos)))), List.append(&2, Ops.Item, items, Main.laid.new(Main.laid.walk(rest, Nat.max(pos, at), List.drop(&2, Ops.Item, state, Nat.sub(at, pos)))))), Main.laid.new(List.append(&2, Main.Laid, Main.laid.all(" ", List.take(&2, Ops.Item, state, Nat.sub(at, pos))), List.append(&2, Main.Laid, Main.laid.all("+", items), Main.laid.walk(rest, Nat.max(pos, at), List.drop(&2, Ops.Item, state, Nat.sub(at, pos)))))),
        Equal.cong(List<&2, Ops.Item>, List<&2, Ops.Item>, l => List.append(&2, Ops.Item, l, List.append(&2, Ops.Item, items, Main.laid.new(Main.laid.walk(rest, Nat.max(pos, at), List.drop(&2, Ops.Item, state, Nat.sub(at, pos)))))), List.take(&2, Ops.Item, state, Nat.sub(at, pos)), Main.laid.new(Main.laid.all(" ", List.take(&2, Ops.Item, state, Nat.sub(at, pos)))), Equal.sym(List<&2, Ops.Item>, Main.laid.new(Main.laid.all(" ", List.take(&2, Ops.Item, state, Nat.sub(at, pos)))), List.take(&2, Ops.Item, state, Nat.sub(at, pos)), new_ctx(List.take(&2, Ops.Item, state, Nat.sub(at, pos))))),
        Equal.trans(List<&2, Ops.Item>, List.append(&2, Ops.Item, Main.laid.new(Main.laid.all(" ", List.take(&2, Ops.Item, state, Nat.sub(at, pos)))), List.append(&2, Ops.Item, items, Main.laid.new(Main.laid.walk(rest, Nat.max(pos, at), List.drop(&2, Ops.Item, state, Nat.sub(at, pos)))))), List.append(&2, Ops.Item, Main.laid.new(Main.laid.all(" ", List.take(&2, Ops.Item, state, Nat.sub(at, pos)))), List.append(&2, Ops.Item, Main.laid.new(Main.laid.all("+", items)), Main.laid.new(Main.laid.walk(rest, Nat.max(pos, at), List.drop(&2, Ops.Item, state, Nat.sub(at, pos)))))), Main.laid.new(List.append(&2, Main.Laid, Main.laid.all(" ", List.take(&2, Ops.Item, state, Nat.sub(at, pos))), List.append(&2, Main.Laid, Main.laid.all("+", items), Main.laid.walk(rest, Nat.max(pos, at), List.drop(&2, Ops.Item, state, Nat.sub(at, pos)))))),
        Equal.cong(List<&2, Ops.Item>, List<&2, Ops.Item>, l => List.append(&2, Ops.Item, Main.laid.new(Main.laid.all(" ", List.take(&2, Ops.Item, state, Nat.sub(at, pos)))), List.append(&2, Ops.Item, l, Main.laid.new(Main.laid.walk(rest, Nat.max(pos, at), List.drop(&2, Ops.Item, state, Nat.sub(at, pos)))))), items, Main.laid.new(Main.laid.all("+", items)), Equal.sym(List<&2, Ops.Item>, Main.laid.new(Main.laid.all("+", items)), items, new_plus(items))),
        Equal.trans(List<&2, Ops.Item>, List.append(&2, Ops.Item, Main.laid.new(Main.laid.all(" ", List.take(&2, Ops.Item, state, Nat.sub(at, pos)))), List.append(&2, Ops.Item, Main.laid.new(Main.laid.all("+", items)), Main.laid.new(Main.laid.walk(rest, Nat.max(pos, at), List.drop(&2, Ops.Item, state, Nat.sub(at, pos)))))), List.append(&2, Ops.Item, Main.laid.new(Main.laid.all(" ", List.take(&2, Ops.Item, state, Nat.sub(at, pos)))), Main.laid.new(List.append(&2, Main.Laid, Main.laid.all("+", items), Main.laid.walk(rest, Nat.max(pos, at), List.drop(&2, Ops.Item, state, Nat.sub(at, pos)))))), Main.laid.new(List.append(&2, Main.Laid, Main.laid.all(" ", List.take(&2, Ops.Item, state, Nat.sub(at, pos))), List.append(&2, Main.Laid, Main.laid.all("+", items), Main.laid.walk(rest, Nat.max(pos, at), List.drop(&2, Ops.Item, state, Nat.sub(at, pos)))))),
        Equal.cong(List<&2, Ops.Item>, List<&2, Ops.Item>, l => List.append(&2, Ops.Item, Main.laid.new(Main.laid.all(" ", List.take(&2, Ops.Item, state, Nat.sub(at, pos)))), l), List.append(&2, Ops.Item, Main.laid.new(Main.laid.all("+", items)), Main.laid.new(Main.laid.walk(rest, Nat.max(pos, at), List.drop(&2, Ops.Item, state, Nat.sub(at, pos))))), Main.laid.new(List.append(&2, Main.Laid, Main.laid.all("+", items), Main.laid.walk(rest, Nat.max(pos, at), List.drop(&2, Ops.Item, state, Nat.sub(at, pos))))), Equal.sym(List<&2, Ops.Item>, Main.laid.new(List.append(&2, Main.Laid, Main.laid.all("+", items), Main.laid.walk(rest, Nat.max(pos, at), List.drop(&2, Ops.Item, state, Nat.sub(at, pos))))), List.append(&2, Ops.Item, Main.laid.new(Main.laid.all("+", items)), Main.laid.new(Main.laid.walk(rest, Nat.max(pos, at), List.drop(&2, Ops.Item, state, Nat.sub(at, pos))))), new_app(Main.laid.all("+", items), Main.laid.walk(rest, Nat.max(pos, at), List.drop(&2, Ops.Item, state, Nat.sub(at, pos)))))),
        Equal.sym(List<&2, Ops.Item>, Main.laid.new(List.append(&2, Main.Laid, Main.laid.all(" ", List.take(&2, Ops.Item, state, Nat.sub(at, pos))), List.append(&2, Main.Laid, Main.laid.all("+", items), Main.laid.walk(rest, Nat.max(pos, at), List.drop(&2, Ops.Item, state, Nat.sub(at, pos)))))), List.append(&2, Ops.Item, Main.laid.new(Main.laid.all(" ", List.take(&2, Ops.Item, state, Nat.sub(at, pos)))), Main.laid.new(List.append(&2, Main.Laid, Main.laid.all("+", items), Main.laid.walk(rest, Nat.max(pos, at), List.drop(&2, Ops.Item, state, Nat.sub(at, pos)))))), new_app(Main.laid.all(" ", List.take(&2, Ops.Item, state, Nat.sub(at, pos))), List.append(&2, Main.Laid, Main.laid.all("+", items), Main.laid.walk(rest, Nat.max(pos, at), List.drop(&2, Ops.Item, state, Nat.sub(at, pos))))))))))))
    case Ops.Op{Ops.Delete{}, +at, +items} <> +rest:
      Equal.trans(Result<&2, &2, String, List<&2, Ops.Item>>, Cursor.combine(Cursor.disagreement(at, Spec.prefix_matches(items, List.drop(&2, Ops.Item, state, Nat.sub(at, pos)))), List.take(&2, Ops.Item, state, Nat.sub(at, pos)), Cursor.walk(rest, Nat.add(at, List.length(&2, Ops.Item, items)), List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, state, Nat.sub(at, pos)), List.length(&2, Ops.Item, items)))), Cursor.combine(None{}, List.take(&2, Ops.Item, state, Nat.sub(at, pos)), Cursor.walk(rest, Nat.add(at, List.length(&2, Ops.Item, items)), List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, state, Nat.sub(at, pos)), List.length(&2, Ops.Item, items)))), Done{Main.laid.new(List.append(&2, Main.Laid, Main.laid.all(" ", List.take(&2, Ops.Item, state, Nat.sub(at, pos))), List.append(&2, Main.Laid, Main.laid.all("-", List.take(&2, Ops.Item, List.drop(&2, Ops.Item, state, Nat.sub(at, pos)), List.length(&2, Ops.Item, items))), Main.laid.walk(rest, Nat.add(at, List.length(&2, Ops.Item, items)), List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, state, Nat.sub(at, pos)), List.length(&2, Ops.Item, items))))))},
        Equal.cong(Maybe<&2, String>, Result<&2, &2, String, List<&2, Ops.Item>>, x => Cursor.combine(x, List.take(&2, Ops.Item, state, Nat.sub(at, pos)), Cursor.walk(rest, Nat.add(at, List.length(&2, Ops.Item, items)), List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, state, Nat.sub(at, pos)), List.length(&2, Ops.Item, items)))), Cursor.disagreement(at, Spec.prefix_matches(items, List.drop(&2, Ops.Item, state, Nat.sub(at, pos)))), None{}, comb_e(Cursor.disagreement(at, Spec.prefix_matches(items, List.drop(&2, Ops.Item, state, Nat.sub(at, pos)))), List.take(&2, Ops.Item, state, Nat.sub(at, pos)), Cursor.walk(rest, Nat.add(at, List.length(&2, Ops.Item, items)), List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, state, Nat.sub(at, pos)), List.length(&2, Ops.Item, items))), h)),
        Equal.trans(Result<&2, &2, String, List<&2, Ops.Item>>, Cursor.combine(None{}, List.take(&2, Ops.Item, state, Nat.sub(at, pos)), Cursor.walk(rest, Nat.add(at, List.length(&2, Ops.Item, items)), List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, state, Nat.sub(at, pos)), List.length(&2, Ops.Item, items)))), Cursor.combine(None{}, List.take(&2, Ops.Item, state, Nat.sub(at, pos)), Done{Main.laid.new(Main.laid.walk(rest, Nat.add(at, List.length(&2, Ops.Item, items)), List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, state, Nat.sub(at, pos)), List.length(&2, Ops.Item, items))))}), Done{Main.laid.new(List.append(&2, Main.Laid, Main.laid.all(" ", List.take(&2, Ops.Item, state, Nat.sub(at, pos))), List.append(&2, Main.Laid, Main.laid.all("-", List.take(&2, Ops.Item, List.drop(&2, Ops.Item, state, Nat.sub(at, pos)), List.length(&2, Ops.Item, items))), Main.laid.walk(rest, Nat.add(at, List.length(&2, Ops.Item, items)), List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, state, Nat.sub(at, pos)), List.length(&2, Ops.Item, items))))))},
          Equal.cong(Result<&2, &2, String, List<&2, Ops.Item>>, Result<&2, &2, String, List<&2, Ops.Item>>, w => Cursor.combine(None{}, List.take(&2, Ops.Item, state, Nat.sub(at, pos)), w), Cursor.walk(rest, Nat.add(at, List.length(&2, Ops.Item, items)), List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, state, Nat.sub(at, pos)), List.length(&2, Ops.Item, items))), Done{Main.laid.new(Main.laid.walk(rest, Nat.add(at, List.length(&2, Ops.Item, items)), List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, state, Nat.sub(at, pos)), List.length(&2, Ops.Item, items))))}, new_walk(rest, Nat.add(at, List.length(&2, Ops.Item, items)), List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, state, Nat.sub(at, pos)), List.length(&2, Ops.Item, items)), comb_w(Cursor.disagreement(at, Spec.prefix_matches(items, List.drop(&2, Ops.Item, state, Nat.sub(at, pos)))), List.take(&2, Ops.Item, state, Nat.sub(at, pos)), Cursor.walk(rest, Nat.add(at, List.length(&2, Ops.Item, items)), List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, state, Nat.sub(at, pos)), List.length(&2, Ops.Item, items))), h))),
          Equal.cong(List<&2, Ops.Item>, Result<&2, &2, String, List<&2, Ops.Item>>, l => Done{l}, List.append(&2, Ops.Item, List.take(&2, Ops.Item, state, Nat.sub(at, pos)), Main.laid.new(Main.laid.walk(rest, Nat.add(at, List.length(&2, Ops.Item, items)), List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, state, Nat.sub(at, pos)), List.length(&2, Ops.Item, items))))), Main.laid.new(List.append(&2, Main.Laid, Main.laid.all(" ", List.take(&2, Ops.Item, state, Nat.sub(at, pos))), List.append(&2, Main.Laid, Main.laid.all("-", List.take(&2, Ops.Item, List.drop(&2, Ops.Item, state, Nat.sub(at, pos)), List.length(&2, Ops.Item, items))), Main.laid.walk(rest, Nat.add(at, List.length(&2, Ops.Item, items)), List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, state, Nat.sub(at, pos)), List.length(&2, Ops.Item, items)))))),
            Equal.trans(List<&2, Ops.Item>, List.append(&2, Ops.Item, List.take(&2, Ops.Item, state, Nat.sub(at, pos)), Main.laid.new(Main.laid.walk(rest, Nat.add(at, List.length(&2, Ops.Item, items)), List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, state, Nat.sub(at, pos)), List.length(&2, Ops.Item, items))))), List.append(&2, Ops.Item, Main.laid.new(Main.laid.all(" ", List.take(&2, Ops.Item, state, Nat.sub(at, pos)))), Main.laid.new(Main.laid.walk(rest, Nat.add(at, List.length(&2, Ops.Item, items)), List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, state, Nat.sub(at, pos)), List.length(&2, Ops.Item, items))))), Main.laid.new(List.append(&2, Main.Laid, Main.laid.all(" ", List.take(&2, Ops.Item, state, Nat.sub(at, pos))), List.append(&2, Main.Laid, Main.laid.all("-", List.take(&2, Ops.Item, List.drop(&2, Ops.Item, state, Nat.sub(at, pos)), List.length(&2, Ops.Item, items))), Main.laid.walk(rest, Nat.add(at, List.length(&2, Ops.Item, items)), List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, state, Nat.sub(at, pos)), List.length(&2, Ops.Item, items)))))),
        Equal.cong(List<&2, Ops.Item>, List<&2, Ops.Item>, l => List.append(&2, Ops.Item, l, Main.laid.new(Main.laid.walk(rest, Nat.add(at, List.length(&2, Ops.Item, items)), List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, state, Nat.sub(at, pos)), List.length(&2, Ops.Item, items))))), List.take(&2, Ops.Item, state, Nat.sub(at, pos)), Main.laid.new(Main.laid.all(" ", List.take(&2, Ops.Item, state, Nat.sub(at, pos)))), Equal.sym(List<&2, Ops.Item>, Main.laid.new(Main.laid.all(" ", List.take(&2, Ops.Item, state, Nat.sub(at, pos)))), List.take(&2, Ops.Item, state, Nat.sub(at, pos)), new_ctx(List.take(&2, Ops.Item, state, Nat.sub(at, pos))))),
        Equal.trans(List<&2, Ops.Item>, List.append(&2, Ops.Item, Main.laid.new(Main.laid.all(" ", List.take(&2, Ops.Item, state, Nat.sub(at, pos)))), Main.laid.new(Main.laid.walk(rest, Nat.add(at, List.length(&2, Ops.Item, items)), List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, state, Nat.sub(at, pos)), List.length(&2, Ops.Item, items))))), List.append(&2, Ops.Item, Main.laid.new(Main.laid.all(" ", List.take(&2, Ops.Item, state, Nat.sub(at, pos)))), List.append(&2, Ops.Item, Main.laid.new(Main.laid.all("-", List.take(&2, Ops.Item, List.drop(&2, Ops.Item, state, Nat.sub(at, pos)), List.length(&2, Ops.Item, items)))), Main.laid.new(Main.laid.walk(rest, Nat.add(at, List.length(&2, Ops.Item, items)), List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, state, Nat.sub(at, pos)), List.length(&2, Ops.Item, items)))))), Main.laid.new(List.append(&2, Main.Laid, Main.laid.all(" ", List.take(&2, Ops.Item, state, Nat.sub(at, pos))), List.append(&2, Main.Laid, Main.laid.all("-", List.take(&2, Ops.Item, List.drop(&2, Ops.Item, state, Nat.sub(at, pos)), List.length(&2, Ops.Item, items))), Main.laid.walk(rest, Nat.add(at, List.length(&2, Ops.Item, items)), List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, state, Nat.sub(at, pos)), List.length(&2, Ops.Item, items)))))),
        Equal.cong(List<&2, Ops.Item>, List<&2, Ops.Item>, l => List.append(&2, Ops.Item, Main.laid.new(Main.laid.all(" ", List.take(&2, Ops.Item, state, Nat.sub(at, pos)))), List.append(&2, Ops.Item, l, Main.laid.new(Main.laid.walk(rest, Nat.add(at, List.length(&2, Ops.Item, items)), List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, state, Nat.sub(at, pos)), List.length(&2, Ops.Item, items)))))), Nil{}, Main.laid.new(Main.laid.all("-", List.take(&2, Ops.Item, List.drop(&2, Ops.Item, state, Nat.sub(at, pos)), List.length(&2, Ops.Item, items)))), Equal.sym(List<&2, Ops.Item>, Main.laid.new(Main.laid.all("-", List.take(&2, Ops.Item, List.drop(&2, Ops.Item, state, Nat.sub(at, pos)), List.length(&2, Ops.Item, items)))), Nil{}, new_minus(List.take(&2, Ops.Item, List.drop(&2, Ops.Item, state, Nat.sub(at, pos)), List.length(&2, Ops.Item, items))))),
        Equal.trans(List<&2, Ops.Item>, List.append(&2, Ops.Item, Main.laid.new(Main.laid.all(" ", List.take(&2, Ops.Item, state, Nat.sub(at, pos)))), List.append(&2, Ops.Item, Main.laid.new(Main.laid.all("-", List.take(&2, Ops.Item, List.drop(&2, Ops.Item, state, Nat.sub(at, pos)), List.length(&2, Ops.Item, items)))), Main.laid.new(Main.laid.walk(rest, Nat.add(at, List.length(&2, Ops.Item, items)), List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, state, Nat.sub(at, pos)), List.length(&2, Ops.Item, items)))))), List.append(&2, Ops.Item, Main.laid.new(Main.laid.all(" ", List.take(&2, Ops.Item, state, Nat.sub(at, pos)))), Main.laid.new(List.append(&2, Main.Laid, Main.laid.all("-", List.take(&2, Ops.Item, List.drop(&2, Ops.Item, state, Nat.sub(at, pos)), List.length(&2, Ops.Item, items))), Main.laid.walk(rest, Nat.add(at, List.length(&2, Ops.Item, items)), List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, state, Nat.sub(at, pos)), List.length(&2, Ops.Item, items)))))), Main.laid.new(List.append(&2, Main.Laid, Main.laid.all(" ", List.take(&2, Ops.Item, state, Nat.sub(at, pos))), List.append(&2, Main.Laid, Main.laid.all("-", List.take(&2, Ops.Item, List.drop(&2, Ops.Item, state, Nat.sub(at, pos)), List.length(&2, Ops.Item, items))), Main.laid.walk(rest, Nat.add(at, List.length(&2, Ops.Item, items)), List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, state, Nat.sub(at, pos)), List.length(&2, Ops.Item, items)))))),
        Equal.cong(List<&2, Ops.Item>, List<&2, Ops.Item>, l => List.append(&2, Ops.Item, Main.laid.new(Main.laid.all(" ", List.take(&2, Ops.Item, state, Nat.sub(at, pos)))), l), List.append(&2, Ops.Item, Main.laid.new(Main.laid.all("-", List.take(&2, Ops.Item, List.drop(&2, Ops.Item, state, Nat.sub(at, pos)), List.length(&2, Ops.Item, items)))), Main.laid.new(Main.laid.walk(rest, Nat.add(at, List.length(&2, Ops.Item, items)), List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, state, Nat.sub(at, pos)), List.length(&2, Ops.Item, items))))), Main.laid.new(List.append(&2, Main.Laid, Main.laid.all("-", List.take(&2, Ops.Item, List.drop(&2, Ops.Item, state, Nat.sub(at, pos)), List.length(&2, Ops.Item, items))), Main.laid.walk(rest, Nat.add(at, List.length(&2, Ops.Item, items)), List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, state, Nat.sub(at, pos)), List.length(&2, Ops.Item, items))))), Equal.sym(List<&2, Ops.Item>, Main.laid.new(List.append(&2, Main.Laid, Main.laid.all("-", List.take(&2, Ops.Item, List.drop(&2, Ops.Item, state, Nat.sub(at, pos)), List.length(&2, Ops.Item, items))), Main.laid.walk(rest, Nat.add(at, List.length(&2, Ops.Item, items)), List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, state, Nat.sub(at, pos)), List.length(&2, Ops.Item, items))))), List.append(&2, Ops.Item, Main.laid.new(Main.laid.all("-", List.take(&2, Ops.Item, List.drop(&2, Ops.Item, state, Nat.sub(at, pos)), List.length(&2, Ops.Item, items)))), Main.laid.new(Main.laid.walk(rest, Nat.add(at, List.length(&2, Ops.Item, items)), List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, state, Nat.sub(at, pos)), List.length(&2, Ops.Item, items))))), new_app(Main.laid.all("-", List.take(&2, Ops.Item, List.drop(&2, Ops.Item, state, Nat.sub(at, pos)), List.length(&2, Ops.Item, items))), Main.laid.walk(rest, Nat.add(at, List.length(&2, Ops.Item, items)), List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, state, Nat.sub(at, pos)), List.length(&2, Ops.Item, items)))))),
        Equal.sym(List<&2, Ops.Item>, Main.laid.new(List.append(&2, Main.Laid, Main.laid.all(" ", List.take(&2, Ops.Item, state, Nat.sub(at, pos))), List.append(&2, Main.Laid, Main.laid.all("-", List.take(&2, Ops.Item, List.drop(&2, Ops.Item, state, Nat.sub(at, pos)), List.length(&2, Ops.Item, items))), Main.laid.walk(rest, Nat.add(at, List.length(&2, Ops.Item, items)), List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, state, Nat.sub(at, pos)), List.length(&2, Ops.Item, items)))))), List.append(&2, Ops.Item, Main.laid.new(Main.laid.all(" ", List.take(&2, Ops.Item, state, Nat.sub(at, pos)))), Main.laid.new(List.append(&2, Main.Laid, Main.laid.all("-", List.take(&2, Ops.Item, List.drop(&2, Ops.Item, state, Nat.sub(at, pos)), List.length(&2, Ops.Item, items))), Main.laid.walk(rest, Nat.add(at, List.length(&2, Ops.Item, items)), List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, state, Nat.sub(at, pos)), List.length(&2, Ops.Item, items)))))), new_app(Main.laid.all(" ", List.take(&2, Ops.Item, state, Nat.sub(at, pos))), List.append(&2, Main.Laid, Main.laid.all("-", List.take(&2, Ops.Item, List.drop(&2, Ops.Item, state, Nat.sub(at, pos)), List.length(&2, Ops.Item, items))), Main.laid.walk(rest, Nat.add(at, List.length(&2, Ops.Item, items)), List.drop(&2, Ops.Item, List.drop(&2, Ops.Item, state, Nat.sub(at, pos)), List.length(&2, Ops.Item, items))))))))))))

# Past the checks
# ---------------

def fdisc(r: Result<&2, &2, String, List<&2, Ops.Item>>) -> Type:
  match r:
    case Done{x}:
      Empty
    case Fail{e}:
      Unit

def fail_done(-e: String, -x: List<&2, Ops.Item>, h: {Fail{e} == Done{x} : Result<&2, &2, String, List<&2, Ops.Item>>}) -> Empty:
  %h : {fdisc(_) : Type}
  Unit{}

def done_items(-a: List<&2, Ops.Item>, -b: List<&2, Ops.Item>, h: {Done{a} == Done{b} : Result<&2, &2, String, List<&2, Ops.Item>>}) -> {a == b : List<&2, Ops.Item>}:
  Equal.cong(Result<&2, &2, String, List<&2, Ops.Item>>, List<&2, Ops.Item>, r => Result.default(&2, &2, String, List<&2, Ops.Item>, r, a), Done{a}, Done{b}, h)

def after_done(+w: List<&2, Ops.Item>, tb: Bool, dig: Result<&2, &2, String, Unit>, -c: List<&2, Ops.Item>, e: {Diff.after_checks(w, tb, dig) == Done{c} : Result<&2, &2, String, List<&2, Ops.Item>>}) -> {w == c : List<&2, Ops.Item>}:
  match tb dig:
    case True{} Done{u}:
      done_items(w, c, e)
    case True{} Fail{m}:
      Empty.absurd({w == c : List<&2, Ops.Item>}, fail_done(m, c, e))
    case False{} Done{u}:
      Empty.absurd({w == c : List<&2, Ops.Item>}, fail_done("line 0: an item without a newline that is not the last", c, e))
    case False{} Fail{m}:
      Empty.absurd({w == c : List<&2, Ops.Item>}, fail_done("line 0: an item without a newline that is not the last", c, e))

def checked_done(in_range: Bool, +result: Maybe<&2, String>, replayed: Result<&2, &2, String, List<&2, Ops.Item>>, -c: List<&2, Ops.Item>, e: {Cursor.checked(in_range, result, replayed) == Done{c} : Result<&2, &2, String, List<&2, Ops.Item>>}) -> {replayed == Done{c} : Result<&2, &2, String, List<&2, Ops.Item>>}:
  match in_range replayed:
    case False{} Done{w}:
      Empty.absurd({Done{w} == Done{c} : Result<&2, &2, String, List<&2, Ops.Item>>}, fail_done("an operation counts past the end of the parent", c, e))
    case False{} Fail{m}:
      Empty.absurd({Fail{m} == Done{c} : Result<&2, &2, String, List<&2, Ops.Item>>}, fail_done("an operation counts past the end of the parent", c, e))
    case True{} Fail{m}:
      Empty.absurd({Fail{m} == Done{c} : Result<&2, &2, String, List<&2, Ops.Item>>}, fail_done(m, c, e))
    case True{} Done{+w}:
      Equal.cong(List<&2, Ops.Item>, Result<&2, &2, String, List<&2, Ops.Item>>, l => Done{l}, w, c, after_done(w, Ops.terminated_but_last(w), Ops.check_result(result, w), c,
        Equal.trans(Result<&2, &2, String, List<&2, Ops.Item>>, Diff.after_checks(w, Ops.terminated_but_last(w), Ops.check_result(result, w)), Ops.apply.checked(result, w), Done{c}, Equal.sym(Result<&2, &2, String, List<&2, Ops.Item>>, Ops.apply.checked(result, w), Diff.after_checks(w, Ops.terminated_but_last(w), Ops.check_result(result, w)), Refuse.checked_is(w, result)), e)))

# The laws
# --------

def laid_keeps_parent(+parent: List<&2, Ops.Item>, doc: Ops.Doc) -> {Main.laid.old(Main.laid(parent, doc)) == parent : List<&2, Ops.Item>}:
  match doc:
    case Ops.Doc{f, r, ops}:
      old_walk(ops, 0n, parent)

def laid_reads_child(+parent: List<&2, Ops.Item>, doc: Ops.Doc, +c: List<&2, Ops.Item>, e: {Cursor.apply(parent, doc) == Done{c} : Result<&2, &2, String, List<&2, Ops.Item>>}) -> {Main.laid.new(Main.laid(parent, doc)) == c : List<&2, Ops.Item>}:
  match doc:
    case Ops.Doc{f, +r, +ops}:
      +w1 = checked_done(Ops.in_range(ops, List.length(&2, Ops.Item, parent)), r, Cursor.walk(ops, 0n, parent), c, e)
      done_items(Main.laid.new(Main.laid.walk(ops, 0n, parent)), c,
        Equal.trans(Result<&2, &2, String, List<&2, Ops.Item>>, Done{Main.laid.new(Main.laid.walk(ops, 0n, parent))}, Cursor.walk(ops, 0n, parent), Done{c},
          Equal.sym(Result<&2, &2, String, List<&2, Ops.Item>>, Cursor.walk(ops, 0n, parent), Done{Main.laid.new(Main.laid.walk(ops, 0n, parent))},
            new_walk(ops, 0n, parent, (%Equal.sym(Result<&2, &2, String, List<&2, Ops.Item>>, Cursor.walk(ops, 0n, parent), Done{c}, w1) : {is_done(_) == True{} : Bool}
              {==}))),
          w1))
