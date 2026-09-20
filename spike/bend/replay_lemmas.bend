# List algebra for the replay invariant. All arguments are arbitrary;
# these lemmas expose no implementation-specific operation assumptions.
import Base
import ./ops.bend as Ops
import ./cursor_spec.bend as Cursor

def append_nil(xs: List<&2, Ops.Item>) -> {List.append(&2, Ops.Item, xs, Nil{}) == xs : List<&2, Ops.Item>}:
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      %append_nil(t) : {h <> List.append(&2, Ops.Item, t, Nil{}) == h <> _ : List<&2, Ops.Item>}
      {==}

def append_assoc(xs: List<&2, Ops.Item>, -ys: List<&2, Ops.Item>, -zs: List<&2, Ops.Item>) -> {List.append(&2, Ops.Item, List.append(&2, Ops.Item, xs, ys), zs) == List.append(&2, Ops.Item, xs, List.append(&2, Ops.Item, ys, zs)) : List<&2, Ops.Item>}:
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      %append_assoc(t, ys, zs) : {h <> List.append(&2, Ops.Item, List.append(&2, Ops.Item, t, ys), zs) == h <> _ : List<&2, Ops.Item>}
      {==}

def reverse_extend(xs: List<&2, Ops.Item>, acc: List<&2, Ops.Item>, -tail: List<&2, Ops.Item>) -> {List.reverse.go(&2, Ops.Item, xs, List.append(&2, Ops.Item, acc, tail)) == List.append(&2, Ops.Item, List.reverse.go(&2, Ops.Item, xs, acc), tail) : List<&2, Ops.Item>}:
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      reverse_extend(t, h <> acc, tail)

def reverse_twice(xs: List<&2, Ops.Item>, acc: List<&2, Ops.Item>, -tail: List<&2, Ops.Item>) -> {List.reverse.go(&2, Ops.Item, List.reverse.go(&2, Ops.Item, xs, acc), tail) == List.reverse.go(&2, Ops.Item, acc, List.append(&2, Ops.Item, xs, tail)) : List<&2, Ops.Item>}:
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      reverse_twice(t, h <> acc, tail)

# Reading a reversed accumulator after moving a prefix appends that prefix
# in its original order. This is the representation invariant's key step.
def reverse_move(+xs: List<&2, Ops.Item>, +acc: List<&2, Ops.Item>) -> {List.reverse(&2, Ops.Item, List.reverse.go(&2, Ops.Item, xs, acc)) == List.append(&2, Ops.Item, List.reverse(&2, Ops.Item, acc), xs) : List<&2, Ops.Item>}:
  %reverse_extend(acc, Nil{}, xs) : {List.reverse(&2, Ops.Item, List.reverse.go(&2, Ops.Item, xs, acc)) == _ : List<&2, Ops.Item>}
  %append_nil(xs) : {List.reverse(&2, Ops.Item, List.reverse.go(&2, Ops.Item, xs, acc)) == List.reverse.go(&2, Ops.Item, acc, _) : List<&2, Ops.Item>}
  reverse_twice(xs, acc, Nil{})

def reverse_insert(+items: List<&2, Ops.Item>, +acc: List<&2, Ops.Item>) -> {List.reverse(&2, Ops.Item, List.append(&2, Ops.Item, List.reverse(&2, Ops.Item, items), acc)) == List.append(&2, Ops.Item, List.reverse(&2, Ops.Item, acc), items) : List<&2, Ops.Item>}:
  %reverse_extend(items, Nil{}, acc) : {List.reverse(&2, Ops.Item, _) == List.append(&2, Ops.Item, List.reverse(&2, Ops.Item, acc), items) : List<&2, Ops.Item>}
  reverse_move(items, acc)

# Earlier errors win; successful segments associate in forward order.
def combine_assoc(e: Maybe<&2, String>, f: Maybe<&2, String>, a: List<&2, Ops.Item>, -b: List<&2, Ops.Item>, r: Result<&2, &2, String, List<&2, Ops.Item>>) -> {Cursor.combine(e, a, Cursor.combine(f, b, r)) == Cursor.combine(Maybe.or(&2, String, e, f), List.append(&2, Ops.Item, a, b), r) : Result<&2, &2, String, List<&2, Ops.Item>>}:
  match e f r:
    case Some{err} _ _:
      {==}
    case None{} Some{err} _:
      {==}
    case None{} None{} Fail{err}:
      {==}
    case None{} None{} Done{items}:
      %append_assoc(a, b, items) : {Done{_} == Done{List.append(&2, Ops.Item, List.append(&2, Ops.Item, a, b), items)} : Result<&2, &2, String, List<&2, Ops.Item>>}
      {==}

def combine_split(e: Maybe<&2, String>, f: Maybe<&2, String>, a: List<&2, Ops.Item>, -b: List<&2, Ops.Item>, r: Result<&2, &2, String, List<&2, Ops.Item>>) -> {Cursor.combine(Maybe.or(&2, String, e, f), List.append(&2, Ops.Item, a, b), r) == Cursor.combine(e, a, Cursor.combine(f, b, r)) : Result<&2, &2, String, List<&2, Ops.Item>>}:
  Equal.sym(Result<&2, &2, String, List<&2, Ops.Item>>, Cursor.combine(e, a, Cursor.combine(f, b, r)), Cursor.combine(Maybe.or(&2, String, e, f), List.append(&2, Ops.Item, a, b), r), combine_assoc(e, f, a, b, r))

def or_none(e: Maybe<&2, String>) -> {Maybe.or(&2, String, e, None{}) == e : Maybe<&2, String>}:
  match e:
    case None{}:
      {==}
    case Some{x}:
      {==}

def insert_acc(+items: List<&2, Ops.Item>, +prefix: List<&2, Ops.Item>, +acc: List<&2, Ops.Item>) -> {List.reverse(&2, Ops.Item, List.append(&2, Ops.Item, List.reverse(&2, Ops.Item, items), List.reverse.go(&2, Ops.Item, prefix, acc))) == List.append(&2, Ops.Item, List.reverse(&2, Ops.Item, acc), List.append(&2, Ops.Item, prefix, items)) : List<&2, Ops.Item>}:
  %append_assoc(List.reverse(&2, Ops.Item, acc), prefix, items) : {List.reverse(&2, Ops.Item, List.append(&2, Ops.Item, List.reverse(&2, Ops.Item, items), List.reverse.go(&2, Ops.Item, prefix, acc))) == _ : List<&2, Ops.Item>}
  %reverse_move(prefix, acc) : {List.reverse(&2, Ops.Item, List.append(&2, Ops.Item, List.reverse(&2, Ops.Item, items), List.reverse.go(&2, Ops.Item, prefix, acc))) == List.append(&2, Ops.Item, _, items) : List<&2, Ops.Item>}
  reverse_insert(items, List.reverse.go(&2, Ops.Item, prefix, acc))

def combine_nil(r: Result<&2, &2, String, List<&2, Ops.Item>>) -> {Cursor.combine(None{}, Nil{}, r) == r : Result<&2, &2, String, List<&2, Ops.Item>>}:
  match r:
    case Fail{e}:
      {==}
    case Done{items}:
      {==}
