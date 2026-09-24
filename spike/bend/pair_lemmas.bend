# What `diff` pairs, file by file. `both` sorts each side by file and walks
# the two together; for any file, the pairs it lists under that file are the
# entries each side holds under it, paired in order as far as either goes —
# so where each side holds a file once, `diff` compares it once, with each
# side's entry for it.
import Base
import ./tree.bend as Tree
import ./commands.bend as Main
import ./sort_lemmas.bend as SortL
import ./string_lemmas.bend as S
import ./composition_lemmas.bend as Comp
import ./position_lemmas.bend as Pos

def kd_at(+f: String, xs: List<&2, Tree.Entry>) -> {Main.entries.at(f, xs) == SortL.keyed(~Tree.Entry, ~Tree.entry_file, f, xs) : List<&2, Tree.Entry>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      %Equal.sym(List<&2, Tree.Entry>, Main.entries.at(f, rest), SortL.keyed(~Tree.Entry, ~Tree.entry_file, f, rest), kd_at(f, rest)) : {Bool.pick(List<&2, Tree.Entry>, String.eq(Tree.entry_file(x), f), x <> _, _) == SortL.keyed(~Tree.Entry, ~Tree.entry_file, f, x <> rest) : List<&2, Tree.Entry>}
      {==}

# A run sorted above a name is sorted above any name below it.
def sf_weaken(l: List<&2, Tree.Entry>, +k: String, +k0: String, h0: {String.is_le(k0, k) == True{} : Bool}, +h: {SortL.sorted.from(~Tree.Entry, ~Tree.entry_file, l, k) == True{} : Bool}) -> {SortL.sorted.from(~Tree.Entry, ~Tree.entry_file, l, k0) == True{} : Bool}:
  match l:
    case Nil{}:
      {==}
    case +z <> r:
      SortL.band_i(String.is_le(k0, Tree.entry_file(z)), SortL.sorted.from(~Tree.Entry, ~Tree.entry_file, r, Tree.entry_file(z)), SortL.str_le(k0, k, Tree.entry_file(z), h0, SortL.band_l(String.is_le(k, Tree.entry_file(z)), SortL.sorted.from(~Tree.Entry, ~Tree.entry_file, r, Tree.entry_file(z)), h)), SortL.band_r(String.is_le(k, Tree.entry_file(z)), SortL.sorted.from(~Tree.Entry, ~Tree.entry_file, r, Tree.entry_file(z)), h))

def sorted_tail(+x: Tree.Entry, xr: List<&2, Tree.Entry>, h: {SortL.sorted.from(~Tree.Entry, ~Tree.entry_file, x <> xr, SNil{}) == True{} : Bool}) -> {SortL.sorted.from(~Tree.Entry, ~Tree.entry_file, xr, SNil{}) == True{} : Bool}:
  sf_weaken(xr, Tree.entry_file(x), SNil{}, SortL.le_empty(Tree.entry_file(x)), SortL.band_r(String.is_le(SNil{}, Tree.entry_file(x)), SortL.sorted.from(~Tree.Entry, ~Tree.entry_file, xr, Tree.entry_file(x)), h))

def sorted_from_head(+x: Tree.Entry, xr: List<&2, Tree.Entry>, h: {SortL.sorted.from(~Tree.Entry, ~Tree.entry_file, x <> xr, SNil{}) == True{} : Bool}) -> {SortL.sorted.from(~Tree.Entry, ~Tree.entry_file, x <> xr, Tree.entry_file(x)) == True{} : Bool}:
  SortL.band_i(String.is_le(Tree.entry_file(x), Tree.entry_file(x)), SortL.sorted.from(~Tree.Entry, ~Tree.entry_file, xr, Tree.entry_file(x)), SortL.le_self(Tree.entry_file(x)), SortL.band_r(String.is_le(SNil{}, Tree.entry_file(x)), SortL.sorted.from(~Tree.Entry, ~Tree.entry_file, xr, Tree.entry_file(x)), h))

def left_t(+f: String, +x: Tree.Entry, +xr: List<&2, Tree.Entry>, +b: List<&2, Tree.Entry>, +q: List<&2, Main.Both>, +fx: {Tree.entry_file(x) == f : String}, +z: {SortL.keyed(~Tree.Entry, ~Tree.entry_file, f, b) == Nil{} : List<&2, Tree.Entry>}, ih: {Main.both.at(f, q) == Main.both.zip(f, SortL.keyed(~Tree.Entry, ~Tree.entry_file, f, xr), SortL.keyed(~Tree.Entry, ~Tree.entry_file, f, b)) : List<&2, Main.Both>}) -> {Main.Both{Tree.entry_file(x), Some{x}, None{}} <> Main.both.at(f, q) == Main.both.zip(f, x <> SortL.keyed(~Tree.Entry, ~Tree.entry_file, f, xr), SortL.keyed(~Tree.Entry, ~Tree.entry_file, f, b)) : List<&2, Main.Both>}:
  %Equal.sym(String, Tree.entry_file(x), f, fx) : {Main.Both{_, Some{x}, None{}} <> Main.both.at(f, q) == Main.both.zip(f, x <> SortL.keyed(~Tree.Entry, ~Tree.entry_file, f, xr), SortL.keyed(~Tree.Entry, ~Tree.entry_file, f, b)) : List<&2, Main.Both>}
  %Equal.sym(List<&2, Tree.Entry>, SortL.keyed(~Tree.Entry, ~Tree.entry_file, f, b), Nil{}, z) : {Main.Both{f, Some{x}, None{}} <> Main.both.at(f, q) == Main.both.zip(f, x <> SortL.keyed(~Tree.Entry, ~Tree.entry_file, f, xr), _) : List<&2, Main.Both>}
  Equal.cong(List<&2, Main.Both>, List<&2, Main.Both>, l => Main.Both{f, Some{x}, None{}} <> l, Main.both.at(f, q), Main.both.zip(f, SortL.keyed(~Tree.Entry, ~Tree.entry_file, f, xr), Nil{}),
    Equal.trans(List<&2, Main.Both>, Main.both.at(f, q), Main.both.zip(f, SortL.keyed(~Tree.Entry, ~Tree.entry_file, f, xr), SortL.keyed(~Tree.Entry, ~Tree.entry_file, f, b)), Main.both.zip(f, SortL.keyed(~Tree.Entry, ~Tree.entry_file, f, xr), Nil{}), ih,
      Equal.cong(List<&2, Tree.Entry>, List<&2, Main.Both>, l => Main.both.zip(f, SortL.keyed(~Tree.Entry, ~Tree.entry_file, f, xr), l), SortL.keyed(~Tree.Entry, ~Tree.entry_file, f, b), Nil{}, z)))

# An entry listed with nothing beside it: the other side holds nothing under
# its file.
def left(e: Bool, +f: String, +x: Tree.Entry, +xr: List<&2, Tree.Entry>, +b: List<&2, Tree.Entry>, +q: List<&2, Main.Both>, +ee: {String.eq(Tree.entry_file(x), f) == e : Bool}, kb: {String.eq(Tree.entry_file(x), f) == True{} : Bool} -> {SortL.keyed(~Tree.Entry, ~Tree.entry_file, f, b) == Nil{} : List<&2, Tree.Entry>}, ih: {Main.both.at(f, q) == Main.both.zip(f, SortL.keyed(~Tree.Entry, ~Tree.entry_file, f, xr), SortL.keyed(~Tree.Entry, ~Tree.entry_file, f, b)) : List<&2, Main.Both>}) -> {Bool.pick(List<&2, Main.Both>, e, Main.Both{Tree.entry_file(x), Some{x}, None{}} <> Main.both.at(f, q), Main.both.at(f, q)) == Main.both.zip(f, Bool.pick(List<&2, Tree.Entry>, e, x <> SortL.keyed(~Tree.Entry, ~Tree.entry_file, f, xr), SortL.keyed(~Tree.Entry, ~Tree.entry_file, f, xr)), SortL.keyed(~Tree.Entry, ~Tree.entry_file, f, b)) : List<&2, Main.Both>}:
  match e:
    case False{}:
      ih
    case True{}:
      left_t(f, x, xr, b, q, S.eq_true(Tree.entry_file(x), f, ee), kb(ee), ih)

def right_t(+f: String, +y: Tree.Entry, +yr: List<&2, Tree.Entry>, +a: List<&2, Tree.Entry>, +q: List<&2, Main.Both>, +fy: {Tree.entry_file(y) == f : String}, +z: {SortL.keyed(~Tree.Entry, ~Tree.entry_file, f, a) == Nil{} : List<&2, Tree.Entry>}, ih: {Main.both.at(f, q) == Main.both.zip(f, SortL.keyed(~Tree.Entry, ~Tree.entry_file, f, a), SortL.keyed(~Tree.Entry, ~Tree.entry_file, f, yr)) : List<&2, Main.Both>}) -> {Main.Both{Tree.entry_file(y), None{}, Some{y}} <> Main.both.at(f, q) == Main.both.zip(f, SortL.keyed(~Tree.Entry, ~Tree.entry_file, f, a), y <> SortL.keyed(~Tree.Entry, ~Tree.entry_file, f, yr)) : List<&2, Main.Both>}:
  %Equal.sym(String, Tree.entry_file(y), f, fy) : {Main.Both{_, None{}, Some{y}} <> Main.both.at(f, q) == Main.both.zip(f, SortL.keyed(~Tree.Entry, ~Tree.entry_file, f, a), y <> SortL.keyed(~Tree.Entry, ~Tree.entry_file, f, yr)) : List<&2, Main.Both>}
  %Equal.sym(List<&2, Tree.Entry>, SortL.keyed(~Tree.Entry, ~Tree.entry_file, f, a), Nil{}, z) : {Main.Both{f, None{}, Some{y}} <> Main.both.at(f, q) == Main.both.zip(f, _, y <> SortL.keyed(~Tree.Entry, ~Tree.entry_file, f, yr)) : List<&2, Main.Both>}
  Equal.cong(List<&2, Main.Both>, List<&2, Main.Both>, l => Main.Both{f, None{}, Some{y}} <> l, Main.both.at(f, q), Main.both.zip(f, Nil{}, SortL.keyed(~Tree.Entry, ~Tree.entry_file, f, yr)),
    Equal.trans(List<&2, Main.Both>, Main.both.at(f, q), Main.both.zip(f, SortL.keyed(~Tree.Entry, ~Tree.entry_file, f, a), SortL.keyed(~Tree.Entry, ~Tree.entry_file, f, yr)), Main.both.zip(f, Nil{}, SortL.keyed(~Tree.Entry, ~Tree.entry_file, f, yr)), ih,
      Equal.cong(List<&2, Tree.Entry>, List<&2, Main.Both>, l => Main.both.zip(f, l, SortL.keyed(~Tree.Entry, ~Tree.entry_file, f, yr)), SortL.keyed(~Tree.Entry, ~Tree.entry_file, f, a), Nil{}, z)))

def right(e: Bool, +f: String, +y: Tree.Entry, +yr: List<&2, Tree.Entry>, +a: List<&2, Tree.Entry>, +q: List<&2, Main.Both>, +ee: {String.eq(Tree.entry_file(y), f) == e : Bool}, ka: {String.eq(Tree.entry_file(y), f) == True{} : Bool} -> {SortL.keyed(~Tree.Entry, ~Tree.entry_file, f, a) == Nil{} : List<&2, Tree.Entry>}, ih: {Main.both.at(f, q) == Main.both.zip(f, SortL.keyed(~Tree.Entry, ~Tree.entry_file, f, a), SortL.keyed(~Tree.Entry, ~Tree.entry_file, f, yr)) : List<&2, Main.Both>}) -> {Bool.pick(List<&2, Main.Both>, e, Main.Both{Tree.entry_file(y), None{}, Some{y}} <> Main.both.at(f, q), Main.both.at(f, q)) == Main.both.zip(f, SortL.keyed(~Tree.Entry, ~Tree.entry_file, f, a), Bool.pick(List<&2, Tree.Entry>, e, y <> SortL.keyed(~Tree.Entry, ~Tree.entry_file, f, yr), SortL.keyed(~Tree.Entry, ~Tree.entry_file, f, yr))) : List<&2, Main.Both>}:
  match e:
    case False{}:
      ih
    case True{}:
      right_t(f, y, yr, a, q, S.eq_true(Tree.entry_file(y), f, ee), ka(ee), ih)

# Two entries under one file, paired.
def pair(e: Bool, +f: String, +x: Tree.Entry, +xr: List<&2, Tree.Entry>, +y: Tree.Entry, +yr: List<&2, Tree.Entry>, +q: List<&2, Main.Both>, +ee: {String.eq(Tree.entry_file(x), f) == e : Bool}, ih: {Main.both.at(f, q) == Main.both.zip(f, SortL.keyed(~Tree.Entry, ~Tree.entry_file, f, xr), SortL.keyed(~Tree.Entry, ~Tree.entry_file, f, yr)) : List<&2, Main.Both>}) -> {Bool.pick(List<&2, Main.Both>, e, Main.Both{Tree.entry_file(x), Some{x}, Some{y}} <> Main.both.at(f, q), Main.both.at(f, q)) == Main.both.zip(f, Bool.pick(List<&2, Tree.Entry>, e, x <> SortL.keyed(~Tree.Entry, ~Tree.entry_file, f, xr), SortL.keyed(~Tree.Entry, ~Tree.entry_file, f, xr)), Bool.pick(List<&2, Tree.Entry>, e, y <> SortL.keyed(~Tree.Entry, ~Tree.entry_file, f, yr), SortL.keyed(~Tree.Entry, ~Tree.entry_file, f, yr))) : List<&2, Main.Both>}:
  match e:
    case False{}:
      ih
    case True{}:
      %Equal.sym(String, Tree.entry_file(x), f, S.eq_true(Tree.entry_file(x), f, ee)) : {Main.Both{_, Some{x}, Some{y}} <> Main.both.at(f, q) == Main.both.zip(f, x <> SortL.keyed(~Tree.Entry, ~Tree.entry_file, f, xr), y <> SortL.keyed(~Tree.Entry, ~Tree.entry_file, f, yr)) : List<&2, Main.Both>}
      Equal.cong(List<&2, Main.Both>, List<&2, Main.Both>, l => Main.Both{f, Some{x}, Some{y}} <> l, Main.both.at(f, q), Main.both.zip(f, SortL.keyed(~Tree.Entry, ~Tree.entry_file, f, xr), SortL.keyed(~Tree.Entry, ~Tree.entry_file, f, yr)), ih)

# The walk
# --------

def join(fuel: Nat, a: List<&2, Tree.Entry>, b: List<&2, Tree.Entry>, c: Cmp, +f: String, +ec: {Main.both.cmp(a, b) == c : Cmp}, +ha: {SortL.sorted.from(~Tree.Entry, ~Tree.entry_file, a, SNil{}) == True{} : Bool}, +hb: {SortL.sorted.from(~Tree.Entry, ~Tree.entry_file, b, SNil{}) == True{} : Bool}, hf: {Nat.is_le(1n+Nat.add(List.length(&2, Tree.Entry, a), List.length(&2, Tree.Entry, b)), fuel) == True{} : Bool}) -> {Main.both.at(f, Main.both.go(fuel, a, b, c)) == Main.both.zip(f, SortL.keyed(~Tree.Entry, ~Tree.entry_file, f, a), SortL.keyed(~Tree.Entry, ~Tree.entry_file, f, b)) : List<&2, Main.Both>}:
  match fuel:
    case 0n:
      Empty.absurd({Main.both.at(f, Main.both.go(0n, a, b, c)) == Main.both.zip(f, SortL.keyed(~Tree.Entry, ~Tree.entry_file, f, a), SortL.keyed(~Tree.Entry, ~Tree.entry_file, f, b)) : List<&2, Main.Both>}, S.false_true(hf))
    case 1n++fu:
      match a:
        case Nil{}:
          match b:
            case Nil{}:
              match c:
                case LT{}:
                  {==}
                case EQ{}:
                  {==}
                case GT{}:
                  {==}
            case +y <> +yr:
              match c:
                case LT{}:
                  Empty.absurd({Main.both.at(f, Main.both.go(1n+fu, Nil{}, y <> yr, LT{})) == Main.both.zip(f, SortL.keyed(~Tree.Entry, ~Tree.entry_file, f, Nil{}), SortL.keyed(~Tree.Entry, ~Tree.entry_file, f, y <> yr)) : List<&2, Main.Both>}, SortL.lt_not(GT{}, ec, {==}))
                case EQ{}:
                  Empty.absurd({Main.both.at(f, Main.both.go(1n+fu, Nil{}, y <> yr, EQ{})) == Main.both.zip(f, SortL.keyed(~Tree.Entry, ~Tree.entry_file, f, Nil{}), SortL.keyed(~Tree.Entry, ~Tree.entry_file, f, y <> yr)) : List<&2, Main.Both>}, S.gt_eq(ec))
                case GT{}:
                  right(String.eq(Tree.entry_file(y), f), f, y, yr, Nil{}, Main.both.go(fu, Nil{}, yr, Main.both.cmp(Nil{}, yr)), {==}, h => {==},
                    join(fu, Nil{}, yr, Main.both.cmp(Nil{}, yr), f, {==}, {==}, sorted_tail(y, yr, hb), hf))
        case +x <> +xr:
          match b:
            case Nil{}:
              match c:
                case LT{}:
                  left(String.eq(Tree.entry_file(x), f), f, x, xr, Nil{}, Main.both.go(fu, xr, Nil{}, Main.both.cmp(xr, Nil{})), {==}, h => {==},
                    join(fu, xr, Nil{}, Main.both.cmp(xr, Nil{}), f, {==}, sorted_tail(x, xr, ha), {==}, hf))
                case EQ{}:
                  Empty.absurd({Main.both.at(f, Main.both.go(1n+fu, x <> xr, Nil{}, EQ{})) == Main.both.zip(f, SortL.keyed(~Tree.Entry, ~Tree.entry_file, f, x <> xr), SortL.keyed(~Tree.Entry, ~Tree.entry_file, f, Nil{})) : List<&2, Main.Both>}, S.lt_eq(ec))
                case GT{}:
                  Empty.absurd({Main.both.at(f, Main.both.go(1n+fu, x <> xr, Nil{}, GT{})) == Main.both.zip(f, SortL.keyed(~Tree.Entry, ~Tree.entry_file, f, x <> xr), SortL.keyed(~Tree.Entry, ~Tree.entry_file, f, Nil{})) : List<&2, Main.Both>}, S.true_false(Equal.cong(Cmp, Bool, Cmp.is_lt, LT{}, GT{}, ec)))
            case +y <> +yr:
              match c:
                case EQ{}:
                  %S.order_eq(Tree.entry_file(x), Tree.entry_file(y), ec) : {Main.both.at(f, Main.both.go(1n+fu, x <> xr, y <> yr, EQ{})) == Main.both.zip(f, SortL.keyed(~Tree.Entry, ~Tree.entry_file, f, x <> xr), Bool.pick(List<&2, Tree.Entry>, String.eq(_, f), y <> SortL.keyed(~Tree.Entry, ~Tree.entry_file, f, yr), SortL.keyed(~Tree.Entry, ~Tree.entry_file, f, yr))) : List<&2, Main.Both>}
                  pair(String.eq(Tree.entry_file(x), f), f, x, xr, y, yr, Main.both.go(fu, xr, yr, Main.both.cmp(xr, yr)), {==},
                    join(fu, xr, yr, Main.both.cmp(xr, yr), f, {==}, sorted_tail(x, xr, ha), sorted_tail(y, yr, hb), Comp.le_pred(1n+Nat.add(List.length(&2, Tree.Entry, xr), List.length(&2, Tree.Entry, yr)), fu, Equal.trans(Bool, Nat.is_le(1n+1n+Nat.add(List.length(&2, Tree.Entry, xr), List.length(&2, Tree.Entry, yr)), fu), Nat.is_le(1n+Nat.add(List.length(&2, Tree.Entry, xr), 1n+List.length(&2, Tree.Entry, yr)), fu), True{}, Equal.cong(Nat, Bool, v => Nat.is_le(1n+v, fu), 1n+Nat.add(List.length(&2, Tree.Entry, xr), List.length(&2, Tree.Entry, yr)), Nat.add(List.length(&2, Tree.Entry, xr), 1n+List.length(&2, Tree.Entry, yr)), Equal.sym(Nat, Nat.add(List.length(&2, Tree.Entry, xr), 1n+List.length(&2, Tree.Entry, yr)), 1n+Nat.add(List.length(&2, Tree.Entry, xr), List.length(&2, Tree.Entry, yr)), Pos.add_succ(List.length(&2, Tree.Entry, xr), List.length(&2, Tree.Entry, yr)))), hf))))
                case LT{}:
                  left(String.eq(Tree.entry_file(x), f), f, x, xr, y <> yr, Main.both.go(fu, xr, y <> yr, Main.both.cmp(xr, y <> yr)), {==},
                    h => SortL.keyed_none(~Tree.Entry, ~Tree.entry_file, y <> yr, Tree.entry_file(y), f, Equal.trans(Bool, String.is_le(Tree.entry_file(y), f), String.is_le(Tree.entry_file(y), Tree.entry_file(x)), False{}, Equal.cong(String, Bool, v => String.is_le(Tree.entry_file(y), v), f, Tree.entry_file(x), Equal.sym(String, Tree.entry_file(x), f, S.eq_true(Tree.entry_file(x), f, h))), Equal.cong(Cmp, Bool, Cmp.is_le, String.order(Tree.entry_file(y), Tree.entry_file(x)), GT{}, Equal.trans(Cmp, String.order(Tree.entry_file(y), Tree.entry_file(x)), SortL.cflip(String.order(Tree.entry_file(x), Tree.entry_file(y))), GT{}, SortL.str_flip(Tree.entry_file(x), Tree.entry_file(y)), Equal.cong(Cmp, Cmp, SortL.cflip, String.order(Tree.entry_file(x), Tree.entry_file(y)), LT{}, ec)))), sorted_from_head(y, yr, hb)),
                    join(fu, xr, y <> yr, Main.both.cmp(xr, y <> yr), f, {==}, sorted_tail(x, xr, ha), hb, hf))
                case GT{}:
                  right(String.eq(Tree.entry_file(y), f), f, y, yr, x <> xr, Main.both.go(fu, x <> xr, yr, Main.both.cmp(x <> xr, yr)), {==},
                    h => SortL.keyed_none(~Tree.Entry, ~Tree.entry_file, x <> xr, Tree.entry_file(x), f, Equal.trans(Bool, String.is_le(Tree.entry_file(x), f), String.is_le(Tree.entry_file(x), Tree.entry_file(y)), False{}, Equal.cong(String, Bool, v => String.is_le(Tree.entry_file(x), v), f, Tree.entry_file(y), Equal.sym(String, Tree.entry_file(y), f, S.eq_true(Tree.entry_file(y), f, h))), Equal.cong(Cmp, Bool, Cmp.is_le, String.order(Tree.entry_file(x), Tree.entry_file(y)), GT{}, ec)), sorted_from_head(x, xr, ha)),
                    join(fu, x <> xr, yr, Main.both.cmp(x <> xr, yr), f, {==}, ha, sorted_tail(y, yr, hb), Equal.trans(Bool, Nat.is_le(1n+1n+Nat.add(List.length(&2, Tree.Entry, xr), List.length(&2, Tree.Entry, yr)), fu), Nat.is_le(1n+Nat.add(List.length(&2, Tree.Entry, xr), 1n+List.length(&2, Tree.Entry, yr)), fu), True{}, Equal.cong(Nat, Bool, v => Nat.is_le(1n+v, fu), 1n+Nat.add(List.length(&2, Tree.Entry, xr), List.length(&2, Tree.Entry, yr)), Nat.add(List.length(&2, Tree.Entry, xr), 1n+List.length(&2, Tree.Entry, yr)), Equal.sym(Nat, Nat.add(List.length(&2, Tree.Entry, xr), 1n+List.length(&2, Tree.Entry, yr)), 1n+Nat.add(List.length(&2, Tree.Entry, xr), List.length(&2, Tree.Entry, yr)), Pos.add_succ(List.length(&2, Tree.Entry, xr), List.length(&2, Tree.Entry, yr)))), hf)))

# `both` pairs, under each file, the entries each side holds under it.
def pairs_by_file(+xs: List<&2, Tree.Entry>, +ys: List<&2, Tree.Entry>, +f: String) -> {Main.both.at(f, Main.both(xs, ys)) == Main.both.zip(f, Main.entries.at(f, xs), Main.entries.at(f, ys)) : List<&2, Main.Both>}:
  %Equal.sym(List<&2, Tree.Entry>, Main.entries.at(f, xs), SortL.keyed(~Tree.Entry, ~Tree.entry_file, f, xs), kd_at(f, xs)) : {Main.both.at(f, Main.both(xs, ys)) == Main.both.zip(f, _, Main.entries.at(f, ys)) : List<&2, Main.Both>}
  %Equal.sym(List<&2, Tree.Entry>, Main.entries.at(f, ys), SortL.keyed(~Tree.Entry, ~Tree.entry_file, f, ys), kd_at(f, ys)) : {Main.both.at(f, Main.both(xs, ys)) == Main.both.zip(f, SortL.keyed(~Tree.Entry, ~Tree.entry_file, f, xs), _) : List<&2, Main.Both>}
  %SortL.sort_keyed(~Tree.Entry, ~Tree.entry_file, xs, f) : {Main.both.at(f, Main.both(xs, ys)) == Main.both.zip(f, _, SortL.keyed(~Tree.Entry, ~Tree.entry_file, f, ys)) : List<&2, Main.Both>}
  %SortL.sort_keyed(~Tree.Entry, ~Tree.entry_file, ys, f) : {Main.both.at(f, Main.both(xs, ys)) == Main.both.zip(f, SortL.keyed(~Tree.Entry, ~Tree.entry_file, f, List.sort(~Tree.Entry, ~(a => b => String.is_le(Tree.entry_file(a), Tree.entry_file(b))), xs)), _) : List<&2, Main.Both>}
  join(1n+Nat.add(List.length(&2, Tree.Entry, List.sort(~Tree.Entry, ~(a => b => String.is_le(Tree.entry_file(a), Tree.entry_file(b))), xs)), List.length(&2, Tree.Entry, List.sort(~Tree.Entry, ~(a => b => String.is_le(Tree.entry_file(a), Tree.entry_file(b))), ys))), List.sort(~Tree.Entry, ~(a => b => String.is_le(Tree.entry_file(a), Tree.entry_file(b))), xs), List.sort(~Tree.Entry, ~(a => b => String.is_le(Tree.entry_file(a), Tree.entry_file(b))), ys), Main.both.cmp(List.sort(~Tree.Entry, ~(a => b => String.is_le(Tree.entry_file(a), Tree.entry_file(b))), xs), List.sort(~Tree.Entry, ~(a => b => String.is_le(Tree.entry_file(a), Tree.entry_file(b))), ys)), f, {==},
    SortL.sort_sorted(~Tree.Entry, ~Tree.entry_file, xs), SortL.sort_sorted(~Tree.Entry, ~Tree.entry_file, ys), Comp.le_refl(1n+Nat.add(List.length(&2, Tree.Entry, List.sort(~Tree.Entry, ~(a => b => String.is_le(Tree.entry_file(a), Tree.entry_file(b))), xs)), List.length(&2, Tree.Entry, List.sort(~Tree.Entry, ~(a => b => String.is_le(Tree.entry_file(a), Tree.entry_file(b))), ys)))))
