# The decimal spelling of a number is the digits it was read from:
# `T.spell(n) == s` whenever `T.number(s) == Some{n}`. Counting up in digit
# lists (`T.dsucc`) is what connects the reader's value to the writer's
# digits, and the digit table connects characters to digits.
import Base
import ./text.bend as T
import ./composition_lemmas.bend as Comp
import ./equality_lemmas.bend as Eq

def ndisc(m: Maybe<&2, Nat>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      Empty

def none_some(-x: Nat, e: {None{} == Some{x} : Maybe<&2, Nat>}) -> Empty:
  %e : {ndisc(_) : Type}
  Unit{}

def maybe_nat(m: Maybe<&2, Nat>) -> Nat:
  match m:
    case None{}:
      0n
    case Some{x}:
      x

def some_inj(-x: Nat, -y: Nat, e: {Some{x} == Some{y} : Maybe<&2, Nat>}) -> {x == y : Nat}:
  Equal.cong(Maybe<&2, Nat>, Nat, maybe_nat, Some{x}, Some{y}, e)

def lt_of_le_succ(a: Nat, b: Nat, e: {Nat.is_le(1n+a, b) == True{} : Bool}) -> {Nat.is_lt(a, b) == True{} : Bool}:
  match a b:
    case 0n 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, Comp.false_true(e))
    case 0n 1n+bp:
      {==}
    case 1n+ap 0n:
      Empty.absurd({Nat.is_lt(1n+ap, 0n) == True{} : Bool}, Comp.false_true(e))
    case 1n+ap 1n+bp:
      lt_of_le_succ(ap, bp, e)

# The digit table
# ---------------

def go_le.fin(+c: Char, +k: Nat, +d: Nat, ch: Char, rest: List<&2, Char>, same: Bool, e: {Bool.pick(Maybe<&2, Nat>, same, Some{k}, T.digit_of.go(rest, c, 1n+k)) == Some{d} : Maybe<&2, Nat>}, ih: {T.digit_of.go(rest, c, 1n+k) == Some{d} : Maybe<&2, Nat>} -> {Nat.is_le(1n+k, d) == True{} : Bool}) -> {Nat.is_le(k, d) == True{} : Bool}:
  match same:
    case True{}:
      %some_inj(k, d, e) : {Nat.is_le(k, _) == True{} : Bool}
      Comp.le_refl(k)
    case False{}:
      Comp.le_pred(k, d, ih(e))

def go_le(table: List<&2, Char>, +c: Char, +k: Nat, +d: Nat, e: {T.digit_of.go(table, c, k) == Some{d} : Maybe<&2, Nat>}) -> {Nat.is_le(k, d) == True{} : Bool}:
  match table:
    case Nil{}:
      Empty.absurd({Nat.is_le(k, d) == True{} : Bool}, none_some(d, e))
    case +ch <> +rest:
      go_le.fin(c, k, d, ch, rest, Char.is_eq(c, ch), e, x => go_le(rest, c, 1n+k, d, x))

def go_char.fin(+c: Char, +k: Nat, +d: Nat, +ch: Char, +rest: List<&2, Char>, same: Bool, +eq: {Char.is_eq(c, ch) == same : Bool}, +e: {Bool.pick(Maybe<&2, Nat>, same, Some{k}, T.digit_of.go(rest, c, 1n+k)) == Some{d} : Maybe<&2, Nat>}, ih: {T.digit_of.go(rest, c, 1n+k) == Some{d} : Maybe<&2, Nat>} -> {T.char_of.go(rest, 1n+k, d) == c : Char}) -> {Bool.pick(Char, Nat.is_eq(k, d), ch, T.char_of.go(rest, 1n+k, d)) == c : Char}:
  match same:
    case True{}:
      %some_inj(k, d, e) : {Bool.pick(Char, Nat.is_eq(k, _), ch, T.char_of.go(rest, 1n+k, _)) == c : Char}
      %Equal.sym(Bool, Nat.is_eq(k, k), True{}, Comp.eq_refl(k)) : {Bool.pick(Char, _, ch, T.char_of.go(rest, 1n+k, k)) == c : Char}
      %Eq.char_eq(c, ch, eq) : {_ == c : Char}
      {==}
    case False{}:
      %Equal.sym(Bool, Nat.is_eq(k, d), False{}, Comp.lt_not_eq(k, d, lt_of_le_succ(k, d, go_le(rest, c, 1n+k, d, e)))) : {Bool.pick(Char, _, ch, T.char_of.go(rest, 1n+k, d)) == c : Char}
      ih(e)

def go_char(table: List<&2, Char>, +c: Char, +k: Nat, +d: Nat, e: {T.digit_of.go(table, c, k) == Some{d} : Maybe<&2, Nat>}) -> {T.char_of.go(table, k, d) == c : Char}:
  match table:
    case Nil{}:
      Empty.absurd({'?' == c : Char}, none_some(d, e))
    case +ch <> +rest:
      go_char.fin(c, k, d, ch, rest, Char.is_eq(c, ch), {==}, e, x => go_char(rest, c, 1n+k, d, x))

# A character read as a digit is that digit's character.
def digit_char(+c: Char, +d: Nat, e: {T.digit_of(c) == Some{d} : Maybe<&2, Nat>}) -> {T.char_of(d) == c : Char}:
  go_char(T.digits_table(), c, 0n, d, e)

def ldisc(m: Maybe<&2, List<&2, Nat>>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      Empty

def none_some_list(-x: List<&2, Nat>, e: {None{} == Some{x} : Maybe<&2, List<&2, Nat>>}) -> Empty:
  %e : {ldisc(_) : Type}
  Unit{}

def maybe_list(m: Maybe<&2, List<&2, Nat>>) -> List<&2, Nat>:
  match m:
    case None{}:
      Nil{}
    case Some{x}:
      x

def chars_of.push(+c: Char, +t: String, dm: Maybe<&2, Nat>, tm: Maybe<&2, List<&2, Nat>>, +ds: List<&2, Nat>, ed: {T.digit_of(c) == dm : Maybe<&2, Nat>}, et: {T.to_digits(t) == tm : Maybe<&2, List<&2, Nat>>}, e: {T.to_digits.push(dm, tm) == Some{ds} : Maybe<&2, List<&2, Nat>>}, ih: @+xs: List<&2, Nat> -> {T.to_digits(t) == Some{xs} : Maybe<&2, List<&2, Nat>>} -> {T.chars(xs) == t : String}) -> {T.chars(ds) == SCon{c, t} : String}:
  match dm tm:
    case Some{+x} Some{+xs}:
      %Equal.cong(Maybe<&2, List<&2, Nat>>, List<&2, Nat>, maybe_list, Some{x <> xs}, Some{ds}, e) : {T.chars(_) == SCon{c, t} : String}
      %Equal.sym(Char, T.char_of(x), c, digit_char(c, x, ed)) : {SCon{_, T.chars(xs)} == SCon{c, t} : String}
      %Equal.sym(String, T.chars(xs), t, ih(xs, et)) : {SCon{c, _} == SCon{c, t} : String}
      {==}
    case None{} Some{xs}:
      Empty.absurd({T.chars(ds) == SCon{c, t} : String}, none_some_list(ds, e))
    case Some{x} None{}:
      Empty.absurd({T.chars(ds) == SCon{c, t} : String}, none_some_list(ds, e))
    case None{} None{}:
      Empty.absurd({T.chars(ds) == SCon{c, t} : String}, none_some_list(ds, e))

# Digits read off a string spell it back.
def chars_of(rs: String, +ds: List<&2, Nat>, e: {T.to_digits(rs) == Some{ds} : Maybe<&2, List<&2, Nat>>}) -> {T.chars(ds) == rs : String}:
  match rs:
    case SNil{}:
      %Equal.cong(Maybe<&2, List<&2, Nat>>, List<&2, Nat>, maybe_list, Some{Nil{}}, Some{ds}, e) : {T.chars(_) == SNil{} : String}
      {==}
    case SCon{+c, +t}:
      chars_of.push(c, t, T.digit_of(c), T.to_digits(t), ds, {==}, {==}, e, xs => h => chars_of(t, xs, h))

# Multiplying with an accumulator multiplies the same.
def mul10_shift(n: Nat, acc: Nat) -> {T.mul10.go(n, 1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+acc) == 1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+T.mul10.go(n, acc) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      mul10_shift(p, 1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+acc)

def mul10_spec(n: Nat) -> {T.mul10(n) == T.mul10.spec(n) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n++p:
      %Equal.sym(Nat, T.mul10.go(p, 1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+0n), 1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+T.mul10.go(p, 0n), mul10_shift(p, 0n)) : {_ == 1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+T.mul10.spec(p) : Nat}
      %Equal.sym(Nat, T.mul10.go(p, 0n), T.mul10.spec(p), mul10_spec(p)) : {1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+_ == 1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+T.mul10.spec(p) : Nat}
      {==}

# Counting with an accumulator counts the same.
def digits_shift(n: Nat, acc: List<&2, Nat>) -> {T.digits.go(n, T.dsucc(acc)) == T.dsucc(T.digits.go(n, acc)) : List<&2, Nat>}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      digits_shift(p, T.dsucc(acc))

def digits_spec(n: Nat) -> {T.digits(n) == T.digits.spec(n) : List<&2, Nat>}:
  match n:
    case 0n:
      {==}
    case 1n++p:
      %Equal.sym(List<&2, Nat>, T.digits.go(p, T.dsucc([0n])), T.dsucc(T.digits.go(p, [0n])), digits_shift(p, [0n])) : {_ == T.dsucc(T.digits.spec(p)) : List<&2, Nat>}
      %Equal.sym(List<&2, Nat>, T.digits.go(p, [0n]), T.digits.spec(p), digits_spec(p)) : {T.dsucc(_) == T.dsucc(T.digits.spec(p)) : List<&2, Nat>}
      {==}

# Counting
# --------

# A digit below ten added to a number whose digits start with zero puts
# that digit in front: `dsucc` cycles the low digit without a carry.
def small_digit(d: Nat, -x: Nat, -tail: List<&2, Nat>, lt: {Nat.is_lt(d, 10n) == True{} : Bool}, hx: {T.digits.spec(x) == 0n <> tail : List<&2, Nat>}) -> {T.digits.spec(Nat.add(d, x)) == d <> tail : List<&2, Nat>}:
  match d:
    case 0n:
      %Equal.sym(List<&2, Nat>, T.digits.spec(x), 0n <> tail, hx) : {_ == (0n) <> tail : List<&2, Nat>}
      {==}
    case 1n+d1:
      match d1:
        case 0n:
          %Equal.sym(List<&2, Nat>, T.digits.spec(x), 0n <> tail, hx) : {T.dsucc(_) == (1n+0n) <> tail : List<&2, Nat>}
          {==}
        case 1n+d2:
          match d2:
            case 0n:
              %Equal.sym(List<&2, Nat>, T.digits.spec(x), 0n <> tail, hx) : {T.dsucc(T.dsucc(_)) == (1n+1n+0n) <> tail : List<&2, Nat>}
              {==}
            case 1n+d3:
              match d3:
                case 0n:
                  %Equal.sym(List<&2, Nat>, T.digits.spec(x), 0n <> tail, hx) : {T.dsucc(T.dsucc(T.dsucc(_))) == (1n+1n+1n+0n) <> tail : List<&2, Nat>}
                  {==}
                case 1n+d4:
                  match d4:
                    case 0n:
                      %Equal.sym(List<&2, Nat>, T.digits.spec(x), 0n <> tail, hx) : {T.dsucc(T.dsucc(T.dsucc(T.dsucc(_)))) == (1n+1n+1n+1n+0n) <> tail : List<&2, Nat>}
                      {==}
                    case 1n+d5:
                      match d5:
                        case 0n:
                          %Equal.sym(List<&2, Nat>, T.digits.spec(x), 0n <> tail, hx) : {T.dsucc(T.dsucc(T.dsucc(T.dsucc(T.dsucc(_))))) == (1n+1n+1n+1n+1n+0n) <> tail : List<&2, Nat>}
                          {==}
                        case 1n+d6:
                          match d6:
                            case 0n:
                              %Equal.sym(List<&2, Nat>, T.digits.spec(x), 0n <> tail, hx) : {T.dsucc(T.dsucc(T.dsucc(T.dsucc(T.dsucc(T.dsucc(_)))))) == (1n+1n+1n+1n+1n+1n+0n) <> tail : List<&2, Nat>}
                              {==}
                            case 1n+d7:
                              match d7:
                                case 0n:
                                  %Equal.sym(List<&2, Nat>, T.digits.spec(x), 0n <> tail, hx) : {T.dsucc(T.dsucc(T.dsucc(T.dsucc(T.dsucc(T.dsucc(T.dsucc(_))))))) == (1n+1n+1n+1n+1n+1n+1n+0n) <> tail : List<&2, Nat>}
                                  {==}
                                case 1n+d8:
                                  match d8:
                                    case 0n:
                                      %Equal.sym(List<&2, Nat>, T.digits.spec(x), 0n <> tail, hx) : {T.dsucc(T.dsucc(T.dsucc(T.dsucc(T.dsucc(T.dsucc(T.dsucc(T.dsucc(_)))))))) == (1n+1n+1n+1n+1n+1n+1n+1n+0n) <> tail : List<&2, Nat>}
                                      {==}
                                    case 1n+d9:
                                      match d9:
                                        case 0n:
                                          %Equal.sym(List<&2, Nat>, T.digits.spec(x), 0n <> tail, hx) : {T.dsucc(T.dsucc(T.dsucc(T.dsucc(T.dsucc(T.dsucc(T.dsucc(T.dsucc(T.dsucc(_))))))))) == (1n+1n+1n+1n+1n+1n+1n+1n+1n+0n) <> tail : List<&2, Nat>}
                                          {==}
                                        case 1n+d10:
                                          match d10:
                                            case 0n:
                                              Empty.absurd({T.digits.spec(Nat.add(1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+0n, x)) == (1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+0n) <> tail : List<&2, Nat>}, Comp.false_true(lt))
                                            case 1n+d11:
                                              Empty.absurd({T.digits.spec(Nat.add(1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+d11, x)) == (1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+d11) <> tail : List<&2, Nat>}, Comp.false_true(lt))

# Ten times a positive number: a zero in front of its digits.
def digits_mul10(p: Nat) -> {T.digits.spec(T.mul10.spec(1n+p)) == 0n <> T.digits.spec(1n+p) : List<&2, Nat>}:
  match p:
    case 0n:
      {==}
    case 1n+q:
      %Equal.sym(List<&2, Nat>, T.digits.spec(T.mul10.spec(1n+q)), 0n <> T.digits.spec(1n+q), digits_mul10(q)) : {T.dsucc(T.dsucc(T.dsucc(T.dsucc(T.dsucc(T.dsucc(T.dsucc(T.dsucc(T.dsucc(T.dsucc(_)))))))))) == 0n <> T.digits.spec(1n+1n+q) : List<&2, Nat>}
      {==}

def pos_add(d: Nat, -x: Nat) -> {Nat.is_lt(0n, Nat.add(d, 1n+x)) == True{} : Bool}:
  match d:
    case 0n:
      {==}
    case 1n+p:
      {==}

def pos_add_zero(d: Nat, pos: {Nat.is_lt(0n, d) == True{} : Bool}) -> {Nat.is_lt(0n, Nat.add(d, 0n)) == True{} : Bool}:
  match d:
    case 0n:
      pos
    case 1n+p:
      {==}

def pos_step(d: Nat, v: Nat, pos: {Nat.is_lt(0n, v) == True{} : Bool}) -> {Nat.is_lt(0n, Nat.add(d, T.mul10(v))) == True{} : Bool}:
  match v:
    case 0n:
      Empty.absurd({Nat.is_lt(0n, Nat.add(d, T.mul10(0n))) == True{} : Bool}, Comp.false_true(pos))
    case 1n++q:
      %Equal.sym(Nat, T.mul10(1n+q), T.mul10.spec(1n+q), mul10_spec(1n+q)) : {Nat.is_lt(0n, Nat.add(d, _)) == True{} : Bool}
      pos_add(d, 1n+1n+1n+1n+1n+1n+1n+1n+1n+T.mul10.spec(q))

# A normalized tail has a nonzero value: its last digit is not zero.
def pos_value(ds: List<&2, Nat>, +nt: {T.normalized.tail(ds) == True{} : Bool}) -> {Nat.is_lt(0n, T.value(ds)) == True{} : Bool}:
  match ds:
    case Nil{}:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, Comp.false_true(nt))
    case +d <> Nil{}:
      pos_add_zero(d, Comp.and_right(Nat.is_lt(d, 10n), Nat.is_lt(0n, d), nt))
    case +d <> +e <> +more:
      pos_step(d, T.value(e <> more), pos_value(e <> more, Comp.and_right(Nat.is_lt(d, 10n), T.normalized.tail(e <> more), nt)))

def digits_step.v(+d: Nat, +tail: List<&2, Nat>, v: Nat, ev: {T.value(tail) == v : Nat}, lt: {Nat.is_lt(d, 10n) == True{} : Bool}, ih: {T.digits.spec(v) == tail : List<&2, Nat>}, pos: {Nat.is_lt(0n, v) == True{} : Bool}) -> {T.digits.spec(Nat.add(d, T.mul10(v))) == d <> tail : List<&2, Nat>}:
  match v:
    case 0n:
      Empty.absurd({T.digits.spec(Nat.add(d, T.mul10(0n))) == d <> tail : List<&2, Nat>}, Comp.false_true(pos))
    case 1n++q:
      %ih : {T.digits.spec(Nat.add(d, T.mul10(1n+q))) == d <> _ : List<&2, Nat>}
      %Equal.sym(Nat, T.mul10(1n+q), T.mul10.spec(1n+q), mul10_spec(1n+q)) : {T.digits.spec(Nat.add(d, _)) == d <> T.digits.spec(1n+q) : List<&2, Nat>}
      small_digit(d, T.mul10.spec(1n+q), T.digits.spec(1n+q), lt, digits_mul10(q))

# One more digit in front of a normalized tail.
def digits_step(+d: Nat, +tail: List<&2, Nat>, lt: {Nat.is_lt(d, 10n) == True{} : Bool}, ih: {T.digits.spec(T.value(tail)) == tail : List<&2, Nat>}, pos: {Nat.is_lt(0n, T.value(tail)) == True{} : Bool}) -> {T.digits.spec(Nat.add(d, T.mul10(T.value(tail)))) == d <> tail : List<&2, Nat>}:
  digits_step.v(d, tail, T.value(tail), {==}, lt, ih, pos)

def digits_one(d: Nat, lt: {Nat.is_lt(d, 10n) == True{} : Bool}) -> {T.digits.spec(Nat.add(d, 0n)) == [d] : List<&2, Nat>}:
  small_digit(d, 0n, Nil{}, lt, {==})

def digits_value.tail(ds: List<&2, Nat>, +nt: {T.normalized.tail(ds) == True{} : Bool}) -> {T.digits.spec(T.value(ds)) == ds : List<&2, Nat>}:
  match ds:
    case Nil{}:
      Empty.absurd({T.digits.spec(0n) == Nil{} : List<&2, Nat>}, Comp.false_true(nt))
    case +d <> Nil{}:
      digits_one(d, Comp.and_left(Nat.is_lt(d, 10n), Nat.is_lt(0n, d), nt))
    case +d <> +e <> +more:
      +rest = Comp.and_right(Nat.is_lt(d, 10n), T.normalized.tail(e <> more), nt)
      digits_step(d, e <> more, Comp.and_left(Nat.is_lt(d, 10n), T.normalized.tail(e <> more), nt), digits_value.tail(e <> more, rest), pos_value(e <> more, rest))

# The digits of a normalized list's value are that list.
def digits_value(ds: List<&2, Nat>, +norm: {T.normalized(ds) == True{} : Bool}) -> {T.digits.spec(T.value(ds)) == ds : List<&2, Nat>}:
  match ds:
    case Nil{}:
      Empty.absurd({T.digits.spec(0n) == Nil{} : List<&2, Nat>}, Comp.false_true(norm))
    case +d <> Nil{}:
      digits_one(d, norm)
    case +d <> +e <> +more:
      +rest = Comp.and_right(Nat.is_lt(d, 10n), T.normalized.tail(e <> more), norm)
      digits_step(d, e <> more, Comp.and_left(Nat.is_lt(d, 10n), T.normalized.tail(e <> more), norm), digits_value.tail(e <> more, rest), pos_value(e <> more, rest))

# Reversal
# --------

def rev_twice(xs: String, acc: String, -tail: String) -> {String.reverse.go(String.reverse.go(xs, acc), tail) == String.reverse.go(acc, xs ++ tail) : String}:
  match xs:
    case SNil{}:
      {==}
    case SCon{h, t}:
      rev_twice(t, SCon{h, acc}, tail)

def rev_rev(+s: String) -> {String.reverse(String.reverse(s)) == s : String}:
  %Eq.app_nil(s) : {String.reverse(String.reverse(s)) == _ : String}
  rev_twice(s, SNil{}, SNil{})

# The theorem
# -----------

def spell_number.norm(+s: String, +n: Nat, +xs: List<&2, Nat>, norm: Bool, +eq: {T.normalized(xs) == norm : Bool}, +em: {T.to_digits(String.reverse(s)) == Some{xs} : Maybe<&2, List<&2, Nat>>}, e: {Bool.pick(Maybe<&2, Nat>, norm, Some{T.value(xs)}, None{}) == Some{n} : Maybe<&2, Nat>}) -> {T.spell(n) == s : String}:
  match norm:
    case False{}:
      Empty.absurd({T.spell(n) == s : String}, none_some(n, e))
    case True{}:
      %Equal.sym(List<&2, Nat>, T.digits(n), T.digits.spec(n), digits_spec(n)) : {String.reverse(T.chars(_)) == s : String}
      %some_inj(T.value(xs), n, e) : {String.reverse(T.chars(T.digits.spec(_))) == s : String}
      %Equal.sym(List<&2, Nat>, T.digits.spec(T.value(xs)), xs, digits_value(xs, eq)) : {String.reverse(T.chars(_)) == s : String}
      %Equal.sym(String, T.chars(xs), String.reverse(s), chars_of(String.reverse(s), xs, em)) : {String.reverse(_) == s : String}
      rev_rev(s)

def spell_number.of(+s: String, +n: Nat, m: Maybe<&2, List<&2, Nat>>, +em: {T.to_digits(String.reverse(s)) == m : Maybe<&2, List<&2, Nat>>}, e: {T.number.of(m) == Some{n} : Maybe<&2, Nat>}) -> {T.spell(n) == s : String}:
  match m:
    case None{}:
      Empty.absurd({T.spell(n) == s : String}, none_some(n, e))
    case Some{+xs}:
      spell_number.norm(s, n, xs, T.normalized(xs), {==}, em, e)

# A number is spelled as it was read.
def spell_number(+s: String, +n: Nat, e: {T.number(s) == Some{n} : Maybe<&2, Nat>}) -> {T.spell(n) == s : String}:
  spell_number.of(s, n, T.to_digits(String.reverse(s)), {==}, e)

def main() -> Unit:
  Unit{}
