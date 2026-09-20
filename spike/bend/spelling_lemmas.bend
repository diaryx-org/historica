# The writer spells what the parser read: `Ops.write(doc) == s` whenever
# `Ops.parse(s) == Done{doc}`.
import Base
import ./ops.bend as Ops
import ./text.bend as T
import ./replay_lemmas.bend as L
import ./composition_lemmas.bend as Comp
import ./parser_lemmas.bend as Parse
import ./equality_lemmas.bend as Eq
import ./decimal_lemmas.bend as Dec

# String algebra
# --------------

def app_nil(s: String) -> {s ++ SNil{} == s : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{h, t}:
      %Equal.sym(String, t ++ SNil{}, t, app_nil(t)) : {SCon{h, _} == SCon{h, t} : String}
      {==}

def app_assoc(a: String, -b: String, -c: String) -> {(a ++ b) ++ c == a ++ (b ++ c) : String}:
  match a:
    case SNil{}:
      {==}
    case SCon{h, t}:
      %Equal.sym(String, (t ++ b) ++ c, t ++ (b ++ c), app_assoc(t, b, c)) : {SCon{h, _} == SCon{h, t ++ (b ++ c)} : String}
      {==}

def rev_extend(xs: String, acc: String, -tail: String) -> {String.reverse.go(xs, acc ++ tail) == String.reverse.go(xs, acc) ++ tail : String}:
  match xs:
    case SNil{}:
      {==}
    case SCon{h, t}:
      rev_extend(t, SCon{h, acc}, tail)

# Reading a reversed accumulator followed by the rest of the input.
def rev_go(acc: String, -s: String) -> {String.reverse.go(acc, s) == String.reverse(acc) ++ s : String}:
  rev_extend(acc, SNil{}, s)

# Lines and back
# --------------

def unlines(ls: List<&2, T.Line>) -> String:
  match ls:
    case Nil{}:
      SNil{}
    case T.Line{t, term} <> rest:
      t ++ (Bool.pick(String, term, "\n", SNil{}) ++ unlines(rest))

def joined(parts: List<&2, String>) -> String:
  match parts:
    case Nil{}:
      SNil{}
    case p <> Nil{}:
      p
    case p <> q <> more:
      p ++ ("\n" ++ joined(q <> more))

def nonempty(-A: Data, xs: List<&2, A>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case h <> t:
      True{}

def split_nonempty.fin(c: Char, cut: Bool, r: List<&2, String>, -ne: {nonempty(String, r) == True{} : Bool}) -> {nonempty(String, String.split.fin(c, r, cut)) == True{} : Bool}:
  match cut:
    case True{}:
      {==}
    case False{}:
      match r:
        case Nil{}:
          {==}
        case h <> t:
          {==}

def split_nonempty(s: String, +sep: Char) -> {nonempty(String, String.split(s, sep)) == True{} : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      split_nonempty.fin(h, Char.is_eq(h, sep), String.split(t, sep), split_nonempty(t, sep))

def joined_cons(p: String, r: List<&2, String>, ne: {nonempty(String, r) == True{} : Bool}) -> {joined(p <> r) == p ++ ("\n" ++ joined(r)) : String}:
  match r:
    case Nil{}:
      Empty.absurd({joined([p]) == p ++ ("\n" ++ joined(Nil{})) : String}, Comp.false_true(ne))
    case q <> more:
      {==}

def joined_push(c: Char, r: List<&2, String>, ne: {nonempty(String, r) == True{} : Bool}) -> {joined(String.split.push(c, r)) == SCon{c, joined(r)} : String}:
  match r:
    case Nil{}:
      Empty.absurd({joined(String.split.push(c, Nil{})) == SCon{c, joined(Nil{})} : String}, Comp.false_true(ne))
    case p <> Nil{}:
      {==}
    case p <> q <> more:
      {==}

def joined_split.fin(h: Char, +t: String, cut: Bool, eq: {Char.is_eq(h, '\n') == cut : Bool}, ih: {joined(String.split(t, '\n')) == t : String}) -> {joined(String.split.fin(h, String.split(t, '\n'), cut)) == SCon{h, t} : String}:
  match cut:
    case True{}:
      %Equal.sym(String, joined(SNil{} <> String.split(t, '\n')), SNil{} ++ ("\n" ++ joined(String.split(t, '\n'))), joined_cons(SNil{}, String.split(t, '\n'), split_nonempty(t, '\n'))) : {_ == SCon{h, t} : String}
      %Equal.sym(String, joined(String.split(t, '\n')), t, ih) : {SCon{'\n', _} == SCon{h, t} : String}
      %Eq.char_eq(h, '\n', eq) : {SCon{_, t} == SCon{h, t} : String}
      {==}
    case False{}:
      %Equal.sym(String, joined(String.split.push(h, String.split(t, '\n'))), SCon{h, joined(String.split(t, '\n'))}, joined_push(h, String.split(t, '\n'), split_nonempty(t, '\n'))) : {_ == SCon{h, t} : String}
      %Equal.sym(String, joined(String.split(t, '\n')), t, ih) : {SCon{h, _} == SCon{h, t} : String}
      {==}

def joined_split(s: String) -> {joined(String.split(s, '\n')) == s : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      joined_split.fin(h, t, Char.is_eq(h, '\n'), {==}, joined_split(t))

def unlines_last(last: String) -> {unlines(T.lines.go([last])) == last : String}:
  match last:
    case SNil{}:
      {==}
    case SCon{h, t}:
      %Equal.sym(String, t ++ SNil{}, t, app_nil(t)) : {SCon{h, _} == SCon{h, t} : String}
      {==}

def unlines_go(parts: List<&2, String>, ne: {nonempty(String, parts) == True{} : Bool}) -> {unlines(T.lines.go(parts)) == joined(parts) : String}:
  match parts:
    case Nil{}:
      Empty.absurd({unlines(T.lines.go(Nil{})) == joined(Nil{}) : String}, Comp.false_true(ne))
    case last <> Nil{}:
      unlines_last(last)
    case p <> q <> more:
      %Equal.sym(String, unlines(T.lines.go(q <> more)), joined(q <> more), unlines_go(q <> more, {==})) : {p ++ ("\n" ++ _) == p ++ ("\n" ++ joined(q <> more)) : String}
      {==}

# Every string is its lines, written back.
def unlines_lines(+s: String) -> {unlines(T.lines(s)) == s : String}:
  %joined_split(s) : {unlines(T.lines(s)) == _ : String}
  unlines_go(String.split(s, '\n'), split_nonempty(s, '\n'))

# Items
# -----

def strip_eq.fin(x: Char, +xt: String, y: Char, +yt: String, +r: String, same: Bool, eq: {Char.is_eq(x, y) == same : Bool}, e: {Bool.pick(Maybe<&2, String>, same, T.strip_prefix(xt, yt), None{}) == Some{r} : Maybe<&2, String>}, ih: {T.strip_prefix(xt, yt) == Some{r} : Maybe<&2, String>} -> {xt == yt ++ r : String}) -> {SCon{x, xt} == SCon{y, yt} ++ r : String}:
  match same:
    case False{}:
      Empty.absurd({SCon{x, xt} == SCon{y, yt} ++ r : String}, Parse.some_none(r, Equal.sym(Maybe<&2, String>, None{}, Some{r}, e)))
    case True{}:
      %Equal.sym(Char, x, y, Eq.char_eq(x, y, eq)) : {SCon{_, xt} == SCon{y, yt} ++ r : String}
      %Equal.sym(String, xt, yt ++ r, ih(e)) : {SCon{y, _} == SCon{y, yt} ++ r : String}
      {==}

def maybe_str(m: Maybe<&2, String>) -> String:
  match m:
    case None{}:
      SNil{}
    case Some{x}:
      x

# A prefix stripped is a prefix that was there.
def strip_eq(s: String, p: String, +r: String, e: {T.strip_prefix(s, p) == Some{r} : Maybe<&2, String>}) -> {s == p ++ r : String}:
  match s p:
    case SNil{} SNil{}:
      Equal.cong(Maybe<&2, String>, String, maybe_str, Some{SNil{}}, Some{r}, e)
    case SCon{x, xt} SNil{}:
      Equal.cong(Maybe<&2, String>, String, maybe_str, Some{SCon{x, xt}}, Some{r}, e)
    case SNil{} SCon{y, yt}:
      Empty.absurd({SNil{} == SCon{y, yt} ++ r : String}, Parse.some_none(r, Equal.sym(Maybe<&2, String>, None{}, Some{r}, e)))
    case SCon{+x, +xt} SCon{+y, +yt}:
      strip_eq.fin(x, xt, y, yt, r, Char.is_eq(x, y), {==}, e, h => strip_eq(xt, yt, r, h))

def body_disc(r: Ops.Read) -> Type:
  match r:
    case Ops.Body{text}:
      Empty
    case Ops.NoNewline{}:
      Unit
    case Ops.Forgotten{}:
      Unit
    case Ops.Other{}:
      Unit

def nonl_disc(r: Ops.Read) -> Type:
  match r:
    case Ops.Body{text}:
      Unit
    case Ops.NoNewline{}:
      Empty
    case Ops.Forgotten{}:
      Unit
    case Ops.Other{}:
      Unit

def forgot_disc(r: Ops.Read) -> Type:
  match r:
    case Ops.Body{text}:
      Unit
    case Ops.NoNewline{}:
      Unit
    case Ops.Forgotten{}:
      Empty
    case Ops.Other{}:
      Unit

def nonl_body(-b: String, e: {Ops.NoNewline{} == Ops.Body{b} : Ops.Read}) -> Empty:
  %e : {body_disc(_) : Type}
  Unit{}

def forgot_body(-b: String, e: {Ops.Forgotten{} == Ops.Body{b} : Ops.Read}) -> Empty:
  %e : {body_disc(_) : Type}
  Unit{}

def other_body(-b: String, e: {Ops.Other{} == Ops.Body{b} : Ops.Read}) -> Empty:
  %e : {body_disc(_) : Type}
  Unit{}

def body_nonl(-a: String, e: {Ops.Body{a} == Ops.NoNewline{} : Ops.Read}) -> Empty:
  %e : {nonl_disc(_) : Type}
  Unit{}

def forgot_nonl(e: {Ops.Forgotten{} == Ops.NoNewline{} : Ops.Read}) -> Empty:
  %e : {nonl_disc(_) : Type}
  Unit{}

def other_nonl(e: {Ops.Other{} == Ops.NoNewline{} : Ops.Read}) -> Empty:
  %e : {nonl_disc(_) : Type}
  Unit{}

def body_forgot(-a: String, e: {Ops.Body{a} == Ops.Forgotten{} : Ops.Read}) -> Empty:
  %e : {forgot_disc(_) : Type}
  Unit{}

def nonl_forgot(e: {Ops.NoNewline{} == Ops.Forgotten{} : Ops.Read}) -> Empty:
  %e : {forgot_disc(_) : Type}
  Unit{}

def other_forgot(e: {Ops.Other{} == Ops.Forgotten{} : Ops.Read}) -> Empty:
  %e : {forgot_disc(_) : Type}
  Unit{}

def read_text(r: Ops.Read) -> String:
  match r:
    case Ops.Body{text}:
      text
    case Ops.NoNewline{}:
      SNil{}
    case Ops.Forgotten{}:
      SNil{}
    case Ops.Other{}:
      SNil{}

# What a classification says about the line.
def classify_body.of(stripped: Maybe<&2, String>, nn: Bool, fg: Bool, -body: String, e: {Ops.classify.of(stripped, nn, fg) == Ops.Body{body} : Ops.Read}) -> {stripped == Some{body} : Maybe<&2, String>}:
  match stripped:
    case Some{b}:
      Equal.cong(Ops.Read, Maybe<&2, String>, r => Some{read_text(r)}, Ops.Body{b}, Ops.Body{body}, e)
    case None{}:
      match nn:
        case True{}:
          Empty.absurd({None{} == Some{body} : Maybe<&2, String>}, nonl_body(body, e))
        case False{}:
          match fg:
            case True{}:
              Empty.absurd({None{} == Some{body} : Maybe<&2, String>}, forgot_body(body, e))
            case False{}:
              Empty.absurd({None{} == Some{body} : Maybe<&2, String>}, other_body(body, e))

def classify_body(+t: String, +p: Char, +body: String, e: {Ops.classify(t, p) == Ops.Body{body} : Ops.Read}) -> {t == SCon{p, body} : String}:
  strip_eq(t, SCon{p, SNil{}}, body, classify_body.of(T.strip_prefix(t, SCon{p, SNil{}}), T.same(t, "\\ no newline"), T.same(t, "\\ forgotten"), body, e))

def classify_nonl.of(stripped: Maybe<&2, String>, nn: Bool, fg: Bool, e: {Ops.classify.of(stripped, nn, fg) == Ops.NoNewline{} : Ops.Read}) -> {nn == True{} : Bool}:
  match stripped:
    case Some{b}:
      Empty.absurd({nn == True{} : Bool}, body_nonl(b, e))
    case None{}:
      match nn:
        case True{}:
          {==}
        case False{}:
          match fg:
            case True{}:
              Empty.absurd({False{} == True{} : Bool}, forgot_nonl(e))
            case False{}:
              Empty.absurd({False{} == True{} : Bool}, other_nonl(e))

def classify_nonl(+t: String, +p: Char, e: {Ops.classify(t, p) == Ops.NoNewline{} : Ops.Read}) -> {t == "\\ no newline" : String}:
  Eq.same_eq(t, "\\ no newline", classify_nonl.of(T.strip_prefix(t, SCon{p, SNil{}}), T.same(t, "\\ no newline"), T.same(t, "\\ forgotten"), e))

def classify_forgot.of(stripped: Maybe<&2, String>, nn: Bool, fg: Bool, e: {Ops.classify.of(stripped, nn, fg) == Ops.Forgotten{} : Ops.Read}) -> {fg == True{} : Bool}:
  match stripped:
    case Some{b}:
      Empty.absurd({fg == True{} : Bool}, body_forgot(b, e))
    case None{}:
      match nn:
        case True{}:
          Empty.absurd({fg == True{} : Bool}, nonl_forgot(e))
        case False{}:
          match fg:
            case True{}:
              {==}
            case False{}:
              Empty.absurd({False{} == True{} : Bool}, other_forgot(e))

def classify_forgot(+t: String, +p: Char, e: {Ops.classify(t, p) == Ops.Forgotten{} : Ops.Read}) -> {t == "\\ forgotten" : String}:
  Eq.same_eq(t, "\\ forgotten", classify_forgot.of(T.strip_prefix(t, SCon{p, SNil{}}), T.same(t, "\\ no newline"), T.same(t, "\\ forgotten"), e))

# What the writer makes of one item.
def item_line(p: Char, body: String) -> {Ops.write_item(p, Ops.line(body)) == SCon{p, body ++ "\n"} : String}:
  app_nil(SCon{p, body ++ "\n"})

def item_forgotten(p: Char) -> {Ops.write_item(p, Ops.forgotten()) == "\\ forgotten\n" : String}:
  app_nil("\\ forgotten\n")

def item_marker(p: Char, t2: String, f2: Bool) -> {Ops.write_item(p, Ops.Item{t2, False{}, f2}) == Ops.write_item(p, Ops.Item{t2, True{}, f2}) ++ "\\ no newline\n" : String}:
  match f2:
    case True{}:
      %Equal.sym(String, "\\ forgotten\n" ++ SNil{}, "\\ forgotten\n", app_nil("\\ forgotten\n")) : {"\\ forgotten\n" ++ "\\ no newline\n" == _ ++ "\\ no newline\n" : String}
      {==}
    case False{}:
      %Equal.sym(String, SCon{p, t2 ++ "\n"} ++ SNil{}, SCon{p, t2 ++ "\n"}, app_nil(SCon{p, t2 ++ "\n"})) : {SCon{p, t2 ++ "\n"} ++ "\\ no newline\n" == _ ++ "\\ no newline\n" : String}
      {==}

def write_items_snoc(+p: Char, a: List<&2, Ops.Item>, +x: Ops.Item) -> {Ops.write_items(p, List.append(&2, Ops.Item, a, [x])) == Ops.write_items(p, a) ++ Ops.write_item(p, x) : String}:
  match a:
    case Nil{}:
      app_nil(Ops.write_item(p, x))
    case h <> t:
      %Equal.sym(String, Ops.write_items(p, List.append(&2, Ops.Item, t, [x])), Ops.write_items(p, t) ++ Ops.write_item(p, x), write_items_snoc(p, t, x)) : {Ops.write_item(p, h) ++ _ == (Ops.write_item(p, h) ++ Ops.write_items(p, t)) ++ Ops.write_item(p, x) : String}
      Equal.sym(String, (Ops.write_item(p, h) ++ Ops.write_items(p, t)) ++ Ops.write_item(p, x), Ops.write_item(p, h) ++ (Ops.write_items(p, t) ++ Ops.write_item(p, x)), app_assoc(Ops.write_item(p, h), Ops.write_items(p, t), Ops.write_item(p, x)))

def rev_snoc(+x: Ops.Item, +acc: List<&2, Ops.Item>) -> {List.reverse(&2, Ops.Item, x <> acc) == List.append(&2, Ops.Item, List.reverse(&2, Ops.Item, acc), [x]) : List<&2, Ops.Item>}:
  L.reverse_move([x], acc)

# The string algebra of one consumed line, in the three shapes it takes.
def shape_body(+w: String, p: Char, +body: String, +u: String) -> {w ++ (SCon{p, body} ++ ("\n" ++ u)) == (w ++ SCon{p, body ++ "\n"}) ++ u : String}:
  %Equal.sym(String, (w ++ SCon{p, body ++ "\n"}) ++ u, w ++ (SCon{p, body ++ "\n"} ++ u), app_assoc(w, SCon{p, body ++ "\n"}, u)) : {w ++ (SCon{p, body} ++ ("\n" ++ u)) == _ : String}
  %app_assoc(body, "\n", u) : {w ++ SCon{p, _} == w ++ SCon{p, (body ++ "\n") ++ u} : String}
  {==}

def shape_marker(+a: String, +i: String, +m: String, +u: String) -> {(a ++ i) ++ (m ++ u) == (a ++ (i ++ m)) ++ u : String}:
  %Equal.sym(String, (a ++ (i ++ m)) ++ u, a ++ ((i ++ m) ++ u), app_assoc(a, i ++ m, u)) : {(a ++ i) ++ (m ++ u) == _ : String}
  %Equal.sym(String, (i ++ m) ++ u, i ++ (m ++ u), app_assoc(i, m, u)) : {(a ++ i) ++ (m ++ u) == a ++ _ : String}
  app_assoc(a, i, m ++ u)

def shape_literal(+w: String, +l: String, +u: String) -> {w ++ (l ++ ("\n" ++ u)) == (w ++ (l ++ "\n")) ++ u : String}:
  %Equal.sym(String, (w ++ (l ++ "\n")) ++ u, w ++ ((l ++ "\n") ++ u), app_assoc(w, l ++ "\n", u)) : {w ++ (l ++ ("\n" ++ u)) == _ : String}
  %app_assoc(l, "\n", u) : {w ++ _ == w ++ ((l ++ "\n") ++ u) : String}
  {==}

def taken_items(r: Result<&2, &2, String, Ops.Taken>) -> List<&2, Ops.Item>:
  match r:
    case Fail{msg}:
      Nil{}
    case Done{Ops.Taken{items, rest, at}}:
      items

def taken_rest(r: Result<&2, &2, String, Ops.Taken>) -> List<&2, T.Line>:
  match r:
    case Fail{msg}:
      Nil{}
    case Done{Ops.Taken{items, rest, at}}:
      rest

def tdisc(r: Result<&2, &2, String, Ops.Taken>) -> Type:
  match r:
    case Fail{msg}:
      Unit
    case Done{tk}:
      Empty

def tfail(-msg: String, -tk: Ops.Taken, e: {Fail{msg} == Done{tk} : Result<&2, &2, String, Ops.Taken>}) -> Empty:
  %e : {tdisc(_) : Type}
  Unit{}


# A `\ no newline` line unterminates the item above it, which the writer
# spells as that item followed by the marker.
def taken.marker(more: List<&2, T.Line>, +at: Nat, +p: Char, acc: List<&2, Ops.Item>, -items: List<&2, Ops.Item>, -rest: List<&2, T.Line>, -at2: Nat, +t: String, tm: {t == "\\ no newline" : String}, +e: {Ops.take_items(T.Line{t, True{}} <> more, Ops.NoNewline{}, at, p, acc) == Done{Ops.Taken{items, rest, at2}} : Result<&2, &2, String, Ops.Taken>}, ih: @+xs: List<&2, Ops.Item> -> {Ops.take_items(more, Ops.classify_head(more, p), 1n+at, p, xs) == Done{Ops.Taken{items, rest, at2}} : Result<&2, &2, String, Ops.Taken>} -> {Ops.write_items(p, List.reverse(&2, Ops.Item, xs)) ++ unlines(more) == Ops.write_items(p, List.reverse(&2, Ops.Item, items)) ++ unlines(rest) : String}) -> {Ops.write_items(p, List.reverse(&2, Ops.Item, acc)) ++ unlines(T.Line{t, True{}} <> more) == Ops.write_items(p, List.reverse(&2, Ops.Item, items)) ++ unlines(rest) : String}:
  match acc:
    case Nil{}:
      Empty.absurd({Ops.write_items(p, List.reverse(&2, Ops.Item, Nil{})) ++ unlines(T.Line{t, True{}} <> more) == Ops.write_items(p, List.reverse(&2, Ops.Item, items)) ++ unlines(rest) : String}, tfail("line " ++ Nat.show(at) ++ ": " ++ "`\\ no newline` without an item above it", Ops.Taken{items, rest, at2}, e))
    case Ops.Item{+t2, True{}, +f2} <> +acc_rest:
      +a = Ops.write_items(p, List.reverse(&2, Ops.Item, acc_rest))
      +i = Ops.write_item(p, Ops.Item{t2, True{}, f2})
      +u = unlines(more)
      %ih(Ops.Item{t2, False{}, f2} <> acc_rest, e) : {Ops.write_items(p, List.reverse(&2, Ops.Item, Ops.Item{t2, True{}, f2} <> acc_rest)) ++ (t ++ ("\n" ++ u)) == _ : String}
      %Equal.sym(String, t, "\\ no newline", tm) : {Ops.write_items(p, List.reverse(&2, Ops.Item, Ops.Item{t2, True{}, f2} <> acc_rest)) ++ (_ ++ ("\n" ++ u)) == Ops.write_items(p, List.reverse(&2, Ops.Item, Ops.Item{t2, False{}, f2} <> acc_rest)) ++ u : String}
      %Equal.sym(List<&2, Ops.Item>, List.reverse(&2, Ops.Item, Ops.Item{t2, True{}, f2} <> acc_rest), List.append(&2, Ops.Item, List.reverse(&2, Ops.Item, acc_rest), [Ops.Item{t2, True{}, f2}]), rev_snoc(Ops.Item{t2, True{}, f2}, acc_rest)) : {Ops.write_items(p, _) ++ ("\\ no newline" ++ ("\n" ++ u)) == Ops.write_items(p, List.reverse(&2, Ops.Item, Ops.Item{t2, False{}, f2} <> acc_rest)) ++ u : String}
      %Equal.sym(List<&2, Ops.Item>, List.reverse(&2, Ops.Item, Ops.Item{t2, False{}, f2} <> acc_rest), List.append(&2, Ops.Item, List.reverse(&2, Ops.Item, acc_rest), [Ops.Item{t2, False{}, f2}]), rev_snoc(Ops.Item{t2, False{}, f2}, acc_rest)) : {Ops.write_items(p, List.append(&2, Ops.Item, List.reverse(&2, Ops.Item, acc_rest), [Ops.Item{t2, True{}, f2}])) ++ ("\\ no newline" ++ ("\n" ++ u)) == Ops.write_items(p, _) ++ u : String}
      %Equal.sym(String, Ops.write_items(p, List.append(&2, Ops.Item, List.reverse(&2, Ops.Item, acc_rest), [Ops.Item{t2, True{}, f2}])), a ++ i, write_items_snoc(p, List.reverse(&2, Ops.Item, acc_rest), Ops.Item{t2, True{}, f2})) : {_ ++ ("\\ no newline" ++ ("\n" ++ u)) == Ops.write_items(p, List.append(&2, Ops.Item, List.reverse(&2, Ops.Item, acc_rest), [Ops.Item{t2, False{}, f2}])) ++ u : String}
      %Equal.sym(String, Ops.write_items(p, List.append(&2, Ops.Item, List.reverse(&2, Ops.Item, acc_rest), [Ops.Item{t2, False{}, f2}])), a ++ Ops.write_item(p, Ops.Item{t2, False{}, f2}), write_items_snoc(p, List.reverse(&2, Ops.Item, acc_rest), Ops.Item{t2, False{}, f2})) : {(a ++ i) ++ ("\\ no newline" ++ ("\n" ++ u)) == _ ++ u : String}
      %Equal.sym(String, Ops.write_item(p, Ops.Item{t2, False{}, f2}), i ++ "\\ no newline\n", item_marker(p, t2, f2)) : {(a ++ i) ++ ("\\ no newline" ++ ("\n" ++ u)) == (a ++ _) ++ u : String}
      shape_marker(a, i, "\\ no newline\n", u)
    case Ops.Item{t2, False{}, f2} <> acc_rest:
      Empty.absurd({Ops.write_items(p, List.reverse(&2, Ops.Item, Ops.Item{t2, False{}, f2} <> acc_rest)) ++ unlines(T.Line{t, True{}} <> more) == Ops.write_items(p, List.reverse(&2, Ops.Item, items)) ++ unlines(rest) : String}, tfail("line " ++ Nat.show(at) ++ ": " ++ "`\\ no newline` without an item above it", Ops.Taken{items, rest, at2}, e))

# The items under an operation, written back, are the lines they came from.
def taken(ls: List<&2, T.Line>, r: Ops.Read, +at: Nat, +p: Char, +acc: List<&2, Ops.Item>, -items: List<&2, Ops.Item>, -rest: List<&2, T.Line>, -at2: Nat, +eq: {Ops.classify_head(ls, p) == r : Ops.Read}, +e: {Ops.take_items(ls, r, at, p, acc) == Done{Ops.Taken{items, rest, at2}} : Result<&2, &2, String, Ops.Taken>}) -> {Ops.write_items(p, List.reverse(&2, Ops.Item, acc)) ++ unlines(ls) == Ops.write_items(p, List.reverse(&2, Ops.Item, items)) ++ unlines(rest) : String}:
  match ls r:
    case Nil{} _:
      %Equal.cong(Result<&2, &2, String, Ops.Taken>, List<&2, Ops.Item>, taken_items, Done{Ops.Taken{acc, Nil{}, at}}, Done{Ops.Taken{items, rest, at2}}, e) : {Ops.write_items(p, List.reverse(&2, Ops.Item, acc)) ++ unlines(Nil{}) == Ops.write_items(p, List.reverse(&2, Ops.Item, _)) ++ unlines(rest) : String}
      %Equal.cong(Result<&2, &2, String, Ops.Taken>, List<&2, T.Line>, taken_rest, Done{Ops.Taken{acc, Nil{}, at}}, Done{Ops.Taken{items, rest, at2}}, e) : {Ops.write_items(p, List.reverse(&2, Ops.Item, acc)) ++ unlines(Nil{}) == Ops.write_items(p, List.reverse(&2, Ops.Item, acc)) ++ unlines(_) : String}
      {==}
    case T.Line{+t, True{}} <> +more Ops.Body{+body}:
      +w = Ops.write_items(p, List.reverse(&2, Ops.Item, acc))
      +u = unlines(more)
      %taken(more, Ops.classify_head(more, p), 1n+at, p, Ops.line(body) <> acc, items, rest, at2, {==}, e) : {w ++ (t ++ ("\n" ++ u)) == _ : String}
      %Equal.sym(String, t, SCon{p, body}, classify_body(t, p, body, eq)) : {w ++ (_ ++ ("\n" ++ u)) == Ops.write_items(p, List.reverse(&2, Ops.Item, Ops.line(body) <> acc)) ++ u : String}
      %Equal.sym(List<&2, Ops.Item>, List.reverse(&2, Ops.Item, Ops.line(body) <> acc), List.append(&2, Ops.Item, List.reverse(&2, Ops.Item, acc), [Ops.line(body)]), rev_snoc(Ops.line(body), acc)) : {w ++ (SCon{p, body} ++ ("\n" ++ u)) == Ops.write_items(p, _) ++ u : String}
      %Equal.sym(String, Ops.write_items(p, List.append(&2, Ops.Item, List.reverse(&2, Ops.Item, acc), [Ops.line(body)])), w ++ Ops.write_item(p, Ops.line(body)), write_items_snoc(p, List.reverse(&2, Ops.Item, acc), Ops.line(body))) : {w ++ (SCon{p, body} ++ ("\n" ++ u)) == _ ++ u : String}
      %Equal.sym(String, Ops.write_item(p, Ops.line(body)), SCon{p, body ++ "\n"}, item_line(p, body)) : {w ++ (SCon{p, body} ++ ("\n" ++ u)) == (w ++ _) ++ u : String}
      shape_body(w, p, body, u)
    case T.Line{t, False{}} <> more Ops.Body{body}:
      Empty.absurd({Ops.write_items(p, List.reverse(&2, Ops.Item, acc)) ++ unlines(T.Line{t, False{}} <> more) == Ops.write_items(p, List.reverse(&2, Ops.Item, items)) ++ unlines(rest) : String}, tfail("line " ++ Nat.show(at) ++ ": " ++ "unterminated line", Ops.Taken{items, rest, at2}, e))
    case T.Line{+t, True{}} <> +more Ops.NoNewline{}:
      taken.marker(more, at, p, acc, items, rest, at2, t, classify_nonl(t, p, eq), e, xs => h => taken(more, Ops.classify_head(more, p), 1n+at, p, xs, items, rest, at2, {==}, h))
    case T.Line{t, False{}} <> more Ops.NoNewline{}:
      Empty.absurd({Ops.write_items(p, List.reverse(&2, Ops.Item, acc)) ++ unlines(T.Line{t, False{}} <> more) == Ops.write_items(p, List.reverse(&2, Ops.Item, items)) ++ unlines(rest) : String}, tfail("line " ++ Nat.show(at) ++ ": " ++ "unterminated line", Ops.Taken{items, rest, at2}, e))
    case T.Line{+t, True{}} <> +more Ops.Forgotten{}:
      +w = Ops.write_items(p, List.reverse(&2, Ops.Item, acc))
      +u = unlines(more)
      %taken(more, Ops.classify_head(more, p), 1n+at, p, Ops.forgotten() <> acc, items, rest, at2, {==}, e) : {w ++ (t ++ ("\n" ++ u)) == _ : String}
      %Equal.sym(String, t, "\\ forgotten", classify_forgot(t, p, eq)) : {w ++ (_ ++ ("\n" ++ u)) == Ops.write_items(p, List.reverse(&2, Ops.Item, Ops.forgotten() <> acc)) ++ u : String}
      %Equal.sym(List<&2, Ops.Item>, List.reverse(&2, Ops.Item, Ops.forgotten() <> acc), List.append(&2, Ops.Item, List.reverse(&2, Ops.Item, acc), [Ops.forgotten()]), rev_snoc(Ops.forgotten(), acc)) : {w ++ ("\\ forgotten" ++ ("\n" ++ u)) == Ops.write_items(p, _) ++ u : String}
      %Equal.sym(String, Ops.write_items(p, List.append(&2, Ops.Item, List.reverse(&2, Ops.Item, acc), [Ops.forgotten()])), w ++ Ops.write_item(p, Ops.forgotten()), write_items_snoc(p, List.reverse(&2, Ops.Item, acc), Ops.forgotten())) : {w ++ ("\\ forgotten" ++ ("\n" ++ u)) == _ ++ u : String}
      %Equal.sym(String, Ops.write_item(p, Ops.forgotten()), "\\ forgotten\n", item_forgotten(p)) : {w ++ ("\\ forgotten" ++ ("\n" ++ u)) == (w ++ _) ++ u : String}
      shape_literal(w, "\\ forgotten", u)
    case T.Line{t, False{}} <> more Ops.Forgotten{}:
      Empty.absurd({Ops.write_items(p, List.reverse(&2, Ops.Item, acc)) ++ unlines(T.Line{t, False{}} <> more) == Ops.write_items(p, List.reverse(&2, Ops.Item, items)) ++ unlines(rest) : String}, tfail("line " ++ Nat.show(at) ++ ": " ++ "unterminated line", Ops.Taken{items, rest, at2}, e))
    case T.Line{t, True{}} <> more Ops.Other{}:
      %Equal.cong(Result<&2, &2, String, Ops.Taken>, List<&2, Ops.Item>, taken_items, Done{Ops.Taken{acc, T.Line{t, True{}} <> more, at}}, Done{Ops.Taken{items, rest, at2}}, e) : {Ops.write_items(p, List.reverse(&2, Ops.Item, acc)) ++ unlines(T.Line{t, True{}} <> more) == Ops.write_items(p, List.reverse(&2, Ops.Item, _)) ++ unlines(rest) : String}
      %Equal.cong(Result<&2, &2, String, Ops.Taken>, List<&2, T.Line>, taken_rest, Done{Ops.Taken{acc, T.Line{t, True{}} <> more, at}}, Done{Ops.Taken{items, rest, at2}}, e) : {Ops.write_items(p, List.reverse(&2, Ops.Item, acc)) ++ unlines(T.Line{t, True{}} <> more) == Ops.write_items(p, List.reverse(&2, Ops.Item, acc)) ++ unlines(_) : String}
      {==}
    case T.Line{t, False{}} <> more Ops.Other{}:
      %Equal.cong(Result<&2, &2, String, Ops.Taken>, List<&2, Ops.Item>, taken_items, Done{Ops.Taken{acc, T.Line{t, False{}} <> more, at}}, Done{Ops.Taken{items, rest, at2}}, e) : {Ops.write_items(p, List.reverse(&2, Ops.Item, acc)) ++ unlines(T.Line{t, False{}} <> more) == Ops.write_items(p, List.reverse(&2, Ops.Item, _)) ++ unlines(rest) : String}
      %Equal.cong(Result<&2, &2, String, Ops.Taken>, List<&2, T.Line>, taken_rest, Done{Ops.Taken{acc, T.Line{t, False{}} <> more, at}}, Done{Ops.Taken{items, rest, at2}}, e) : {Ops.write_items(p, List.reverse(&2, Ops.Item, acc)) ++ unlines(T.Line{t, False{}} <> more) == Ops.write_items(p, List.reverse(&2, Ops.Item, acc)) ++ unlines(_) : String}
      {==}

def split_disc(m: Maybe<&2, T.Split>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      Empty

def split_none(-h: String, -r: String, e: {None{} == Some{T.Split{h, r}} : Maybe<&2, T.Split>}) -> Empty:
  %e : {split_disc(_) : Type}
  Unit{}

def split_head(m: Maybe<&2, T.Split>) -> String:
  match m:
    case None{}:
      SNil{}
    case Some{T.Split{h, r}}:
      h

def split_rest(m: Maybe<&2, T.Split>) -> String:
  match m:
    case None{}:
      SNil{}
    case Some{T.Split{h, r}}:
      r

def split_go.fin(+t: String, +acc: String, +h: String, +r: String, +c: Char, cut: Bool, eq: {Char.is_eq(c, ' ') == cut : Bool}, +e: {Bool.pick(Maybe<&2, T.Split>, cut, Some{T.Split{String.reverse(acc), t}}, T.split_once.go(t, SCon{c, acc})) == Some{T.Split{h, r}} : Maybe<&2, T.Split>}, ih: {T.split_once.go(t, SCon{c, acc}) == Some{T.Split{h, r}} : Maybe<&2, T.Split>} -> {String.reverse.go(SCon{c, acc}, t) == h ++ (" " ++ r) : String}) -> {String.reverse.go(acc, SCon{c, t}) == h ++ (" " ++ r) : String}:
  match cut:
    case False{}:
      ih(e)
    case True{}:
      %Equal.cong(Maybe<&2, T.Split>, String, split_head, Some{T.Split{String.reverse(acc), t}}, Some{T.Split{h, r}}, e) : {String.reverse.go(acc, SCon{c, t}) == _ ++ (" " ++ r) : String}
      %Equal.cong(Maybe<&2, T.Split>, String, split_rest, Some{T.Split{String.reverse(acc), t}}, Some{T.Split{h, r}}, e) : {String.reverse.go(acc, SCon{c, t}) == String.reverse(acc) ++ (" " ++ _) : String}
      %Equal.sym(Char, c, ' ', Eq.char_eq(c, ' ', eq)) : {String.reverse.go(acc, SCon{_, t}) == String.reverse(acc) ++ (" " ++ t) : String}
      rev_go(acc, SCon{' ', t})

def shape_delete.tail(+cs: String, +w: String, +u: String) -> {(" " ++ cs) ++ ("\n" ++ (w ++ u)) == (" " ++ (cs ++ ("\n" ++ w))) ++ u : String}:
  %Equal.sym(String, (cs ++ ("\n" ++ w)) ++ u, cs ++ (("\n" ++ w) ++ u), app_assoc(cs, "\n" ++ w, u)) : {(" " ++ cs) ++ ("\n" ++ (w ++ u)) == SCon{' ', _} : String}
  %Equal.sym(String, ("\n" ++ w) ++ u, "\n" ++ (w ++ u), app_assoc("\n", w, u)) : {(" " ++ cs) ++ ("\n" ++ (w ++ u)) == SCon{' ', cs ++ _} : String}
  {==}

def shape_delete.core(+ps: String, +cs: String, +w: String, +u: String) -> {(ps ++ (" " ++ cs)) ++ ("\n" ++ (w ++ u)) == (ps ++ (" " ++ (cs ++ ("\n" ++ w)))) ++ u : String}:
  %Equal.sym(String, (ps ++ (" " ++ (cs ++ ("\n" ++ w)))) ++ u, ps ++ ((" " ++ (cs ++ ("\n" ++ w))) ++ u), app_assoc(ps, " " ++ (cs ++ ("\n" ++ w)), u)) : {(ps ++ (" " ++ cs)) ++ ("\n" ++ (w ++ u)) == _ : String}
  %Equal.sym(String, (ps ++ (" " ++ cs)) ++ ("\n" ++ (w ++ u)), ps ++ ((" " ++ cs) ++ ("\n" ++ (w ++ u))), app_assoc(ps, " " ++ cs, "\n" ++ (w ++ u))) : {_ == ps ++ ((" " ++ (cs ++ ("\n" ++ w))) ++ u) : String}
  Equal.cong(String, String, x => ps ++ x, (" " ++ cs) ++ ("\n" ++ (w ++ u)), (" " ++ (cs ++ ("\n" ++ w))) ++ u, shape_delete.tail(cs, w, u))

def shape_insert.core(+ps: String, +w: String, +u: String) -> {ps ++ ("\n" ++ (w ++ u)) == (ps ++ ("\n" ++ w)) ++ u : String}:
  %Equal.sym(String, (ps ++ ("\n" ++ w)) ++ u, ps ++ (("\n" ++ w) ++ u), app_assoc(ps, "\n" ++ w, u)) : {ps ++ ("\n" ++ (w ++ u)) == _ : String}
  %Equal.sym(String, ("\n" ++ w) ++ u, "\n" ++ (w ++ u), app_assoc("\n", w, u)) : {ps ++ ("\n" ++ (w ++ u)) == ps ++ _ : String}
  {==}

# Operation lines
# ---------------

# What `next_op` returning `n` says about the lines it read.
def spelled(ls: List<&2, T.Line>, n: Ops.Next) -> Type:
  match n:
    case Ops.More{op, rest, at}:
      {unlines(ls) == Ops.write_op(op) ++ unlines(rest) : String}
    case Ops.End{}:
      {ls == Nil{} : List<&2, T.Line>}
    case Ops.Bad{at, msg}:
      Unit

def split_go(s: String, +acc: String, +h: String, +r: String, e: {T.split_once.go(s, acc) == Some{T.Split{h, r}} : Maybe<&2, T.Split>}) -> {String.reverse.go(acc, s) == h ++ (" " ++ r) : String}:
  match s:
    case SNil{}:
      Empty.absurd({String.reverse.go(acc, SNil{}) == h ++ (" " ++ r) : String}, split_none(h, r, e))
    case SCon{+c, +t}:
      split_go.fin(t, acc, h, r, c, Char.is_eq(c, ' '), {==}, e, x => split_go(t, SCon{c, acc}, h, r, x))

def shape_delete(+ps: String, +cs: String, +w: String, +u: String) -> {("delete" ++ (" " ++ (ps ++ (" " ++ cs)))) ++ ("\n" ++ (w ++ u)) == ("delete " ++ (ps ++ (" " ++ (cs ++ ("\n" ++ w))))) ++ u : String}:
  %Equal.sym(String, ("delete " ++ (ps ++ (" " ++ (cs ++ ("\n" ++ w))))) ++ u, "delete " ++ ((ps ++ (" " ++ (cs ++ ("\n" ++ w)))) ++ u), app_assoc("delete ", ps ++ (" " ++ (cs ++ ("\n" ++ w))), u)) : {("delete" ++ (" " ++ (ps ++ (" " ++ cs)))) ++ ("\n" ++ (w ++ u)) == _ : String}
  %Equal.sym(String, ("delete " ++ (ps ++ (" " ++ cs))) ++ ("\n" ++ (w ++ u)), "delete " ++ ((ps ++ (" " ++ cs)) ++ ("\n" ++ (w ++ u))), app_assoc("delete ", ps ++ (" " ++ cs), "\n" ++ (w ++ u))) : {_ == "delete " ++ ((ps ++ (" " ++ (cs ++ ("\n" ++ w)))) ++ u) : String}
  Equal.cong(String, String, x => "delete " ++ x, (ps ++ (" " ++ cs)) ++ ("\n" ++ (w ++ u)), (ps ++ (" " ++ (cs ++ ("\n" ++ w)))) ++ u, shape_delete.core(ps, cs, w, u))

def shape_insert(+ps: String, +w: String, +u: String) -> {("insert" ++ (" " ++ ps)) ++ ("\n" ++ (w ++ u)) == ("insert " ++ (ps ++ ("\n" ++ w))) ++ u : String}:
  %Equal.sym(String, ("insert " ++ (ps ++ ("\n" ++ w))) ++ u, "insert " ++ ((ps ++ ("\n" ++ w)) ++ u), app_assoc("insert ", ps ++ ("\n" ++ w), u)) : {("insert" ++ (" " ++ ps)) ++ ("\n" ++ (w ++ u)) == _ : String}
  %Equal.sym(String, ("insert " ++ ps) ++ ("\n" ++ (w ++ u)), "insert " ++ (ps ++ ("\n" ++ (w ++ u))), app_assoc("insert ", ps, "\n" ++ (w ++ u))) : {_ == "insert " ++ ((ps ++ ("\n" ++ w)) ++ u) : String}
  Equal.cong(String, String, x => "insert " ++ x, ps ++ ("\n" ++ (w ++ u)), (ps ++ ("\n" ++ w)) ++ u, shape_insert.core(ps, w, u))

def delete_sp.count(+more: List<&2, T.Line>, +at: Nat, +ps: String, +cs: String, +pos: Nat, +c: Nat, +rev: List<&2, Ops.Item>, +rest: List<&2, T.Line>, -at2: Nat, same: Bool, eq: {Nat.is_eq(List.length(&2, Ops.Item, List.reverse(&2, Ops.Item, rev)), c) == same : Bool}, eqtk: {Ops.take_items(more, Ops.classify_head(more, '-'), 1n+at, '-', Nil{}) == Done{Ops.Taken{rev, rest, at2}} : Result<&2, &2, String, Ops.Taken>}, np: {T.number(ps) == Some{pos} : Maybe<&2, Nat>}, nc: {T.number(cs) == Some{c} : Maybe<&2, Nat>}) -> spelled(T.Line{"delete" ++ (" " ++ (ps ++ (" " ++ cs))), True{}} <> more, Bool.pick(Ops.Next, same, Ops.More{Ops.Op{Ops.Delete{}, pos, List.reverse(&2, Ops.Item, rev)}, rest, at2}, Ops.Bad{at, "a delete whose count disagrees with its items"})):
  match same:
    case False{}:
      Unit{}
    case True{}:
      +items = List.reverse(&2, Ops.Item, rev)
      +w = Ops.write_items('-', items)
      +u = unlines(rest)
      %Equal.sym(String, unlines(more), w ++ u, taken(more, Ops.classify_head(more, '-'), 1n+at, '-', Nil{}, rev, rest, at2, {==}, eqtk)) : {("delete" ++ (" " ++ (ps ++ (" " ++ cs)))) ++ ("\n" ++ _) == ("delete " ++ (T.spell(pos) ++ (" " ++ (T.spell(List.length(&2, Ops.Item, items)) ++ ("\n" ++ w))))) ++ u : String}
      %Equal.sym(Nat, List.length(&2, Ops.Item, items), c, Comp.eq_of_is_eq(List.length(&2, Ops.Item, items), c, eq)) : {("delete" ++ (" " ++ (ps ++ (" " ++ cs)))) ++ ("\n" ++ (w ++ u)) == ("delete " ++ (T.spell(pos) ++ (" " ++ (T.spell(_) ++ ("\n" ++ w))))) ++ u : String}
      %Dec.spell_number(cs, c, nc) : {("delete" ++ (" " ++ (ps ++ (" " ++ _)))) ++ ("\n" ++ (w ++ u)) == ("delete " ++ (T.spell(pos) ++ (" " ++ (T.spell(c) ++ ("\n" ++ w))))) ++ u : String}
      %Dec.spell_number(ps, pos, np) : {("delete" ++ (" " ++ (_ ++ (" " ++ T.spell(c))))) ++ ("\n" ++ (w ++ u)) == ("delete " ++ (T.spell(pos) ++ (" " ++ (T.spell(c) ++ ("\n" ++ w))))) ++ u : String}
      shape_delete(T.spell(pos), T.spell(c), w, u)

# A delete line and its items, written back.
def delete_sp(+more: List<&2, T.Line>, +at: Nat, +ps: String, +cs: String, +pos: Nat, +c: Nat, tk: Result<&2, &2, String, Ops.Taken>, eqtk: {Ops.take_items(more, Ops.classify_head(more, '-'), 1n+at, '-', Nil{}) == tk : Result<&2, &2, String, Ops.Taken>}, np: {T.number(ps) == Some{pos} : Maybe<&2, Nat>}, nc: {T.number(cs) == Some{c} : Maybe<&2, Nat>}) -> spelled(T.Line{"delete" ++ (" " ++ (ps ++ (" " ++ cs))), True{}} <> more, Ops.next_op.items(Ops.Delete{}, pos, Some{c}, at, tk)):
  match tk:
    case Fail{msg}:
      Unit{}
    case Done{Ops.Taken{+rev, +rest, +at2}}:
      delete_sp.count(more, at, ps, cs, pos, c, rev, rest, at2, Nat.is_eq(List.length(&2, Ops.Item, List.reverse(&2, Ops.Item, rev)), c), {==}, eqtk, np, nc)

def insert_sp.count(+more: List<&2, T.Line>, +at: Nat, +ps: String, +pos: Nat, +rev: List<&2, Ops.Item>, +rest: List<&2, T.Line>, -at2: Nat, empty: Bool, eqtk: {Ops.take_items(more, Ops.classify_head(more, '+'), 1n+at, '+', Nil{}) == Done{Ops.Taken{rev, rest, at2}} : Result<&2, &2, String, Ops.Taken>}, np: {T.number(ps) == Some{pos} : Maybe<&2, Nat>}) -> spelled(T.Line{"insert" ++ (" " ++ ps), True{}} <> more, Bool.pick(Ops.Next, empty, Ops.Bad{at, "an insert with no items"}, Ops.More{Ops.Op{Ops.Insert{}, pos, List.reverse(&2, Ops.Item, rev)}, rest, at2})):
  match empty:
    case True{}:
      Unit{}
    case False{}:
      +items = List.reverse(&2, Ops.Item, rev)
      +w = Ops.write_items('+', items)
      +u = unlines(rest)
      %Equal.sym(String, unlines(more), w ++ u, taken(more, Ops.classify_head(more, '+'), 1n+at, '+', Nil{}, rev, rest, at2, {==}, eqtk)) : {("insert" ++ (" " ++ ps)) ++ ("\n" ++ _) == ("insert " ++ (T.spell(pos) ++ ("\n" ++ w))) ++ u : String}
      %Dec.spell_number(ps, pos, np) : {("insert" ++ (" " ++ _)) ++ ("\n" ++ (w ++ u)) == ("insert " ++ (T.spell(pos) ++ ("\n" ++ w))) ++ u : String}
      shape_insert(T.spell(pos), w, u)

# An insert line and its items, written back.
def insert_sp(+more: List<&2, T.Line>, +at: Nat, +ps: String, +pos: Nat, tk: Result<&2, &2, String, Ops.Taken>, eqtk: {Ops.take_items(more, Ops.classify_head(more, '+'), 1n+at, '+', Nil{}) == tk : Result<&2, &2, String, Ops.Taken>}, np: {T.number(ps) == Some{pos} : Maybe<&2, Nat>}) -> spelled(T.Line{"insert" ++ (" " ++ ps), True{}} <> more, Ops.next_op.items(Ops.Insert{}, pos, None{}, at, tk)):
  match tk:
    case Fail{msg}:
      Unit{}
    case Done{Ops.Taken{+rev, +rest, +at2}}:
      insert_sp.count(more, at, ps, pos, rev, rest, at2, Nat.is_eq(List.length(&2, Ops.Item, List.reverse(&2, Ops.Item, rev)), 0n), eqtk, np)

# A delete's arguments, once split: positions that read, or a refusal.
def delete_args_sp(+more: List<&2, T.Line>, +at: Nat, +ps: String, +cs: String, np: Maybe<&2, Nat>, nc: Maybe<&2, Nat>, spaced: Bool, +ep: {T.number(ps) == np : Maybe<&2, Nat>}, +ec: {T.number(cs) == nc : Maybe<&2, Nat>}) -> spelled(T.Line{"delete" ++ (" " ++ (ps ++ (" " ++ cs))), True{}} <> more, Ops.next_op.delete(more, at, np, nc, spaced)):
  match np nc spaced:
    case Some{pos} Some{0n} False{}:
      Unit{}
    case Some{+pos} Some{1n+c} False{}:
      delete_sp(more, at, ps, cs, pos, 1n+c, Ops.take_items(more, Ops.classify_head(more, '-'), 1n+at, '-', Nil{}), {==}, ep, ec)
    case Some{pos} Some{0n} True{}:
      Unit{}
    case Some{pos} Some{1n+c} True{}:
      Unit{}
    case Some{pos} None{} False{}:
      Unit{}
    case Some{pos} None{} True{}:
      Unit{}
    case None{} Some{0n} False{}:
      Unit{}
    case None{} Some{1n+c} False{}:
      Unit{}
    case None{} Some{0n} True{}:
      Unit{}
    case None{} Some{1n+c} True{}:
      Unit{}
    case None{} None{} False{}:
      Unit{}
    case None{} None{} True{}:
      Unit{}

def delete_cut_sp(+more: List<&2, T.Line>, +at: Nat, +args: String, cut: Maybe<&2, T.Split>, eq: {T.split_once(args) == cut : Maybe<&2, T.Split>}) -> spelled(T.Line{"delete" ++ (" " ++ args), True{}} <> more, Ops.next_op.delete_args(more, at, cut)):
  match cut:
    case None{}:
      Unit{}
    case Some{T.Split{+ps, +cs}}:
      %Equal.sym(String, args, ps ++ (" " ++ cs), split_go(args, SNil{}, ps, cs, eq)) : {spelled(T.Line{"delete" ++ (" " ++ _), True{}} <> more, Ops.next_op.delete(more, at, T.number(ps), T.number(cs), T.has_char(cs, ' '))) : Type}
      delete_args_sp(more, at, ps, cs, T.number(ps), T.number(cs), T.has_char(cs, ' '), {==}, {==})

def insert_pos_sp(+more: List<&2, T.Line>, +at: Nat, +args: String, np: Maybe<&2, Nat>, ep: {T.number(args) == np : Maybe<&2, Nat>}) -> spelled(T.Line{"insert" ++ (" " ++ args), True{}} <> more, Ops.next_op.insert(more, at, np)):
  match np:
    case None{}:
      Unit{}
    case Some{+pos}:
      insert_sp(more, at, args, pos, Ops.take_items(more, Ops.classify_head(more, '+'), 1n+at, '+', Nil{}), {==}, ep)

def insert_args_sp(+more: List<&2, T.Line>, +at: Nat, +args: String, malformed: Bool) -> spelled(T.Line{"insert" ++ (" " ++ args), True{}} <> more, Bool.pick(Ops.Next, malformed, Ops.Bad{at, "a malformed insert"}, Ops.next_op.insert(more, at, T.number(args)))):
  match malformed:
    case True{}:
      Unit{}
    case False{}:
      insert_pos_sp(more, at, args, T.number(args), {==})

# The operation line, once cut at its first space.
def keyword_sp(+more: List<&2, T.Line>, +at: Nat, +kw: String, +args: String, d: Bool, i: Bool, c: Bool, m: Bool, ed: {T.same(kw, "delete") == d : Bool}, ei: {T.same(kw, "insert") == i : Bool}) -> spelled(T.Line{kw ++ (" " ++ args), True{}} <> more, Ops.next_op.keyword(more, at, kw ++ (" " ++ args), args, d, i, c, m)):
  match d:
    case True{}:
      %Equal.sym(String, kw, "delete", Eq.same_eq(kw, "delete", ed)) : {spelled(T.Line{_ ++ (" " ++ args), True{}} <> more, Ops.next_op.delete_args(more, at, T.split_once(args))) : Type}
      delete_cut_sp(more, at, args, T.split_once(args), {==})
    case False{}:
      match i:
        case True{}:
          %Equal.sym(String, kw, "insert", Eq.same_eq(kw, "insert", ei)) : {spelled(T.Line{_ ++ (" " ++ args), True{}} <> more, Bool.pick(Ops.Next, Bool.or(String.is_empty(args), T.has_char(args, ' ')), Ops.Bad{at, "a malformed insert"}, Ops.next_op.insert(more, at, T.number(args)))) : Type}
          insert_args_sp(more, at, args, Bool.or(String.is_empty(args), T.has_char(args, ' ')))
        case False{}:
          match c:
            case True{}:
              Unit{}
            case False{}:
              match m:
                case True{}:
                  Unit{}
                case False{}:
                  Unit{}

# A line with no space is no operation.
def keyword_bare(-more: List<&2, T.Line>, -at: Nat, -t: String, d: Bool, i: Bool, c: Bool, m: Bool) -> spelled(T.Line{t, True{}} <> more, Ops.next_op.keyword(more, at, t, SNil{}, d, i, c, m)):
  match d:
    case True{}:
      Unit{}
    case False{}:
      match i:
        case True{}:
          Unit{}
        case False{}:
          match c:
            case True{}:
              Unit{}
            case False{}:
              match m:
                case True{}:
                  Unit{}
                case False{}:
                  Unit{}

def split_sp(+more: List<&2, T.Line>, +at: Nat, +t: String, cut: Maybe<&2, T.Split>, eq: {T.split_once(t) == cut : Maybe<&2, T.Split>}) -> spelled(T.Line{t, True{}} <> more, Ops.next_op.split(more, at, t, cut)):
  match cut:
    case None{}:
      keyword_bare(more, at, t, T.same(t, "delete"), T.same(t, "insert"), Bool.or(String.starts_with(t, "-"), String.starts_with(t, "+")), T.same(t, "\\ no newline"))
    case Some{T.Split{+kw, +args}}:
      %Equal.sym(String, t, kw ++ (" " ++ args), split_go(t, SNil{}, kw, args, eq)) : {spelled(T.Line{_, True{}} <> more, Ops.next_op.keyword(more, at, _, args, T.same(kw, "delete"), T.same(kw, "insert"), Bool.or(String.starts_with(_, "-"), String.starts_with(_, "+")), False{})) : Type}
      keyword_sp(more, at, kw, args, T.same(kw, "delete"), T.same(kw, "insert"), Bool.or(String.starts_with(kw ++ (" " ++ args), "-"), String.starts_with(kw ++ (" " ++ args), "+")), False{}, {==}, {==})

def next_op_sp.cr(+more: List<&2, T.Line>, +at: Nat, +t: String, cr: Bool) -> spelled(T.Line{t, True{}} <> more, Bool.pick(Ops.Next, cr, Ops.Bad{at, "a carriage return in an operation line"}, Ops.next_op.split(more, at, t, T.split_once(t)))):
  match cr:
    case True{}:
      Unit{}
    case False{}:
      split_sp(more, at, t, T.split_once(t), {==})

# Whatever `next_op` reads, the writer spells.
def next_op_sp(ls: List<&2, T.Line>, +at: Nat) -> spelled(ls, Ops.next_op(ls, at)):
  match ls:
    case Nil{}:
      {==}
    case T.Line{t, False{}} <> rest:
      Unit{}
    case T.Line{+t, True{}} <> +rest:
      next_op_sp.cr(rest, at, t, T.has_char(t, '\r'))

def bounded_sp.fin(-ls: List<&2, T.Line>, -op: Ops.Op, -rest: List<&2, T.Line>, -at: Nat, c: Maybe<&2, String>, s: {unlines(ls) == Ops.write_op(op) ++ unlines(rest) : String}) -> spelled(ls, Ops.next_op.fin(op, rest, at, c)):
  match c:
    case None{}:
      s
    case Some{msg}:
      Unit{}

def bounded_sp(-ls: List<&2, T.Line>, +prev: Maybe<&2, Ops.Op>, +pd: Maybe<&2, Ops.Op>, m: Ops.Next, s: spelled(ls, m)) -> spelled(ls, Ops.next_op.bounded(prev, pd, m)):
  match m:
    case Ops.End{}:
      s
    case Ops.Bad{at, msg}:
      Unit{}
    case Ops.More{+op, rest, at}:
      bounded_sp.fin(ls, op, rest, at, Maybe.or(&2, String, Ops.ordered(prev, op), Ops.ordered(pd, op)), s)

# The parse loop
# --------------

def collect_sp.step(+op: Ops.Op, r: Result<&2, &2, String, List<&2, Ops.Op>>, -ls: List<&2, T.Line>, +rest: List<&2, T.Line>, -ops: List<&2, Ops.Op>, sp: {unlines(ls) == Ops.write_op(op) ++ unlines(rest) : String}, e: {Parse.prepend_one(op, r) == Done{ops} : Result<&2, &2, String, List<&2, Ops.Op>>}, ih: @-xs: List<&2, Ops.Op> -> {r == Done{xs} : Result<&2, &2, String, List<&2, Ops.Op>>} -> {unlines(rest) == Ops.write_ops(xs) : String}) -> {unlines(ls) == Ops.write_ops(ops) : String}:
  match r:
    case Fail{msg}:
      Empty.absurd({unlines(ls) == Ops.write_ops(ops) : String}, Parse.fail_done(msg, ops, e))
    case Done{+xs}:
      %Parse.done_inj(op <> xs, ops, e) : {unlines(ls) == Ops.write_ops(_) : String}
      %Equal.sym(String, unlines(ls), Ops.write_op(op) ++ unlines(rest), sp) : {_ == Ops.write_op(op) ++ Ops.write_ops(xs) : String}
      %Equal.sym(String, unlines(rest), Ops.write_ops(xs), ih(xs, {==})) : {Ops.write_op(op) ++ _ == Ops.write_op(op) ++ Ops.write_ops(xs) : String}
      {==}

# Every operation the loop collects was spelled by the lines it consumed.
def collect_sp(fuel: Nat, n: Ops.Next, +pd: Maybe<&2, Ops.Op>, -ls: List<&2, T.Line>, -ops: List<&2, Ops.Op>, sp: spelled(ls, n), e: {Parse.collect(fuel, n, pd) == Done{ops} : Result<&2, &2, String, List<&2, Ops.Op>>}) -> {unlines(ls) == Ops.write_ops(ops) : String}:
  match fuel n:
    case 0n Ops.End{}:
      %Parse.done_inj(Nil{}, ops, e) : {unlines(ls) == Ops.write_ops(_) : String}
      %Equal.sym(List<&2, T.Line>, ls, Nil{}, sp) : {unlines(_) == Ops.write_ops(Nil{}) : String}
      {==}
    case 1n+p Ops.End{}:
      %Parse.done_inj(Nil{}, ops, e) : {unlines(ls) == Ops.write_ops(_) : String}
      %Equal.sym(List<&2, T.Line>, ls, Nil{}, sp) : {unlines(_) == Ops.write_ops(Nil{}) : String}
      {==}
    case 0n Ops.Bad{at, msg}:
      Empty.absurd({unlines(ls) == Ops.write_ops(ops) : String}, Parse.fail_done("line " ++ Nat.show(at) ++ ": " ++ msg, ops, e))
    case 1n+p Ops.Bad{at, msg}:
      Empty.absurd({unlines(ls) == Ops.write_ops(ops) : String}, Parse.fail_done("line " ++ Nat.show(at) ++ ": " ++ msg, ops, e))
    case 0n Ops.More{op, rest, at}:
      Empty.absurd({unlines(ls) == Ops.write_ops(ops) : String}, Parse.fail_done("the walk ran out of lines", ops, e))
    case 1n++p Ops.More{+op, +rest, +at}:
      +deletion = Ops.remember_delete(op, pd)
      +next = Ops.next_op.bounded(Some{op}, deletion, Ops.next_op(rest, at))
      collect_sp.step(op, Parse.collect(p, next, deletion), ls, rest, ops, sp, e, xs => h => collect_sp(p, next, deletion, rest, xs, bounded_sp(rest, Some{op}, deletion, Ops.next_op(rest, at), next_op_sp(rest, at)), h))

# The headers
# -----------

def key_line(key: String, v: Maybe<&2, String>) -> String:
  match v:
    case None{}:
      SNil{}
    case Some{d}:
      key ++ (d ++ "\n")

def headed_value(h: Ops.Headed) -> Maybe<&2, String>:
  match h:
    case Ops.Headed{value, rest, at}:
      value

def headed_rest(h: Ops.Headed) -> List<&2, T.Line>:
  match h:
    case Ops.Headed{value, rest, at}:
      rest

def header_sp.of(+t: String, +more: List<&2, T.Line>, +at: Nat, +key: String, st: Maybe<&2, String>, eq: {T.strip_prefix(t, key) == st : Maybe<&2, String>}, -value: Maybe<&2, String>, -rest: List<&2, T.Line>, -at2: Nat, +e: {Ops.header.of(t, True{}, more, at, st) == Ops.Headed{value, rest, at2} : Ops.Headed}) -> {unlines(T.Line{t, True{}} <> more) == key_line(key, value) ++ unlines(rest) : String}:
  match st:
    case None{}:
      %Equal.cong(Ops.Headed, Maybe<&2, String>, headed_value, Ops.Headed{None{}, T.Line{t, True{}} <> more, at}, Ops.Headed{value, rest, at2}, e) : {unlines(T.Line{t, True{}} <> more) == key_line(key, _) ++ unlines(rest) : String}
      %Equal.cong(Ops.Headed, List<&2, T.Line>, headed_rest, Ops.Headed{None{}, T.Line{t, True{}} <> more, at}, Ops.Headed{value, rest, at2}, e) : {unlines(T.Line{t, True{}} <> more) == key_line(key, None{}) ++ unlines(_) : String}
      {==}
    case Some{+v}:
      %Equal.cong(Ops.Headed, Maybe<&2, String>, headed_value, Ops.Headed{Some{v}, more, 1n+at}, Ops.Headed{value, rest, at2}, e) : {unlines(T.Line{t, True{}} <> more) == key_line(key, _) ++ unlines(rest) : String}
      %Equal.cong(Ops.Headed, List<&2, T.Line>, headed_rest, Ops.Headed{Some{v}, more, 1n+at}, Ops.Headed{value, rest, at2}, e) : {unlines(T.Line{t, True{}} <> more) == key_line(key, Some{v}) ++ unlines(_) : String}
      %Equal.sym(String, t, key ++ v, strip_eq(t, key, v, eq)) : {_ ++ ("\n" ++ unlines(more)) == (key ++ (v ++ "\n")) ++ unlines(more) : String}
      %Equal.sym(String, (key ++ v) ++ ("\n" ++ unlines(more)), key ++ (v ++ ("\n" ++ unlines(more))), app_assoc(key, v, "\n" ++ unlines(more))) : {_ == (key ++ (v ++ "\n")) ++ unlines(more) : String}
      shape_literal(key, v, unlines(more))

# A header line is written as the value it carried, or not at all.
def header_sp(ls: List<&2, T.Line>, +at: Nat, +key: String, -value: Maybe<&2, String>, -rest: List<&2, T.Line>, -at2: Nat, +e: {Ops.header(ls, at, key) == Ops.Headed{value, rest, at2} : Ops.Headed}) -> {unlines(ls) == key_line(key, value) ++ unlines(rest) : String}:
  match ls:
    case Nil{}:
      %Equal.cong(Ops.Headed, Maybe<&2, String>, headed_value, Ops.Headed{None{}, Nil{}, at}, Ops.Headed{value, rest, at2}, e) : {unlines(Nil{}) == key_line(key, _) ++ unlines(rest) : String}
      %Equal.cong(Ops.Headed, List<&2, T.Line>, headed_rest, Ops.Headed{None{}, Nil{}, at}, Ops.Headed{value, rest, at2}, e) : {unlines(Nil{}) == key_line(key, None{}) ++ unlines(_) : String}
      {==}
    case T.Line{+t, False{}} <> +more:
      %Equal.cong(Ops.Headed, Maybe<&2, String>, headed_value, Ops.Headed{None{}, T.Line{t, False{}} <> more, at}, Ops.Headed{value, rest, at2}, e) : {unlines(T.Line{t, False{}} <> more) == key_line(key, _) ++ unlines(rest) : String}
      %Equal.cong(Ops.Headed, List<&2, T.Line>, headed_rest, Ops.Headed{None{}, T.Line{t, False{}} <> more, at}, Ops.Headed{value, rest, at2}, e) : {unlines(T.Line{t, False{}} <> more) == key_line(key, None{}) ++ unlines(_) : String}
      {==}
    case T.Line{+t, True{}} <> +more:
      header_sp.of(t, more, at, key, T.strip_prefix(t, key), {==}, value, rest, at2, e)

def doc_forgets(r: Result<&2, &2, String, Ops.Doc>) -> Maybe<&2, String>:
  match r:
    case Fail{msg}:
      None{}
    case Done{Ops.Doc{f, d, ops}}:
      f

def doc_result(r: Result<&2, &2, String, Ops.Doc>) -> Maybe<&2, String>:
  match r:
    case Fail{msg}:
      None{}
    case Done{Ops.Doc{f, d, ops}}:
      d

# The document carries the headers the parser read.
def body_forgets(+f: Maybe<&2, String>, +r: Maybe<&2, String>, res: Result<&2, &2, String, List<&2, Ops.Op>>, -f2: Maybe<&2, String>, -r2: Maybe<&2, String>, -ops: List<&2, Ops.Op>, e: {Ops.parse.body(f, r, res) == Done{Ops.Doc{f2, r2, ops}} : Result<&2, &2, String, Ops.Doc>}) -> {f == f2 : Maybe<&2, String>}:
  match res:
    case Fail{msg}:
      Empty.absurd({f == f2 : Maybe<&2, String>}, Parse.refuse(Fail{msg}, Ops.Doc{f2, r2, ops}, {==}, e))
    case Done{xs}:
      match xs:
        case Nil{}:
          Empty.absurd({f == f2 : Maybe<&2, String>}, Parse.refuse(Fail{"no operations"}, Ops.Doc{f2, r2, ops}, {==}, e))
        case +o <> +os:
          Equal.cong(Result<&2, &2, String, Ops.Doc>, Maybe<&2, String>, doc_forgets, Done{Ops.Doc{f, r, o <> os}}, Done{Ops.Doc{f2, r2, ops}}, Parse.pick_done(Ops.markers_ok(o <> os), Done{Ops.Doc{f, r, o <> os}}, Fail{"`\\ no newline` on an item that is not last"}, Ops.Doc{f2, r2, ops}, {==}, e))

def body_result(+f: Maybe<&2, String>, +r: Maybe<&2, String>, res: Result<&2, &2, String, List<&2, Ops.Op>>, -f2: Maybe<&2, String>, -r2: Maybe<&2, String>, -ops: List<&2, Ops.Op>, e: {Ops.parse.body(f, r, res) == Done{Ops.Doc{f2, r2, ops}} : Result<&2, &2, String, Ops.Doc>}) -> {r == r2 : Maybe<&2, String>}:
  match res:
    case Fail{msg}:
      Empty.absurd({r == r2 : Maybe<&2, String>}, Parse.refuse(Fail{msg}, Ops.Doc{f2, r2, ops}, {==}, e))
    case Done{xs}:
      match xs:
        case Nil{}:
          Empty.absurd({r == r2 : Maybe<&2, String>}, Parse.refuse(Fail{"no operations"}, Ops.Doc{f2, r2, ops}, {==}, e))
        case +o <> +os:
          Equal.cong(Result<&2, &2, String, Ops.Doc>, Maybe<&2, String>, doc_result, Done{Ops.Doc{f, r, o <> os}}, Done{Ops.Doc{f2, r2, ops}}, Parse.pick_done(Ops.markers_ok(o <> os), Done{Ops.Doc{f, r, o <> os}}, Fail{"`\\ no newline` on an item that is not last"}, Ops.Doc{f2, r2, ops}, {==}, e))

# The lines after the blank one are the operations, written.
def separator_sp(ls: List<&2, T.Line>, +at: Nat, +f: Maybe<&2, String>, +r: Maybe<&2, String>, -f2: Maybe<&2, String>, -r2: Maybe<&2, String>, +ops: List<&2, Ops.Op>, e: {Ops.parse.separator(f, r, ls, at) == Done{Ops.Doc{f2, r2, ops}} : Result<&2, &2, String, Ops.Doc>}) -> {unlines(ls) == "\n" ++ Ops.write_ops(ops) : String}:
  match ls:
    case Nil{}:
      Empty.absurd({unlines(Nil{}) == "\n" ++ Ops.write_ops(ops) : String}, Parse.refuse(Ops.fail(Ops.Doc, at, "missing the blank line after the headers"), Ops.Doc{f2, r2, ops}, {==}, e))
    case T.Line{t, term} <> +rest:
      match t term:
        case SNil{} True{}:
          +fuel = {1n+List.length(&2, T.Line, rest) : Nat}
          +start = Ops.next_op(rest, 1n+at)
          +n = Ops.next_op.bounded(None{}, None{}, start)
          %Equal.sym(String, unlines(rest), Ops.write_ops(ops), collect_sp(fuel, n, None{}, rest, ops, bounded_sp(rest, None{}, None{}, start, next_op_sp(rest, 1n+at)), Parse.collect_of_ops(fuel, n, None{}, ops, Parse.body_ops(f, r, Ops.parse.ops(fuel, n, Nil{}, None{}), f2, r2, ops, e)))) : {SNil{} ++ ("\n" ++ _) == "\n" ++ Ops.write_ops(ops) : String}
          {==}
        case SNil{} False{}:
          Empty.absurd({unlines(T.Line{SNil{}, False{}} <> rest) == "\n" ++ Ops.write_ops(ops) : String}, Parse.refuse(Ops.fail(Ops.Doc, at, "missing the blank line after the headers"), Ops.Doc{f2, r2, ops}, {==}, e))
        case SCon{c, cs} True{}:
          Empty.absurd({unlines(T.Line{SCon{c, cs}, True{}} <> rest) == "\n" ++ Ops.write_ops(ops) : String}, Parse.refuse(Ops.fail(Ops.Doc, at, "missing the blank line after the headers"), Ops.Doc{f2, r2, ops}, {==}, e))
        case SCon{c, cs} False{}:
          Empty.absurd({unlines(T.Line{SCon{c, cs}, False{}} <> rest) == "\n" ++ Ops.write_ops(ops) : String}, Parse.refuse(Ops.fail(Ops.Doc, at, "missing the blank line after the headers"), Ops.Doc{f2, r2, ops}, {==}, e))

def separator_forgets(ls: List<&2, T.Line>, +at: Nat, +f: Maybe<&2, String>, +r: Maybe<&2, String>, -f2: Maybe<&2, String>, -r2: Maybe<&2, String>, -ops: List<&2, Ops.Op>, e: {Ops.parse.separator(f, r, ls, at) == Done{Ops.Doc{f2, r2, ops}} : Result<&2, &2, String, Ops.Doc>}) -> {f == f2 : Maybe<&2, String>}:
  match ls:
    case Nil{}:
      Empty.absurd({f == f2 : Maybe<&2, String>}, Parse.refuse(Ops.fail(Ops.Doc, at, "missing the blank line after the headers"), Ops.Doc{f2, r2, ops}, {==}, e))
    case T.Line{t, term} <> +rest:
      match t term:
        case SNil{} True{}:
          body_forgets(f, r, Ops.parse.ops(1n+List.length(&2, T.Line, rest), Ops.next_op.bounded(None{}, None{}, Ops.next_op(rest, 1n+at)), Nil{}, None{}), f2, r2, ops, e)
        case SNil{} False{}:
          Empty.absurd({f == f2 : Maybe<&2, String>}, Parse.refuse(Ops.fail(Ops.Doc, at, "missing the blank line after the headers"), Ops.Doc{f2, r2, ops}, {==}, e))
        case SCon{c, cs} True{}:
          Empty.absurd({f == f2 : Maybe<&2, String>}, Parse.refuse(Ops.fail(Ops.Doc, at, "missing the blank line after the headers"), Ops.Doc{f2, r2, ops}, {==}, e))
        case SCon{c, cs} False{}:
          Empty.absurd({f == f2 : Maybe<&2, String>}, Parse.refuse(Ops.fail(Ops.Doc, at, "missing the blank line after the headers"), Ops.Doc{f2, r2, ops}, {==}, e))

def separator_result(ls: List<&2, T.Line>, +at: Nat, +f: Maybe<&2, String>, +r: Maybe<&2, String>, -f2: Maybe<&2, String>, -r2: Maybe<&2, String>, -ops: List<&2, Ops.Op>, e: {Ops.parse.separator(f, r, ls, at) == Done{Ops.Doc{f2, r2, ops}} : Result<&2, &2, String, Ops.Doc>}) -> {r == r2 : Maybe<&2, String>}:
  match ls:
    case Nil{}:
      Empty.absurd({r == r2 : Maybe<&2, String>}, Parse.refuse(Ops.fail(Ops.Doc, at, "missing the blank line after the headers"), Ops.Doc{f2, r2, ops}, {==}, e))
    case T.Line{t, term} <> +rest:
      match t term:
        case SNil{} True{}:
          body_result(f, r, Ops.parse.ops(1n+List.length(&2, T.Line, rest), Ops.next_op.bounded(None{}, None{}, Ops.next_op(rest, 1n+at)), Nil{}, None{}), f2, r2, ops, e)
        case SNil{} False{}:
          Empty.absurd({r == r2 : Maybe<&2, String>}, Parse.refuse(Ops.fail(Ops.Doc, at, "missing the blank line after the headers"), Ops.Doc{f2, r2, ops}, {==}, e))
        case SCon{c, cs} True{}:
          Empty.absurd({r == r2 : Maybe<&2, String>}, Parse.refuse(Ops.fail(Ops.Doc, at, "missing the blank line after the headers"), Ops.Doc{f2, r2, ops}, {==}, e))
        case SCon{c, cs} False{}:
          Empty.absurd({r == r2 : Maybe<&2, String>}, Parse.refuse(Ops.fail(Ops.Doc, at, "missing the blank line after the headers"), Ops.Doc{f2, r2, ops}, {==}, e))

# `parse.result` over a destructured header: what it establishes.
def result_sep(f: Maybe<&2, String>, rv: Maybe<&2, String>, +rest: List<&2, T.Line>, +at: Nat, -f2: Maybe<&2, String>, -r2: Maybe<&2, String>, -ops: List<&2, Ops.Op>, e: {Ops.parse.result(f, Ops.Headed{rv, rest, at}) == Done{Ops.Doc{f2, r2, ops}} : Result<&2, &2, String, Ops.Doc>}) -> {Ops.parse.separator(f, rv, rest, at) == Done{Ops.Doc{f2, r2, ops}} : Result<&2, &2, String, Ops.Doc>}:
  match f rv:
    case Some{x} Some{y}:
      Empty.absurd({Ops.parse.separator(Some{x}, Some{y}, rest, at) == Done{Ops.Doc{f2, r2, ops}} : Result<&2, &2, String, Ops.Doc>}, Parse.refuse(Ops.fail(Ops.Doc, at, "a result beside forgets"), Ops.Doc{f2, r2, ops}, {==}, e))
    case Some{+x} None{}:
      Parse.pick_done(Ops.valid_digest(None{}), Ops.parse.separator(Some{x}, None{}, rest, at), Ops.fail(Ops.Doc, at, "a malformed result"), Ops.Doc{f2, r2, ops}, {==}, e)
    case None{} Some{+y}:
      Parse.pick_done(Ops.valid_digest(Some{y}), Ops.parse.separator(None{}, Some{y}, rest, at), Ops.fail(Ops.Doc, at, "a malformed result"), Ops.Doc{f2, r2, ops}, {==}, e)
    case None{} None{}:
      Parse.pick_done(Ops.valid_digest(None{}), Ops.parse.separator(None{}, None{}, rest, at), Ops.fail(Ops.Doc, at, "a malformed result"), Ops.Doc{f2, r2, ops}, {==}, e)

def key_header_forgets(v: Maybe<&2, String>) -> {key_line("forgets ", v) == Ops.header_line("forgets", v) : String}:
  match v:
    case None{}:
      {==}
    case Some{d}:
      {==}

def key_header_result(v: Maybe<&2, String>) -> {key_line("result ", v) == Ops.header_line("result", v) : String}:
  match v:
    case None{}:
      {==}
    case Some{d}:
      {==}

# After the `forgets` header: the `result` header, the blank line, and the operations.
def forgets_sp.of(+fv: Maybe<&2, String>, +rest: List<&2, T.Line>, +at: Nat, +rv: Maybe<&2, String>, +rest2: List<&2, T.Line>, +at2: Nat, +eh: {Ops.header(rest, at, "result ") == Ops.Headed{rv, rest2, at2} : Ops.Headed}, +f2: Maybe<&2, String>, +r2: Maybe<&2, String>, +ops: List<&2, Ops.Op>, +e: {Ops.parse.result(fv, Ops.Headed{rv, rest2, at2}) == Done{Ops.Doc{f2, r2, ops}} : Result<&2, &2, String, Ops.Doc>}) -> {unlines(rest) == Ops.header_line("result", r2) ++ ("\n" ++ Ops.write_ops(ops)) : String}:
  +sep = result_sep(fv, rv, rest2, at2, f2, r2, ops, e)
  %Equal.sym(String, unlines(rest), key_line("result ", rv) ++ unlines(rest2), header_sp(rest, at, "result ", rv, rest2, at2, eh)) : {_ == Ops.header_line("result", r2) ++ ("\n" ++ Ops.write_ops(ops)) : String}
  %Equal.sym(String, unlines(rest2), "\n" ++ Ops.write_ops(ops), separator_sp(rest2, at2, fv, rv, f2, r2, ops, sep)) : {key_line("result ", rv) ++ _ == Ops.header_line("result", r2) ++ ("\n" ++ Ops.write_ops(ops)) : String}
  %Equal.sym(Maybe<&2, String>, rv, r2, separator_result(rest2, at2, fv, rv, f2, r2, ops, sep)) : {key_line("result ", _) ++ ("\n" ++ Ops.write_ops(ops)) == Ops.header_line("result", r2) ++ ("\n" ++ Ops.write_ops(ops)) : String}
  %Equal.sym(String, key_line("result ", r2), Ops.header_line("result", r2), key_header_result(r2)) : {_ ++ ("\n" ++ Ops.write_ops(ops)) == Ops.header_line("result", r2) ++ ("\n" ++ Ops.write_ops(ops)) : String}
  {==}

def forgets_sp.doc(+fv: Maybe<&2, String>, +rest: List<&2, T.Line>, +at: Nat, +rv: Maybe<&2, String>, +rest2: List<&2, T.Line>, +at2: Nat, -f2: Maybe<&2, String>, -r2: Maybe<&2, String>, +ops: List<&2, Ops.Op>, +e: {Ops.parse.result(fv, Ops.Headed{rv, rest2, at2}) == Done{Ops.Doc{f2, r2, ops}} : Result<&2, &2, String, Ops.Doc>}) -> {fv == f2 : Maybe<&2, String>}:
  separator_forgets(rest2, at2, fv, rv, f2, r2, ops, result_sep(fv, rv, rest2, at2, f2, r2, ops, e))

# `parse.forgets` over a destructured header, with the `result` header
# generalized so that it can be opened.
def forgets_sp.result(+fv: Maybe<&2, String>, +rest: List<&2, T.Line>, +at: Nat, +rv: Maybe<&2, String>, +rest2: List<&2, T.Line>, +at2: Nat, eh: {Ops.header(rest, at, "result ") == Ops.Headed{rv, rest2, at2} : Ops.Headed}, -f2: Maybe<&2, String>, -r2: Maybe<&2, String>, -ops: List<&2, Ops.Op>, e: {Ops.parse.forgets(Ops.Headed{fv, rest, at}) == Done{Ops.Doc{f2, r2, ops}} : Result<&2, &2, String, Ops.Doc>}) -> {Ops.parse.result(fv, Ops.Headed{rv, rest2, at2}) == Done{Ops.Doc{f2, r2, ops}} : Result<&2, &2, String, Ops.Doc>}:
  %eh : {Ops.parse.result(fv, _) == Done{Ops.Doc{f2, r2, ops}} : Result<&2, &2, String, Ops.Doc>}
  Parse.pick_done(Ops.valid_digest(fv), Ops.parse.result(fv, Ops.header(rest, at, "result ")), Ops.fail(Ops.Doc, at, "a malformed forgets"), Ops.Doc{f2, r2, ops}, {==}, e)

def forgets_sp.h(+fv: Maybe<&2, String>, +rest: List<&2, T.Line>, +at: Nat, h: Ops.Headed, +eh: {Ops.header(rest, at, "result ") == h : Ops.Headed}, +f2: Maybe<&2, String>, +r2: Maybe<&2, String>, +ops: List<&2, Ops.Op>, +e: {Ops.parse.forgets(Ops.Headed{fv, rest, at}) == Done{Ops.Doc{f2, r2, ops}} : Result<&2, &2, String, Ops.Doc>}) -> {unlines(rest) == Ops.header_line("result", r2) ++ ("\n" ++ Ops.write_ops(ops)) : String}:
  match h:
    case Ops.Headed{+rv, +rest2, +at2}:
      forgets_sp.of(fv, rest, at, rv, rest2, at2, eh, f2, r2, ops, forgets_sp.result(fv, rest, at, rv, rest2, at2, eh, f2, r2, ops, e))

def forgets_sp.doc_h(+fv: Maybe<&2, String>, +rest: List<&2, T.Line>, +at: Nat, h: Ops.Headed, +eh: {Ops.header(rest, at, "result ") == h : Ops.Headed}, +f2: Maybe<&2, String>, +r2: Maybe<&2, String>, +ops: List<&2, Ops.Op>, +e: {Ops.parse.forgets(Ops.Headed{fv, rest, at}) == Done{Ops.Doc{f2, r2, ops}} : Result<&2, &2, String, Ops.Doc>}) -> {fv == f2 : Maybe<&2, String>}:
  match h:
    case Ops.Headed{+rv, +rest2, +at2}:
      forgets_sp.doc(fv, rest, at, rv, rest2, at2, f2, r2, ops, forgets_sp.result(fv, rest, at, rv, rest2, at2, eh, f2, r2, ops, e))

# After the `historica` line: both headers, the blank line, the operations.
def preamble_sp.h(+rest: List<&2, T.Line>, h: Ops.Headed, +eh: {Ops.header(rest, 2n, "forgets ") == h : Ops.Headed}, +f2: Maybe<&2, String>, +r2: Maybe<&2, String>, +ops: List<&2, Ops.Op>, +e: {Ops.parse.forgets(h) == Done{Ops.Doc{f2, r2, ops}} : Result<&2, &2, String, Ops.Doc>}) -> {unlines(rest) == Ops.header_line("forgets", f2) ++ (Ops.header_line("result", r2) ++ ("\n" ++ Ops.write_ops(ops))) : String}:
  match h:
    case Ops.Headed{+fv, +rest2, +at2}:
      %Equal.sym(String, unlines(rest), key_line("forgets ", fv) ++ unlines(rest2), header_sp(rest, 2n, "forgets ", fv, rest2, at2, eh)) : {_ == Ops.header_line("forgets", f2) ++ (Ops.header_line("result", r2) ++ ("\n" ++ Ops.write_ops(ops))) : String}
      %Equal.sym(String, unlines(rest2), Ops.header_line("result", r2) ++ ("\n" ++ Ops.write_ops(ops)), forgets_sp.h(fv, rest2, at2, Ops.header(rest2, at2, "result "), {==}, f2, r2, ops, e)) : {key_line("forgets ", fv) ++ _ == Ops.header_line("forgets", f2) ++ (Ops.header_line("result", r2) ++ ("\n" ++ Ops.write_ops(ops))) : String}
      %Equal.sym(Maybe<&2, String>, fv, f2, forgets_sp.doc_h(fv, rest2, at2, Ops.header(rest2, at2, "result "), {==}, f2, r2, ops, e)) : {key_line("forgets ", _) ++ (Ops.header_line("result", r2) ++ ("\n" ++ Ops.write_ops(ops))) == Ops.header_line("forgets", f2) ++ (Ops.header_line("result", r2) ++ ("\n" ++ Ops.write_ops(ops))) : String}
      %Equal.sym(String, key_line("forgets ", f2), Ops.header_line("forgets", f2), key_header_forgets(f2)) : {_ ++ (Ops.header_line("result", r2) ++ ("\n" ++ Ops.write_ops(ops))) == Ops.header_line("forgets", f2) ++ (Ops.header_line("result", r2) ++ ("\n" ++ Ops.write_ops(ops))) : String}
      {==}

def preamble_sp(ls: List<&2, T.Line>, +f2: Maybe<&2, String>, +r2: Maybe<&2, String>, +ops: List<&2, Ops.Op>, +e: {Ops.parse.preamble(ls) == Done{Ops.Doc{f2, r2, ops}} : Result<&2, &2, String, Ops.Doc>}) -> {unlines(ls) == Ops.write(Ops.Doc{f2, r2, ops}) : String}:
  match ls:
    case Nil{}:
      Empty.absurd({unlines(Nil{}) == Ops.write(Ops.Doc{f2, r2, ops}) : String}, Parse.refuse(Ops.fail(Ops.Doc, 1n, "not a historica document"), Ops.Doc{f2, r2, ops}, {==}, e))
    case T.Line{+t, term} <> +rest:
      match term:
        case False{}:
          Empty.absurd({unlines(T.Line{t, False{}} <> rest) == Ops.write(Ops.Doc{f2, r2, ops}) : String}, Parse.refuse(Ops.fail(Ops.Doc, 1n, "not a historica document"), Ops.Doc{f2, r2, ops}, {==}, e))
        case True{}:
          +accepted = Parse.pick_done(T.same(t, "historica"), Ops.parse.forgets(Ops.header(rest, 2n, "forgets ")), Ops.fail(Ops.Doc, 1n, "not a historica document: " ++ t), Ops.Doc{f2, r2, ops}, {==}, e)
          %Equal.sym(String, t, "historica", Eq.same_eq(t, "historica", Parse.pick_true(T.same(t, "historica"), Ops.parse.forgets(Ops.header(rest, 2n, "forgets ")), Ops.fail(Ops.Doc, 1n, "not a historica document: " ++ t), Ops.Doc{f2, r2, ops}, {==}, e))) : {_ ++ ("\n" ++ unlines(rest)) == Ops.write(Ops.Doc{f2, r2, ops}) : String}
          %Equal.sym(String, unlines(rest), Ops.header_line("forgets", f2) ++ (Ops.header_line("result", r2) ++ ("\n" ++ Ops.write_ops(ops))), preamble_sp.h(rest, Ops.header(rest, 2n, "forgets "), {==}, f2, r2, ops, accepted)) : {"historica" ++ ("\n" ++ _) == Ops.write(Ops.Doc{f2, r2, ops}) : String}
          {==}

# The theorem: what the parser accepts, the writer spells back byte for byte.
def write_parse(+s: String, doc: Ops.Doc, e: {Ops.parse(s) == Done{doc} : Result<&2, &2, String, Ops.Doc>}) -> {Ops.write(doc) == s : String}:
  match doc:
    case Ops.Doc{+f, +r, +ops}:
      Equal.trans(String, Ops.write(Ops.Doc{f, r, ops}), unlines(T.lines(s)), s, Equal.sym(String, unlines(T.lines(s)), Ops.write(Ops.Doc{f, r, ops}), preamble_sp(T.lines(s), f, r, ops, e)), unlines_lines(s))

def main() -> Unit:
  Unit{}
