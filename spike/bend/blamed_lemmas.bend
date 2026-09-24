# What `blame` prints. The rows it attributes are the lines the walk reads,
# and it prints each of them once, numbered as the file numbers it.
import Base
import ./ops.bend as Ops
import ./merge.bend as Merge
import ./main.bend as Main
import ./store.bend as Store
import ./string_lemmas.bend as S
import ./diff_lemmas.bend as Diff

def rdisc(-A: Data, r: Result<&2, &2, Main.Refused, A>) -> Type:
  match r:
    case Done{x}:
      Empty
    case Fail{e}:
      Unit

def fail_done(-A: Data, -e: Main.Refused, -x: A, h: {Fail{e} == Done{x} : Result<&2, &2, Main.Refused, A>}) -> Empty:
  %h : {rdisc(A, _) : Type}
  Unit{}

def done_eq(-A: Data, -a: A, -b: A, h: {Done{a} == Done{b} : Result<&2, &2, Main.Refused, A>}) -> {a == b : A}:
  Equal.cong(Result<&2, &2, Main.Refused, A>, A, r => Result.default(&2, &2, Main.Refused, A, r, a), Done{a}, Done{b}, h)

# The walk
# --------

def rows_walk(ns: List<&2, Merge.Node>, +names: List<&2, String>) -> {Main.rows.items(Main.walked.rows(ns, names)) == Merge.file.of(ns) : List<&2, Ops.Item>}:
  match ns:
    case Nil{}:
      {==}
    case +n <> rest:
      Equal.cong(List<&2, Ops.Item>, List<&2, Ops.Item>, l => Merge.Node.item(n) <> l, Main.rows.items(Main.walked.rows(rest, names)), Merge.file.of(rest), rows_walk(rest, names))

def origins_file(w: Main.Walked) -> {Main.rows.items(Main.walked.origins(w)) == Main.walked.file(w) : List<&2, Ops.Item>}:
  match w:
    case Main.Walked{+names, t}:
      rows_walk(Merge.visible(t), names)

def walked_rows(r: Result<&2, &2, String, Main.Walked>, +rs: List<&2, Main.Row>, e: {Main.blame.walked.r(r) == Done{rs} : Result<&2, &2, Main.Refused, List<&2, Main.Row>>}) -> {Result.map(&2, &2, String, Main.Walked, List<&2, Ops.Item>, w => Main.walked.file(w), r) == Done{Main.rows.items(rs)} : Result<&2, &2, String, List<&2, Ops.Item>>}:
  match r:
    case Fail{x}:
      Empty.absurd({Fail{x} == Done{Main.rows.items(rs)} : Result<&2, &2, String, List<&2, Ops.Item>>}, fail_done(List<&2, Main.Row>, Main.Refused{1, x}, rs, e))
    case Done{+w}:
      +d = done_eq(List<&2, Main.Row>, Main.walked.origins(w), rs, e)
      %d : {Done{Main.walked.file(w)} == Done{Main.rows.items(_)} : Result<&2, &2, String, List<&2, Ops.Item>>}
      Equal.cong(List<&2, Ops.Item>, Result<&2, &2, String, List<&2, Ops.Item>>, l => Done{l}, Main.walked.file(w), Main.rows.items(Main.walked.origins(w)), Equal.sym(List<&2, Ops.Item>, Main.rows.items(Main.walked.origins(w)), Main.walked.file(w), origins_file(w)))

def rows_of(+oldest: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +id: String, +file: String, r: Result<&2, &2, String, List<&2, Ops.Item>>, +rs: List<&2, Main.Row>, e: {Main.blame.rows.of(oldest, ds, id, file, r) == Done{rs} : Result<&2, &2, Main.Refused, List<&2, Main.Row>>}) -> {Main.walked(oldest, ds, id, file) == Done{Main.rows.items(rs)} : Result<&2, &2, String, List<&2, Ops.Item>>}:
  match r:
    case Fail{x}:
      Empty.absurd({Main.walked(oldest, ds, id, file) == Done{Main.rows.items(rs)} : Result<&2, &2, String, List<&2, Ops.Item>>}, fail_done(List<&2, Main.Row>, Main.Refused{1, x}, rs, e))
    case Done{items}:
      walked_rows(Main.walked.of(oldest, ds, id, file), rs, e)

# The rows `blame <target> <path>` attributes are the lines the walk reads.
def rows_walked(+oldest: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +id: String, +file: String, +rs: List<&2, Main.Row>, e: {Main.blame.rows.r(oldest, ds, id, file) == Done{rs} : Result<&2, &2, Main.Refused, List<&2, Main.Row>>}) -> {Main.walked(oldest, ds, id, file) == Done{Main.rows.items(rs)} : Result<&2, &2, String, List<&2, Ops.Item>>}:
  rows_of(oldest, ds, id, file, Main.content.in(oldest, ds, id, file), rs, e)

# The span
# --------

def is_fail(-A: Data, r: Result<&2, &2, Main.Refused, A>) -> Bool:
  match r:
    case Fail{e}:
      True{}
    case Done{x}:
      False{}

# A refusal is not an answer: computing that `r` fails refutes it.
def refuse(-A: Data, r: Result<&2, &2, Main.Refused, A>, -x: A, bad: {is_fail(A, r) == True{} : Bool}, e: {r == Done{x} : Result<&2, &2, Main.Refused, A>}) -> Empty:
  match r:
    case Fail{er}:
      fail_done(A, er, x, e)
    case Done{y}:
      S.false_true(bad)

def all_lines(rs: List<&2, Main.Row>, +k: Nat) -> {Main.blamed.lines(Main.rows.all(rs, k)) == Main.lines.numbered(Main.rows.items(rs), k) : List<&2, Main.NLine>}:
  match rs:
    case Nil{}:
      {==}
    case Main.Row{by, +it} <> rest:
      Equal.cong(List<&2, Main.NLine>, List<&2, Main.NLine>, l => Main.NLine{k, it} <> l, Main.blamed.lines(Main.rows.all(rest, 1n+k)), Main.lines.numbered(Main.rows.items(rest), 1n+k), all_lines(rest, 1n+k))

def keep_lines(b: Bool, +k: Nat, -by: Maybe<&2, String>, +it: Ops.Item, +bl: List<&2, Main.Blamed>, +ln: List<&2, Main.NLine>, ih: {Main.blamed.lines(bl) == ln : List<&2, Main.NLine>}) -> {Main.blamed.lines(Main.rows.keep(b, Main.Blamed{k, Main.Row{by, it}}, bl)) == Main.nline.keep(b, Main.NLine{k, it}, ln) : List<&2, Main.NLine>}:
  match b:
    case True{}:
      Equal.cong(List<&2, Main.NLine>, List<&2, Main.NLine>, l => Main.NLine{k, it} <> l, Main.blamed.lines(bl), ln, ih)
    case False{}:
      ih

def in_lines(rs: List<&2, Main.Row>, +k: Nat, +f: Nat, +l: Nat) -> {Main.blamed.lines(Main.rows.in(rs, k, f, l)) == Main.lines.in_span(Main.lines.numbered(Main.rows.items(rs), k), f, l) : List<&2, Main.NLine>}:
  match rs:
    case Nil{}:
      {==}
    case Main.Row{by, +it} <> +rest:
      keep_lines(Bool.and(Nat.is_le(f, k), Nat.is_le(k, l)), k, by, it, Main.rows.in(rest, 1n+k, f, l), Main.lines.in_span(Main.lines.numbered(Main.rows.items(rest), 1n+k), f, l), in_lines(rest, 1n+k, f, l))

def span_at(+rs: List<&2, Main.Row>, +f: Nat, +l: Nat, past: Bool, +bl: List<&2, Main.Blamed>, e: {Main.blame.span.at(rs, f, l, past) == Done{bl} : Result<&2, &2, Main.Refused, List<&2, Main.Blamed>>}) -> {Main.blamed.lines(bl) == Main.lines.in_span(Main.lines.numbered(Main.rows.items(rs), 1n), f, l) : List<&2, Main.NLine>}:
  match past:
    case True{}:
      Empty.absurd({Main.blamed.lines(bl) == Main.lines.in_span(Main.lines.numbered(Main.rows.items(rs), 1n), f, l) : List<&2, Main.NLine>}, refuse(List<&2, Main.Blamed>, Main.blame.span.at(rs, f, l, True{}), bl, {==}, e))
    case False{}:
      +d = done_eq(List<&2, Main.Blamed>, Main.rows.in(rs, 1n, f, l), bl, e)
      %d : {Main.blamed.lines(_) == Main.lines.in_span(Main.lines.numbered(Main.rows.items(rs), 1n), f, l) : List<&2, Main.NLine>}
      in_lines(rs, 1n, f, l)

# `blame` prints each line of the span asked, numbered as the file numbers
# it, and no other.
def span_lines(+rs: List<&2, Main.Row>, span: Maybe<&2, Main.Wanted>, +bl: List<&2, Main.Blamed>, e: {Main.blame.span.r(rs, span) == Done{bl} : Result<&2, &2, Main.Refused, List<&2, Main.Blamed>>}) -> {Main.blamed.lines(bl) == Main.lines.asked(Main.lines.numbered(Main.rows.items(rs), 1n), span) : List<&2, Main.NLine>}:
  match span:
    case None{}:
      +d = done_eq(List<&2, Main.Blamed>, Main.rows.all(rs, 1n), bl, e)
      %d : {Main.blamed.lines(_) == Main.lines.numbered(Main.rows.items(rs), 1n) : List<&2, Main.NLine>}
      all_lines(rs, 1n)
    case Some{Main.Wanted{+f, +l}}:
      span_at(rs, f, l, Nat.is_gt(f, List.length(&2, Main.Row, rs)), bl, e)

# Printing
# --------

def app_nil(a: String) -> {String.append(a, SNil{}) == a : String}:
  match a:
    case SNil{}:
      {==}
    case SCon{+h, t}:
      Equal.cong(String, String, x => SCon{h, x}, String.append(t, SNil{}), t, app_nil(t))

def app_assoc(a: String, +b: String, +c: String) -> {String.append(String.append(a, b), c) == String.append(a, String.append(b, c)) : String}:
  match a:
    case SNil{}:
      {==}
    case SCon{+h, t}:
      Equal.cong(String, String, x => SCon{h, x}, String.append(String.append(t, b), c), String.append(t, String.append(b, c)), app_assoc(t, b, c))

def rev_go_app(a: String, +b: String, acc: String) -> {String.reverse.go(String.append(a, b), acc) == String.reverse.go(b, String.reverse.go(a, acc)) : String}:
  match a:
    case SNil{}:
      {==}
    case SCon{h, t}:
      rev_go_app(t, b, SCon{h, acc})

def rev_acc(s: String, +acc: String) -> {String.reverse.go(s, acc) == String.append(String.reverse.go(s, SNil{}), acc) : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      Equal.trans(String, String.reverse.go(t, SCon{h, acc}), String.append(String.reverse.go(t, SNil{}), SCon{h, acc}), String.append(String.reverse.go(t, SCon{h, SNil{}}), acc),
        rev_acc(t, SCon{h, acc}),
        Equal.trans(String, String.append(String.reverse.go(t, SNil{}), SCon{h, acc}), String.append(String.append(String.reverse.go(t, SNil{}), SCon{h, SNil{}}), acc), String.append(String.reverse.go(t, SCon{h, SNil{}}), acc),
          Equal.sym(String, String.append(String.append(String.reverse.go(t, SNil{}), SCon{h, SNil{}}), acc), String.append(String.reverse.go(t, SNil{}), SCon{h, acc}), app_assoc(String.reverse.go(t, SNil{}), SCon{h, SNil{}}, acc)),
          Equal.cong(String, String, x => String.append(x, acc), String.append(String.reverse.go(t, SNil{}), SCon{h, SNil{}}), String.reverse.go(t, SCon{h, SNil{}}), Equal.sym(String, String.reverse.go(t, SCon{h, SNil{}}), String.append(String.reverse.go(t, SNil{}), SCon{h, SNil{}}), rev_acc(t, SCon{h, SNil{}})))))

def rev_app(+a: String, +b: String) -> {String.reverse(String.append(a, b)) == String.append(String.reverse(b), String.reverse(a)) : String}:
  Equal.trans(String, String.reverse.go(String.append(a, b), SNil{}), String.reverse.go(b, String.reverse.go(a, SNil{})), String.append(String.reverse.go(b, SNil{}), String.reverse.go(a, SNil{})),
    rev_go_app(a, b, SNil{}), rev_acc(b, String.reverse.go(a, SNil{})))

def sw_if(c: Bool, -z: String, xt: String, yt: String, h: {String.starts_with.if(xt, yt, c) == True{} : Bool}, ih: {String.starts_with(xt, yt) == True{} : Bool} -> {String.starts_with(String.append(xt, z), yt) == True{} : Bool}) -> {String.starts_with.if(String.append(xt, z), yt, c) == True{} : Bool}:
  match c:
    case True{}:
      ih(h)
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, S.false_true(h))

def sw_nil(z: String) -> {String.starts_with(z, SNil{}) == True{} : Bool}:
  match z:
    case SNil{}:
      {==}
    case SCon{h, t}:
      {==}

# What starts with `b` still does with anything after it.
def sw_ext(a: String, b: String, +z: String, h: {String.starts_with(a, b) == True{} : Bool}) -> {String.starts_with(String.append(a, z), b) == True{} : Bool}:
  match a b:
    case SNil{} SNil{}:
      sw_nil(z)
    case SNil{} SCon{y, +yt}:
      Empty.absurd({String.starts_with(z, SCon{y, yt}) == True{} : Bool}, S.false_true(h))
    case SCon{x, +xt} SNil{}:
      {==}
    case SCon{x, xt} SCon{y, +yt}:
      sw_if(Char.is_eq(x, y), z, xt, yt, h, hh => sw_ext(xt, yt, z, hh))

def sw_refl(a: String) -> {String.starts_with(a, a) == True{} : Bool}:
  match a:
    case SNil{}:
      {==}
    case SCon{+x, +t}:
      +r = Equal.sym(Bool, Char.is_eq(x, x), True{}, Diff.char_eq_refl(x))
      %r : {String.starts_with.if(t, t, _) == True{} : Bool}
      sw_refl(t)

def ends_refl(+t: String) -> {String.ends_with(t, t) == True{} : Bool}:
  sw_refl(String.reverse(t))

# What ends with `t` still does with anything before it.
def ends_pre(+p: String, +s: String, +t: String, h: {String.ends_with(s, t) == True{} : Bool}) -> {String.ends_with(String.append(p, s), t) == True{} : Bool}:
  +ra = Equal.sym(String, String.reverse(String.append(p, s)), String.append(String.reverse(s), String.reverse(p)), rev_app(p, s))
  %ra : {String.starts_with(_, String.reverse(t)) == True{} : Bool}
  sw_ext(String.reverse(s), String.reverse(t), String.reverse(p), h)

def and_tt(a: Bool, -b: Bool, ha: {a == True{} : Bool}, hb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  match a:
    case True{}:
      hb
    case False{}:
      Empty.absurd({Bool.and(False{}, b) == True{} : Bool}, S.false_true(ha))

def line_ends(+c: String, +w: String, +d: String, +n: Nat, +cw: Nat, +ww: Nat, +dw: Nat, +nw: Nat, +t: String, +term: Bool, +forgot: Bool) -> {String.ends_with(String.append(Main.pad_left(c, cw), String.append("  ", String.append(Main.pad(w, ww), String.append("  ", String.append(Main.pad(d, dw), String.append("  ", String.append(Main.pad_left(Nat.show(n), nw), String.append("  ", Ops.shown(Ops.Item{t, term, forgot}))))))))), Ops.shown(Ops.Item{t, term, forgot})) == True{} : Bool}:
  ends_pre(Main.pad_left(c, cw), String.append("  ", String.append(Main.pad(w, ww), String.append("  ", String.append(Main.pad(d, dw), String.append("  ", String.append(Main.pad_left(Nat.show(n), nw), String.append("  ", Ops.shown(Ops.Item{t, term, forgot})))))))), Ops.shown(Ops.Item{t, term, forgot}), ends_pre("  ", String.append(Main.pad(w, ww), String.append("  ", String.append(Main.pad(d, dw), String.append("  ", String.append(Main.pad_left(Nat.show(n), nw), String.append("  ", Ops.shown(Ops.Item{t, term, forgot}))))))), Ops.shown(Ops.Item{t, term, forgot}), ends_pre(Main.pad(w, ww), String.append("  ", String.append(Main.pad(d, dw), String.append("  ", String.append(Main.pad_left(Nat.show(n), nw), String.append("  ", Ops.shown(Ops.Item{t, term, forgot})))))), Ops.shown(Ops.Item{t, term, forgot}), ends_pre("  ", String.append(Main.pad(d, dw), String.append("  ", String.append(Main.pad_left(Nat.show(n), nw), String.append("  ", Ops.shown(Ops.Item{t, term, forgot}))))), Ops.shown(Ops.Item{t, term, forgot}), ends_pre(Main.pad(d, dw), String.append("  ", String.append(Main.pad_left(Nat.show(n), nw), String.append("  ", Ops.shown(Ops.Item{t, term, forgot})))), Ops.shown(Ops.Item{t, term, forgot}), ends_pre("  ", String.append(Main.pad_left(Nat.show(n), nw), String.append("  ", Ops.shown(Ops.Item{t, term, forgot}))), Ops.shown(Ops.Item{t, term, forgot}), ends_pre(Main.pad_left(Nat.show(n), nw), String.append("  ", Ops.shown(Ops.Item{t, term, forgot})), Ops.shown(Ops.Item{t, term, forgot}), ends_pre("  ", Ops.shown(Ops.Item{t, term, forgot}), Ops.shown(Ops.Item{t, term, forgot}), ends_refl(Ops.shown(Ops.Item{t, term, forgot}))))))))))

def ends_row(term: Bool, +c: String, +w: String, +d: String, +n: Nat, +cw: Nat, +ww: Nat, +dw: Nat, +nw: Nat, +t: String, +forgot: Bool, +r: List<&2, String>, +es: List<&2, String>, ih: {Main.ends_all(r, es) == True{} : Bool}) -> {Main.ends_all(Main.blame.line(String.append(Main.pad_left(c, cw), String.append("  ", String.append(Main.pad(w, ww), String.append("  ", String.append(Main.pad(d, dw), String.append("  ", String.append(Main.pad_left(Nat.show(n), nw), String.append("  ", Ops.shown(Ops.Item{t, term, forgot}))))))))), term, r), Main.blame.ends.item(Ops.shown(Ops.Item{t, term, forgot}), term, es)) == True{} : Bool}:
  match term:
    case True{}:
      and_tt(String.ends_with(String.append(Main.pad_left(c, cw), String.append("  ", String.append(Main.pad(w, ww), String.append("  ", String.append(Main.pad(d, dw), String.append("  ", String.append(Main.pad_left(Nat.show(n), nw), String.append("  ", Ops.shown(Ops.Item{t, True{}, forgot}))))))))), Ops.shown(Ops.Item{t, True{}, forgot})), Main.ends_all(r, es), line_ends(c, w, d, n, cw, ww, dw, nw, t, True{}, forgot), ih)
    case False{}:
      and_tt(String.ends_with(String.append(Main.pad_left(c, cw), String.append("  ", String.append(Main.pad(w, ww), String.append("  ", String.append(Main.pad(d, dw), String.append("  ", String.append(Main.pad_left(Nat.show(n), nw), String.append("  ", Ops.shown(Ops.Item{t, False{}, forgot}))))))))), Ops.shown(Ops.Item{t, False{}, forgot})), Bool.and(String.ends_with("\\ no newline at end of file", "\\ no newline at end of file"), Main.ends_all(r, es)), line_ends(c, w, d, n, cw, ww, dw, nw, t, False{}, forgot),
        and_tt(String.ends_with("\\ no newline at end of file", "\\ no newline at end of file"), Main.ends_all(r, es), ends_refl("\\ no newline at end of file"), ih))

# Each line `blame` prints ends with the line it attributes, whatever the
# columns before it, and a line without a newline is followed by the marker.
def shown_ends(ss: List<&2, Main.Shown>, +cw: Nat, +ww: Nat, +dw: Nat, +nw: Nat) -> {Main.ends_all(Main.blame.lines(ss, cw, ww, dw, nw), Main.blame.ends(Main.shown.items(ss))) == True{} : Bool}:
  match ss:
    case Nil{}:
      {==}
    case Main.Shown{+n, Main.Columns{+c, +w, +d}, Ops.Item{+t, +term, +forgot}} <> +rest:
      ends_row(term, c, w, d, n, cw, ww, dw, nw, t, forgot, Main.blame.lines(rest, cw, ww, dw, nw), Main.blame.ends(Main.shown.items(rest)), shown_ends(rest, cw, ww, dw, nw))

def items_shown(+fs: List<&2, Main.Full>, +cs: List<&2, String>, bl: List<&2, Main.Blamed>) -> {Main.shown.items(Main.shown.rows(fs, cs, bl)) == Main.lines.items(Main.blamed.lines(bl)) : List<&2, Ops.Item>}:
  match bl:
    case Nil{}:
      {==}
    case Main.Blamed{n, Main.Row{by, +it}} <> rest:
      Equal.cong(List<&2, Ops.Item>, List<&2, Ops.Item>, l => it <> l, Main.shown.items(Main.shown.rows(fs, cs, rest)), Main.lines.items(Main.blamed.lines(rest)), items_shown(fs, cs, rest))

def printed(+fs: List<&2, Main.Full>, +cs: List<&2, String>, +rs: List<&2, Main.Row>, +span: Maybe<&2, Main.Wanted>, r: Result<&2, &2, Main.Refused, List<&2, Main.Blamed>>, +er: {Main.blame.span.r(rs, span) == r : Result<&2, &2, Main.Refused, List<&2, Main.Blamed>>}, +out: List<&2, String>, e: {Main.blame.shown(fs, cs, r) == Done{out} : Result<&2, &2, Main.Refused, List<&2, String>>}) -> {Main.ends_all(out, Main.blame.ends(Main.lines.items(Main.lines.asked(Main.lines.numbered(Main.rows.items(rs), 1n), span)))) == True{} : Bool}:
  match r:
    case Fail{x}:
      Empty.absurd({Main.ends_all(out, Main.blame.ends(Main.lines.items(Main.lines.asked(Main.lines.numbered(Main.rows.items(rs), 1n), span)))) == True{} : Bool}, fail_done(List<&2, String>, x, out, e))
    case Done{+bl}:
      +d = done_eq(List<&2, String>, Main.blame.print(Main.shown.rows(fs, cs, bl)), out, e)
      %d : {Main.ends_all(_, Main.blame.ends(Main.lines.items(Main.lines.asked(Main.lines.numbered(Main.rows.items(rs), 1n), span)))) == True{} : Bool}
      +sl = span_lines(rs, span, bl, er)
      %sl : {Main.ends_all(Main.blame.print(Main.shown.rows(fs, cs, bl)), Main.blame.ends(Main.lines.items(_))) == True{} : Bool}
      +ixs = items_shown(fs, cs, bl)
      %ixs : {Main.ends_all(Main.blame.print(Main.shown.rows(fs, cs, bl)), Main.blame.ends(_)) == True{} : Bool}
      shown_ends(Main.shown.rows(fs, cs, bl), Main.widest.col(Main.shown.rows(fs, cs, bl), 0n), Main.widest.col(Main.shown.rows(fs, cs, bl), 1n), Main.widest.col(Main.shown.rows(fs, cs, bl), 2n), Main.last_number(Main.shown.rows(fs, cs, bl)))

# What `blame` prints is one line for each line of the span asked, ending
# with that line, and the marker after a line without a newline.
def printed_lines(+fs: List<&2, Main.Full>, +cs: List<&2, String>, +rs: List<&2, Main.Row>, +span: Maybe<&2, Main.Wanted>, +out: List<&2, String>, e: {Main.blame.limited.r(fs, cs, rs, span) == Done{out} : Result<&2, &2, Main.Refused, List<&2, String>>}) -> {Main.ends_all(out, Main.blame.ends(Main.lines.items(Main.lines.asked(Main.lines.numbered(Main.rows.items(rs), 1n), span)))) == True{} : Bool}:
  printed(fs, cs, rs, span, Main.blame.span.r(rs, span), {==}, out, e)
