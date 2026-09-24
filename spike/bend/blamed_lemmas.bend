# What `blame` prints. The rows it attributes are the lines the walk reads,
# and it prints each of them once, numbered as the file numbers it.
import Base
import ./ops.bend as Ops
import ./merge.bend as Merge
import ./main.bend as Main
import ./store.bend as Store
import ./string_lemmas.bend as S
import ./diff_lemmas.bend as Diff
import ./tree.bend as Tree
import ./revision.bend as Rev
import ./bookmark.bend as Bm
import ./text.bend as T
import ./graph_lemmas.bend as GL
import ./anchor_lemmas.bend as AL
import ./target_lemmas.bend as TG
import ./fileat_lemmas.bend as FileAt
import ./blame_lemmas.bend as BlameL
import ./folder.bend as Folder

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

# The position
# ------------

def cur_held(+fs: List<&2, Main.Full>, +x: String, m: {Rev.member(Main.current_heads(Main.history(fs)), x) == True{} : Bool}) -> {Rev.member(Main.ids(fs), x) == True{} : Bool}:
  AL.or_cases({Rev.member(Main.ids(fs), x) == True{} : Bool}, Rev.member(Rev.heads(Main.history(fs)), x), Rev.member(Rev.without(Rev.heads(Main.history(fs)), Rev.superseded(Main.history(fs))), x),
    TG.cur_mem(Rev.heads(Main.history(fs)), Rev.without(Rev.heads(Main.history(fs)), Rev.superseded(Main.history(fs))), x, m),
    l => TG.head_held(fs, x, l),
    r => TG.head_held(fs, x, GL.without_sub(Rev.heads(Main.history(fs)), Rev.superseded(Main.history(fs)), x, r)))

def head_left(+fs: List<&2, Main.Full>, +bs: List<&2, Bm.Bookmark>, heads: List<&2, String>, +l: Maybe<&2, String>, e: {Main.the_head.r(fs, bs, heads) == Done{l} : Result<&2, &2, Main.Refused, Maybe<&2, String>>}, k: @x: String -> {Rev.member(heads, x) == True{} : Bool} -> {Rev.member(Main.ids(fs), x) == True{} : Bool}) -> {Main.left.ok(fs, l) == True{} : Bool}:
  match heads:
    case Nil{}:
      +d = done_eq(Maybe<&2, String>, None{}, l, e)
      %d : {Main.left.ok(fs, _) == True{} : Bool}
      {==}
    case +only <> Nil{}:
      +d = done_eq(Maybe<&2, String>, Some{only}, l, e)
      %d : {Main.left.ok(fs, _) == True{} : Bool}
      k(only, GL.member_head(only, Nil{}))
    case +x <> +y <> +r:
      Empty.absurd({Main.left.ok(fs, l) == True{} : Bool}, refuse(Maybe<&2, String>, Main.the_head.r(fs, bs, x <> y <> r), l, {==}, e))

def at_r(+f: String, p: Maybe<&2, String>, +t: Tree.Tree(), +h: Main.Held, e: {Main.wcf.at.r(f, p) == Done{h} : Result<&2, &2, Main.Refused, Main.Held>}, hf: {Tree.holds(t, f) == True{} : Bool}) -> {Main.held.ok(t, h) == True{} : Bool}:
  match p:
    case None{}:
      Empty.absurd({Main.held.ok(t, h) == True{} : Bool}, refuse(Main.Held, Main.wcf.at.r(f, None{}), h, {==}, e))
    case Some{path}:
      +d = done_eq(Main.Held, Main.Held{Some{f}, path}, h, e)
      %d : {Main.held.ok(t, _) == True{} : Bool}
      hf

def file_bind(+id: String, +bs: List<&2, Bm.Bookmark>, +t: Tree.Tree(), +sp: String, r: Result<&2, &2, Main.Refused, String>, +er: {Main.file_in.r(id, bs, sp, t) == r : Result<&2, &2, Main.Refused, String>}, +h: Main.Held, e: {Result.bind(&2, &2, Main.Refused, String, Main.Held, r, f => Main.wcf.path_of(t, f)) == Done{h} : Result<&2, &2, Main.Refused, Main.Held>}) -> {Main.held.ok(t, h) == True{} : Bool}:
  match r:
    case Fail{x}:
      Empty.absurd({Main.held.ok(t, h) == True{} : Bool}, fail_done(Main.Held, x, h, e))
    case Done{+f}:
      at_r(f, Tree.path(t, f), t, h, e, FileAt.file_ok(id, bs, sp, t, f, er))

def file_r(+bs: List<&2, Bm.Bookmark>, +t: Tree.Tree(), +sp: String, left: Maybe<&2, String>, +h: Main.Held, e: {Main.wcf.file.r(bs, t, sp, left) == Done{h} : Result<&2, &2, Main.Refused, Main.Held>}) -> {Main.held.ok(t, h) == True{} : Bool}:
  match left:
    case None{}:
      Empty.absurd({Main.held.ok(t, h) == True{} : Bool}, refuse(Main.Held, Main.wcf.file.r(bs, t, sp, None{}), h, {==}, e))
    case Some{+id}:
      file_bind(id, bs, t, sp, Main.file_in.r(id, bs, sp, t), {==}, h, e)

def several_bind(+id: String, +bs: List<&2, Bm.Bookmark>, +t: Tree.Tree(), +path: String, r: Result<&2, &2, Main.Refused, String>, +er: {Main.file_in.r(id, bs, path, t) == r : Result<&2, &2, Main.Refused, String>}, +h: Main.Held, e: {Result.bind(&2, &2, Main.Refused, String, Main.Held, r, f => Done{Main.Held{Some{f}, path}}) == Done{h} : Result<&2, &2, Main.Refused, Main.Held>}) -> {Main.held.ok(t, h) == True{} : Bool}:
  match r:
    case Fail{x}:
      Empty.absurd({Main.held.ok(t, h) == True{} : Bool}, fail_done(Main.Held, x, h, e))
    case Done{+f}:
      +d = done_eq(Main.Held, Main.Held{Some{f}, path}, h, e)
      %d : {Main.held.ok(t, _) == True{} : Bool}
      FileAt.file_ok(id, bs, path, t, f, er)

def several_r(+bs: List<&2, Bm.Bookmark>, +t: Tree.Tree(), +path: String, left: Maybe<&2, String>, +h: Main.Held, e: {Main.wcf.several.r(bs, t, path, left) == Done{h} : Result<&2, &2, Main.Refused, Main.Held>}) -> {Main.held.ok(t, h) == True{} : Bool}:
  match left:
    case None{}:
      Empty.absurd({Main.held.ok(t, h) == True{} : Bool}, refuse(Main.Held, Main.wcf.several.r(bs, t, path, None{}), h, {==}, e))
    case Some{+id}:
      several_bind(id, bs, t, path, Main.file_in.r(id, bs, path, t), {==}, h, e)

def at_mem(+t: Tree.Tree(), +path: String, at: List<&2, String>, ea: {Tree.at(t, path) == at : List<&2, String>}, +x: String, m: {Rev.member(at, x) == True{} : Bool}) -> {Rev.member(Tree.at(t, path), x) == True{} : Bool}:
  +es = Equal.sym(List<&2, String>, Tree.at(t, path), at, ea)
  %es : {Rev.member(_, x) == True{} : Bool}
  m

def path_r(+bs: List<&2, Bm.Bookmark>, +t: Tree.Tree(), +path: String, +left: Maybe<&2, String>, at: List<&2, String>, +ea: {Tree.at(t, path) == at : List<&2, String>}, +h: Main.Held, e: {Main.wcf.path.r(bs, t, path, left, at) == Done{h} : Result<&2, &2, Main.Refused, Main.Held>}) -> {Main.held.ok(t, h) == True{} : Bool}:
  match at:
    case Nil{}:
      +d = done_eq(Main.Held, Main.Held{None{}, path}, h, e)
      %d : {Main.held.ok(t, _) == True{} : Bool}
      +es = Equal.sym(List<&2, String>, Tree.at(t, path), Nil{}, ea)
      %es : {List.is_empty(&2, String, _) == True{} : Bool}
      {==}
    case +x <> rest:
      match rest:
        case Nil{}:
          +d = done_eq(Main.Held, Main.Held{Some{x}, path}, h, e)
          %d : {Main.held.ok(t, _) == True{} : Bool}
          FileAt.files_holds(t, x, FileAt.at_files(t, path, x, at_mem(t, path, [x], ea, x, GL.member_head(x, Nil{}))))
        case y <> r:
          several_r(bs, t, path, left, h, e)

def spelled_r(+bs: List<&2, Bm.Bookmark>, +t: Tree.Tree(), +sp: String, +left: Maybe<&2, String>, file: Bool, +h: Main.Held, e: {Main.wcf.spelled.r(bs, t, sp, left, file) == Done{h} : Result<&2, &2, Main.Refused, Main.Held>}) -> {Main.held.ok(t, h) == True{} : Bool}:
  match file:
    case True{}:
      file_r(bs, t, sp, left, h, e)
    case False{}:
      path_r(bs, t, Maybe.default(&2, String, T.strip_prefix(sp, "path:"), sp), left, Tree.at(t, Maybe.default(&2, String, T.strip_prefix(sp, "path:"), sp)), {==}, h, e)

def held_r(+bs: List<&2, Bm.Bookmark>, +t: Tree.Tree(), +sp: String, +left: Maybe<&2, String>, +h: Main.Held, e: {Main.wcf.held.r(bs, t, sp, left) == Done{h} : Result<&2, &2, Main.Refused, Main.Held>}) -> {Main.held.ok(t, h) == True{} : Bool}:
  spelled_r(bs, t, sp, left, String.starts_with(sp, "file:"), h, e)

def pos_tree(+fs: List<&2, Main.Full>, +bs: List<&2, Bm.Bookmark>, +sp: String, +l: Maybe<&2, String>, +t: Tree.Tree(), +hl: {Main.left.ok(fs, l) == True{} : Bool}, r: Result<&2, &2, Main.Refused, Main.Held>, +er: {Main.wcf.held.r(bs, t, sp, l) == r : Result<&2, &2, Main.Refused, Main.Held>}, +p: Main.Position, e: {Result.bind(&2, &2, Main.Refused, Main.Held, Main.Position, r, h => Done{Main.Position{l, t, h}}) == Done{p} : Result<&2, &2, Main.Refused, Main.Position>}) -> {Main.position.ok(fs, p) == True{} : Bool}:
  match r:
    case Fail{x}:
      Empty.absurd({Main.position.ok(fs, p) == True{} : Bool}, fail_done(Main.Position, x, p, e))
    case Done{+h}:
      +d = done_eq(Main.Position, Main.Position{l, t, h}, p, e)
      %d : {Main.position.ok(fs, _) == True{} : Bool}
      and_tt(Main.left.ok(fs, l), Main.held.ok(t, h), hl, held_r(bs, t, sp, l, h, er))

def pos_left(+fs: List<&2, Main.Full>, +bs: List<&2, Bm.Bookmark>, +sp: String, +l: Maybe<&2, String>, +hl: {Main.left.ok(fs, l) == True{} : Bool}, r: Result<&2, &2, Main.Refused, Tree.Tree()>, +p: Main.Position, e: {Result.bind(&2, &2, Main.Refused, Tree.Tree(), Main.Position, r, t => Main.wcf.position.tree(bs, sp, l, t)) == Done{p} : Result<&2, &2, Main.Refused, Main.Position>}) -> {Main.position.ok(fs, p) == True{} : Bool}:
  match r:
    case Fail{x}:
      Empty.absurd({Main.position.ok(fs, p) == True{} : Bool}, fail_done(Main.Position, x, p, e))
    case Done{+t}:
      pos_tree(fs, bs, sp, l, t, hl, Main.wcf.held.r(bs, t, sp, l), {==}, p, e)

def pos_head(+fs: List<&2, Main.Full>, +bs: List<&2, Bm.Bookmark>, +sp: String, r: Result<&2, &2, Main.Refused, Maybe<&2, String>>, +er: {Main.the_head.r(fs, bs, Main.current_heads(Main.history(fs))) == r : Result<&2, &2, Main.Refused, Maybe<&2, String>>}, +p: Main.Position, e: {Result.bind(&2, &2, Main.Refused, Maybe<&2, String>, Main.Position, r, l => Main.wcf.position.left(fs, bs, sp, l)) == Done{p} : Result<&2, &2, Main.Refused, Main.Position>}) -> {Main.position.ok(fs, p) == True{} : Bool}:
  match r:
    case Fail{x}:
      Empty.absurd({Main.position.ok(fs, p) == True{} : Bool}, fail_done(Main.Position, x, p, e))
    case Done{+l}:
      pos_left(fs, bs, sp, l, head_left(fs, bs, Main.current_heads(Main.history(fs)), l, er, x => m => cur_held(fs, x, m)), Main.tree.maybe.r(fs, l), p, e)

# `blame <path>` compares the folder with a revision the store holds, and
# the file it names there is one that revision's tree holds.
def position_ok(+fs: List<&2, Main.Full>, +bs: List<&2, Bm.Bookmark>, +sp: String, +p: Main.Position, e: {Main.wcf.position.r(fs, bs, sp) == Done{p} : Result<&2, &2, Main.Refused, Main.Position>}) -> {Main.position.ok(fs, p) == True{} : Bool}:
  pos_head(fs, bs, sp, Main.the_head.r(fs, bs, Main.current_heads(Main.history(fs))), {==}, p, e)

# The revision and file `blame <target> <path>` reads
# ----------------------------------------------------

def mdisc_f(m: Maybe<&2, Main.Full>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      Empty

def some_eq_f(-a: Main.Full, -b: Main.Full, h: {Some{a} == Some{b} : Maybe<&2, Main.Full>}) -> {a == b : Main.Full}:
  Equal.cong(Maybe<&2, Main.Full>, Main.Full, m => Maybe.default(&2, Main.Full, m, a), Some{a}, Some{b}, h)

def find_at(b: Bool, +i: String, +change: String, +parents: List<&2, String>, +supersedes: List<&2, String>, +author: String, +when: String, +revised_by: Maybe<&2, String>, +revised: Maybe<&2, String>, +facts: List<&2, Rev.Header>, +message: String, +rest: List<&2, Main.Full>, +x: String, +g: Main.Full, e: {Bool.pick(Maybe<&2, Main.Full>, b, Some{Main.Full{i, change, parents, supersedes, author, when, revised_by, revised, facts, message}}, Main.find(rest, x)) == Some{g} : Maybe<&2, Main.Full>}, ih: {Main.find(rest, x) == Some{g} : Maybe<&2, Main.Full>} -> {Rev.member(Main.ids(rest), Main.id_of(g)) == True{} : Bool}) -> {Rev.member(i <> Main.ids(rest), Main.id_of(g)) == True{} : Bool}:
  match b:
    case True{}:
      +d = some_eq_f(Main.Full{i, change, parents, supersedes, author, when, revised_by, revised, facts, message}, g, e)
      %d : {Rev.member(i <> Main.ids(rest), Main.id_of(_)) == True{} : Bool}
      GL.member_head(i, Main.ids(rest))
    case False{}:
      GL.member_tail(i, Main.ids(rest), Main.id_of(g), ih(e))

# What `find` finds is one of the revisions it looked through.
def find_mem(fs: List<&2, Main.Full>, +x: String, +g: Main.Full, e: {Main.find(fs, x) == Some{g} : Maybe<&2, Main.Full>}) -> {Rev.member(Main.ids(fs), Main.id_of(g)) == True{} : Bool}:
  match fs:
    case Nil{}:
      Empty.absurd({Rev.member(Main.ids(Nil{}), Main.id_of(g)) == True{} : Bool}, (%e : {mdisc_f(_) : Type} Unit{}))
    case Main.Full{+i, +change, +parents, +supersedes, +author, +when, +revised_by, +revised, +facts, +message} <> +rest:
      find_at(String.eq(i, x), i, change, parents, supersedes, author, when, revised_by, revised, facts, message, rest, x, g, e, h => find_mem(rest, x, g, h))

def found_mem(+fs: List<&2, Main.Full>, +id: String, m: Maybe<&2, Main.Full>, +em: {Main.find(fs, id) == m : Maybe<&2, Main.Full>}, +f: Main.Full, e: {Main.resolved.found.r(id, m) == Done{f} : Result<&2, &2, Main.Refused, Main.Full>}) -> {Rev.member(Main.ids(fs), Main.id_of(f)) == True{} : Bool}:
  match m:
    case None{}:
      Empty.absurd({Rev.member(Main.ids(fs), Main.id_of(f)) == True{} : Bool}, refuse(Main.Full, Main.resolved.found.r(id, None{}), f, {==}, e))
    case Some{+g}:
      +d = done_eq(Main.Full, g, f, e)
      %d : {Rev.member(Main.ids(fs), Main.id_of(_)) == True{} : Bool}
      find_mem(fs, id, g, em)

def resolved_of_mem(+fs: List<&2, Main.Full>, r: Result<&2, &2, String, String>, +f: Main.Full, e: {Main.resolved.of.r(fs, r) == Done{f} : Result<&2, &2, Main.Refused, Main.Full>}) -> {Rev.member(Main.ids(fs), Main.id_of(f)) == True{} : Bool}:
  match r:
    case Fail{x}:
      Empty.absurd({Rev.member(Main.ids(fs), Main.id_of(f)) == True{} : Bool}, fail_done(Main.Full, Main.Refused{1, x}, f, e))
    case Done{+id}:
      found_mem(fs, id, Main.find(fs, id), {==}, f, e)

# A target resolves to a revision the store holds.
def resolved_mem(+fs: List<&2, Main.Full>, +bs: List<&2, Bm.Bookmark>, +target: String, +f: Main.Full, e: {Main.resolved.r(fs, bs, target) == Done{f} : Result<&2, &2, Main.Refused, Main.Full>}) -> {Rev.member(Main.ids(fs), Main.id_of(f)) == True{} : Bool}:
  resolved_of_mem(fs, Main.resolve(fs, bs, target), f, e)

def lines_ok(+x: String, k: Maybe<&2, Tree.FileKind>, +u: Unit, e: {Main.lines_only.r(x, k) == Done{u} : Result<&2, &2, Main.Refused, Unit>}) -> {Main.kind.has_lines(k) == True{} : Bool}:
  match k:
    case None{}:
      {==}
    case Some{kd}:
      match kd:
        case Tree.Lines{}:
          {==}
        case Tree.Whole{}:
          Empty.absurd({Main.kind.has_lines(Some{Tree.Whole{}}) == True{} : Bool}, refuse(Unit, Main.lines_only.r(x, Some{Tree.Whole{}}), u, {==}, e))
        case Tree.Link{}:
          Empty.absurd({Main.kind.has_lines(Some{Tree.Link{}}) == True{} : Bool}, refuse(Unit, Main.lines_only.r(x, Some{Tree.Link{}}), u, {==}, e))

def pk_file(+fs: List<&2, Main.Full>, +id: String, +hm: {Rev.member(Main.ids(fs), id) == True{} : Bool}, +t: Tree.Tree(), +file: String, +sp: String, +et: {Main.tree.r(fs, id) == Done{t} : Result<&2, &2, Main.Refused, Tree.Tree()>}, +hh: {Tree.holds(t, file) == True{} : Bool}, r: Result<&2, &2, Main.Refused, Unit>, +er: {Main.lines_only.r(Maybe.default(&2, String, Tree.path(t, file), sp), Tree.kind(t, file)) == r : Result<&2, &2, Main.Refused, Unit>}, +p: Main.Picked, e: {Result.bind(&2, &2, Main.Refused, Unit, Main.Picked, r, u => Done{Main.Picked{id, file}}) == Done{p} : Result<&2, &2, Main.Refused, Main.Picked>}) -> {Main.picked.ok(fs, p) == True{} : Bool}:
  match r:
    case Fail{x}:
      Empty.absurd({Main.picked.ok(fs, p) == True{} : Bool}, fail_done(Main.Picked, x, p, e))
    case Done{+u}:
      +d = done_eq(Main.Picked, Main.Picked{id, file}, p, e)
      %d : {Main.picked.ok(fs, _) == True{} : Bool}
      +es = Equal.sym(Result<&2, &2, Main.Refused, Tree.Tree()>, Main.tree.r(fs, id), Done{t}, et)
      %es : {Bool.and(Rev.member(Main.ids(fs), id), Main.tree.has_lines(_, file)) == True{} : Bool}
      and_tt(Rev.member(Main.ids(fs), id), Bool.and(Tree.holds(t, file), Main.kind.has_lines(Tree.kind(t, file))), hm,
        and_tt(Tree.holds(t, file), Main.kind.has_lines(Tree.kind(t, file)), hh, lines_ok(Maybe.default(&2, String, Tree.path(t, file), sp), Tree.kind(t, file), u, er)))

def pk_tree(+fs: List<&2, Main.Full>, +id: String, +hm: {Rev.member(Main.ids(fs), id) == True{} : Bool}, +bs: List<&2, Bm.Bookmark>, +sp: String, +t: Tree.Tree(), +et: {Main.tree.r(fs, id) == Done{t} : Result<&2, &2, Main.Refused, Tree.Tree()>}, r: Result<&2, &2, Main.Refused, String>, +er: {Main.file_in.r(id, bs, sp, t) == r : Result<&2, &2, Main.Refused, String>}, +p: Main.Picked, e: {Result.bind(&2, &2, Main.Refused, String, Main.Picked, r, file => Main.blame.picked.file(t, sp, id, file)) == Done{p} : Result<&2, &2, Main.Refused, Main.Picked>}) -> {Main.picked.ok(fs, p) == True{} : Bool}:
  match r:
    case Fail{x}:
      Empty.absurd({Main.picked.ok(fs, p) == True{} : Bool}, fail_done(Main.Picked, x, p, e))
    case Done{+file}:
      pk_file(fs, id, hm, t, file, sp, et, FileAt.file_ok(id, bs, sp, t, file, er), Main.lines_only.r(Maybe.default(&2, String, Tree.path(t, file), sp), Tree.kind(t, file)), {==}, p, e)

def pk_full(+fs: List<&2, Main.Full>, +id: String, +hm: {Rev.member(Main.ids(fs), id) == True{} : Bool}, +bs: List<&2, Bm.Bookmark>, +sp: String, r: Result<&2, &2, Main.Refused, Tree.Tree()>, +er: {Main.tree.r(fs, id) == r : Result<&2, &2, Main.Refused, Tree.Tree()>}, +p: Main.Picked, e: {Result.bind(&2, &2, Main.Refused, Tree.Tree(), Main.Picked, r, t => Main.blame.picked.tree(bs, sp, id, t)) == Done{p} : Result<&2, &2, Main.Refused, Main.Picked>}) -> {Main.picked.ok(fs, p) == True{} : Bool}:
  match r:
    case Fail{x}:
      Empty.absurd({Main.picked.ok(fs, p) == True{} : Bool}, fail_done(Main.Picked, x, p, e))
    case Done{+t}:
      pk_tree(fs, id, hm, bs, sp, t, er, Main.file_in.r(id, bs, sp, t), {==}, p, e)

def pk_r(+fs: List<&2, Main.Full>, +bs: List<&2, Bm.Bookmark>, +target: String, +sp: String, r: Result<&2, &2, Main.Refused, Main.Full>, +er: {Main.resolved.r(fs, bs, target) == r : Result<&2, &2, Main.Refused, Main.Full>}, +p: Main.Picked, e: {Result.bind(&2, &2, Main.Refused, Main.Full, Main.Picked, r, f => Main.blame.picked.full(fs, bs, sp, Main.id_of(f))) == Done{p} : Result<&2, &2, Main.Refused, Main.Picked>}) -> {Main.picked.ok(fs, p) == True{} : Bool}:
  match r:
    case Fail{x}:
      Empty.absurd({Main.picked.ok(fs, p) == True{} : Bool}, fail_done(Main.Picked, x, p, e))
    case Done{+f}:
      pk_full(fs, Main.id_of(f), resolved_mem(fs, bs, target, f, er), bs, sp, Main.tree.r(fs, Main.id_of(f)), {==}, p, e)

# `blame <target> <path>` reads a revision the store holds, and a file
# with lines that revision's tree holds.
def picked_ok(+fs: List<&2, Main.Full>, +bs: List<&2, Bm.Bookmark>, +target: String, +sp: String, +p: Main.Picked, e: {Main.blame.picked.r(fs, bs, target, sp) == Done{p} : Result<&2, &2, Main.Refused, Main.Picked>}) -> {Main.picked.ok(fs, p) == True{} : Bool}:
  pk_r(fs, bs, target, sp, Main.resolved.r(fs, bs, target), {==}, p, e)

# What `blame` prints
# -------------------

def sniff(+path: String, +bs: List<&2, U32>, b: Bool, +eb: {Folder.is_text(bs) == b : Bool}, +u: Unit, e: {Main.wcf.sniffed.r(path, b) == Done{u} : Result<&2, &2, Main.Refused, Unit>}) -> {Folder.is_text(bs) == True{} : Bool}:
  match b:
    case True{}:
      eb
    case False{}:
      Empty.absurd({Folder.is_text(bs) == True{} : Bool}, refuse(Unit, Main.wcf.sniffed.r(path, False{}), u, {==}, e))

def folder_kind(+path: String, k: Maybe<&2, Tree.FileKind>, +bs: List<&2, U32>, +u: Unit, e: {Main.wcf.kind.r(path, k, bs) == Done{u} : Result<&2, &2, Main.Refused, Unit>}) -> {Main.folder.has_lines(k, bs) == True{} : Bool}:
  match k:
    case Some{kd}:
      lines_ok(path, Some{kd}, u, e)
    case None{}:
      sniff(path, bs, Folder.is_text(bs), {==}, u, e)

def fold_ends(+rows: List<&2, Main.Row>, +bs: List<&2, U32>, +span: Maybe<&2, Main.Wanted>, +out: List<&2, String>, pl: {Main.ends_all(out, Main.blame.ends(Main.lines.items(Main.lines.asked(Main.lines.numbered(Main.rows.items(Main.wc.overlay(rows, Ops.from_text(Folder.lossy(bs)))), 1n), span)))) == True{} : Bool}) -> {Main.ends_all(out, Main.blame.ends(Main.lines.items(Main.lines.asked(Main.lines.numbered(Ops.from_text(Folder.lossy(bs)), 1n), span)))) == True{} : Bool}:
  +fl = BlameL.folder_lines(rows, Folder.lossy(bs))
  %fl : {Main.ends_all(out, Main.blame.ends(Main.lines.items(Main.lines.asked(Main.lines.numbered(_, 1n), span)))) == True{} : Bool}
  pl

def fold_bind(+fs: List<&2, Main.Full>, +path: String, +k: Maybe<&2, Tree.FileKind>, +bs: List<&2, U32>, +rows: List<&2, Main.Row>, +span: Maybe<&2, Main.Wanted>, r: Result<&2, &2, Main.Refused, Unit>, +er: {Main.wcf.kind.r(path, k, bs) == r : Result<&2, &2, Main.Refused, Unit>}, +out: List<&2, String>, e: {Result.bind(&2, &2, Main.Refused, Unit, List<&2, String>, r, u => Main.blame.limited.r(fs, Main.changes(fs), Main.wc.overlay(rows, Ops.from_text(Folder.lossy(bs))), span)) == Done{out} : Result<&2, &2, Main.Refused, List<&2, String>>}) -> {Bool.and(Main.folder.has_lines(k, bs), Main.ends_all(out, Main.blame.ends(Main.lines.items(Main.lines.asked(Main.lines.numbered(Ops.from_text(Folder.lossy(bs)), 1n), span))))) == True{} : Bool}:
  match r:
    case Fail{x}:
      Empty.absurd({Bool.and(Main.folder.has_lines(k, bs), Main.ends_all(out, Main.blame.ends(Main.lines.items(Main.lines.asked(Main.lines.numbered(Ops.from_text(Folder.lossy(bs)), 1n), span))))) == True{} : Bool}, fail_done(List<&2, String>, x, out, e))
    case Done{+u}:
      and_tt(Main.folder.has_lines(k, bs), Main.ends_all(out, Main.blame.ends(Main.lines.items(Main.lines.asked(Main.lines.numbered(Ops.from_text(Folder.lossy(bs)), 1n), span)))), folder_kind(path, k, bs, u, er),
        fold_ends(rows, bs, span, out, printed_lines(fs, Main.changes(fs), Main.wc.overlay(rows, Ops.from_text(Folder.lossy(bs))), span, out, e)))

# `blame <path>` prints the folder's text: a file with lines, one printed
# line for each line of the span, ending with it.
def folder_printed(+fs: List<&2, Main.Full>, +path: String, +k: Maybe<&2, Tree.FileKind>, +bs: List<&2, U32>, +rows: List<&2, Main.Row>, +span: Maybe<&2, Main.Wanted>, +out: List<&2, String>, e: {Main.blame.folder.r(fs, path, k, bs, rows, span) == Done{out} : Result<&2, &2, Main.Refused, List<&2, String>>}) -> {Bool.and(Main.folder.has_lines(k, bs), Main.ends_all(out, Main.blame.ends(Main.lines.items(Main.lines.asked(Main.lines.numbered(Ops.from_text(Folder.lossy(bs)), 1n), span))))) == True{} : Bool}:
  fold_bind(fs, path, k, bs, rows, span, Main.wcf.kind.r(path, k, bs), {==}, out, e)

def done_eq_s(-a: List<&2, Ops.Item>, -b: List<&2, Ops.Item>, h: {Done{a} == Done{b} : Result<&2, &2, String, List<&2, Ops.Item>>}) -> {a == b : List<&2, Ops.Item>}:
  Equal.cong(Result<&2, &2, String, List<&2, Ops.Item>>, List<&2, Ops.Item>, r => Result.default(&2, &2, String, List<&2, Ops.Item>, r, a), Done{a}, Done{b}, h)

def rec_bind(+fs: List<&2, Main.Full>, +all: List<&2, Store.Doc>, +id: String, +file: String, +span: Maybe<&2, Main.Wanted>, r: Result<&2, &2, Main.Refused, List<&2, Main.Row>>, +er: {Main.blame.rows.r(Main.oldest_of(fs, Some{id}), all, id, file) == r : Result<&2, &2, Main.Refused, List<&2, Main.Row>>}, +out: List<&2, String>, e: {Result.bind(&2, &2, Main.Refused, List<&2, Main.Row>, List<&2, String>, r, rows => Main.blame.limited.r(fs, Main.changes(fs), rows, span)) == Done{out} : Result<&2, &2, Main.Refused, List<&2, String>>}, +w: List<&2, Ops.Item>, +ew: {Main.walked(Main.oldest_of(fs, Some{id}), all, id, file) == Done{w} : Result<&2, &2, String, List<&2, Ops.Item>>}) -> {Main.ends_all(out, Main.blame.ends(Main.lines.items(Main.lines.asked(Main.lines.numbered(w, 1n), span)))) == True{} : Bool}:
  match r:
    case Fail{x}:
      Empty.absurd({Main.ends_all(out, Main.blame.ends(Main.lines.items(Main.lines.asked(Main.lines.numbered(w, 1n), span)))) == True{} : Bool}, fail_done(List<&2, String>, x, out, e))
    case Done{+rs}:
      +rw = rows_walked(Main.oldest_of(fs, Some{id}), all, id, file, rs, er)
      +dw = done_eq_s(Main.rows.items(rs), w, Equal.trans(Result<&2, &2, String, List<&2, Ops.Item>>, Done{Main.rows.items(rs)}, Main.walked(Main.oldest_of(fs, Some{id}), all, id, file), Done{w}, Equal.sym(Result<&2, &2, String, List<&2, Ops.Item>>, Main.walked(Main.oldest_of(fs, Some{id}), all, id, file), Done{Main.rows.items(rs)}, rw), ew))
      %dw : {Main.ends_all(out, Main.blame.ends(Main.lines.items(Main.lines.asked(Main.lines.numbered(_, 1n), span)))) == True{} : Bool}
      printed_lines(fs, Main.changes(fs), rs, span, out, e)

# `blame <target> <path>` prints the file the walk reads: one printed line
# for each line of the span, ending with it.
def recorded_printed(+fs: List<&2, Main.Full>, +all: List<&2, Store.Doc>, +id: String, +file: String, +span: Maybe<&2, Main.Wanted>, +out: List<&2, String>, e: {Main.blame.recorded.r(fs, all, id, file, span) == Done{out} : Result<&2, &2, Main.Refused, List<&2, String>>}, +w: List<&2, Ops.Item>, +ew: {Main.walked(Main.oldest_of(fs, Some{id}), all, id, file) == Done{w} : Result<&2, &2, String, List<&2, Ops.Item>>}) -> {Main.ends_all(out, Main.blame.ends(Main.lines.items(Main.lines.asked(Main.lines.numbered(w, 1n), span)))) == True{} : Bool}:
  rec_bind(fs, all, id, file, span, Main.blame.rows.r(Main.oldest_of(fs, Some{id}), all, id, file), {==}, out, e, w, ew)

# `blame`'s arguments
# -------------------

def rdisc_s(-A: Data, r: Result<&2, &2, String, A>) -> Type:
  match r:
    case Done{x}:
      Empty
    case Fail{e}:
      Unit

def fail_done_s(-A: Data, -e: String, -x: A, h: {Fail{e} == Done{x} : Result<&2, &2, String, A>}) -> Empty:
  %h : {rdisc_s(A, _) : Type}
  Unit{}

def done_eq_a(-a: Main.BlameAsked, -b: Main.BlameAsked, h: {Done{a} == Done{b} : Result<&2, &2, String, Main.BlameAsked>}) -> {a == b : Main.BlameAsked}:
  Equal.cong(Result<&2, &2, String, Main.BlameAsked>, Main.BlameAsked, r => Result.default(&2, &2, String, Main.BlameAsked, r, a), Done{a}, Done{b}, h)

def lapp_nil(xs: List<&2, String>) -> {List.append(&2, String, xs, Nil{}) == xs : List<&2, String>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> rest:
      Equal.cong(List<&2, String>, List<&2, String>, l => x <> l, List.append(&2, String, rest, Nil{}), rest, lapp_nil(rest))

def lapp_assoc(xs: List<&2, String>, +ys: List<&2, String>, +zs: List<&2, String>) -> {List.append(&2, String, List.append(&2, String, xs, ys), zs) == List.append(&2, String, xs, List.append(&2, String, ys, zs)) : List<&2, String>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> rest:
      Equal.cong(List<&2, String>, List<&2, String>, l => x <> l, List.append(&2, String, List.append(&2, String, rest, ys), zs), List.append(&2, String, rest, List.append(&2, String, ys, zs)), lapp_assoc(rest, ys, zs))

# Once a word is refused, the rest are not read.
def run_fail(args: List<&2, String>, +e: String, +want: Bool) -> {Main.basked.run(args, Main.BRead{Fail{e}, want}) == Main.BRead{Fail{e}, want} : Main.BRead}:
  match args:
    case Nil{}:
      {==}
    case w <> rest:
      run_fail(rest, e, want)

def run_word(f: Bool, +w: String, rest: List<&2, String>, +l: Maybe<&2, String>, +acc: List<&2, String>, +fin: Main.BlameAsked, e: {Main.basked.end(Main.basked.run(rest, Main.BRead{Main.basked.word(Main.BlameAsked{l, acc}, w, f), False{}})) == Done{fin} : Result<&2, &2, String, Main.BlameAsked>}, ih: {Main.basked.end(Main.basked.run(rest, Main.BRead{Done{Main.BlameAsked{l, List.append(&2, String, acc, [w])}}, False{}})) == Done{fin} : Result<&2, &2, String, Main.BlameAsked>} -> {fin == Main.BlameAsked{Main.bargs.lines(rest, False{}, l), List.append(&2, String, List.append(&2, String, acc, [w]), Main.bargs.words(rest, False{}))} : Main.BlameAsked}) -> {fin == Main.BlameAsked{Main.bargs.lines(rest, False{}, l), List.append(&2, String, acc, w <> Main.bargs.words(rest, False{}))} : Main.BlameAsked}:
  match f:
    case True{}:
      +m = "`" ++ w ++ "` is not an argument `blame` takes"
      Empty.absurd({fin == Main.BlameAsked{Main.bargs.lines(rest, False{}, l), List.append(&2, String, acc, w <> Main.bargs.words(rest, False{}))} : Main.BlameAsked},
        fail_done_s(Main.BlameAsked, m, fin, Equal.trans(Result<&2, &2, String, Main.BlameAsked>, Fail{m}, Main.basked.end(Main.basked.run(rest, Main.BRead{Fail{m}, False{}})), Done{fin},
          Equal.cong(Main.BRead, Result<&2, &2, String, Main.BlameAsked>, r => Main.basked.end(r), Main.BRead{Fail{m}, False{}}, Main.basked.run(rest, Main.BRead{Fail{m}, False{}}), Equal.sym(Main.BRead, Main.basked.run(rest, Main.BRead{Fail{m}, False{}}), Main.BRead{Fail{m}, False{}}, run_fail(rest, m, False{}))), e)))
    case False{}:
      Equal.trans(Main.BlameAsked, fin, Main.BlameAsked{Main.bargs.lines(rest, False{}, l), List.append(&2, String, List.append(&2, String, acc, [w]), Main.bargs.words(rest, False{}))}, Main.BlameAsked{Main.bargs.lines(rest, False{}, l), List.append(&2, String, acc, w <> Main.bargs.words(rest, False{}))},
        ih(e),
        Equal.cong(List<&2, String>, Main.BlameAsked, x => Main.BlameAsked{Main.bargs.lines(rest, False{}, l), x}, List.append(&2, String, List.append(&2, String, acc, [w]), Main.bargs.words(rest, False{})), List.append(&2, String, acc, w <> Main.bargs.words(rest, False{})), lapp_assoc(acc, [w], Main.bargs.words(rest, False{}))))

def run_plain(b: Bool, +w: String, rest: List<&2, String>, +l: Maybe<&2, String>, +acc: List<&2, String>, +fin: Main.BlameAsked, e: {Main.basked.end(Main.basked.run(rest, Main.basked.plain(Main.BlameAsked{l, acc}, w, b))) == Done{fin} : Result<&2, &2, String, Main.BlameAsked>}, ht: {Main.basked.end(Main.basked.run(rest, Main.BRead{Done{Main.BlameAsked{l, acc}}, True{}})) == Done{fin} : Result<&2, &2, String, Main.BlameAsked>} -> {fin == Main.BlameAsked{Main.bargs.lines(rest, True{}, l), List.append(&2, String, acc, Main.bargs.words(rest, True{}))} : Main.BlameAsked}, hf: {Main.basked.end(Main.basked.run(rest, Main.BRead{Done{Main.BlameAsked{l, List.append(&2, String, acc, [w])}}, False{}})) == Done{fin} : Result<&2, &2, String, Main.BlameAsked>} -> {fin == Main.BlameAsked{Main.bargs.lines(rest, False{}, l), List.append(&2, String, List.append(&2, String, acc, [w]), Main.bargs.words(rest, False{}))} : Main.BlameAsked}) -> {fin == Main.BlameAsked{Bool.pick(Maybe<&2, String>, b, Main.bargs.lines(rest, True{}, l), Main.bargs.lines(rest, False{}, l)), List.append(&2, String, acc, Bool.pick(List<&2, String>, b, Main.bargs.words(rest, True{}), w <> Main.bargs.words(rest, False{})))} : Main.BlameAsked}:
  match b:
    case True{}:
      ht(e)
    case False{}:
      run_word(String.starts_with(w, "-"), w, rest, l, acc, fin, e, hf)

# One pass over the arguments reads what their plain reading says: the
# last `--lines` value, and every other word after what was read before.
def run_ok(args: List<&2, String>, want: Bool, +l: Maybe<&2, String>, +acc: List<&2, String>, +fin: Main.BlameAsked, e: {Main.basked.end(Main.basked.run(args, Main.BRead{Done{Main.BlameAsked{l, acc}}, want})) == Done{fin} : Result<&2, &2, String, Main.BlameAsked>}) -> {fin == Main.BlameAsked{Main.bargs.lines(args, want, l), List.append(&2, String, acc, Main.bargs.words(args, want))} : Main.BlameAsked}:
  match args:
    case Nil{}:
      match want:
        case True{}:
          Empty.absurd({fin == Main.BlameAsked{Main.bargs.lines(Nil{}, True{}, l), List.append(&2, String, acc, Main.bargs.words(Nil{}, True{}))} : Main.BlameAsked}, fail_done_s(Main.BlameAsked, "`--lines` wants a span, as `<first>..<last>`", fin, e))
        case False{}:
          Equal.trans(Main.BlameAsked, fin, Main.BlameAsked{l, acc}, Main.BlameAsked{Main.bargs.lines(Nil{}, False{}, l), List.append(&2, String, acc, Main.bargs.words(Nil{}, False{}))},
            Equal.sym(Main.BlameAsked, Main.BlameAsked{l, acc}, fin, done_eq_a(Main.BlameAsked{l, acc}, fin, e)),
            Equal.cong(List<&2, String>, Main.BlameAsked, x => Main.BlameAsked{l, x}, acc, List.append(&2, String, acc, Nil{}), Equal.sym(List<&2, String>, List.append(&2, String, acc, Nil{}), acc, lapp_nil(acc))))
    case +w <> +rest:
      match want:
        case True{}:
          run_ok(rest, False{}, Some{w}, acc, fin, e)
        case False{}:
          run_plain(String.eq(w, "--lines"), w, rest, l, acc, fin, e, h => run_ok(rest, True{}, l, acc, fin, h), h => run_ok(rest, False{}, l, List.append(&2, String, acc, [w]), fin, h))

def span_said(+named: Maybe<&2, String>, +path: String, +lines: Maybe<&2, String>, r: Result<&2, &2, Main.Refused, Maybe<&2, Main.Wanted>>, +er: {Main.blame.span.of(lines) == r : Result<&2, &2, Main.Refused, Maybe<&2, Main.Wanted>>}, +b: Main.Blame, e: {Main.blame.asked.span(named, path, r) == Done{b} : Result<&2, &2, Main.Refused, Main.Blame>}) -> {Main.BSaid{Main.blame.names(named, path), Main.blame.span.of(lines)} == Main.blame.said(b) : Main.BSaid}:
  match r:
    case Fail{x}:
      Empty.absurd({Main.BSaid{Main.blame.names(named, path), Main.blame.span.of(lines)} == Main.blame.said(b) : Main.BSaid}, fail_done(Main.Blame, x, b, e))
    case Done{+sp}:
      +d = done_eq(Main.Blame, Main.Blame{named, path, sp}, b, e)
      %d : {Main.BSaid{Main.blame.names(named, path), Main.blame.span.of(lines)} == Main.blame.said(_) : Main.BSaid}
      Equal.cong(Result<&2, &2, Main.Refused, Maybe<&2, Main.Wanted>>, Main.BSaid, x => Main.BSaid{Main.blame.names(named, path), x}, Main.blame.span.of(lines), Done{sp}, er)

def first_said(+x: String, +lines: Maybe<&2, String>, t: Bool, +b: Main.Blame, e: {Main.blame.first.r(x, lines, t) == Done{b} : Result<&2, &2, Main.Refused, Main.Blame>}) -> {Main.BSaid{[x], Main.blame.span.of(lines)} == Main.blame.said(b) : Main.BSaid}:
  match t:
    case True{}:
      Empty.absurd({Main.BSaid{[x], Main.blame.span.of(lines)} == Main.blame.said(b) : Main.BSaid}, refuse(Main.Blame, Main.blame.first.r(x, lines, True{}), b, {==}, e))
    case False{}:
      span_said(None{}, x, lines, Main.blame.span.of(lines), {==}, b, e)

# What is left once the flags are read is the target and the path, in order.
def split_said(+bs: List<&2, Bm.Bookmark>, +lines: Maybe<&2, String>, rest: List<&2, String>, +b: Main.Blame, e: {Main.blame.split.r(bs, lines, rest) == Done{b} : Result<&2, &2, Main.Refused, Main.Blame>}) -> {Main.BSaid{rest, Main.blame.span.of(lines)} == Main.blame.said(b) : Main.BSaid}:
  match rest:
    case Nil{}:
      Empty.absurd({Main.BSaid{Nil{}, Main.blame.span.of(lines)} == Main.blame.said(b) : Main.BSaid}, refuse(Main.Blame, Main.blame.split.r(bs, lines, Nil{}), b, {==}, e))
    case +x <> r1:
      match r1:
        case Nil{}:
          first_said(x, lines, Main.could_be_target(bs, x), b, e)
        case +y <> r2:
          match r2:
            case Nil{}:
              span_said(Some{x}, y, lines, Main.blame.span.of(lines), {==}, b, e)
            case +z <> +r3:
              Empty.absurd({Main.BSaid{x <> y <> z <> r3, Main.blame.span.of(lines)} == Main.blame.said(b) : Main.BSaid}, refuse(Main.Blame, Main.blame.split.r(bs, lines, x <> y <> z <> r3), b, {==}, e))

def ba_lines(a: Main.BlameAsked) -> Maybe<&2, String>:
  match a:
    case Main.BlameAsked{l, r}:
      l

def ba_rest(a: Main.BlameAsked) -> List<&2, String>:
  match a:
    case Main.BlameAsked{l, r}:
      r

def asked_said(+bs: List<&2, Bm.Bookmark>, +args: List<&2, String>, r: Result<&2, &2, String, Main.BlameAsked>, +er: {Main.basked.go(args) == r : Result<&2, &2, String, Main.BlameAsked>}, +b: Main.Blame, e: {Main.blame.asked.r(bs, r) == Done{b} : Result<&2, &2, Main.Refused, Main.Blame>}) -> {Main.bargs.said(args) == Main.blame.said(b) : Main.BSaid}:
  match r:
    case Fail{x}:
      Empty.absurd({Main.bargs.said(args) == Main.blame.said(b) : Main.BSaid}, fail_done(Main.Blame, Main.Refused{2, x}, b, e))
    case Done{a}:
      match a:
        case Main.BlameAsked{+lines, +rest}:
          +ro = run_ok(args, False{}, None{}, Nil{}, Main.BlameAsked{lines, rest}, er)
          +el = Equal.cong(Main.BlameAsked, Maybe<&2, String>, x => ba_lines(x), Main.BlameAsked{lines, rest}, Main.BlameAsked{Main.bargs.lines(args, False{}, None{}), Main.bargs.words(args, False{})}, ro)
          +erest = Equal.cong(Main.BlameAsked, List<&2, String>, x => ba_rest(x), Main.BlameAsked{lines, rest}, Main.BlameAsked{Main.bargs.lines(args, False{}, None{}), Main.bargs.words(args, False{})}, ro)
          %el : {Main.BSaid{Main.bargs.words(args, False{}), Main.blame.span.of(_)} == Main.blame.said(b) : Main.BSaid}
          %erest : {Main.BSaid{_, Main.blame.span.of(lines)} == Main.blame.said(b) : Main.BSaid}
          split_said(bs, lines, rest, b, e)

# `blame` reads its arguments as their plain reading says.
def args_said(+bs: List<&2, Bm.Bookmark>, +args: List<&2, String>, +b: Main.Blame, e: {Main.blame.args.r(bs, args) == Done{b} : Result<&2, &2, Main.Refused, Main.Blame>}) -> {Main.bargs.said(args) == Main.blame.said(b) : Main.BSaid}:
  asked_said(bs, args, Main.basked.go(args), {==}, b, e)

# The folder's file
# -----------------

def kind_refl(x: Tree.FileKind) -> {Tree.kind_eq(x, x) == True{} : Bool}:
  match x:
    case Tree.Lines{}:
      {==}
    case Tree.Whole{}:
      {==}
    case Tree.Link{}:
      {==}

def same_refl(m: Maybe<&2, Tree.FileKind>) -> {Main.kind.same(m, m) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{x}:
      kind_refl(x)

def ck_lines(+found: List<&2, Folder.Found>, +path: String, +t: Tree.Tree(), +file: Maybe<&2, String>, +p: String, +rn: Bool, +n: Nat, +em: {Main.found_at(found, path) == Some{Folder.Found.File{p, rn, n}} : Maybe<&2, Folder.Found>}, r: Result<&2, &2, Main.Refused, Unit>, +er: {Main.lines_only.r(path, Main.wcf.kind_of(t, file)) == r : Result<&2, &2, Main.Refused, Unit>}, +k: Maybe<&2, Tree.FileKind>, e: {Result.bind(&2, &2, Main.Refused, Unit, Maybe<&2, Tree.FileKind>, r, u => Done{Main.wcf.kind_of(t, file)}) == Done{k} : Result<&2, &2, Main.Refused, Maybe<&2, Tree.FileKind>>}) -> {Main.checked.ok(found, path, t, file, k) == True{} : Bool}:
  match r:
    case Fail{x}:
      Empty.absurd({Main.checked.ok(found, path, t, file, k) == True{} : Bool}, fail_done(Maybe<&2, Tree.FileKind>, x, k, e))
    case Done{+u}:
      +d = done_eq(Maybe<&2, Tree.FileKind>, Main.wcf.kind_of(t, file), k, e)
      %d : {Main.checked.ok(found, path, t, file, _) == True{} : Bool}
      +ef = Equal.sym(Maybe<&2, Folder.Found>, Main.found_at(found, path), Some{Folder.Found.File{p, rn, n}}, em)
      %ef : {Bool.and(Main.found.regular(_), Bool.and(Main.kind.same(Main.wcf.kind_of(t, file), Main.wcf.kind_of(t, file)), Main.kind.has_lines(Main.wcf.kind_of(t, file)))) == True{} : Bool}
      and_tt(Main.kind.same(Main.wcf.kind_of(t, file), Main.wcf.kind_of(t, file)), Main.kind.has_lines(Main.wcf.kind_of(t, file)), same_refl(Main.wcf.kind_of(t, file)), lines_ok(path, Main.wcf.kind_of(t, file), u, er))

def ck_found(+found: List<&2, Folder.Found>, +path: String, +t: Tree.Tree(), +file: Maybe<&2, String>, m: Maybe<&2, Folder.Found>, +em: {Main.found_at(found, path) == m : Maybe<&2, Folder.Found>}, +k: Maybe<&2, Tree.FileKind>, e: {Result.bind(&2, &2, Main.Refused, Folder.Found, Maybe<&2, Tree.FileKind>, Main.wcf.found.r(path, m), f => Result.bind(&2, &2, Main.Refused, Unit, Maybe<&2, Tree.FileKind>, Main.wcf.link.r(path, f), u => Result.bind(&2, &2, Main.Refused, Unit, Maybe<&2, Tree.FileKind>, Main.lines_only.r(path, Main.wcf.kind_of(t, file)), v => Done{Main.wcf.kind_of(t, file)}))) == Done{k} : Result<&2, &2, Main.Refused, Maybe<&2, Tree.FileKind>>}) -> {Main.checked.ok(found, path, t, file, k) == True{} : Bool}:
  match m:
    case None{}:
      Empty.absurd({Main.checked.ok(found, path, t, file, k) == True{} : Bool}, refuse(Maybe<&2, Tree.FileKind>, Result.bind(&2, &2, Main.Refused, Folder.Found, Maybe<&2, Tree.FileKind>, Main.wcf.found.r(path, None{}), f => Result.bind(&2, &2, Main.Refused, Unit, Maybe<&2, Tree.FileKind>, Main.wcf.link.r(path, f), u => Result.bind(&2, &2, Main.Refused, Unit, Maybe<&2, Tree.FileKind>, Main.lines_only.r(path, Main.wcf.kind_of(t, file)), v => Done{Main.wcf.kind_of(t, file)}))), k, {==}, e))
    case Some{f}:
      match f:
        case Folder.Found.File{+p, +rn, +n}:
          ck_lines(found, path, t, file, p, rn, n, em, Main.lines_only.r(path, Main.wcf.kind_of(t, file)), {==}, k, e)
        case Folder.Found.Link{p, tg}:
          Empty.absurd({Main.checked.ok(found, path, t, file, k) == True{} : Bool}, refuse(Maybe<&2, Tree.FileKind>, Result.bind(&2, &2, Main.Refused, Folder.Found, Maybe<&2, Tree.FileKind>, Main.wcf.found.r(path, Some{Folder.Found.Link{p, tg}}), f => Result.bind(&2, &2, Main.Refused, Unit, Maybe<&2, Tree.FileKind>, Main.wcf.link.r(path, f), u => Result.bind(&2, &2, Main.Refused, Unit, Maybe<&2, Tree.FileKind>, Main.lines_only.r(path, Main.wcf.kind_of(t, file)), v => Done{Main.wcf.kind_of(t, file)}))), k, {==}, e))

# `blame <path>` reads a file the folder holds at the path, not a link, and
# goes on with the kind the position gives it, one with lines.
def checked_ok(+path: String, +t: Tree.Tree(), +file: Maybe<&2, String>, +found: List<&2, Folder.Found>, +k: Maybe<&2, Tree.FileKind>, e: {Main.wcf.checked.r(path, t, file, found) == Done{k} : Result<&2, &2, Main.Refused, Maybe<&2, Tree.FileKind>>}) -> {Main.checked.ok(found, path, t, file, k) == True{} : Bool}:
  ck_found(found, path, t, file, Main.found_at(found, path), {==}, k, e)
