# `blame` over the folder attributes the folder's lines. It lays the
# folder's file over the lines history holds (`laid`), and walks what is
# laid alongside those lines' origins: a line that stayed keeps its author,
# one that arrived is the folder's own. The rows it prints are the folder's
# lines, each once and in order.
import Base
import ./ops.bend as Ops
import ./cursor_spec.bend as Cursor
import ./commands.bend as Main
import ./similar.bend as Sim
import ./composition_lemmas.bend as Comp
import ./string_lemmas.bend as S
import ./diff_lemmas.bend as Diff
import ./similar_lemmas.bend as SimL
import ./laid_lemmas.bend as LaidL

def ldisc(xs: List<&2, Ops.Item>) -> Type:
  match xs:
    case Nil{}:
      Unit
    case x <> rest:
      Empty

def nil_cons(-x: Ops.Item, -rest: List<&2, Ops.Item>, e: {Nil{} == x <> rest : List<&2, Ops.Item>}) -> Empty:
  %e : {ldisc(_) : Type}
  Unit{}

def ltail(l: List<&2, Ops.Item>) -> List<&2, Ops.Item>:
  match l:
    case Nil{}:
      Nil{}
    case x <> rest:
      rest

def tail_eq(-x: Ops.Item, -xs: List<&2, Ops.Item>, -y: Ops.Item, -ys: List<&2, Ops.Item>, e: {x <> xs == y <> ys : List<&2, Ops.Item>}) -> {xs == ys : List<&2, Ops.Item>}:
  Equal.cong(List<&2, Ops.Item>, List<&2, Ops.Item>, l => ltail(l), x <> xs, y <> ys, e)

# One laid line, walked alongside the origins of what history holds.
def put_items(plus: Bool, +by: Maybe<&2, String>, +it: Ops.Item, origins: List<&2, Main.Row>, minus: Bool, +s: String, +rest: List<&2, Main.Laid>, ep: {String.eq(s, "+") == plus : Bool}, em: {String.eq(s, "-") == minus : Bool}, h: {Main.rows.items(origins) == Main.laid.side(plus, it, Main.laid.old(rest)) : List<&2, Ops.Item>}, ih: @o2: List<&2, Main.Row> -> {Main.rows.items(o2) == Main.laid.old(rest) : List<&2, Ops.Item>} -> {Main.rows.items(Main.overlay(rest, o2, by)) == Main.laid.new(rest) : List<&2, Ops.Item>}) -> {Main.rows.items(Main.overlay.put(plus, by, it, origins, minus, Main.overlay(rest, Main.overlay.next(plus, origins), by))) == Main.laid.side(minus, it, Main.laid.new(rest)) : List<&2, Ops.Item>}:
  match plus:
    case True{}:
      (%Equal.sym(Bool, minus, False{}, Equal.trans(Bool, minus, String.eq(s, "-"), False{}, Equal.sym(Bool, String.eq(s, "-"), minus, em), (%Equal.sym(String, s, "+", S.eq_true(s, "+", ep)) : {String.eq(_, "-") == False{} : Bool}
        {==}))) : {it <> Main.rows.items(Main.overlay(rest, origins, by)) == Main.laid.side(_, it, Main.laid.new(rest)) : List<&2, Ops.Item>}
        Equal.cong(List<&2, Ops.Item>, List<&2, Ops.Item>, l => it <> l, Main.rows.items(Main.overlay(rest, origins, by)), Main.laid.new(rest), ih(origins, h)))
    case False{}:
      match origins:
        case Nil{}:
          Empty.absurd({Main.rows.items(Nil{}) == Main.laid.side(minus, it, Main.laid.new(rest)) : List<&2, Ops.Item>}, nil_cons(it, Main.laid.old(rest), h))
        case Main.Row{b, i} <> +more:
          match minus:
            case True{}:
              ih(more, tail_eq(i, Main.rows.items(more), it, Main.laid.old(rest), h))
            case False{}:
              Equal.cong(List<&2, Ops.Item>, List<&2, Ops.Item>, l => it <> l, Main.rows.items(Main.overlay(rest, more, by)), Main.laid.new(rest), ih(more, tail_eq(i, Main.rows.items(more), it, Main.laid.old(rest), h)))

# Walked alongside origins for exactly the lines history holds, what is
# laid attributes exactly the lines that stay and arrive.
def overlay_items(ls: List<&2, Main.Laid>, +origins: List<&2, Main.Row>, +by: Maybe<&2, String>, h: {Main.rows.items(origins) == Main.laid.old(ls) : List<&2, Ops.Item>}) -> {Main.rows.items(Main.overlay(ls, origins, by)) == Main.laid.new(ls) : List<&2, Ops.Item>}:
  match ls:
    case Nil{}:
      {==}
    case Main.Laid{+s, +it} <> +rest:
      put_items(String.eq(s, "+"), by, it, origins, String.eq(s, "-"), s, rest, {==}, {==}, h, o2 => h2 => overlay_items(rest, o2, by, h2))

# Where `similar`'s search finds nothing to change, the two sides agree.
def diff_of_none(ops: List<&2, Ops.Op>, +sd: String, e: {Ops.diff.of(ops, sd) == None{} : Maybe<&2, Ops.Doc>}) -> {ops == Nil{} : List<&2, Ops.Op>}:
  match ops:
    case Nil{}:
      {==}
    case op <> rest:
      Empty.absurd({op <> rest == Nil{} : List<&2, Ops.Op>}, SimL.some_none(Ops.Doc{None{}, Some{sd}, op <> rest}, e))

def walked_nil(+parent: List<&2, Ops.Item>, +child: List<&2, Ops.Item>, e: {Cursor.apply(parent, Ops.Doc{None{}, Some{Ops.state_digest(child)}, Nil{}}) == Done{child} : Result<&2, &2, String, List<&2, Ops.Item>>}) -> {parent == child : List<&2, Ops.Item>}:
  LaidL.done_items(parent, child, LaidL.checked_done(True{}, Some{Ops.state_digest(child)}, Done{parent}, child, e))

def none_checked(+parent: List<&2, Ops.Item>, +child: List<&2, Ops.Item>, +moves: List<&2, Ops.Move>, ok: Bool, +eo: {Sim.fit(moves, parent, child) == ok : Bool}, +tbl: {Ops.terminated_but_last(child) == True{} : Bool}, e: {Sim.diff.checked(parent, child, moves, ok) == None{} : Maybe<&2, Ops.Doc>}) -> {parent == child : List<&2, Ops.Item>}:
  match ok:
    case True{}:
      walked_nil(parent, child, SimL.moves_walk(parent, child, moves, Nil{}, diff_of_none(Ops.script(Ops.runs(moves, 0n, Nil{}, Nil{}), 0n), Ops.state_digest(child), e), SimL.fit_apply(moves, parent, child, eo), tbl))
    case False{}:
      walked_nil(parent, child, Diff.diff_walks(parent, child, Nil{}, diff_of_none(Ops.script(Ops.runs(Ops.edits(parent, child), 0n, Nil{}, Nil{}), 0n), Ops.state_digest(child), e), tbl))

def sim_none(+parent: List<&2, Ops.Item>, +child: List<&2, Ops.Item>, +tbl: {Ops.terminated_but_last(child) == True{} : Bool}, e: {Sim.diff(parent, child) == None{} : Maybe<&2, Ops.Doc>}) -> {parent == child : List<&2, Ops.Item>}:
  none_checked(parent, child, Sim.walked.moves(Sim.walked.go(Sim.ops(parent, child), Sim.Walked{parent, child, Nil{}})), Sim.fit(Sim.walked.moves(Sim.walked.go(Sim.ops(parent, child), Sim.Walked{parent, child, Nil{}})), parent, child), {==}, tbl, e)

def overlay_of(+rows: List<&2, Main.Row>, +after: List<&2, Ops.Item>, d: Maybe<&2, Ops.Doc>, ed: {Sim.diff(Main.rows.items(rows), after) == d : Maybe<&2, Ops.Doc>}, +tbl: {Ops.terminated_but_last(after) == True{} : Bool}) -> {Main.rows.items(Main.wc.overlay.of(rows, d)) == after : List<&2, Ops.Item>}:
  match d:
    case None{}:
      sim_none(Main.rows.items(rows), after, tbl, ed)
    case Some{+doc}:
      Equal.trans(List<&2, Ops.Item>, Main.rows.items(Main.overlay(Main.laid(Main.rows.items(rows), doc), rows, None{})), Main.laid.new(Main.laid(Main.rows.items(rows), doc)), after,
        overlay_items(Main.laid(Main.rows.items(rows), doc), rows, None{}, Equal.sym(List<&2, Ops.Item>, Main.laid.old(Main.laid(Main.rows.items(rows), doc)), Main.rows.items(rows), LaidL.laid_keeps_parent(Main.rows.items(rows), doc))),
        LaidL.laid_reads_child(Main.rows.items(rows), doc, after, SimL.similar_applies(Main.rows.items(rows), after, tbl, doc, ed)))

# `blame` over the folder prints the folder's lines, each once and in order.
def wc_overlay_items(+rows: List<&2, Main.Row>, +after: List<&2, Ops.Item>, +tbl: {Ops.terminated_but_last(after) == True{} : Bool}) -> {Main.rows.items(Main.wc.overlay(rows, after)) == after : List<&2, Ops.Item>}:
  overlay_of(rows, after, Sim.diff(Main.rows.items(rows), after), {==}, tbl)

# A file's text read as lines ends every line but the last.
def tbl_cons(+t: String, g: List<&2, Ops.Item>, hg: {Ops.terminated_but_last(g) == True{} : Bool}) -> {Ops.terminated_but_last(Ops.line(t) <> g) == True{} : Bool}:
  match g:
    case Nil{}:
      {==}
    case it <> rest:
      hg

def tbl_last(last: String, empty: Bool) -> {Ops.terminated_but_last(Bool.pick(List<&2, Ops.Item>, empty, Nil{}, [Ops.unterminated(last)])) == True{} : Bool}:
  match empty:
    case True{}:
      {==}
    case False{}:
      {==}

def tbl_go(parts: List<&2, String>) -> {Ops.terminated_but_last(Ops.from_text.go(parts)) == True{} : Bool}:
  match parts:
    case Nil{}:
      {==}
    case +last <> Nil{}:
      tbl_last(last, String.is_empty(last))
    case +x <> +y <> +r:
      tbl_cons(x, Ops.from_text.go(y <> r), tbl_go(y <> r))

def tbl_text(s: String) -> {Ops.terminated_but_last(Ops.from_text(s)) == True{} : Bool}:
  tbl_go(String.split(s, '\n'))

# `blame <path>` prints the folder's file: its lines, each once and in order.
def folder_lines(+rows: List<&2, Main.Row>, +s: String) -> {Main.rows.items(Main.wc.overlay(rows, Ops.from_text(s))) == Ops.from_text(s) : List<&2, Ops.Item>}:
  wc_overlay_items(rows, Ops.from_text(s), tbl_text(s))
