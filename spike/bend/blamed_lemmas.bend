# What `blame` prints. The rows it attributes are the lines the walk reads,
# and it prints each of them once, numbered as the file numbers it.
import Base
import ./ops.bend as Ops
import ./merge.bend as Merge
import ./main.bend as Main
import ./store.bend as Store
import ./string_lemmas.bend as S

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
