# What `record` decides before it writes.
#
# It reads its words as their plain reading says, and so do `amend`,
# `abandon` and `carry`; and what it states each file holds is what the
# folder holds there.
import Base
import ./commands.bend as Main
import ./text.bend as T
import ./sort_lemmas.bend as SortL
import ./blamed_lemmas.bend as B
import ./string_lemmas.bend as S
import ./hunk_lemmas.bend as HunkL
import ./blame_lemmas.bend as BlameL
import ./ops.bend as Ops
import ./utf8.bend as Utf8
import ./tree.bend as Tree
import ./folder.bend as Folder
import ./revision.bend as Rev
import ./survey.bend as Sv
import ./naming.bend as Naming
import ./bookmark.bend as Bm
import ./sha256.bend as Sha
import ./status_lemmas.bend as StatusL
import ./map_lemmas.bend as ML
import ./survey_lemmas.bend as SurveyL
import ./store.bend as Store
import ./conflict.bend as Conflict
import ./resolution.bend as Res

# Its words
# ---------

def done_rc(-a: Main.RecordCmd, -b: Main.RecordCmd, h: {Done{a} == Done{b} : Result<&2, &2, Main.Refused, Main.RecordCmd>}) -> {a == b : Main.RecordCmd}:
  B.done_eq(Main.RecordCmd, a, b, h)

# What `record.split` cuts is `rargs.cut`.
def cut_of(+v: String, +msg: String, parts: List<&2, String>, -s: T.Split, h: {Main.record.split.of(msg, parts) == Done{s} : Result<&2, &2, Main.Refused, T.Split>}) -> {s == Main.rargs.cut.of(v, parts) : T.Split}:
  match parts:
    case Nil{}:
      Empty.absurd({s == Main.rargs.cut.of(v, Nil{}) : T.Split}, B.fail_done(T.Split, Main.Refused{2, msg}, s, h))
    case +a <> Nil{}:
      Empty.absurd({s == Main.rargs.cut.of(v, [a]) : T.Split}, B.fail_done(T.Split, Main.Refused{2, msg}, s, h))
    case +a <> +b <> +rest:
      Equal.sym(T.Split, T.Split{a, String.join(b <> rest, "=")}, s, B.done_eq(T.Split, T.Split{a, String.join(b <> rest, "=")}, s, h))

def split_cut(+v: String, +msg: String, -s: T.Split, h: {Main.record.split(v, msg) == Done{s} : Result<&2, &2, Main.Refused, T.Split>}) -> {s == Main.rargs.cut(v) : T.Split}:
  cut_of(v, msg, String.split(v, '='), s, h)

def pick_done(-A: Data, b: Bool, -x: Main.Refused, -y: A, -z: A, h: {Bool.pick(Result<&2, &2, Main.Refused, A>, b, Fail{x}, Done{y}) == Done{z} : Result<&2, &2, Main.Refused, A>}) -> {y == z : A}:
  match b:
    case True{}:
      Empty.absurd({y == z : A}, B.fail_done(A, x, z, h))
    case False{}:
      B.done_eq(A, y, z, h)

def at_bind(+v: String, +rest: List<&2, String>, +o: Maybe<&2, String>, +ms: List<&2, String>, +ac: List<&2, String>, +at: List<&2, T.Split>, +mv: List<&2, T.Split>, +ks: List<&2, T.Split>, +ns: List<&2, String>, +d: Bool, +f: Bool, +mg: Maybe<&2, String>, r: Result<&2, &2, Main.Refused, T.Split>, +cmd: Main.RecordCmd, er: {Main.record.split(v, "`--at` is spelled `--at <file>=<path>`") == r : Result<&2, &2, Main.Refused, T.Split>}, e: {Result.bind(&2, &2, Main.Refused, T.Split, Main.RecordCmd, r, s => Main.record.args.go(rest, Main.rc.at(Main.RecordCmd{o, ms, ac, at, mv, ks, ns, d, f, mg}, s), Main.rword(rest))) == Done{cmd} : Result<&2, &2, Main.Refused, Main.RecordCmd>}, ih: @at2: List<&2, T.Split> -> {Main.record.args.go(rest, Main.RecordCmd{o, ms, ac, at2, mv, ks, ns, d, f, mg}, Main.rword(rest)) == Done{cmd} : Result<&2, &2, Main.Refused, Main.RecordCmd>} -> {cmd == Main.RecordCmd{Main.rargs.last(Main.rargs.read(rest, Main.rword(rest)), "--onto", o), List.append(&2, String, ms, Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "--merge")), List.reverse.go(&2, String, Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "--accept"), ac), List.append(&2, T.Split, at2, Main.rargs.cuts(Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "--at"))), List.append(&2, T.Split, mv, Main.rargs.cuts(Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "--move"))), List.append(&2, T.Split, ks, Main.rargs.kinds(Main.rargs.read(rest, Main.rword(rest)))), List.reverse.go(&2, String, Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "path"), ns), Main.rargs.has(Main.rargs.read(rest, Main.rword(rest)), "--dry-run", d), Main.rargs.has(Main.rargs.read(rest, Main.rword(rest)), "--fields", f), Main.rargs.last(Main.rargs.read(rest, Main.rword(rest)), "-m", mg)} : Main.RecordCmd}) -> {cmd == Main.RecordCmd{Main.rargs.last(Main.rargs.read(rest, Main.rword(rest)), "--onto", o), List.append(&2, String, ms, Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "--merge")), List.reverse.go(&2, String, Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "--accept"), ac), List.append(&2, T.Split, at, Main.rargs.cut(v) <> Main.rargs.cuts(Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "--at"))), List.append(&2, T.Split, mv, Main.rargs.cuts(Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "--move"))), List.append(&2, T.Split, ks, Main.rargs.kinds(Main.rargs.read(rest, Main.rword(rest)))), List.reverse.go(&2, String, Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "path"), ns), Main.rargs.has(Main.rargs.read(rest, Main.rword(rest)), "--dry-run", d), Main.rargs.has(Main.rargs.read(rest, Main.rword(rest)), "--fields", f), Main.rargs.last(Main.rargs.read(rest, Main.rword(rest)), "-m", mg)} : Main.RecordCmd}:
  match r:
    case Fail{x}:
      Empty.absurd({cmd == Main.RecordCmd{Main.rargs.last(Main.rargs.read(rest, Main.rword(rest)), "--onto", o), List.append(&2, String, ms, Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "--merge")), List.reverse.go(&2, String, Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "--accept"), ac), List.append(&2, T.Split, at, Main.rargs.cut(v) <> Main.rargs.cuts(Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "--at"))), List.append(&2, T.Split, mv, Main.rargs.cuts(Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "--move"))), List.append(&2, T.Split, ks, Main.rargs.kinds(Main.rargs.read(rest, Main.rword(rest)))), List.reverse.go(&2, String, Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "path"), ns), Main.rargs.has(Main.rargs.read(rest, Main.rword(rest)), "--dry-run", d), Main.rargs.has(Main.rargs.read(rest, Main.rword(rest)), "--fields", f), Main.rargs.last(Main.rargs.read(rest, Main.rword(rest)), "-m", mg)} : Main.RecordCmd}, B.fail_done(Main.RecordCmd, x, cmd, e))
    case Done{+s}:
      +hs = split_cut(v, "`--at` is spelled `--at <file>=<path>`", s, er)
      +assoc = Equal.trans(List<&2, T.Split>, List.append(&2, T.Split, List.append(&2, T.Split, at, [s]), Main.rargs.cuts(Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "--at"))), List.append(&2, T.Split, at, s <> Main.rargs.cuts(Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "--at"))), List.append(&2, T.Split, at, Main.rargs.cut(v) <> Main.rargs.cuts(Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "--at"))),
        SortL.app_assoc(T.Split, at, [s], Main.rargs.cuts(Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "--at"))),
        Equal.cong(T.Split, List<&2, T.Split>, y => List.append(&2, T.Split, at, y <> Main.rargs.cuts(Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "--at"))), s, Main.rargs.cut(v), hs))
      Equal.trans(Main.RecordCmd, cmd, Main.RecordCmd{Main.rargs.last(Main.rargs.read(rest, Main.rword(rest)), "--onto", o), List.append(&2, String, ms, Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "--merge")), List.reverse.go(&2, String, Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "--accept"), ac), List.append(&2, T.Split, List.append(&2, T.Split, at, [s]), Main.rargs.cuts(Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "--at"))), List.append(&2, T.Split, mv, Main.rargs.cuts(Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "--move"))), List.append(&2, T.Split, ks, Main.rargs.kinds(Main.rargs.read(rest, Main.rword(rest)))), List.reverse.go(&2, String, Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "path"), ns), Main.rargs.has(Main.rargs.read(rest, Main.rword(rest)), "--dry-run", d), Main.rargs.has(Main.rargs.read(rest, Main.rword(rest)), "--fields", f), Main.rargs.last(Main.rargs.read(rest, Main.rword(rest)), "-m", mg)}, Main.RecordCmd{Main.rargs.last(Main.rargs.read(rest, Main.rword(rest)), "--onto", o), List.append(&2, String, ms, Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "--merge")), List.reverse.go(&2, String, Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "--accept"), ac), List.append(&2, T.Split, at, Main.rargs.cut(v) <> Main.rargs.cuts(Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "--at"))), List.append(&2, T.Split, mv, Main.rargs.cuts(Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "--move"))), List.append(&2, T.Split, ks, Main.rargs.kinds(Main.rargs.read(rest, Main.rword(rest)))), List.reverse.go(&2, String, Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "path"), ns), Main.rargs.has(Main.rargs.read(rest, Main.rword(rest)), "--dry-run", d), Main.rargs.has(Main.rargs.read(rest, Main.rword(rest)), "--fields", f), Main.rargs.last(Main.rargs.read(rest, Main.rword(rest)), "-m", mg)},
        ih(List.append(&2, T.Split, at, [s]), e),
        Equal.cong(List<&2, T.Split>, Main.RecordCmd, x => Main.RecordCmd{Main.rargs.last(Main.rargs.read(rest, Main.rword(rest)), "--onto", o), List.append(&2, String, ms, Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "--merge")), List.reverse.go(&2, String, Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "--accept"), ac), x, List.append(&2, T.Split, mv, Main.rargs.cuts(Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "--move"))), List.append(&2, T.Split, ks, Main.rargs.kinds(Main.rargs.read(rest, Main.rword(rest)))), List.reverse.go(&2, String, Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "path"), ns), Main.rargs.has(Main.rargs.read(rest, Main.rword(rest)), "--dry-run", d), Main.rargs.has(Main.rargs.read(rest, Main.rword(rest)), "--fields", f), Main.rargs.last(Main.rargs.read(rest, Main.rword(rest)), "-m", mg)}, List.append(&2, T.Split, List.append(&2, T.Split, at, [s]), Main.rargs.cuts(Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "--at"))), List.append(&2, T.Split, at, Main.rargs.cut(v) <> Main.rargs.cuts(Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "--at"))), assoc))

def move_bind(+v: String, +rest: List<&2, String>, +o: Maybe<&2, String>, +ms: List<&2, String>, +ac: List<&2, String>, +at: List<&2, T.Split>, +mv: List<&2, T.Split>, +ks: List<&2, T.Split>, +ns: List<&2, String>, +d: Bool, +f: Bool, +mg: Maybe<&2, String>, r: Result<&2, &2, Main.Refused, T.Split>, +cmd: Main.RecordCmd, er: {Main.record.split(v, "`--move` is spelled `--move <old>=<new>`") == r : Result<&2, &2, Main.Refused, T.Split>}, e: {Result.bind(&2, &2, Main.Refused, T.Split, Main.RecordCmd, r, s => Main.record.args.go(rest, Main.rc.move(Main.RecordCmd{o, ms, ac, at, mv, ks, ns, d, f, mg}, s), Main.rword(rest))) == Done{cmd} : Result<&2, &2, Main.Refused, Main.RecordCmd>}, ih: @mv2: List<&2, T.Split> -> {Main.record.args.go(rest, Main.RecordCmd{o, ms, ac, at, mv2, ks, ns, d, f, mg}, Main.rword(rest)) == Done{cmd} : Result<&2, &2, Main.Refused, Main.RecordCmd>} -> {cmd == Main.RecordCmd{Main.rargs.last(Main.rargs.read(rest, Main.rword(rest)), "--onto", o), List.append(&2, String, ms, Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "--merge")), List.reverse.go(&2, String, Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "--accept"), ac), List.append(&2, T.Split, at, Main.rargs.cuts(Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "--at"))), List.append(&2, T.Split, mv2, Main.rargs.cuts(Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "--move"))), List.append(&2, T.Split, ks, Main.rargs.kinds(Main.rargs.read(rest, Main.rword(rest)))), List.reverse.go(&2, String, Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "path"), ns), Main.rargs.has(Main.rargs.read(rest, Main.rword(rest)), "--dry-run", d), Main.rargs.has(Main.rargs.read(rest, Main.rword(rest)), "--fields", f), Main.rargs.last(Main.rargs.read(rest, Main.rword(rest)), "-m", mg)} : Main.RecordCmd}) -> {cmd == Main.RecordCmd{Main.rargs.last(Main.rargs.read(rest, Main.rword(rest)), "--onto", o), List.append(&2, String, ms, Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "--merge")), List.reverse.go(&2, String, Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "--accept"), ac), List.append(&2, T.Split, at, Main.rargs.cuts(Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "--at"))), List.append(&2, T.Split, mv, Main.rargs.cut(v) <> Main.rargs.cuts(Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "--move"))), List.append(&2, T.Split, ks, Main.rargs.kinds(Main.rargs.read(rest, Main.rword(rest)))), List.reverse.go(&2, String, Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "path"), ns), Main.rargs.has(Main.rargs.read(rest, Main.rword(rest)), "--dry-run", d), Main.rargs.has(Main.rargs.read(rest, Main.rword(rest)), "--fields", f), Main.rargs.last(Main.rargs.read(rest, Main.rword(rest)), "-m", mg)} : Main.RecordCmd}:
  match r:
    case Fail{x}:
      Empty.absurd({cmd == Main.RecordCmd{Main.rargs.last(Main.rargs.read(rest, Main.rword(rest)), "--onto", o), List.append(&2, String, ms, Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "--merge")), List.reverse.go(&2, String, Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "--accept"), ac), List.append(&2, T.Split, at, Main.rargs.cuts(Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "--at"))), List.append(&2, T.Split, mv, Main.rargs.cut(v) <> Main.rargs.cuts(Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "--move"))), List.append(&2, T.Split, ks, Main.rargs.kinds(Main.rargs.read(rest, Main.rword(rest)))), List.reverse.go(&2, String, Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "path"), ns), Main.rargs.has(Main.rargs.read(rest, Main.rword(rest)), "--dry-run", d), Main.rargs.has(Main.rargs.read(rest, Main.rword(rest)), "--fields", f), Main.rargs.last(Main.rargs.read(rest, Main.rword(rest)), "-m", mg)} : Main.RecordCmd}, B.fail_done(Main.RecordCmd, x, cmd, e))
    case Done{+s}:
      +hs = split_cut(v, "`--move` is spelled `--move <old>=<new>`", s, er)
      +assoc = Equal.trans(List<&2, T.Split>, List.append(&2, T.Split, List.append(&2, T.Split, mv, [s]), Main.rargs.cuts(Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "--move"))), List.append(&2, T.Split, mv, s <> Main.rargs.cuts(Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "--move"))), List.append(&2, T.Split, mv, Main.rargs.cut(v) <> Main.rargs.cuts(Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "--move"))),
        SortL.app_assoc(T.Split, mv, [s], Main.rargs.cuts(Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "--move"))),
        Equal.cong(T.Split, List<&2, T.Split>, y => List.append(&2, T.Split, mv, y <> Main.rargs.cuts(Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "--move"))), s, Main.rargs.cut(v), hs))
      Equal.trans(Main.RecordCmd, cmd, Main.RecordCmd{Main.rargs.last(Main.rargs.read(rest, Main.rword(rest)), "--onto", o), List.append(&2, String, ms, Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "--merge")), List.reverse.go(&2, String, Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "--accept"), ac), List.append(&2, T.Split, at, Main.rargs.cuts(Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "--at"))), List.append(&2, T.Split, List.append(&2, T.Split, mv, [s]), Main.rargs.cuts(Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "--move"))), List.append(&2, T.Split, ks, Main.rargs.kinds(Main.rargs.read(rest, Main.rword(rest)))), List.reverse.go(&2, String, Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "path"), ns), Main.rargs.has(Main.rargs.read(rest, Main.rword(rest)), "--dry-run", d), Main.rargs.has(Main.rargs.read(rest, Main.rword(rest)), "--fields", f), Main.rargs.last(Main.rargs.read(rest, Main.rword(rest)), "-m", mg)}, Main.RecordCmd{Main.rargs.last(Main.rargs.read(rest, Main.rword(rest)), "--onto", o), List.append(&2, String, ms, Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "--merge")), List.reverse.go(&2, String, Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "--accept"), ac), List.append(&2, T.Split, at, Main.rargs.cuts(Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "--at"))), List.append(&2, T.Split, mv, Main.rargs.cut(v) <> Main.rargs.cuts(Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "--move"))), List.append(&2, T.Split, ks, Main.rargs.kinds(Main.rargs.read(rest, Main.rword(rest)))), List.reverse.go(&2, String, Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "path"), ns), Main.rargs.has(Main.rargs.read(rest, Main.rword(rest)), "--dry-run", d), Main.rargs.has(Main.rargs.read(rest, Main.rword(rest)), "--fields", f), Main.rargs.last(Main.rargs.read(rest, Main.rword(rest)), "-m", mg)},
        ih(List.append(&2, T.Split, mv, [s]), e),
        Equal.cong(List<&2, T.Split>, Main.RecordCmd, x => Main.RecordCmd{Main.rargs.last(Main.rargs.read(rest, Main.rword(rest)), "--onto", o), List.append(&2, String, ms, Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "--merge")), List.reverse.go(&2, String, Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "--accept"), ac), List.append(&2, T.Split, at, Main.rargs.cuts(Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "--at"))), x, List.append(&2, T.Split, ks, Main.rargs.kinds(Main.rargs.read(rest, Main.rword(rest)))), List.reverse.go(&2, String, Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "path"), ns), Main.rargs.has(Main.rargs.read(rest, Main.rword(rest)), "--dry-run", d), Main.rargs.has(Main.rargs.read(rest, Main.rword(rest)), "--fields", f), Main.rargs.last(Main.rargs.read(rest, Main.rword(rest)), "-m", mg)}, List.append(&2, T.Split, List.append(&2, T.Split, mv, [s]), Main.rargs.cuts(Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "--move"))), List.append(&2, T.Split, mv, Main.rargs.cut(v) <> Main.rargs.cuts(Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "--move"))), assoc))

def path_bind(+tw: String, +rest: List<&2, String>, +o: Maybe<&2, String>, +ms: List<&2, String>, +ac: List<&2, String>, +at: List<&2, T.Split>, +mv: List<&2, T.Split>, +ks: List<&2, T.Split>, +ns: List<&2, String>, +d: Bool, +f: Bool, +mg: Maybe<&2, String>, r: Result<&2, &2, Main.Refused, Main.RecordCmd>, +cmd: Main.RecordCmd, er: {Main.record.path(Main.RecordCmd{o, ms, ac, at, mv, ks, ns, d, f, mg}, tw) == r : Result<&2, &2, Main.Refused, Main.RecordCmd>}, e: {Result.bind(&2, &2, Main.Refused, Main.RecordCmd, Main.RecordCmd, r, more => Main.record.args.go(rest, more, Main.rword(rest))) == Done{cmd} : Result<&2, &2, Main.Refused, Main.RecordCmd>}, ih: @ns2: List<&2, String> -> {Main.record.args.go(rest, Main.RecordCmd{o, ms, ac, at, mv, ks, ns2, d, f, mg}, Main.rword(rest)) == Done{cmd} : Result<&2, &2, Main.Refused, Main.RecordCmd>} -> {cmd == Main.RecordCmd{Main.rargs.last(Main.rargs.read(rest, Main.rword(rest)), "--onto", o), List.append(&2, String, ms, Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "--merge")), List.reverse.go(&2, String, Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "--accept"), ac), List.append(&2, T.Split, at, Main.rargs.cuts(Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "--at"))), List.append(&2, T.Split, mv, Main.rargs.cuts(Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "--move"))), List.append(&2, T.Split, ks, Main.rargs.kinds(Main.rargs.read(rest, Main.rword(rest)))), List.reverse.go(&2, String, Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "path"), ns2), Main.rargs.has(Main.rargs.read(rest, Main.rword(rest)), "--dry-run", d), Main.rargs.has(Main.rargs.read(rest, Main.rword(rest)), "--fields", f), Main.rargs.last(Main.rargs.read(rest, Main.rword(rest)), "-m", mg)} : Main.RecordCmd}) -> {cmd == Main.RecordCmd{Main.rargs.last(Main.rargs.read(rest, Main.rword(rest)), "--onto", o), List.append(&2, String, ms, Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "--merge")), List.reverse.go(&2, String, Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "--accept"), ac), List.append(&2, T.Split, at, Main.rargs.cuts(Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "--at"))), List.append(&2, T.Split, mv, Main.rargs.cuts(Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "--move"))), List.append(&2, T.Split, ks, Main.rargs.kinds(Main.rargs.read(rest, Main.rword(rest)))), List.reverse.go(&2, String, Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "path"), tw <> ns), Main.rargs.has(Main.rargs.read(rest, Main.rword(rest)), "--dry-run", d), Main.rargs.has(Main.rargs.read(rest, Main.rword(rest)), "--fields", f), Main.rargs.last(Main.rargs.read(rest, Main.rword(rest)), "-m", mg)} : Main.RecordCmd}:
  match r:
    case Fail{x}:
      Empty.absurd({cmd == Main.RecordCmd{Main.rargs.last(Main.rargs.read(rest, Main.rword(rest)), "--onto", o), List.append(&2, String, ms, Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "--merge")), List.reverse.go(&2, String, Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "--accept"), ac), List.append(&2, T.Split, at, Main.rargs.cuts(Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "--at"))), List.append(&2, T.Split, mv, Main.rargs.cuts(Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "--move"))), List.append(&2, T.Split, ks, Main.rargs.kinds(Main.rargs.read(rest, Main.rword(rest)))), List.reverse.go(&2, String, Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "path"), tw <> ns), Main.rargs.has(Main.rargs.read(rest, Main.rword(rest)), "--dry-run", d), Main.rargs.has(Main.rargs.read(rest, Main.rword(rest)), "--fields", f), Main.rargs.last(Main.rargs.read(rest, Main.rword(rest)), "-m", mg)} : Main.RecordCmd}, B.fail_done(Main.RecordCmd, x, cmd, e))
    case Done{+more}:
      +hm = pick_done(Main.RecordCmd, String.is_empty(tw), Main.Refused{2, "`record` takes the paths to record, and an empty one names nothing"}, Main.RecordCmd{o, ms, ac, at, mv, ks, tw <> ns, d, f, mg}, more, er)
      ih(tw <> ns, Equal.trans(Result<&2, &2, Main.Refused, Main.RecordCmd>, Main.record.args.go(rest, Main.RecordCmd{o, ms, ac, at, mv, ks, tw <> ns, d, f, mg}, Main.rword(rest)), Main.record.args.go(rest, more, Main.rword(rest)), Done{cmd},
        Equal.cong(Main.RecordCmd, Result<&2, &2, Main.Refused, Main.RecordCmd>, x => Main.record.args.go(rest, x, Main.rword(rest)), Main.RecordCmd{o, ms, ac, at, mv, ks, tw <> ns, d, f, mg}, more, hm), e))

# One pass over the words reads what their plain reading says.
def go_said(args: List<&2, String>, +o: Maybe<&2, String>, +ms: List<&2, String>, +ac: List<&2, String>, +at: List<&2, T.Split>, +mv: List<&2, T.Split>, +ks: List<&2, T.Split>, +ns: List<&2, String>, +d: Bool, +f: Bool, +mg: Maybe<&2, String>, k: Main.RWord, +cmd: Main.RecordCmd, e: {Main.record.args.go(args, Main.RecordCmd{o, ms, ac, at, mv, ks, ns, d, f, mg}, k) == Done{cmd} : Result<&2, &2, Main.Refused, Main.RecordCmd>}) -> {cmd == Main.RecordCmd{Main.rargs.last(Main.rargs.read(args, k), "--onto", o), List.append(&2, String, ms, Main.rargs.values(Main.rargs.read(args, k), "--merge")), List.reverse.go(&2, String, Main.rargs.values(Main.rargs.read(args, k), "--accept"), ac), List.append(&2, T.Split, at, Main.rargs.cuts(Main.rargs.values(Main.rargs.read(args, k), "--at"))), List.append(&2, T.Split, mv, Main.rargs.cuts(Main.rargs.values(Main.rargs.read(args, k), "--move"))), List.append(&2, T.Split, ks, Main.rargs.kinds(Main.rargs.read(args, k))), List.reverse.go(&2, String, Main.rargs.values(Main.rargs.read(args, k), "path"), ns), Main.rargs.has(Main.rargs.read(args, k), "--dry-run", d), Main.rargs.has(Main.rargs.read(args, k), "--fields", f), Main.rargs.last(Main.rargs.read(args, k), "-m", mg)} : Main.RecordCmd}:
  match args k:
    case Nil{} _:
      %done_rc(Main.RecordCmd{o, ms, ac, at, mv, ks, ns, d, f, mg}, cmd, e) : {_ == Main.RecordCmd{o, List.append(&2, String, ms, Nil{}), ac, List.append(&2, T.Split, at, Nil{}), List.append(&2, T.Split, mv, Nil{}), List.append(&2, T.Split, ks, Nil{}), ns, d, f, mg} : Main.RecordCmd}
      %Equal.sym(List<&2, String>, List.append(&2, String, ms, Nil{}), ms, SortL.lapp_nil(String, ms)) : {Main.RecordCmd{o, ms, ac, at, mv, ks, ns, d, f, mg} == Main.RecordCmd{o, _, ac, List.append(&2, T.Split, at, Nil{}), List.append(&2, T.Split, mv, Nil{}), List.append(&2, T.Split, ks, Nil{}), ns, d, f, mg} : Main.RecordCmd}
      %Equal.sym(List<&2, T.Split>, List.append(&2, T.Split, at, Nil{}), at, SortL.lapp_nil(T.Split, at)) : {Main.RecordCmd{o, ms, ac, at, mv, ks, ns, d, f, mg} == Main.RecordCmd{o, ms, ac, _, List.append(&2, T.Split, mv, Nil{}), List.append(&2, T.Split, ks, Nil{}), ns, d, f, mg} : Main.RecordCmd}
      %Equal.sym(List<&2, T.Split>, List.append(&2, T.Split, mv, Nil{}), mv, SortL.lapp_nil(T.Split, mv)) : {Main.RecordCmd{o, ms, ac, at, mv, ks, ns, d, f, mg} == Main.RecordCmd{o, ms, ac, at, _, List.append(&2, T.Split, ks, Nil{}), ns, d, f, mg} : Main.RecordCmd}
      %Equal.sym(List<&2, T.Split>, List.append(&2, T.Split, ks, Nil{}), ks, SortL.lapp_nil(T.Split, ks)) : {Main.RecordCmd{o, ms, ac, at, mv, ks, ns, d, f, mg} == Main.RecordCmd{o, ms, ac, at, mv, _, ns, d, f, mg} : Main.RecordCmd}
      {==}
    case +w <> Nil{} Main.RWord.Message{}:
      Empty.absurd({cmd == Main.RecordCmd{Main.rargs.last(Main.rargs.read([w], Main.RWord.Message{}), "--onto", o), List.append(&2, String, ms, Main.rargs.values(Main.rargs.read([w], Main.RWord.Message{}), "--merge")), List.reverse.go(&2, String, Main.rargs.values(Main.rargs.read([w], Main.RWord.Message{}), "--accept"), ac), List.append(&2, T.Split, at, Main.rargs.cuts(Main.rargs.values(Main.rargs.read([w], Main.RWord.Message{}), "--at"))), List.append(&2, T.Split, mv, Main.rargs.cuts(Main.rargs.values(Main.rargs.read([w], Main.RWord.Message{}), "--move"))), List.append(&2, T.Split, ks, Main.rargs.kinds(Main.rargs.read([w], Main.RWord.Message{}))), List.reverse.go(&2, String, Main.rargs.values(Main.rargs.read([w], Main.RWord.Message{}), "path"), ns), Main.rargs.has(Main.rargs.read([w], Main.RWord.Message{}), "--dry-run", d), Main.rargs.has(Main.rargs.read([w], Main.RWord.Message{}), "--fields", f), Main.rargs.last(Main.rargs.read([w], Main.RWord.Message{}), "-m", mg)} : Main.RecordCmd}, B.fail_done(Main.RecordCmd, Main.Refused{2, "`-m` wants a value"}, cmd, e))
    case w <> +v <> +rest Main.RWord.Message{}:
      go_said(rest, o, ms, ac, at, mv, ks, ns, d, f, Some{v}, Main.rword(rest), cmd, e)
    case +w <> Nil{} Main.RWord.Onto{}:
      Empty.absurd({cmd == Main.RecordCmd{Main.rargs.last(Main.rargs.read([w], Main.RWord.Onto{}), "--onto", o), List.append(&2, String, ms, Main.rargs.values(Main.rargs.read([w], Main.RWord.Onto{}), "--merge")), List.reverse.go(&2, String, Main.rargs.values(Main.rargs.read([w], Main.RWord.Onto{}), "--accept"), ac), List.append(&2, T.Split, at, Main.rargs.cuts(Main.rargs.values(Main.rargs.read([w], Main.RWord.Onto{}), "--at"))), List.append(&2, T.Split, mv, Main.rargs.cuts(Main.rargs.values(Main.rargs.read([w], Main.RWord.Onto{}), "--move"))), List.append(&2, T.Split, ks, Main.rargs.kinds(Main.rargs.read([w], Main.RWord.Onto{}))), List.reverse.go(&2, String, Main.rargs.values(Main.rargs.read([w], Main.RWord.Onto{}), "path"), ns), Main.rargs.has(Main.rargs.read([w], Main.RWord.Onto{}), "--dry-run", d), Main.rargs.has(Main.rargs.read([w], Main.RWord.Onto{}), "--fields", f), Main.rargs.last(Main.rargs.read([w], Main.RWord.Onto{}), "-m", mg)} : Main.RecordCmd}, B.fail_done(Main.RecordCmd, Main.Refused{2, "`--onto` wants a value"}, cmd, e))
    case w <> +v <> +rest Main.RWord.Onto{}:
      go_said(rest, Some{v}, ms, ac, at, mv, ks, ns, d, f, mg, Main.rword(rest), cmd, e)
    case +w <> Nil{} Main.RWord.Merge{}:
      Empty.absurd({cmd == Main.RecordCmd{Main.rargs.last(Main.rargs.read([w], Main.RWord.Merge{}), "--onto", o), List.append(&2, String, ms, Main.rargs.values(Main.rargs.read([w], Main.RWord.Merge{}), "--merge")), List.reverse.go(&2, String, Main.rargs.values(Main.rargs.read([w], Main.RWord.Merge{}), "--accept"), ac), List.append(&2, T.Split, at, Main.rargs.cuts(Main.rargs.values(Main.rargs.read([w], Main.RWord.Merge{}), "--at"))), List.append(&2, T.Split, mv, Main.rargs.cuts(Main.rargs.values(Main.rargs.read([w], Main.RWord.Merge{}), "--move"))), List.append(&2, T.Split, ks, Main.rargs.kinds(Main.rargs.read([w], Main.RWord.Merge{}))), List.reverse.go(&2, String, Main.rargs.values(Main.rargs.read([w], Main.RWord.Merge{}), "path"), ns), Main.rargs.has(Main.rargs.read([w], Main.RWord.Merge{}), "--dry-run", d), Main.rargs.has(Main.rargs.read([w], Main.RWord.Merge{}), "--fields", f), Main.rargs.last(Main.rargs.read([w], Main.RWord.Merge{}), "-m", mg)} : Main.RecordCmd}, B.fail_done(Main.RecordCmd, Main.Refused{2, "`--merge` wants a value"}, cmd, e))
    case w <> +v <> +rest Main.RWord.Merge{}:
      Equal.trans(Main.RecordCmd, cmd, Main.RecordCmd{Main.rargs.last(Main.rargs.read(rest, Main.rword(rest)), "--onto", o), List.append(&2, String, List.append(&2, String, ms, [v]), Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "--merge")), List.reverse.go(&2, String, Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "--accept"), ac), List.append(&2, T.Split, at, Main.rargs.cuts(Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "--at"))), List.append(&2, T.Split, mv, Main.rargs.cuts(Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "--move"))), List.append(&2, T.Split, ks, Main.rargs.kinds(Main.rargs.read(rest, Main.rword(rest)))), List.reverse.go(&2, String, Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "path"), ns), Main.rargs.has(Main.rargs.read(rest, Main.rword(rest)), "--dry-run", d), Main.rargs.has(Main.rargs.read(rest, Main.rword(rest)), "--fields", f), Main.rargs.last(Main.rargs.read(rest, Main.rword(rest)), "-m", mg)}, Main.RecordCmd{Main.rargs.last(Main.rargs.read(rest, Main.rword(rest)), "--onto", o), List.append(&2, String, ms, v <> Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "--merge")), List.reverse.go(&2, String, Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "--accept"), ac), List.append(&2, T.Split, at, Main.rargs.cuts(Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "--at"))), List.append(&2, T.Split, mv, Main.rargs.cuts(Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "--move"))), List.append(&2, T.Split, ks, Main.rargs.kinds(Main.rargs.read(rest, Main.rword(rest)))), List.reverse.go(&2, String, Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "path"), ns), Main.rargs.has(Main.rargs.read(rest, Main.rword(rest)), "--dry-run", d), Main.rargs.has(Main.rargs.read(rest, Main.rword(rest)), "--fields", f), Main.rargs.last(Main.rargs.read(rest, Main.rword(rest)), "-m", mg)},
        go_said(rest, o, List.append(&2, String, ms, [v]), ac, at, mv, ks, ns, d, f, mg, Main.rword(rest), cmd, e),
        Equal.cong(List<&2, String>, Main.RecordCmd, x => Main.RecordCmd{Main.rargs.last(Main.rargs.read(rest, Main.rword(rest)), "--onto", o), x, List.reverse.go(&2, String, Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "--accept"), ac), List.append(&2, T.Split, at, Main.rargs.cuts(Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "--at"))), List.append(&2, T.Split, mv, Main.rargs.cuts(Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "--move"))), List.append(&2, T.Split, ks, Main.rargs.kinds(Main.rargs.read(rest, Main.rword(rest)))), List.reverse.go(&2, String, Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "path"), ns), Main.rargs.has(Main.rargs.read(rest, Main.rword(rest)), "--dry-run", d), Main.rargs.has(Main.rargs.read(rest, Main.rword(rest)), "--fields", f), Main.rargs.last(Main.rargs.read(rest, Main.rword(rest)), "-m", mg)}, List.append(&2, String, List.append(&2, String, ms, [v]), Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "--merge")), List.append(&2, String, ms, v <> Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "--merge")), SortL.app_assoc(String, ms, [v], Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "--merge"))))
    case +w <> Nil{} Main.RWord.Accept{}:
      Empty.absurd({cmd == Main.RecordCmd{Main.rargs.last(Main.rargs.read([w], Main.RWord.Accept{}), "--onto", o), List.append(&2, String, ms, Main.rargs.values(Main.rargs.read([w], Main.RWord.Accept{}), "--merge")), List.reverse.go(&2, String, Main.rargs.values(Main.rargs.read([w], Main.RWord.Accept{}), "--accept"), ac), List.append(&2, T.Split, at, Main.rargs.cuts(Main.rargs.values(Main.rargs.read([w], Main.RWord.Accept{}), "--at"))), List.append(&2, T.Split, mv, Main.rargs.cuts(Main.rargs.values(Main.rargs.read([w], Main.RWord.Accept{}), "--move"))), List.append(&2, T.Split, ks, Main.rargs.kinds(Main.rargs.read([w], Main.RWord.Accept{}))), List.reverse.go(&2, String, Main.rargs.values(Main.rargs.read([w], Main.RWord.Accept{}), "path"), ns), Main.rargs.has(Main.rargs.read([w], Main.RWord.Accept{}), "--dry-run", d), Main.rargs.has(Main.rargs.read([w], Main.RWord.Accept{}), "--fields", f), Main.rargs.last(Main.rargs.read([w], Main.RWord.Accept{}), "-m", mg)} : Main.RecordCmd}, B.fail_done(Main.RecordCmd, Main.Refused{2, "`--accept` wants a value"}, cmd, e))
    case w <> +v <> +rest Main.RWord.Accept{}:
      go_said(rest, o, ms, v <> ac, at, mv, ks, ns, d, f, mg, Main.rword(rest), cmd, e)
    case +w <> Nil{} Main.RWord.At{}:
      Empty.absurd({cmd == Main.RecordCmd{Main.rargs.last(Main.rargs.read([w], Main.RWord.At{}), "--onto", o), List.append(&2, String, ms, Main.rargs.values(Main.rargs.read([w], Main.RWord.At{}), "--merge")), List.reverse.go(&2, String, Main.rargs.values(Main.rargs.read([w], Main.RWord.At{}), "--accept"), ac), List.append(&2, T.Split, at, Main.rargs.cuts(Main.rargs.values(Main.rargs.read([w], Main.RWord.At{}), "--at"))), List.append(&2, T.Split, mv, Main.rargs.cuts(Main.rargs.values(Main.rargs.read([w], Main.RWord.At{}), "--move"))), List.append(&2, T.Split, ks, Main.rargs.kinds(Main.rargs.read([w], Main.RWord.At{}))), List.reverse.go(&2, String, Main.rargs.values(Main.rargs.read([w], Main.RWord.At{}), "path"), ns), Main.rargs.has(Main.rargs.read([w], Main.RWord.At{}), "--dry-run", d), Main.rargs.has(Main.rargs.read([w], Main.RWord.At{}), "--fields", f), Main.rargs.last(Main.rargs.read([w], Main.RWord.At{}), "-m", mg)} : Main.RecordCmd}, B.fail_done(Main.RecordCmd, Main.Refused{2, "`--at` wants a value"}, cmd, e))
    case w <> +v <> +rest Main.RWord.At{}:
      at_bind(v, rest, o, ms, ac, at, mv, ks, ns, d, f, mg, Main.record.split(v, "`--at` is spelled `--at <file>=<path>`"), cmd, {==}, e, at2 => h => go_said(rest, o, ms, ac, at2, mv, ks, ns, d, f, mg, Main.rword(rest), cmd, h))
    case +w <> Nil{} Main.RWord.Move{}:
      Empty.absurd({cmd == Main.RecordCmd{Main.rargs.last(Main.rargs.read([w], Main.RWord.Move{}), "--onto", o), List.append(&2, String, ms, Main.rargs.values(Main.rargs.read([w], Main.RWord.Move{}), "--merge")), List.reverse.go(&2, String, Main.rargs.values(Main.rargs.read([w], Main.RWord.Move{}), "--accept"), ac), List.append(&2, T.Split, at, Main.rargs.cuts(Main.rargs.values(Main.rargs.read([w], Main.RWord.Move{}), "--at"))), List.append(&2, T.Split, mv, Main.rargs.cuts(Main.rargs.values(Main.rargs.read([w], Main.RWord.Move{}), "--move"))), List.append(&2, T.Split, ks, Main.rargs.kinds(Main.rargs.read([w], Main.RWord.Move{}))), List.reverse.go(&2, String, Main.rargs.values(Main.rargs.read([w], Main.RWord.Move{}), "path"), ns), Main.rargs.has(Main.rargs.read([w], Main.RWord.Move{}), "--dry-run", d), Main.rargs.has(Main.rargs.read([w], Main.RWord.Move{}), "--fields", f), Main.rargs.last(Main.rargs.read([w], Main.RWord.Move{}), "-m", mg)} : Main.RecordCmd}, B.fail_done(Main.RecordCmd, Main.Refused{2, "`--move` wants a value"}, cmd, e))
    case w <> +v <> +rest Main.RWord.Move{}:
      move_bind(v, rest, o, ms, ac, at, mv, ks, ns, d, f, mg, Main.record.split(v, "`--move` is spelled `--move <old>=<new>`"), cmd, {==}, e, mv2 => h => go_said(rest, o, ms, ac, at, mv2, ks, ns, d, f, mg, Main.rword(rest), cmd, h))
    case +w <> Nil{} Main.RWord.Bytes{}:
      Empty.absurd({cmd == Main.RecordCmd{Main.rargs.last(Main.rargs.read([w], Main.RWord.Bytes{}), "--onto", o), List.append(&2, String, ms, Main.rargs.values(Main.rargs.read([w], Main.RWord.Bytes{}), "--merge")), List.reverse.go(&2, String, Main.rargs.values(Main.rargs.read([w], Main.RWord.Bytes{}), "--accept"), ac), List.append(&2, T.Split, at, Main.rargs.cuts(Main.rargs.values(Main.rargs.read([w], Main.RWord.Bytes{}), "--at"))), List.append(&2, T.Split, mv, Main.rargs.cuts(Main.rargs.values(Main.rargs.read([w], Main.RWord.Bytes{}), "--move"))), List.append(&2, T.Split, ks, Main.rargs.kinds(Main.rargs.read([w], Main.RWord.Bytes{}))), List.reverse.go(&2, String, Main.rargs.values(Main.rargs.read([w], Main.RWord.Bytes{}), "path"), ns), Main.rargs.has(Main.rargs.read([w], Main.RWord.Bytes{}), "--dry-run", d), Main.rargs.has(Main.rargs.read([w], Main.RWord.Bytes{}), "--fields", f), Main.rargs.last(Main.rargs.read([w], Main.RWord.Bytes{}), "-m", mg)} : Main.RecordCmd}, B.fail_done(Main.RecordCmd, Main.Refused{2, "`--bytes` wants a value"}, cmd, e))
    case w <> +v <> +rest Main.RWord.Bytes{}:
      Equal.trans(Main.RecordCmd, cmd, Main.RecordCmd{Main.rargs.last(Main.rargs.read(rest, Main.rword(rest)), "--onto", o), List.append(&2, String, ms, Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "--merge")), List.reverse.go(&2, String, Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "--accept"), ac), List.append(&2, T.Split, at, Main.rargs.cuts(Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "--at"))), List.append(&2, T.Split, mv, Main.rargs.cuts(Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "--move"))), List.append(&2, T.Split, List.append(&2, T.Split, ks, [T.Split{v, "bytes"}]), Main.rargs.kinds(Main.rargs.read(rest, Main.rword(rest)))), List.reverse.go(&2, String, Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "path"), ns), Main.rargs.has(Main.rargs.read(rest, Main.rword(rest)), "--dry-run", d), Main.rargs.has(Main.rargs.read(rest, Main.rword(rest)), "--fields", f), Main.rargs.last(Main.rargs.read(rest, Main.rword(rest)), "-m", mg)}, Main.RecordCmd{Main.rargs.last(Main.rargs.read(rest, Main.rword(rest)), "--onto", o), List.append(&2, String, ms, Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "--merge")), List.reverse.go(&2, String, Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "--accept"), ac), List.append(&2, T.Split, at, Main.rargs.cuts(Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "--at"))), List.append(&2, T.Split, mv, Main.rargs.cuts(Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "--move"))), List.append(&2, T.Split, ks, T.Split{v, "bytes"} <> Main.rargs.kinds(Main.rargs.read(rest, Main.rword(rest)))), List.reverse.go(&2, String, Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "path"), ns), Main.rargs.has(Main.rargs.read(rest, Main.rword(rest)), "--dry-run", d), Main.rargs.has(Main.rargs.read(rest, Main.rword(rest)), "--fields", f), Main.rargs.last(Main.rargs.read(rest, Main.rword(rest)), "-m", mg)},
        go_said(rest, o, ms, ac, at, mv, List.append(&2, T.Split, ks, [T.Split{v, "bytes"}]), ns, d, f, mg, Main.rword(rest), cmd, e),
        Equal.cong(List<&2, T.Split>, Main.RecordCmd, x => Main.RecordCmd{Main.rargs.last(Main.rargs.read(rest, Main.rword(rest)), "--onto", o), List.append(&2, String, ms, Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "--merge")), List.reverse.go(&2, String, Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "--accept"), ac), List.append(&2, T.Split, at, Main.rargs.cuts(Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "--at"))), List.append(&2, T.Split, mv, Main.rargs.cuts(Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "--move"))), x, List.reverse.go(&2, String, Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "path"), ns), Main.rargs.has(Main.rargs.read(rest, Main.rword(rest)), "--dry-run", d), Main.rargs.has(Main.rargs.read(rest, Main.rword(rest)), "--fields", f), Main.rargs.last(Main.rargs.read(rest, Main.rword(rest)), "-m", mg)}, List.append(&2, T.Split, List.append(&2, T.Split, ks, [T.Split{v, "bytes"}]), Main.rargs.kinds(Main.rargs.read(rest, Main.rword(rest)))), List.append(&2, T.Split, ks, T.Split{v, "bytes"} <> Main.rargs.kinds(Main.rargs.read(rest, Main.rword(rest)))), SortL.app_assoc(T.Split, ks, [T.Split{v, "bytes"}], Main.rargs.kinds(Main.rargs.read(rest, Main.rword(rest))))))
    case +w <> Nil{} Main.RWord.Lines{}:
      Empty.absurd({cmd == Main.RecordCmd{Main.rargs.last(Main.rargs.read([w], Main.RWord.Lines{}), "--onto", o), List.append(&2, String, ms, Main.rargs.values(Main.rargs.read([w], Main.RWord.Lines{}), "--merge")), List.reverse.go(&2, String, Main.rargs.values(Main.rargs.read([w], Main.RWord.Lines{}), "--accept"), ac), List.append(&2, T.Split, at, Main.rargs.cuts(Main.rargs.values(Main.rargs.read([w], Main.RWord.Lines{}), "--at"))), List.append(&2, T.Split, mv, Main.rargs.cuts(Main.rargs.values(Main.rargs.read([w], Main.RWord.Lines{}), "--move"))), List.append(&2, T.Split, ks, Main.rargs.kinds(Main.rargs.read([w], Main.RWord.Lines{}))), List.reverse.go(&2, String, Main.rargs.values(Main.rargs.read([w], Main.RWord.Lines{}), "path"), ns), Main.rargs.has(Main.rargs.read([w], Main.RWord.Lines{}), "--dry-run", d), Main.rargs.has(Main.rargs.read([w], Main.RWord.Lines{}), "--fields", f), Main.rargs.last(Main.rargs.read([w], Main.RWord.Lines{}), "-m", mg)} : Main.RecordCmd}, B.fail_done(Main.RecordCmd, Main.Refused{2, "`--lines` wants a value"}, cmd, e))
    case w <> +v <> +rest Main.RWord.Lines{}:
      Equal.trans(Main.RecordCmd, cmd, Main.RecordCmd{Main.rargs.last(Main.rargs.read(rest, Main.rword(rest)), "--onto", o), List.append(&2, String, ms, Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "--merge")), List.reverse.go(&2, String, Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "--accept"), ac), List.append(&2, T.Split, at, Main.rargs.cuts(Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "--at"))), List.append(&2, T.Split, mv, Main.rargs.cuts(Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "--move"))), List.append(&2, T.Split, List.append(&2, T.Split, ks, [T.Split{v, "lines"}]), Main.rargs.kinds(Main.rargs.read(rest, Main.rword(rest)))), List.reverse.go(&2, String, Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "path"), ns), Main.rargs.has(Main.rargs.read(rest, Main.rword(rest)), "--dry-run", d), Main.rargs.has(Main.rargs.read(rest, Main.rword(rest)), "--fields", f), Main.rargs.last(Main.rargs.read(rest, Main.rword(rest)), "-m", mg)}, Main.RecordCmd{Main.rargs.last(Main.rargs.read(rest, Main.rword(rest)), "--onto", o), List.append(&2, String, ms, Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "--merge")), List.reverse.go(&2, String, Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "--accept"), ac), List.append(&2, T.Split, at, Main.rargs.cuts(Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "--at"))), List.append(&2, T.Split, mv, Main.rargs.cuts(Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "--move"))), List.append(&2, T.Split, ks, T.Split{v, "lines"} <> Main.rargs.kinds(Main.rargs.read(rest, Main.rword(rest)))), List.reverse.go(&2, String, Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "path"), ns), Main.rargs.has(Main.rargs.read(rest, Main.rword(rest)), "--dry-run", d), Main.rargs.has(Main.rargs.read(rest, Main.rword(rest)), "--fields", f), Main.rargs.last(Main.rargs.read(rest, Main.rword(rest)), "-m", mg)},
        go_said(rest, o, ms, ac, at, mv, List.append(&2, T.Split, ks, [T.Split{v, "lines"}]), ns, d, f, mg, Main.rword(rest), cmd, e),
        Equal.cong(List<&2, T.Split>, Main.RecordCmd, x => Main.RecordCmd{Main.rargs.last(Main.rargs.read(rest, Main.rword(rest)), "--onto", o), List.append(&2, String, ms, Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "--merge")), List.reverse.go(&2, String, Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "--accept"), ac), List.append(&2, T.Split, at, Main.rargs.cuts(Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "--at"))), List.append(&2, T.Split, mv, Main.rargs.cuts(Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "--move"))), x, List.reverse.go(&2, String, Main.rargs.values(Main.rargs.read(rest, Main.rword(rest)), "path"), ns), Main.rargs.has(Main.rargs.read(rest, Main.rword(rest)), "--dry-run", d), Main.rargs.has(Main.rargs.read(rest, Main.rword(rest)), "--fields", f), Main.rargs.last(Main.rargs.read(rest, Main.rword(rest)), "-m", mg)}, List.append(&2, T.Split, List.append(&2, T.Split, ks, [T.Split{v, "lines"}]), Main.rargs.kinds(Main.rargs.read(rest, Main.rword(rest)))), List.append(&2, T.Split, ks, T.Split{v, "lines"} <> Main.rargs.kinds(Main.rargs.read(rest, Main.rword(rest)))), SortL.app_assoc(T.Split, ks, [T.Split{v, "lines"}], Main.rargs.kinds(Main.rargs.read(rest, Main.rword(rest))))))
    case w <> Nil{} Main.RWord.Dry{}:
      go_said(Nil{}, o, ms, ac, at, mv, ks, ns, True{}, f, mg, Main.rword(Nil{}), cmd, e)
    case w <> +v <> +rest Main.RWord.Dry{}:
      go_said(v <> rest, o, ms, ac, at, mv, ks, ns, True{}, f, mg, Main.rword(v <> rest), cmd, e)
    case w <> Nil{} Main.RWord.Fields{}:
      go_said(Nil{}, o, ms, ac, at, mv, ks, ns, d, True{}, mg, Main.rword(Nil{}), cmd, e)
    case w <> +v <> +rest Main.RWord.Fields{}:
      go_said(v <> rest, o, ms, ac, at, mv, ks, ns, d, True{}, mg, Main.rword(v <> rest), cmd, e)
    case +w <> Nil{} Main.RWord.Flag{}:
      Empty.absurd({cmd == Main.RecordCmd{Main.rargs.last(Main.rargs.read([w], Main.RWord.Flag{}), "--onto", o), List.append(&2, String, ms, Main.rargs.values(Main.rargs.read([w], Main.RWord.Flag{}), "--merge")), List.reverse.go(&2, String, Main.rargs.values(Main.rargs.read([w], Main.RWord.Flag{}), "--accept"), ac), List.append(&2, T.Split, at, Main.rargs.cuts(Main.rargs.values(Main.rargs.read([w], Main.RWord.Flag{}), "--at"))), List.append(&2, T.Split, mv, Main.rargs.cuts(Main.rargs.values(Main.rargs.read([w], Main.RWord.Flag{}), "--move"))), List.append(&2, T.Split, ks, Main.rargs.kinds(Main.rargs.read([w], Main.RWord.Flag{}))), List.reverse.go(&2, String, Main.rargs.values(Main.rargs.read([w], Main.RWord.Flag{}), "path"), ns), Main.rargs.has(Main.rargs.read([w], Main.RWord.Flag{}), "--dry-run", d), Main.rargs.has(Main.rargs.read([w], Main.RWord.Flag{}), "--fields", f), Main.rargs.last(Main.rargs.read([w], Main.RWord.Flag{}), "-m", mg)} : Main.RecordCmd}, B.fail_done(Main.RecordCmd, Main.Refused{2, "`" ++ w ++ "` is not an argument `record` takes"}, cmd, e))
    case +w <> +v <> +rest Main.RWord.Flag{}:
      Empty.absurd({cmd == Main.RecordCmd{Main.rargs.last(Main.rargs.read(w <> v <> rest, Main.RWord.Flag{}), "--onto", o), List.append(&2, String, ms, Main.rargs.values(Main.rargs.read(w <> v <> rest, Main.RWord.Flag{}), "--merge")), List.reverse.go(&2, String, Main.rargs.values(Main.rargs.read(w <> v <> rest, Main.RWord.Flag{}), "--accept"), ac), List.append(&2, T.Split, at, Main.rargs.cuts(Main.rargs.values(Main.rargs.read(w <> v <> rest, Main.RWord.Flag{}), "--at"))), List.append(&2, T.Split, mv, Main.rargs.cuts(Main.rargs.values(Main.rargs.read(w <> v <> rest, Main.RWord.Flag{}), "--move"))), List.append(&2, T.Split, ks, Main.rargs.kinds(Main.rargs.read(w <> v <> rest, Main.RWord.Flag{}))), List.reverse.go(&2, String, Main.rargs.values(Main.rargs.read(w <> v <> rest, Main.RWord.Flag{}), "path"), ns), Main.rargs.has(Main.rargs.read(w <> v <> rest, Main.RWord.Flag{}), "--dry-run", d), Main.rargs.has(Main.rargs.read(w <> v <> rest, Main.RWord.Flag{}), "--fields", f), Main.rargs.last(Main.rargs.read(w <> v <> rest, Main.RWord.Flag{}), "-m", mg)} : Main.RecordCmd}, B.fail_done(Main.RecordCmd, Main.Refused{2, "`" ++ w ++ "` is not an argument `record` takes"}, cmd, e))
    case +w <> Nil{} Main.RWord.Path{}:
      path_bind(Main.trimmed(w), Nil{}, o, ms, ac, at, mv, ks, ns, d, f, mg, Main.record.path(Main.RecordCmd{o, ms, ac, at, mv, ks, ns, d, f, mg}, Main.trimmed(w)), cmd, {==}, e, ns2 => h => go_said(Nil{}, o, ms, ac, at, mv, ks, ns2, d, f, mg, Main.rword(Nil{}), cmd, h))
    case +w <> +v <> +rest Main.RWord.Path{}:
      path_bind(Main.trimmed(w), v <> rest, o, ms, ac, at, mv, ks, ns, d, f, mg, Main.record.path(Main.RecordCmd{o, ms, ac, at, mv, ks, ns, d, f, mg}, Main.trimmed(w)), cmd, {==}, e, ns2 => h => go_said(v <> rest, o, ms, ac, at, mv, ks, ns2, d, f, mg, Main.rword(v <> rest), cmd, h))

# `record` reads its words as their plain reading says.
def args_said(+args: List<&2, String>, +cmd: Main.RecordCmd, e: {Main.record.args.r(args) == Done{cmd} : Result<&2, &2, Main.Refused, Main.RecordCmd>}) -> {cmd == Main.rargs.said(Main.rargs.read(args, Main.rword(args))) : Main.RecordCmd}:
  go_said(args, None{}, Nil{}, Nil{}, Nil{}, Nil{}, Nil{}, Nil{}, False{}, False{}, None{}, Main.rword(args), cmd, e)

# Rewriting's words
# -----------------

def done_rw(-a: Main.RwCmd, -b: Main.RwCmd, h: {Done{a} == Done{b} : Result<&2, &2, Main.Refused, Main.RwCmd>}) -> {a == b : Main.RwCmd}:
  B.done_eq(Main.RwCmd, a, b, h)

def rw_move_bind(+cmd: String, +v: String, +rest: List<&2, String>, +m: Maybe<&2, String>, +mv: List<&2, T.Split>, +o: Maybe<&2, String>, +n: Maybe<&2, String>, +d: Bool, +f: Bool, +y: Bool, r: Result<&2, &2, Main.Refused, T.Split>, +c: Main.RwCmd, er: {Main.record.split(v, "`--move` is spelled `--move <old>=<new>`") == r : Result<&2, &2, Main.Refused, T.Split>}, e: {Result.bind(&2, &2, Main.Refused, T.Split, Main.RwCmd, r, s => Main.rw.args.go(cmd, rest, Main.rw.move(Main.RwCmd{m, mv, o, n, d, f, y}, s), Main.wword(cmd, rest))) == Done{c} : Result<&2, &2, Main.Refused, Main.RwCmd>}, ih: @mv2: List<&2, T.Split> -> {Main.rw.args.go(cmd, rest, Main.RwCmd{m, mv2, o, n, d, f, y}, Main.wword(cmd, rest)) == Done{c} : Result<&2, &2, Main.Refused, Main.RwCmd>} -> {c == Main.RwCmd{Main.rargs.last(Main.wargs.read(cmd, rest, Main.wword(cmd, rest)), "-m", m), List.append(&2, T.Split, mv2, Main.rargs.cuts(Main.rargs.values(Main.wargs.read(cmd, rest, Main.wword(cmd, rest)), "--move"))), Main.rargs.last(Main.wargs.read(cmd, rest, Main.wword(cmd, rest)), "--onto", o), Main.rargs.last(Main.wargs.read(cmd, rest, Main.wword(cmd, rest)), "target", n), Main.rargs.has(Main.wargs.read(cmd, rest, Main.wword(cmd, rest)), "--dry-run", d), Main.rargs.has(Main.wargs.read(cmd, rest, Main.wword(cmd, rest)), "--fields", f), Main.rargs.has(Main.wargs.read(cmd, rest, Main.wword(cmd, rest)), "--only", y)} : Main.RwCmd}) -> {c == Main.RwCmd{Main.rargs.last(Main.wargs.read(cmd, rest, Main.wword(cmd, rest)), "-m", m), List.append(&2, T.Split, mv, Main.rargs.cut(v) <> Main.rargs.cuts(Main.rargs.values(Main.wargs.read(cmd, rest, Main.wword(cmd, rest)), "--move"))), Main.rargs.last(Main.wargs.read(cmd, rest, Main.wword(cmd, rest)), "--onto", o), Main.rargs.last(Main.wargs.read(cmd, rest, Main.wword(cmd, rest)), "target", n), Main.rargs.has(Main.wargs.read(cmd, rest, Main.wword(cmd, rest)), "--dry-run", d), Main.rargs.has(Main.wargs.read(cmd, rest, Main.wword(cmd, rest)), "--fields", f), Main.rargs.has(Main.wargs.read(cmd, rest, Main.wword(cmd, rest)), "--only", y)} : Main.RwCmd}:
  match r:
    case Fail{x}:
      Empty.absurd({c == Main.RwCmd{Main.rargs.last(Main.wargs.read(cmd, rest, Main.wword(cmd, rest)), "-m", m), List.append(&2, T.Split, mv, Main.rargs.cut(v) <> Main.rargs.cuts(Main.rargs.values(Main.wargs.read(cmd, rest, Main.wword(cmd, rest)), "--move"))), Main.rargs.last(Main.wargs.read(cmd, rest, Main.wword(cmd, rest)), "--onto", o), Main.rargs.last(Main.wargs.read(cmd, rest, Main.wword(cmd, rest)), "target", n), Main.rargs.has(Main.wargs.read(cmd, rest, Main.wword(cmd, rest)), "--dry-run", d), Main.rargs.has(Main.wargs.read(cmd, rest, Main.wword(cmd, rest)), "--fields", f), Main.rargs.has(Main.wargs.read(cmd, rest, Main.wword(cmd, rest)), "--only", y)} : Main.RwCmd}, B.fail_done(Main.RwCmd, x, c, e))
    case Done{+s}:
      +hs = split_cut(v, "`--move` is spelled `--move <old>=<new>`", s, er)
      +assoc = Equal.trans(List<&2, T.Split>, List.append(&2, T.Split, List.append(&2, T.Split, mv, [s]), Main.rargs.cuts(Main.rargs.values(Main.wargs.read(cmd, rest, Main.wword(cmd, rest)), "--move"))), List.append(&2, T.Split, mv, s <> Main.rargs.cuts(Main.rargs.values(Main.wargs.read(cmd, rest, Main.wword(cmd, rest)), "--move"))), List.append(&2, T.Split, mv, Main.rargs.cut(v) <> Main.rargs.cuts(Main.rargs.values(Main.wargs.read(cmd, rest, Main.wword(cmd, rest)), "--move"))),
        SortL.app_assoc(T.Split, mv, [s], Main.rargs.cuts(Main.rargs.values(Main.wargs.read(cmd, rest, Main.wword(cmd, rest)), "--move"))),
        Equal.cong(T.Split, List<&2, T.Split>, z => List.append(&2, T.Split, mv, z <> Main.rargs.cuts(Main.rargs.values(Main.wargs.read(cmd, rest, Main.wword(cmd, rest)), "--move"))), s, Main.rargs.cut(v), hs))
      Equal.trans(Main.RwCmd, c, Main.RwCmd{Main.rargs.last(Main.wargs.read(cmd, rest, Main.wword(cmd, rest)), "-m", m), List.append(&2, T.Split, List.append(&2, T.Split, mv, [s]), Main.rargs.cuts(Main.rargs.values(Main.wargs.read(cmd, rest, Main.wword(cmd, rest)), "--move"))), Main.rargs.last(Main.wargs.read(cmd, rest, Main.wword(cmd, rest)), "--onto", o), Main.rargs.last(Main.wargs.read(cmd, rest, Main.wword(cmd, rest)), "target", n), Main.rargs.has(Main.wargs.read(cmd, rest, Main.wword(cmd, rest)), "--dry-run", d), Main.rargs.has(Main.wargs.read(cmd, rest, Main.wword(cmd, rest)), "--fields", f), Main.rargs.has(Main.wargs.read(cmd, rest, Main.wword(cmd, rest)), "--only", y)}, Main.RwCmd{Main.rargs.last(Main.wargs.read(cmd, rest, Main.wword(cmd, rest)), "-m", m), List.append(&2, T.Split, mv, Main.rargs.cut(v) <> Main.rargs.cuts(Main.rargs.values(Main.wargs.read(cmd, rest, Main.wword(cmd, rest)), "--move"))), Main.rargs.last(Main.wargs.read(cmd, rest, Main.wword(cmd, rest)), "--onto", o), Main.rargs.last(Main.wargs.read(cmd, rest, Main.wword(cmd, rest)), "target", n), Main.rargs.has(Main.wargs.read(cmd, rest, Main.wword(cmd, rest)), "--dry-run", d), Main.rargs.has(Main.wargs.read(cmd, rest, Main.wword(cmd, rest)), "--fields", f), Main.rargs.has(Main.wargs.read(cmd, rest, Main.wword(cmd, rest)), "--only", y)},
        ih(List.append(&2, T.Split, mv, [s]), e),
        Equal.cong(List<&2, T.Split>, Main.RwCmd, x => Main.RwCmd{Main.rargs.last(Main.wargs.read(cmd, rest, Main.wword(cmd, rest)), "-m", m), x, Main.rargs.last(Main.wargs.read(cmd, rest, Main.wword(cmd, rest)), "--onto", o), Main.rargs.last(Main.wargs.read(cmd, rest, Main.wword(cmd, rest)), "target", n), Main.rargs.has(Main.wargs.read(cmd, rest, Main.wword(cmd, rest)), "--dry-run", d), Main.rargs.has(Main.wargs.read(cmd, rest, Main.wword(cmd, rest)), "--fields", f), Main.rargs.has(Main.wargs.read(cmd, rest, Main.wword(cmd, rest)), "--only", y)}, List.append(&2, T.Split, List.append(&2, T.Split, mv, [s]), Main.rargs.cuts(Main.rargs.values(Main.wargs.read(cmd, rest, Main.wword(cmd, rest)), "--move"))), List.append(&2, T.Split, mv, Main.rargs.cut(v) <> Main.rargs.cuts(Main.rargs.values(Main.wargs.read(cmd, rest, Main.wword(cmd, rest)), "--move"))), assoc))

def rw_word(n: Maybe<&2, String>, +cmd: String, +w: String, +tail: List<&2, String>, +m: Maybe<&2, String>, +mv: List<&2, T.Split>, +o: Maybe<&2, String>, +d: Bool, +f: Bool, +y: Bool, +c: Main.RwCmd, e: {Result.bind(&2, &2, Main.Refused, Main.RwCmd, Main.RwCmd, Main.rw.word(cmd, Main.RwCmd{m, mv, o, n, d, f, y}, w), more => Main.rw.args.go(cmd, tail, more, Main.wword(cmd, tail))) == Done{c} : Result<&2, &2, Main.Refused, Main.RwCmd>}, ih: {Main.rw.args.go(cmd, tail, Main.RwCmd{m, mv, o, Some{w}, d, f, y}, Main.wword(cmd, tail)) == Done{c} : Result<&2, &2, Main.Refused, Main.RwCmd>} -> {c == Main.RwCmd{Main.rargs.last(Main.wargs.read(cmd, tail, Main.wword(cmd, tail)), "-m", m), List.append(&2, T.Split, mv, Main.rargs.cuts(Main.rargs.values(Main.wargs.read(cmd, tail, Main.wword(cmd, tail)), "--move"))), Main.rargs.last(Main.wargs.read(cmd, tail, Main.wword(cmd, tail)), "--onto", o), Main.rargs.last(Main.wargs.read(cmd, tail, Main.wword(cmd, tail)), "target", Some{w}), Main.rargs.has(Main.wargs.read(cmd, tail, Main.wword(cmd, tail)), "--dry-run", d), Main.rargs.has(Main.wargs.read(cmd, tail, Main.wword(cmd, tail)), "--fields", f), Main.rargs.has(Main.wargs.read(cmd, tail, Main.wword(cmd, tail)), "--only", y)} : Main.RwCmd}) -> {c == Main.RwCmd{Main.rargs.last(T.Split{"target", w} <> Main.wargs.read(cmd, tail, Main.wword(cmd, tail)), "-m", m), List.append(&2, T.Split, mv, Main.rargs.cuts(Main.rargs.values(T.Split{"target", w} <> Main.wargs.read(cmd, tail, Main.wword(cmd, tail)), "--move"))), Main.rargs.last(T.Split{"target", w} <> Main.wargs.read(cmd, tail, Main.wword(cmd, tail)), "--onto", o), Main.rargs.last(T.Split{"target", w} <> Main.wargs.read(cmd, tail, Main.wword(cmd, tail)), "target", n), Main.rargs.has(T.Split{"target", w} <> Main.wargs.read(cmd, tail, Main.wword(cmd, tail)), "--dry-run", d), Main.rargs.has(T.Split{"target", w} <> Main.wargs.read(cmd, tail, Main.wword(cmd, tail)), "--fields", f), Main.rargs.has(T.Split{"target", w} <> Main.wargs.read(cmd, tail, Main.wword(cmd, tail)), "--only", y)} : Main.RwCmd}:
  match n:
    case None{}:
      ih(e)
    case Some{x}:
      Empty.absurd({c == Main.RwCmd{Main.rargs.last(T.Split{"target", w} <> Main.wargs.read(cmd, tail, Main.wword(cmd, tail)), "-m", m), List.append(&2, T.Split, mv, Main.rargs.cuts(Main.rargs.values(T.Split{"target", w} <> Main.wargs.read(cmd, tail, Main.wword(cmd, tail)), "--move"))), Main.rargs.last(T.Split{"target", w} <> Main.wargs.read(cmd, tail, Main.wword(cmd, tail)), "--onto", o), Main.rargs.last(T.Split{"target", w} <> Main.wargs.read(cmd, tail, Main.wword(cmd, tail)), "target", Some{x}), Main.rargs.has(T.Split{"target", w} <> Main.wargs.read(cmd, tail, Main.wword(cmd, tail)), "--dry-run", d), Main.rargs.has(T.Split{"target", w} <> Main.wargs.read(cmd, tail, Main.wword(cmd, tail)), "--fields", f), Main.rargs.has(T.Split{"target", w} <> Main.wargs.read(cmd, tail, Main.wword(cmd, tail)), "--only", y)} : Main.RwCmd}, B.fail_done(Main.RwCmd, Main.Refused{2, Main.rw.second(cmd, w)}, c, e))

# One pass over the words reads what their plain reading says.
def rw_go_said(+cmd: String, args: List<&2, String>, +m: Maybe<&2, String>, +mv: List<&2, T.Split>, +o: Maybe<&2, String>, +n: Maybe<&2, String>, +d: Bool, +f: Bool, +y: Bool, k: Main.WWord, +c: Main.RwCmd, e: {Main.rw.args.go(cmd, args, Main.RwCmd{m, mv, o, n, d, f, y}, k) == Done{c} : Result<&2, &2, Main.Refused, Main.RwCmd>}) -> {c == Main.RwCmd{Main.rargs.last(Main.wargs.read(cmd, args, k), "-m", m), List.append(&2, T.Split, mv, Main.rargs.cuts(Main.rargs.values(Main.wargs.read(cmd, args, k), "--move"))), Main.rargs.last(Main.wargs.read(cmd, args, k), "--onto", o), Main.rargs.last(Main.wargs.read(cmd, args, k), "target", n), Main.rargs.has(Main.wargs.read(cmd, args, k), "--dry-run", d), Main.rargs.has(Main.wargs.read(cmd, args, k), "--fields", f), Main.rargs.has(Main.wargs.read(cmd, args, k), "--only", y)} : Main.RwCmd}:
  match args k:
    case Nil{} _:
      %done_rw(Main.RwCmd{m, mv, o, n, d, f, y}, c, e) : {_ == Main.RwCmd{m, List.append(&2, T.Split, mv, Nil{}), o, n, d, f, y} : Main.RwCmd}
      %Equal.sym(List<&2, T.Split>, List.append(&2, T.Split, mv, Nil{}), mv, SortL.lapp_nil(T.Split, mv)) : {Main.RwCmd{m, mv, o, n, d, f, y} == Main.RwCmd{m, _, o, n, d, f, y} : Main.RwCmd}
      {==}
    case +w <> Nil{} Main.WWord.Message{}:
      Empty.absurd({c == Main.RwCmd{Main.rargs.last(Main.wargs.read(cmd, [w], Main.WWord.Message{}), "-m", m), List.append(&2, T.Split, mv, Main.rargs.cuts(Main.rargs.values(Main.wargs.read(cmd, [w], Main.WWord.Message{}), "--move"))), Main.rargs.last(Main.wargs.read(cmd, [w], Main.WWord.Message{}), "--onto", o), Main.rargs.last(Main.wargs.read(cmd, [w], Main.WWord.Message{}), "target", n), Main.rargs.has(Main.wargs.read(cmd, [w], Main.WWord.Message{}), "--dry-run", d), Main.rargs.has(Main.wargs.read(cmd, [w], Main.WWord.Message{}), "--fields", f), Main.rargs.has(Main.wargs.read(cmd, [w], Main.WWord.Message{}), "--only", y)} : Main.RwCmd}, B.fail_done(Main.RwCmd, Main.Refused{2, "`-m` wants a value"}, c, e))
    case w <> +v <> +rest Main.WWord.Message{}:
      rw_go_said(cmd, rest, Some{v}, mv, o, n, d, f, y, Main.wword(cmd, rest), c, e)
    case +w <> Nil{} Main.WWord.Move{}:
      Empty.absurd({c == Main.RwCmd{Main.rargs.last(Main.wargs.read(cmd, [w], Main.WWord.Move{}), "-m", m), List.append(&2, T.Split, mv, Main.rargs.cuts(Main.rargs.values(Main.wargs.read(cmd, [w], Main.WWord.Move{}), "--move"))), Main.rargs.last(Main.wargs.read(cmd, [w], Main.WWord.Move{}), "--onto", o), Main.rargs.last(Main.wargs.read(cmd, [w], Main.WWord.Move{}), "target", n), Main.rargs.has(Main.wargs.read(cmd, [w], Main.WWord.Move{}), "--dry-run", d), Main.rargs.has(Main.wargs.read(cmd, [w], Main.WWord.Move{}), "--fields", f), Main.rargs.has(Main.wargs.read(cmd, [w], Main.WWord.Move{}), "--only", y)} : Main.RwCmd}, B.fail_done(Main.RwCmd, Main.Refused{2, "`--move` wants a value"}, c, e))
    case w <> +v <> +rest Main.WWord.Move{}:
      rw_move_bind(cmd, v, rest, m, mv, o, n, d, f, y, Main.record.split(v, "`--move` is spelled `--move <old>=<new>`"), c, {==}, e, mv2 => h => rw_go_said(cmd, rest, m, mv2, o, n, d, f, y, Main.wword(cmd, rest), c, h))
    case +w <> Nil{} Main.WWord.Onto{}:
      Empty.absurd({c == Main.RwCmd{Main.rargs.last(Main.wargs.read(cmd, [w], Main.WWord.Onto{}), "-m", m), List.append(&2, T.Split, mv, Main.rargs.cuts(Main.rargs.values(Main.wargs.read(cmd, [w], Main.WWord.Onto{}), "--move"))), Main.rargs.last(Main.wargs.read(cmd, [w], Main.WWord.Onto{}), "--onto", o), Main.rargs.last(Main.wargs.read(cmd, [w], Main.WWord.Onto{}), "target", n), Main.rargs.has(Main.wargs.read(cmd, [w], Main.WWord.Onto{}), "--dry-run", d), Main.rargs.has(Main.wargs.read(cmd, [w], Main.WWord.Onto{}), "--fields", f), Main.rargs.has(Main.wargs.read(cmd, [w], Main.WWord.Onto{}), "--only", y)} : Main.RwCmd}, B.fail_done(Main.RwCmd, Main.Refused{2, "`--onto` wants a value"}, c, e))
    case w <> +v <> +rest Main.WWord.Onto{}:
      rw_go_said(cmd, rest, m, mv, Some{v}, n, d, f, y, Main.wword(cmd, rest), c, e)
    case w <> Nil{} Main.WWord.Only{}:
      rw_go_said(cmd, Nil{}, m, mv, o, n, d, f, True{}, Main.wword(cmd, Nil{}), c, e)
    case w <> +v <> +rest Main.WWord.Only{}:
      rw_go_said(cmd, v <> rest, m, mv, o, n, d, f, True{}, Main.wword(cmd, v <> rest), c, e)
    case w <> Nil{} Main.WWord.Dry{}:
      rw_go_said(cmd, Nil{}, m, mv, o, n, True{}, f, y, Main.wword(cmd, Nil{}), c, e)
    case w <> +v <> +rest Main.WWord.Dry{}:
      rw_go_said(cmd, v <> rest, m, mv, o, n, True{}, f, y, Main.wword(cmd, v <> rest), c, e)
    case w <> Nil{} Main.WWord.Fields{}:
      rw_go_said(cmd, Nil{}, m, mv, o, n, d, True{}, y, Main.wword(cmd, Nil{}), c, e)
    case w <> +v <> +rest Main.WWord.Fields{}:
      rw_go_said(cmd, v <> rest, m, mv, o, n, d, True{}, y, Main.wword(cmd, v <> rest), c, e)
    case +w <> Nil{} Main.WWord.Flag{}:
      Empty.absurd({c == Main.RwCmd{Main.rargs.last(Main.wargs.read(cmd, [w], Main.WWord.Flag{}), "-m", m), List.append(&2, T.Split, mv, Main.rargs.cuts(Main.rargs.values(Main.wargs.read(cmd, [w], Main.WWord.Flag{}), "--move"))), Main.rargs.last(Main.wargs.read(cmd, [w], Main.WWord.Flag{}), "--onto", o), Main.rargs.last(Main.wargs.read(cmd, [w], Main.WWord.Flag{}), "target", n), Main.rargs.has(Main.wargs.read(cmd, [w], Main.WWord.Flag{}), "--dry-run", d), Main.rargs.has(Main.wargs.read(cmd, [w], Main.WWord.Flag{}), "--fields", f), Main.rargs.has(Main.wargs.read(cmd, [w], Main.WWord.Flag{}), "--only", y)} : Main.RwCmd}, B.fail_done(Main.RwCmd, Main.Refused{2, "`" ++ w ++ "` is not an argument `" ++ cmd ++ "` takes"}, c, e))
    case +w <> +v <> +rest Main.WWord.Flag{}:
      Empty.absurd({c == Main.RwCmd{Main.rargs.last(Main.wargs.read(cmd, w <> v <> rest, Main.WWord.Flag{}), "-m", m), List.append(&2, T.Split, mv, Main.rargs.cuts(Main.rargs.values(Main.wargs.read(cmd, w <> v <> rest, Main.WWord.Flag{}), "--move"))), Main.rargs.last(Main.wargs.read(cmd, w <> v <> rest, Main.WWord.Flag{}), "--onto", o), Main.rargs.last(Main.wargs.read(cmd, w <> v <> rest, Main.WWord.Flag{}), "target", n), Main.rargs.has(Main.wargs.read(cmd, w <> v <> rest, Main.WWord.Flag{}), "--dry-run", d), Main.rargs.has(Main.wargs.read(cmd, w <> v <> rest, Main.WWord.Flag{}), "--fields", f), Main.rargs.has(Main.wargs.read(cmd, w <> v <> rest, Main.WWord.Flag{}), "--only", y)} : Main.RwCmd}, B.fail_done(Main.RwCmd, Main.Refused{2, "`" ++ w ++ "` is not an argument `" ++ cmd ++ "` takes"}, c, e))
    case +w <> Nil{} Main.WWord.Word{}:
      rw_word(n, cmd, w, Nil{}, m, mv, o, d, f, y, c, e, h => rw_go_said(cmd, Nil{}, m, mv, o, Some{w}, d, f, y, Main.wword(cmd, Nil{}), c, h))
    case +w <> +v <> +rest Main.WWord.Word{}:
      rw_word(n, cmd, w, v <> rest, m, mv, o, d, f, y, c, e, h => rw_go_said(cmd, v <> rest, m, mv, o, Some{w}, d, f, y, Main.wword(cmd, v <> rest), c, h))

# `amend`, `abandon` and `carry` read their words as their plain reading
# says.
def rw_args_said(+cmd: String, +args: List<&2, String>, +c: Main.RwCmd, e: {Main.rw.args.r(cmd, args) == Done{c} : Result<&2, &2, Main.Refused, Main.RwCmd>}) -> {c == Main.wargs.said(Main.wargs.read(cmd, args, Main.wword(cmd, args))) : Main.RwCmd}:
  rw_go_said(cmd, args, None{}, Nil{}, None{}, None{}, False{}, False{}, False{}, Main.wword(cmd, args), c, e)


# What it states is what the folder holds
# ---------------------------------------

def u32_refl(x: U32) -> {U32.is_eq(x, x) == True{} : Bool}:
  match x:
    case U32{+w}:
      %Equal.sym(Cmp, Word.cmp(32n, w, w), EQ{}, S.word_refl(32n, w)) : {Cmp.is_eq(_) == True{} : Bool}
      {==}

def bytes_refl(xs: List<&2, U32>) -> {Main.bytes.same(xs, xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      B.and_tt(U32.is_eq(x, x), Main.bytes.same(rest, rest), u32_refl(x), bytes_refl(rest))

def items_refl(xs: List<&2, Ops.Item>) -> {Main.items_eq(xs, xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      B.and_tt(Main.item_eq(x, x), Main.items_eq(rest, rest), HunkL.item_refl(x), items_refl(rest))

def state_app(+befores: List<&2, Main.Before>, +dg: Map<&2, String>, +reads: Map<&2, List<&2, U32>>, cs: List<&2, Main.Content>, +ds: List<&2, Main.Content>, +hc: {Main.contents.state(befores, dg, reads, cs) == True{} : Bool}, hd: {Main.contents.state(befores, dg, reads, ds) == True{} : Bool}) -> {Main.contents.state(befores, dg, reads, List.append(&2, Main.Content, cs, ds)) == True{} : Bool}:
  match cs:
    case Nil{}:
      hd
    case +c <> +rest:
      B.and_tt(Main.content.states(befores, dg, reads, c), Main.contents.state(befores, dg, reads, List.append(&2, Main.Content, rest, ds)),
        SortL.band_l(Main.content.states(befores, dg, reads, c), Main.contents.state(befores, dg, reads, rest), hc),
        state_app(befores, dg, reads, rest, ds, SortL.band_r(Main.content.states(befores, dg, reads, c), Main.contents.state(befores, dg, reads, rest), hc), hd))

def pick_state(+befores: List<&2, Main.Before>, +dg: Map<&2, String>, +reads: Map<&2, List<&2, U32>>, b: Bool, +cs: List<&2, Main.Content>, h: {Main.contents.state(befores, dg, reads, cs) == True{} : Bool}) -> {Main.contents.state(befores, dg, reads, Bool.pick(List<&2, Main.Content>, b, cs, Nil{})) == True{} : Bool}:
  match b:
    case True{}:
      h
    case False{}:
      {==}

def unpick_state(+befores: List<&2, Main.Before>, +dg: Map<&2, String>, +reads: Map<&2, List<&2, U32>>, b: Bool, +cs: List<&2, Main.Content>, h: {Main.contents.state(befores, dg, reads, cs) == True{} : Bool}) -> {Main.contents.state(befores, dg, reads, Bool.pick(List<&2, Main.Content>, b, Nil{}, cs)) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      h

def either_state(+befores: List<&2, Main.Before>, +dg: Map<&2, String>, +reads: Map<&2, List<&2, U32>>, b: Bool, +cs: List<&2, Main.Content>, +ds: List<&2, Main.Content>, hc: {Main.contents.state(befores, dg, reads, cs) == True{} : Bool}, hd: {Main.contents.state(befores, dg, reads, ds) == True{} : Bool}) -> {Main.contents.state(befores, dg, reads, Bool.pick(List<&2, Main.Content>, b, cs, ds)) == True{} : Bool}:
  match b:
    case True{}:
      hc
    case False{}:
      hd

def one_state(+befores: List<&2, Main.Before>, +dg: Map<&2, String>, +reads: Map<&2, List<&2, U32>>, +c: Main.Content, h: {Main.content.states(befores, dg, reads, c) == True{} : Bool}) -> {Main.contents.state(befores, dg, reads, [c]) == True{} : Bool}:
  B.and_tt(Main.content.states(befores, dg, reads, c), True{}, h, {==})

def whole_state(+befores: List<&2, Main.Before>, +dg: Map<&2, String>, +reads: Map<&2, List<&2, U32>>, +f: String, +p: String) -> {Main.contents.state(befores, dg, reads, [Main.Content.Whole{f, p, Main.status.folder_digest(dg, p)}]) == True{} : Bool}:
  one_state(befores, dg, reads, Main.Content.Whole{f, p, Main.status.folder_digest(dg, p)}, S.eq_refl(Main.status.folder_digest(dg, p)))

def text_state(+befores: List<&2, Main.Before>, +dg: Map<&2, String>, +reads: Map<&2, List<&2, U32>>, +f: String, +p: String) -> {Main.contents.state(befores, dg, reads, [Main.Content.Text{f, p, Main.bytes_of(p, Map.get(List<&2, U32>, Nil{}, reads, p))}]) == True{} : Bool}:
  one_state(befores, dg, reads, Main.Content.Text{f, p, Main.bytes_of(p, Map.get(List<&2, U32>, Nil{}, reads, p))}, bytes_refl(Main.bytes_of(p, Map.get(List<&2, U32>, Nil{}, reads, p))))

# An edit is the document the diff finds, which replays.
def edited_state(~da: @parent: List<&2, Ops.Item> -> @child: List<&2, Ops.Item> -> {Ops.terminated_but_last(child) == True{} : Bool} -> @doc: Ops.Doc -> {Ops.diff(parent, child) == Some{doc} : Maybe<&2, Ops.Doc>} -> {Ops.apply(parent, doc) == Done{child} : Result<&2, &2, String, List<&2, Ops.Item>>}, +befores: List<&2, Main.Before>, +dg: Map<&2, String>, +reads: Map<&2, List<&2, U32>>, d: Maybe<&2, Ops.Doc>, +f: String, +p: String, +ed: {Ops.diff(Main.before_of(befores, f), Ops.from_text(Utf8.decode(Main.bytes_of(p, Map.get(List<&2, U32>, Nil{}, reads, p))))) == d : Maybe<&2, Ops.Doc>}) -> {Main.contents.state(befores, dg, reads, Main.edited.content(f, p, d)) == True{} : Bool}:
  match d:
    case None{}:
      {==}
    case Some{+doc}:
      +ha = da(Main.before_of(befores, f), Ops.from_text(Utf8.decode(Main.bytes_of(p, Map.get(List<&2, U32>, Nil{}, reads, p)))), BlameL.tbl_text(Utf8.decode(Main.bytes_of(p, Map.get(List<&2, U32>, Nil{}, reads, p)))), doc, ed)
      +hs = Equal.trans(Bool, Main.content.states(befores, dg, reads, Main.Content.Ops{f, p, Ops.write(doc)}), Main.content.replays(Main.before_of(befores, f), Ops.from_text(Utf8.decode(Main.bytes_of(p, Map.get(List<&2, U32>, Nil{}, reads, p)))), Ops.write(doc), Some{doc}), True{},
        Equal.cong(Maybe<&2, Ops.Doc>, Bool, x => Main.content.replays(Main.before_of(befores, f), Ops.from_text(Utf8.decode(Main.bytes_of(p, Map.get(List<&2, U32>, Nil{}, reads, p)))), Ops.write(doc), x), Ops.diff(Main.before_of(befores, f), Ops.from_text(Utf8.decode(Main.bytes_of(p, Map.get(List<&2, U32>, Nil{}, reads, p))))), Some{doc}, ed),
        B.and_tt(String.eq(Ops.write(doc), Ops.write(doc)), Main.content.applied(Ops.apply(Main.before_of(befores, f), doc), Ops.from_text(Utf8.decode(Main.bytes_of(p, Map.get(List<&2, U32>, Nil{}, reads, p))))), S.eq_refl(Ops.write(doc)),
          Equal.trans(Bool, Main.content.applied(Ops.apply(Main.before_of(befores, f), doc), Ops.from_text(Utf8.decode(Main.bytes_of(p, Map.get(List<&2, U32>, Nil{}, reads, p))))), Main.content.applied(Done{Ops.from_text(Utf8.decode(Main.bytes_of(p, Map.get(List<&2, U32>, Nil{}, reads, p))))}, Ops.from_text(Utf8.decode(Main.bytes_of(p, Map.get(List<&2, U32>, Nil{}, reads, p))))), True{},
            Equal.cong(Result<&2, &2, String, List<&2, Ops.Item>>, Bool, r => Main.content.applied(r, Ops.from_text(Utf8.decode(Main.bytes_of(p, Map.get(List<&2, U32>, Nil{}, reads, p))))), Ops.apply(Main.before_of(befores, f), doc), Done{Ops.from_text(Utf8.decode(Main.bytes_of(p, Map.get(List<&2, U32>, Nil{}, reads, p))))}, ha),
            items_refl(Ops.from_text(Utf8.decode(Main.bytes_of(p, Map.get(List<&2, U32>, Nil{}, reads, p))))))))
      one_state(befores, dg, reads, Main.Content.Ops{f, p, Ops.write(doc)}, hs)

# A resolution is the written form of the one the walk's proposal and the
# folder's lines make.
def resolved_state(+befores: List<&2, Main.Before>, +dg: Map<&2, String>, +reads: Map<&2, List<&2, U32>>, +f: String, +p: String, +j: Conflict.Joined, +ej: {Main.proposed_of(befores, f) == Some{j} : Maybe<&2, Conflict.Joined>}, d: Maybe<&2, Res.Doc>, +ed: {Conflict.resolve(j, Ops.from_text(Utf8.decode(Main.bytes_of(p, Map.get(List<&2, U32>, Nil{}, reads, p))))) == d : Maybe<&2, Res.Doc>}) -> {Main.contents.state(befores, dg, reads, Main.resolved.content(f, p, d)) == True{} : Bool}:
  match d:
    case None{}:
      {==}
    case Some{+doc}:
      %Equal.sym(Maybe<&2, Conflict.Joined>, Main.proposed_of(befores, f), Some{j}, ej) : {Bool.and(Main.resolution.states(_, Ops.from_text(Utf8.decode(Main.bytes_of(p, Map.get(List<&2, U32>, Nil{}, reads, p)))), Res.write(doc)), True{}) == True{} : Bool}
      %Equal.sym(Maybe<&2, Res.Doc>, Conflict.resolve(j, Ops.from_text(Utf8.decode(Main.bytes_of(p, Map.get(List<&2, U32>, Nil{}, reads, p))))), Some{doc}, ed) : {Bool.and(Main.resolution.written(_, Res.write(doc)), True{}) == True{} : Bool}
      %Equal.sym(Bool, String.eq(Res.write(doc), Res.write(doc)), True{}, S.eq_refl(Res.write(doc))) : {Bool.and(_, True{}) == True{} : Bool}
      {==}

# A file of lines states an edit of the position's lines, or, where the
# parents being joined leave it differently, a resolution.
def lines_state(~da: @parent: List<&2, Ops.Item> -> @child: List<&2, Ops.Item> -> {Ops.terminated_but_last(child) == True{} : Bool} -> @doc: Ops.Doc -> {Ops.diff(parent, child) == Some{doc} : Maybe<&2, Ops.Doc>} -> {Ops.apply(parent, doc) == Done{child} : Result<&2, &2, String, List<&2, Ops.Item>>}, +befores: List<&2, Main.Before>, +dg: Map<&2, String>, +reads: Map<&2, List<&2, U32>>, +f: String, +p: String, pr: Maybe<&2, Conflict.Joined>, +ep: {Main.proposed_of(befores, f) == pr : Maybe<&2, Conflict.Joined>}) -> {Main.contents.state(befores, dg, reads, Main.lines.content(f, p, befores, Ops.from_text(Utf8.decode(Main.bytes_of(p, Map.get(List<&2, U32>, Nil{}, reads, p)))), pr)) == True{} : Bool}:
  match pr:
    case Some{+j}:
      resolved_state(befores, dg, reads, f, p, j, ep, Conflict.resolve(j, Ops.from_text(Utf8.decode(Main.bytes_of(p, Map.get(List<&2, U32>, Nil{}, reads, p))))), {==})
    case None{}:
      edited_state(~da, befores, dg, reads, Ops.diff(Main.before_of(befores, f), Ops.from_text(Utf8.decode(Main.bytes_of(p, Map.get(List<&2, U32>, Nil{}, reads, p))))), f, p, {==})

def held_state(~da: @parent: List<&2, Ops.Item> -> @child: List<&2, Ops.Item> -> {Ops.terminated_but_last(child) == True{} : Bool} -> @doc: Ops.Doc -> {Ops.diff(parent, child) == Some{doc} : Maybe<&2, Ops.Doc>} -> {Ops.apply(parent, doc) == Done{child} : Result<&2, &2, String, List<&2, Ops.Item>>}, +befores: List<&2, Main.Before>, +dg: Map<&2, String>, +reads: Map<&2, List<&2, U32>>, e: Maybe<&2, Tree.Entry>, +edited: List<&2, String>, +p: String) -> {Main.contents.state(befores, dg, reads, Main.stating.contents(Main.stating.held(edited, befores, p, e, Main.status.folder_digest(dg, p), Main.bytes_of(p, Map.get(List<&2, U32>, Nil{}, reads, p))))) == True{} : Bool}:
  match e:
    case Some{Tree.Entry{+f, q, Tree.Whole{}, y, g, m}}:
      pick_state(befores, dg, reads, Rev.member(edited, p), [Main.Content.Whole{f, p, Main.status.folder_digest(dg, p)}], whole_state(befores, dg, reads, f, p))
    case Some{Tree.Entry{+f, q, Tree.Lines{}, y, g, m}}:
      pick_state(befores, dg, reads, Rev.member(edited, p), Main.lines.content(f, p, befores, Ops.from_text(Utf8.decode(Main.bytes_of(p, Map.get(List<&2, U32>, Nil{}, reads, p)))), Main.proposed_of(befores, f)), lines_state(~da, befores, dg, reads, f, p, Main.proposed_of(befores, f), {==}))
    case Some{Tree.Entry{f, q, Tree.Link{}, y, g, m}}:
      {==}
    case None{}:
      {==}

def kind_state(+befores: List<&2, Main.Before>, +dg: Map<&2, String>, +reads: Map<&2, List<&2, U32>>, lines: Bool, +file: String, +p: String) -> {Main.contents.state(befores, dg, reads, Main.arriving.kind(file, p, Main.status.folder_digest(dg, p), Main.bytes_of(p, Map.get(List<&2, U32>, Nil{}, reads, p)), lines)) == True{} : Bool}:
  match lines:
    case True{}:
      unpick_state(befores, dg, reads, List.is_empty(&2, U32, Main.bytes_of(p, Map.get(List<&2, U32>, Nil{}, reads, p))), [Main.Content.Text{file, p, Main.bytes_of(p, Map.get(List<&2, U32>, Nil{}, reads, p))}], text_state(befores, dg, reads, file, p))
    case False{}:
      whole_state(befores, dg, reads, file, p)

def arriving_state(+befores: List<&2, Main.Before>, +dg: Map<&2, String>, +reads: Map<&2, List<&2, U32>>, stated: Maybe<&2, String>, +file: String, +p: String) -> {Main.contents.state(befores, dg, reads, Main.arriving.of(file, p, Main.status.folder_digest(dg, p), Main.bytes_of(p, Map.get(List<&2, U32>, Nil{}, reads, p)), stated)) == True{} : Bool}:
  match stated:
    case Some{+k}:
      either_state(befores, dg, reads, String.eq(k, "bytes"), [Main.Content.Whole{file, p, Main.status.folder_digest(dg, p)}], Main.arriving.kind(file, p, Main.status.folder_digest(dg, p), Main.bytes_of(p, Map.get(List<&2, U32>, Nil{}, reads, p)), True{}), whole_state(befores, dg, reads, file, p), kind_state(befores, dg, reads, True{}, file, p))
    case None{}:
      kind_state(befores, dg, reads, Bool.and(Folder.is_utf8(Main.bytes_of(p, Map.get(List<&2, U32>, Nil{}, reads, p))), Bool.not(Folder.has_nul(Main.bytes_of(p, Map.get(List<&2, U32>, Nil{}, reads, p))))), file, p)

def at_state(~da: @parent: List<&2, Ops.Item> -> @child: List<&2, Ops.Item> -> {Ops.terminated_but_last(child) == True{} : Bool} -> @doc: Ops.Doc -> {Ops.diff(parent, child) == Some{doc} : Maybe<&2, Ops.Doc>} -> {Ops.apply(parent, doc) == Done{child} : Result<&2, &2, String, List<&2, Ops.Item>>}, +befores: List<&2, Main.Before>, +dg: Map<&2, String>, +reads: Map<&2, List<&2, U32>>, arrives: Bool, +mint: List<&2, T.Split>, +edited: List<&2, String>, +ks: List<&2, T.Split>, +p: String, e: Maybe<&2, Tree.Entry>, +runs: Bool) -> {Main.contents.state(befores, dg, reads, Main.stating.contents(Main.stating.at(mint, edited, ks, befores, p, e, Main.status.folder_digest(dg, p), Main.bytes_of(p, Map.get(List<&2, U32>, Nil{}, reads, p)), runs, arrives))) == True{} : Bool}:
  match arrives:
    case True{}:
      arriving_state(befores, dg, reads, Main.kind.stated(ks, p), Maybe.default(&2, String, Main.lookup(mint, p), SNil{}), p)
    case False{}:
      held_state(~da, befores, dg, reads, e, edited, p)

def of_state(~da: @parent: List<&2, Ops.Item> -> @child: List<&2, Ops.Item> -> {Ops.terminated_but_last(child) == True{} : Bool} -> @doc: Ops.Doc -> {Ops.diff(parent, child) == Some{doc} : Maybe<&2, Ops.Doc>} -> {Ops.apply(parent, doc) == Done{child} : Result<&2, &2, String, List<&2, Ops.Item>>}, +befores: List<&2, Main.Before>, +dg: Map<&2, String>, +reads: Map<&2, List<&2, U32>>, +mint: List<&2, T.Split>, +arriving: List<&2, String>, +edited: List<&2, String>, +ks: List<&2, T.Split>, h: Main.Here) -> {Main.contents.state(befores, dg, reads, Main.stating.contents(Main.stating.of(mint, arriving, edited, ks, dg, reads, befores, h))) == True{} : Bool}:
  match h:
    case Main.Here{+p, e, Some{Folder.Found.File{q, +runs, n}}}:
      at_state(~da, befores, dg, reads, Rev.member(arriving, p), mint, edited, ks, p, e, runs)
    case Main.Here{p, e, Some{Folder.Found.Link{q, t}}}:
      {==}
    case Main.Here{p, e, None{}}:
      {==}

def join_contents(a: Main.Stating, b: Main.Stating) -> {List.append(&2, Main.Content, Main.stating.contents(a), Main.stating.contents(b)) == Main.stating.contents(Main.stating.join(a, b)) : List<&2, Main.Content>}:
  match a b:
    case Main.Stating{c1, m1} Main.Stating{c2, m2}:
      {==}

def all_state(~da: @parent: List<&2, Ops.Item> -> @child: List<&2, Ops.Item> -> {Ops.terminated_but_last(child) == True{} : Bool} -> @doc: Ops.Doc -> {Ops.diff(parent, child) == Some{doc} : Maybe<&2, Ops.Doc>} -> {Ops.apply(parent, doc) == Done{child} : Result<&2, &2, String, List<&2, Ops.Item>>}, +befores: List<&2, Main.Before>, +dg: Map<&2, String>, +reads: Map<&2, List<&2, U32>>, +mint: List<&2, T.Split>, +arriving: List<&2, String>, +edited: List<&2, String>, +ks: List<&2, T.Split>, hs: List<&2, Main.Here>) -> {Main.contents.state(befores, dg, reads, Main.stating.contents(Main.stating.all(mint, arriving, edited, ks, dg, reads, befores, hs))) == True{} : Bool}:
  match hs:
    case Nil{}:
      {==}
    case +h <> +rest:
      %join_contents(Main.stating.of(mint, arriving, edited, ks, dg, reads, befores, h), Main.stating.all(mint, arriving, edited, ks, dg, reads, befores, rest)) : {Main.contents.state(befores, dg, reads, _) == True{} : Bool}
      state_app(befores, dg, reads, Main.stating.contents(Main.stating.of(mint, arriving, edited, ks, dg, reads, befores, h)), Main.stating.contents(Main.stating.all(mint, arriving, edited, ks, dg, reads, befores, rest)),
        of_state(~da, befores, dg, reads, mint, arriving, edited, ks, h), all_state(~da, befores, dg, reads, mint, arriving, edited, ks, rest))

# What `record` drafts states of each file what the folder holds there.
def drafted_state(~da: @parent: List<&2, Ops.Item> -> @child: List<&2, Ops.Item> -> {Ops.terminated_but_last(child) == True{} : Bool} -> @doc: Ops.Doc -> {Ops.diff(parent, child) == Some{doc} : Maybe<&2, Ops.Doc>} -> {Ops.apply(parent, doc) == Done{child} : Result<&2, &2, String, List<&2, Ops.Item>>}, +befores: List<&2, Main.Before>, +dg: Map<&2, String>, +reads: Map<&2, List<&2, U32>>, +t: Tree.Tree(), +hs: List<&2, Main.Here>, +ks: List<&2, T.Split>, +moves: List<&2, T.Split>, +obs: List<&2, Sv.Obs>, +ls: List<&2, String>, +mint: List<&2, T.Split>) -> {Main.contents.state(befores, dg, reads, Main.drafted.contents(Main.drafted.of(befores, t, hs, dg, reads, ks, moves, obs, ls, mint))) == True{} : Bool}:
  all_state(~da, befores, dg, reads, mint, Sv.sorted(Sv.added(obs)), Sv.edited(obs), ks, hs)

# What it writes is named as it says
# ----------------------------------

def mint_heads(ps: List<&2, String>, +hex: String) -> {Main.strings.same(T.map(~T.Split, ~String, ~(s => Main.split.head(s)), Main.zipped(ps, Main.ids.minted(Nat.add(List.length(&2, String, ps), 1n), hex))), ps) == True{} : Bool}:
  match ps:
    case Nil{}:
      {==}
    case +p <> +rest:
      B.and_tt(String.eq(p, p), Main.strings.same(T.map(~T.Split, ~String, ~(s => Main.split.head(s)), Main.zipped(rest, Main.ids.minted(Nat.add(List.length(&2, String, rest), 1n), String.drop(hex, 24n)))), rest), S.eq_refl(p),
        mint_heads(rest, String.drop(hex, 24n)))

def stem_of_pre(+base: String, +change: String, +id: String, b1: Bool, b2: Bool) -> {String.starts_with(Naming.stem.of(base, change, id, b1, b2), base) == True{} : Bool}:
  match b1:
    case False{}:
      B.sw_refl(base)
    case True{}:
      match b2:
        case True{}:
          B.sw_ext(base, base, " " ++ String.take(change, Naming.CHANGE_CHARS()) ++ " " ++ String.take(id, Naming.DIGEST_CHARS()), B.sw_refl(base))
        case False{}:
          B.sw_ext(base, base, " " ++ String.take(change, Naming.CHANGE_CHARS()), B.sw_refl(base))

# A revision is filed under the name its moment, message and change
# compose, extended only where the store holds that name already.
def stem_pre(+when: String, +message: String, +change: String, +id: String, +ns: List<&2, Naming.Named>) -> {String.starts_with(Naming.stem(when, message, change, id, ns), Naming.compose(when, message, change)) == True{} : Bool}:
  stem_of_pre(Naming.compose(when, message, change), change, id, Naming.sharing_base(ns, Naming.compose(when, message, change)), Naming.sharing_change(ns, Naming.compose(when, message, change), change))

def follow_pick(b: Bool, +changes: List<&2, String>, +n: String, +c: String, +p: Bool, +later: List<&2, Bm.Bookmark>, eb: {Rev.member(changes, c) == b : Bool}, h: {Main.follows(changes, later) == True{} : Bool}) -> {Main.follows(changes, Bool.pick(List<&2, Bm.Bookmark>, b, Bm.Bookmark{n, Bm.Target.Change{c}, p} <> later, later)) == True{} : Bool}:
  match b:
    case True{}:
      B.and_tt(Rev.member(changes, c), Main.follows(changes, later), eb, h)
    case False{}:
      h

# Each bookmark that follows the work names one of the changes it follows.
def advancing_follows(+changes: List<&2, String>, bs: List<&2, Bm.Bookmark>) -> {Main.follows(changes, Main.advancing(changes, bs)) == True{} : Bool}:
  match bs:
    case Nil{}:
      {==}
    case Bm.Bookmark{+n, Bm.Target.Change{+c}, +p} <> +rest:
      follow_pick(Rev.member(changes, c), changes, n, c, p, Main.advancing(changes, rest), {==}, advancing_follows(changes, rest))
    case Bm.Bookmark{n, Bm.Target.Revision{c}, p} <> rest:
      advancing_follows(changes, rest)
    case Bm.Bookmark{n, Bm.Target.File{c}, p} <> rest:
      advancing_follows(changes, rest)

# What `record` writes is named as it says.
def planned_named(w: Main.Writing, +hex: String, +befores: List<&2, Main.Before>, +fs: List<&2, Main.Full>, +bs: List<&2, Bm.Bookmark>, +ps: List<&2, String>, +t: Tree.Tree(), +hs: List<&2, Main.Here>, +dg: Map<&2, String>, +reads: Map<&2, List<&2, U32>>, +ks: List<&2, T.Split>, +moves: List<&2, T.Split>, +obs: List<&2, Sv.Obs>, +ls: List<&2, String>) -> {Main.record.named(w, Sv.sorted(Sv.added(obs)), Main.parents.changes(fs, ps), Main.record.planned(w, hex, befores, fs, bs, ps, t, hs, dg, reads, ks, moves, obs, ls)) == True{} : Bool}:
  match w:
    case Main.Writing{+a, +when, +message, +fl}:
      B.and_tt(Main.strings.same(T.map(~T.Split, ~String, ~(s => Main.split.head(s)), Main.zipped(Sv.sorted(Sv.added(obs)), Main.ids.minted(Nat.add(List.length(&2, String, Sv.sorted(Sv.added(obs))), 1n), hex))), Sv.sorted(Sv.added(obs))), Bool.and(String.eq(Sha.digest(Utf8.encode(Rev.write(Main.writing.rev(Main.Writing{a, when, message, fl}, Maybe.default(&2, String, List.get(&2, String, Main.ids.minted(Nat.add(List.length(&2, String, Sv.sorted(Sv.added(obs))), 1n), hex), List.length(&2, String, Sv.sorted(Sv.added(obs)))), SNil{}), ps, Main.drafted.facts(Main.drafted.of(befores, t, hs, dg, reads, ks, moves, obs, ls, Main.zipped(Sv.sorted(Sv.added(obs)), Main.ids.minted(Nat.add(List.length(&2, String, Sv.sorted(Sv.added(obs))), 1n), hex)))))))), Sha.digest(Utf8.encode(Rev.write(Main.writing.rev(Main.Writing{a, when, message, fl}, Maybe.default(&2, String, List.get(&2, String, Main.ids.minted(Nat.add(List.length(&2, String, Sv.sorted(Sv.added(obs))), 1n), hex), List.length(&2, String, Sv.sorted(Sv.added(obs)))), SNil{}), ps, Main.drafted.facts(Main.drafted.of(befores, t, hs, dg, reads, ks, moves, obs, ls, Main.zipped(Sv.sorted(Sv.added(obs)), Main.ids.minted(Nat.add(List.length(&2, String, Sv.sorted(Sv.added(obs))), 1n), hex))))))))), Bool.and(String.starts_with(Naming.stem(when, message, Maybe.default(&2, String, List.get(&2, String, Main.ids.minted(Nat.add(List.length(&2, String, Sv.sorted(Sv.added(obs))), 1n), hex), List.length(&2, String, Sv.sorted(Sv.added(obs)))), SNil{}), Sha.digest(Utf8.encode(Rev.write(Main.writing.rev(Main.Writing{a, when, message, fl}, Maybe.default(&2, String, List.get(&2, String, Main.ids.minted(Nat.add(List.length(&2, String, Sv.sorted(Sv.added(obs))), 1n), hex), List.length(&2, String, Sv.sorted(Sv.added(obs)))), SNil{}), ps, Main.drafted.facts(Main.drafted.of(befores, t, hs, dg, reads, ks, moves, obs, ls, Main.zipped(Sv.sorted(Sv.added(obs)), Main.ids.minted(Nat.add(List.length(&2, String, Sv.sorted(Sv.added(obs))), 1n), hex)))))))), T.map(~Main.Full, ~Naming.Named, ~(x => Main.full.named(x)), fs)), Naming.compose(when, message, Maybe.default(&2, String, List.get(&2, String, Main.ids.minted(Nat.add(List.length(&2, String, Sv.sorted(Sv.added(obs))), 1n), hex), List.length(&2, String, Sv.sorted(Sv.added(obs)))), SNil{}))), Main.follows(Main.parents.changes(fs, ps), Main.advancing(Main.parents.changes(fs, ps), bs)))), mint_heads(Sv.sorted(Sv.added(obs)), hex),
        B.and_tt(String.eq(Sha.digest(Utf8.encode(Rev.write(Main.writing.rev(Main.Writing{a, when, message, fl}, Maybe.default(&2, String, List.get(&2, String, Main.ids.minted(Nat.add(List.length(&2, String, Sv.sorted(Sv.added(obs))), 1n), hex), List.length(&2, String, Sv.sorted(Sv.added(obs)))), SNil{}), ps, Main.drafted.facts(Main.drafted.of(befores, t, hs, dg, reads, ks, moves, obs, ls, Main.zipped(Sv.sorted(Sv.added(obs)), Main.ids.minted(Nat.add(List.length(&2, String, Sv.sorted(Sv.added(obs))), 1n), hex)))))))), Sha.digest(Utf8.encode(Rev.write(Main.writing.rev(Main.Writing{a, when, message, fl}, Maybe.default(&2, String, List.get(&2, String, Main.ids.minted(Nat.add(List.length(&2, String, Sv.sorted(Sv.added(obs))), 1n), hex), List.length(&2, String, Sv.sorted(Sv.added(obs)))), SNil{}), ps, Main.drafted.facts(Main.drafted.of(befores, t, hs, dg, reads, ks, moves, obs, ls, Main.zipped(Sv.sorted(Sv.added(obs)), Main.ids.minted(Nat.add(List.length(&2, String, Sv.sorted(Sv.added(obs))), 1n), hex))))))))), Bool.and(String.starts_with(Naming.stem(when, message, Maybe.default(&2, String, List.get(&2, String, Main.ids.minted(Nat.add(List.length(&2, String, Sv.sorted(Sv.added(obs))), 1n), hex), List.length(&2, String, Sv.sorted(Sv.added(obs)))), SNil{}), Sha.digest(Utf8.encode(Rev.write(Main.writing.rev(Main.Writing{a, when, message, fl}, Maybe.default(&2, String, List.get(&2, String, Main.ids.minted(Nat.add(List.length(&2, String, Sv.sorted(Sv.added(obs))), 1n), hex), List.length(&2, String, Sv.sorted(Sv.added(obs)))), SNil{}), ps, Main.drafted.facts(Main.drafted.of(befores, t, hs, dg, reads, ks, moves, obs, ls, Main.zipped(Sv.sorted(Sv.added(obs)), Main.ids.minted(Nat.add(List.length(&2, String, Sv.sorted(Sv.added(obs))), 1n), hex)))))))), T.map(~Main.Full, ~Naming.Named, ~(x => Main.full.named(x)), fs)), Naming.compose(when, message, Maybe.default(&2, String, List.get(&2, String, Main.ids.minted(Nat.add(List.length(&2, String, Sv.sorted(Sv.added(obs))), 1n), hex), List.length(&2, String, Sv.sorted(Sv.added(obs)))), SNil{}))), Main.follows(Main.parents.changes(fs, ps), Main.advancing(Main.parents.changes(fs, ps), bs))), S.eq_refl(Sha.digest(Utf8.encode(Rev.write(Main.writing.rev(Main.Writing{a, when, message, fl}, Maybe.default(&2, String, List.get(&2, String, Main.ids.minted(Nat.add(List.length(&2, String, Sv.sorted(Sv.added(obs))), 1n), hex), List.length(&2, String, Sv.sorted(Sv.added(obs)))), SNil{}), ps, Main.drafted.facts(Main.drafted.of(befores, t, hs, dg, reads, ks, moves, obs, ls, Main.zipped(Sv.sorted(Sv.added(obs)), Main.ids.minted(Nat.add(List.length(&2, String, Sv.sorted(Sv.added(obs))), 1n), hex))))))))),
          B.and_tt(String.starts_with(Naming.stem(when, message, Maybe.default(&2, String, List.get(&2, String, Main.ids.minted(Nat.add(List.length(&2, String, Sv.sorted(Sv.added(obs))), 1n), hex), List.length(&2, String, Sv.sorted(Sv.added(obs)))), SNil{}), Sha.digest(Utf8.encode(Rev.write(Main.writing.rev(Main.Writing{a, when, message, fl}, Maybe.default(&2, String, List.get(&2, String, Main.ids.minted(Nat.add(List.length(&2, String, Sv.sorted(Sv.added(obs))), 1n), hex), List.length(&2, String, Sv.sorted(Sv.added(obs)))), SNil{}), ps, Main.drafted.facts(Main.drafted.of(befores, t, hs, dg, reads, ks, moves, obs, ls, Main.zipped(Sv.sorted(Sv.added(obs)), Main.ids.minted(Nat.add(List.length(&2, String, Sv.sorted(Sv.added(obs))), 1n), hex)))))))), T.map(~Main.Full, ~Naming.Named, ~(x => Main.full.named(x)), fs)), Naming.compose(when, message, Maybe.default(&2, String, List.get(&2, String, Main.ids.minted(Nat.add(List.length(&2, String, Sv.sorted(Sv.added(obs))), 1n), hex), List.length(&2, String, Sv.sorted(Sv.added(obs)))), SNil{}))), Main.follows(Main.parents.changes(fs, ps), Main.advancing(Main.parents.changes(fs, ps), bs)), stem_pre(when, message, Maybe.default(&2, String, List.get(&2, String, Main.ids.minted(Nat.add(List.length(&2, String, Sv.sorted(Sv.added(obs))), 1n), hex), List.length(&2, String, Sv.sorted(Sv.added(obs)))), SNil{}), Sha.digest(Utf8.encode(Rev.write(Main.writing.rev(Main.Writing{a, when, message, fl}, Maybe.default(&2, String, List.get(&2, String, Main.ids.minted(Nat.add(List.length(&2, String, Sv.sorted(Sv.added(obs))), 1n), hex), List.length(&2, String, Sv.sorted(Sv.added(obs)))), SNil{}), ps, Main.drafted.facts(Main.drafted.of(befores, t, hs, dg, reads, ks, moves, obs, ls, Main.zipped(Sv.sorted(Sv.added(obs)), Main.ids.minted(Nat.add(List.length(&2, String, Sv.sorted(Sv.added(obs))), 1n), hex)))))))), T.map(~Main.Full, ~Naming.Named, ~(x => Main.full.named(x)), fs)), advancing_follows(Main.parents.changes(fs, ps), bs))))

# What it writes is settled
# -------------------------

def pick_rest(-A: Data, b: Bool, -x: Main.Refused, -r: Result<&2, &2, Main.Refused, A>, -y: A, e: {Bool.pick(Result<&2, &2, Main.Refused, A>, b, Fail{x}, r) == Done{y} : Result<&2, &2, Main.Refused, A>}) -> {r == Done{y} : Result<&2, &2, Main.Refused, A>}:
  match b:
    case True{}:
      Empty.absurd({r == Done{y} : Result<&2, &2, Main.Refused, A>}, B.fail_done(A, x, y, e))
    case False{}:
      e

def pick_no(-A: Data, b: Bool, -x: Main.Refused, -r: Result<&2, &2, Main.Refused, A>, -y: A, e: {Bool.pick(Result<&2, &2, Main.Refused, A>, b, Fail{x}, r) == Done{y} : Result<&2, &2, Main.Refused, A>}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, B.fail_done(A, x, y, e))
    case False{}:
      {==}

def not_true(b: Bool, h: {Bool.not(b) == False{} : Bool}) -> {b == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, S.true_false(h))

def settled_of(+looked: Tree.Tree(), +facts: List<&2, T.Split>, +refused: List<&2, T.Split>, +claimed: List<&2, T.Split>, +accept: List<&2, String>, +emptied: List<&2, String>, +obs: List<&2, Sv.Obs>, +links: List<&2, String>, +accepted: List<&2, String>, -pl2: Sv.Planned, +e: {Bool.pick(Result<&2, &2, Main.Refused, Sv.Planned>, Bool.not(List.is_empty(&2, T.Split, claimed)), Fail{Main.Refused{1, Main.claimed.msg(looked, claimed)}}, Bool.pick(Result<&2, &2, Main.Refused, Sv.Planned>, Bool.not(List.is_empty(&2, T.Split, refused)), Fail{Main.Refused{1, Main.refused.msg(refused)}}, Bool.pick(Result<&2, &2, Main.Refused, Sv.Planned>, Bool.not(List.is_empty(&2, T.Split, Sv.marked(obs))), Fail{Main.Refused{1, Main.unresolved.msg(Sv.marked(obs))}}, Bool.pick(Result<&2, &2, Main.Refused, Sv.Planned>, Bool.not(List.is_empty(&2, String, emptied)), Fail{Main.Refused{1, "a merge states what each contested file is, and there is no way to state that one is empty; leave " ++ Main.these(emptied, "it", "them") ++ " something and remove it in the revision after, or drop it here:" ++ Main.skips_held.lines(emptied)}}, Bool.pick(Result<&2, &2, Main.Refused, Sv.Planned>, Bool.not(List.is_empty(&2, String, Main.minus(accept, accepted))), Fail{Main.Refused{1, "concurrent work states different bytes for " ++ Main.these(Main.minus(accept, accepted), "one attachment", "these attachments") ++ "; inspect " ++ Main.these(Main.minus(accept, accepted), "it", "them") ++ " and explicitly accept what the folder holds:" ++ Main.accept.lines(Main.minus(accept, accepted))}}, Bool.pick(Result<&2, &2, Main.Refused, Sv.Planned>, Bool.not(List.is_empty(&2, String, Main.minus(accepted, accept))), Fail{Main.Refused{1, Main.these(Main.minus(accepted, accept), "this path is not a contested attachment", "these paths are not contested attachments") ++ "; remove the unnecessary acceptance:" ++ Main.accept.lines(Main.minus(accepted, accept))}}, Done{Sv.Planned{facts, refused, claimed, accept, emptied, None{}, obs, links}})))))) == Done{pl2} : Result<&2, &2, Main.Refused, Sv.Planned>}) -> {Main.planned.settled(pl2, accepted) == True{} : Bool}:
  +h1 = not_true(List.is_empty(&2, T.Split, claimed), pick_no(Sv.Planned, Bool.not(List.is_empty(&2, T.Split, claimed)), Main.Refused{1, Main.claimed.msg(looked, claimed)}, Bool.pick(Result<&2, &2, Main.Refused, Sv.Planned>, Bool.not(List.is_empty(&2, T.Split, refused)), Fail{Main.Refused{1, Main.refused.msg(refused)}}, Bool.pick(Result<&2, &2, Main.Refused, Sv.Planned>, Bool.not(List.is_empty(&2, T.Split, Sv.marked(obs))), Fail{Main.Refused{1, Main.unresolved.msg(Sv.marked(obs))}}, Bool.pick(Result<&2, &2, Main.Refused, Sv.Planned>, Bool.not(List.is_empty(&2, String, emptied)), Fail{Main.Refused{1, "a merge states what each contested file is, and there is no way to state that one is empty; leave " ++ Main.these(emptied, "it", "them") ++ " something and remove it in the revision after, or drop it here:" ++ Main.skips_held.lines(emptied)}}, Bool.pick(Result<&2, &2, Main.Refused, Sv.Planned>, Bool.not(List.is_empty(&2, String, Main.minus(accept, accepted))), Fail{Main.Refused{1, "concurrent work states different bytes for " ++ Main.these(Main.minus(accept, accepted), "one attachment", "these attachments") ++ "; inspect " ++ Main.these(Main.minus(accept, accepted), "it", "them") ++ " and explicitly accept what the folder holds:" ++ Main.accept.lines(Main.minus(accept, accepted))}}, Bool.pick(Result<&2, &2, Main.Refused, Sv.Planned>, Bool.not(List.is_empty(&2, String, Main.minus(accepted, accept))), Fail{Main.Refused{1, Main.these(Main.minus(accepted, accept), "this path is not a contested attachment", "these paths are not contested attachments") ++ "; remove the unnecessary acceptance:" ++ Main.accept.lines(Main.minus(accepted, accept))}}, Done{Sv.Planned{facts, refused, claimed, accept, emptied, None{}, obs, links}}))))), pl2, e))
  +e2 = pick_rest(Sv.Planned, Bool.not(List.is_empty(&2, T.Split, claimed)), Main.Refused{1, Main.claimed.msg(looked, claimed)}, Bool.pick(Result<&2, &2, Main.Refused, Sv.Planned>, Bool.not(List.is_empty(&2, T.Split, refused)), Fail{Main.Refused{1, Main.refused.msg(refused)}}, Bool.pick(Result<&2, &2, Main.Refused, Sv.Planned>, Bool.not(List.is_empty(&2, T.Split, Sv.marked(obs))), Fail{Main.Refused{1, Main.unresolved.msg(Sv.marked(obs))}}, Bool.pick(Result<&2, &2, Main.Refused, Sv.Planned>, Bool.not(List.is_empty(&2, String, emptied)), Fail{Main.Refused{1, "a merge states what each contested file is, and there is no way to state that one is empty; leave " ++ Main.these(emptied, "it", "them") ++ " something and remove it in the revision after, or drop it here:" ++ Main.skips_held.lines(emptied)}}, Bool.pick(Result<&2, &2, Main.Refused, Sv.Planned>, Bool.not(List.is_empty(&2, String, Main.minus(accept, accepted))), Fail{Main.Refused{1, "concurrent work states different bytes for " ++ Main.these(Main.minus(accept, accepted), "one attachment", "these attachments") ++ "; inspect " ++ Main.these(Main.minus(accept, accepted), "it", "them") ++ " and explicitly accept what the folder holds:" ++ Main.accept.lines(Main.minus(accept, accepted))}}, Bool.pick(Result<&2, &2, Main.Refused, Sv.Planned>, Bool.not(List.is_empty(&2, String, Main.minus(accepted, accept))), Fail{Main.Refused{1, Main.these(Main.minus(accepted, accept), "this path is not a contested attachment", "these paths are not contested attachments") ++ "; remove the unnecessary acceptance:" ++ Main.accept.lines(Main.minus(accepted, accept))}}, Done{Sv.Planned{facts, refused, claimed, accept, emptied, None{}, obs, links}}))))), pl2, e)
  +h2 = not_true(List.is_empty(&2, T.Split, refused), pick_no(Sv.Planned, Bool.not(List.is_empty(&2, T.Split, refused)), Main.Refused{1, Main.refused.msg(refused)}, Bool.pick(Result<&2, &2, Main.Refused, Sv.Planned>, Bool.not(List.is_empty(&2, T.Split, Sv.marked(obs))), Fail{Main.Refused{1, Main.unresolved.msg(Sv.marked(obs))}}, Bool.pick(Result<&2, &2, Main.Refused, Sv.Planned>, Bool.not(List.is_empty(&2, String, emptied)), Fail{Main.Refused{1, "a merge states what each contested file is, and there is no way to state that one is empty; leave " ++ Main.these(emptied, "it", "them") ++ " something and remove it in the revision after, or drop it here:" ++ Main.skips_held.lines(emptied)}}, Bool.pick(Result<&2, &2, Main.Refused, Sv.Planned>, Bool.not(List.is_empty(&2, String, Main.minus(accept, accepted))), Fail{Main.Refused{1, "concurrent work states different bytes for " ++ Main.these(Main.minus(accept, accepted), "one attachment", "these attachments") ++ "; inspect " ++ Main.these(Main.minus(accept, accepted), "it", "them") ++ " and explicitly accept what the folder holds:" ++ Main.accept.lines(Main.minus(accept, accepted))}}, Bool.pick(Result<&2, &2, Main.Refused, Sv.Planned>, Bool.not(List.is_empty(&2, String, Main.minus(accepted, accept))), Fail{Main.Refused{1, Main.these(Main.minus(accepted, accept), "this path is not a contested attachment", "these paths are not contested attachments") ++ "; remove the unnecessary acceptance:" ++ Main.accept.lines(Main.minus(accepted, accept))}}, Done{Sv.Planned{facts, refused, claimed, accept, emptied, None{}, obs, links}})))), pl2, e2))
  +e3 = pick_rest(Sv.Planned, Bool.not(List.is_empty(&2, T.Split, refused)), Main.Refused{1, Main.refused.msg(refused)}, Bool.pick(Result<&2, &2, Main.Refused, Sv.Planned>, Bool.not(List.is_empty(&2, T.Split, Sv.marked(obs))), Fail{Main.Refused{1, Main.unresolved.msg(Sv.marked(obs))}}, Bool.pick(Result<&2, &2, Main.Refused, Sv.Planned>, Bool.not(List.is_empty(&2, String, emptied)), Fail{Main.Refused{1, "a merge states what each contested file is, and there is no way to state that one is empty; leave " ++ Main.these(emptied, "it", "them") ++ " something and remove it in the revision after, or drop it here:" ++ Main.skips_held.lines(emptied)}}, Bool.pick(Result<&2, &2, Main.Refused, Sv.Planned>, Bool.not(List.is_empty(&2, String, Main.minus(accept, accepted))), Fail{Main.Refused{1, "concurrent work states different bytes for " ++ Main.these(Main.minus(accept, accepted), "one attachment", "these attachments") ++ "; inspect " ++ Main.these(Main.minus(accept, accepted), "it", "them") ++ " and explicitly accept what the folder holds:" ++ Main.accept.lines(Main.minus(accept, accepted))}}, Bool.pick(Result<&2, &2, Main.Refused, Sv.Planned>, Bool.not(List.is_empty(&2, String, Main.minus(accepted, accept))), Fail{Main.Refused{1, Main.these(Main.minus(accepted, accept), "this path is not a contested attachment", "these paths are not contested attachments") ++ "; remove the unnecessary acceptance:" ++ Main.accept.lines(Main.minus(accepted, accept))}}, Done{Sv.Planned{facts, refused, claimed, accept, emptied, None{}, obs, links}})))), pl2, e2)
  +h3 = not_true(List.is_empty(&2, T.Split, Sv.marked(obs)), pick_no(Sv.Planned, Bool.not(List.is_empty(&2, T.Split, Sv.marked(obs))), Main.Refused{1, Main.unresolved.msg(Sv.marked(obs))}, Bool.pick(Result<&2, &2, Main.Refused, Sv.Planned>, Bool.not(List.is_empty(&2, String, emptied)), Fail{Main.Refused{1, "a merge states what each contested file is, and there is no way to state that one is empty; leave " ++ Main.these(emptied, "it", "them") ++ " something and remove it in the revision after, or drop it here:" ++ Main.skips_held.lines(emptied)}}, Bool.pick(Result<&2, &2, Main.Refused, Sv.Planned>, Bool.not(List.is_empty(&2, String, Main.minus(accept, accepted))), Fail{Main.Refused{1, "concurrent work states different bytes for " ++ Main.these(Main.minus(accept, accepted), "one attachment", "these attachments") ++ "; inspect " ++ Main.these(Main.minus(accept, accepted), "it", "them") ++ " and explicitly accept what the folder holds:" ++ Main.accept.lines(Main.minus(accept, accepted))}}, Bool.pick(Result<&2, &2, Main.Refused, Sv.Planned>, Bool.not(List.is_empty(&2, String, Main.minus(accepted, accept))), Fail{Main.Refused{1, Main.these(Main.minus(accepted, accept), "this path is not a contested attachment", "these paths are not contested attachments") ++ "; remove the unnecessary acceptance:" ++ Main.accept.lines(Main.minus(accepted, accept))}}, Done{Sv.Planned{facts, refused, claimed, accept, emptied, None{}, obs, links}}))), pl2, e3))
  +e4 = pick_rest(Sv.Planned, Bool.not(List.is_empty(&2, T.Split, Sv.marked(obs))), Main.Refused{1, Main.unresolved.msg(Sv.marked(obs))}, Bool.pick(Result<&2, &2, Main.Refused, Sv.Planned>, Bool.not(List.is_empty(&2, String, emptied)), Fail{Main.Refused{1, "a merge states what each contested file is, and there is no way to state that one is empty; leave " ++ Main.these(emptied, "it", "them") ++ " something and remove it in the revision after, or drop it here:" ++ Main.skips_held.lines(emptied)}}, Bool.pick(Result<&2, &2, Main.Refused, Sv.Planned>, Bool.not(List.is_empty(&2, String, Main.minus(accept, accepted))), Fail{Main.Refused{1, "concurrent work states different bytes for " ++ Main.these(Main.minus(accept, accepted), "one attachment", "these attachments") ++ "; inspect " ++ Main.these(Main.minus(accept, accepted), "it", "them") ++ " and explicitly accept what the folder holds:" ++ Main.accept.lines(Main.minus(accept, accepted))}}, Bool.pick(Result<&2, &2, Main.Refused, Sv.Planned>, Bool.not(List.is_empty(&2, String, Main.minus(accepted, accept))), Fail{Main.Refused{1, Main.these(Main.minus(accepted, accept), "this path is not a contested attachment", "these paths are not contested attachments") ++ "; remove the unnecessary acceptance:" ++ Main.accept.lines(Main.minus(accepted, accept))}}, Done{Sv.Planned{facts, refused, claimed, accept, emptied, None{}, obs, links}}))), pl2, e3)
  +h4 = not_true(List.is_empty(&2, String, emptied), pick_no(Sv.Planned, Bool.not(List.is_empty(&2, String, emptied)), Main.Refused{1, "a merge states what each contested file is, and there is no way to state that one is empty; leave " ++ Main.these(emptied, "it", "them") ++ " something and remove it in the revision after, or drop it here:" ++ Main.skips_held.lines(emptied)}, Bool.pick(Result<&2, &2, Main.Refused, Sv.Planned>, Bool.not(List.is_empty(&2, String, Main.minus(accept, accepted))), Fail{Main.Refused{1, "concurrent work states different bytes for " ++ Main.these(Main.minus(accept, accepted), "one attachment", "these attachments") ++ "; inspect " ++ Main.these(Main.minus(accept, accepted), "it", "them") ++ " and explicitly accept what the folder holds:" ++ Main.accept.lines(Main.minus(accept, accepted))}}, Bool.pick(Result<&2, &2, Main.Refused, Sv.Planned>, Bool.not(List.is_empty(&2, String, Main.minus(accepted, accept))), Fail{Main.Refused{1, Main.these(Main.minus(accepted, accept), "this path is not a contested attachment", "these paths are not contested attachments") ++ "; remove the unnecessary acceptance:" ++ Main.accept.lines(Main.minus(accepted, accept))}}, Done{Sv.Planned{facts, refused, claimed, accept, emptied, None{}, obs, links}})), pl2, e4))
  +e5 = pick_rest(Sv.Planned, Bool.not(List.is_empty(&2, String, emptied)), Main.Refused{1, "a merge states what each contested file is, and there is no way to state that one is empty; leave " ++ Main.these(emptied, "it", "them") ++ " something and remove it in the revision after, or drop it here:" ++ Main.skips_held.lines(emptied)}, Bool.pick(Result<&2, &2, Main.Refused, Sv.Planned>, Bool.not(List.is_empty(&2, String, Main.minus(accept, accepted))), Fail{Main.Refused{1, "concurrent work states different bytes for " ++ Main.these(Main.minus(accept, accepted), "one attachment", "these attachments") ++ "; inspect " ++ Main.these(Main.minus(accept, accepted), "it", "them") ++ " and explicitly accept what the folder holds:" ++ Main.accept.lines(Main.minus(accept, accepted))}}, Bool.pick(Result<&2, &2, Main.Refused, Sv.Planned>, Bool.not(List.is_empty(&2, String, Main.minus(accepted, accept))), Fail{Main.Refused{1, Main.these(Main.minus(accepted, accept), "this path is not a contested attachment", "these paths are not contested attachments") ++ "; remove the unnecessary acceptance:" ++ Main.accept.lines(Main.minus(accepted, accept))}}, Done{Sv.Planned{facts, refused, claimed, accept, emptied, None{}, obs, links}})), pl2, e4)
  +h5 = not_true(List.is_empty(&2, String, Main.minus(accept, accepted)), pick_no(Sv.Planned, Bool.not(List.is_empty(&2, String, Main.minus(accept, accepted))), Main.Refused{1, "concurrent work states different bytes for " ++ Main.these(Main.minus(accept, accepted), "one attachment", "these attachments") ++ "; inspect " ++ Main.these(Main.minus(accept, accepted), "it", "them") ++ " and explicitly accept what the folder holds:" ++ Main.accept.lines(Main.minus(accept, accepted))}, Bool.pick(Result<&2, &2, Main.Refused, Sv.Planned>, Bool.not(List.is_empty(&2, String, Main.minus(accepted, accept))), Fail{Main.Refused{1, Main.these(Main.minus(accepted, accept), "this path is not a contested attachment", "these paths are not contested attachments") ++ "; remove the unnecessary acceptance:" ++ Main.accept.lines(Main.minus(accepted, accept))}}, Done{Sv.Planned{facts, refused, claimed, accept, emptied, None{}, obs, links}}), pl2, e5))
  +e6 = pick_rest(Sv.Planned, Bool.not(List.is_empty(&2, String, Main.minus(accept, accepted))), Main.Refused{1, "concurrent work states different bytes for " ++ Main.these(Main.minus(accept, accepted), "one attachment", "these attachments") ++ "; inspect " ++ Main.these(Main.minus(accept, accepted), "it", "them") ++ " and explicitly accept what the folder holds:" ++ Main.accept.lines(Main.minus(accept, accepted))}, Bool.pick(Result<&2, &2, Main.Refused, Sv.Planned>, Bool.not(List.is_empty(&2, String, Main.minus(accepted, accept))), Fail{Main.Refused{1, Main.these(Main.minus(accepted, accept), "this path is not a contested attachment", "these paths are not contested attachments") ++ "; remove the unnecessary acceptance:" ++ Main.accept.lines(Main.minus(accepted, accept))}}, Done{Sv.Planned{facts, refused, claimed, accept, emptied, None{}, obs, links}}), pl2, e5)
  +h6 = not_true(List.is_empty(&2, String, Main.minus(accepted, accept)), pick_no(Sv.Planned, Bool.not(List.is_empty(&2, String, Main.minus(accepted, accept))), Main.Refused{1, Main.these(Main.minus(accepted, accept), "this path is not a contested attachment", "these paths are not contested attachments") ++ "; remove the unnecessary acceptance:" ++ Main.accept.lines(Main.minus(accepted, accept))}, Done{Sv.Planned{facts, refused, claimed, accept, emptied, None{}, obs, links}}, pl2, e6))
  +e7 = pick_rest(Sv.Planned, Bool.not(List.is_empty(&2, String, Main.minus(accepted, accept))), Main.Refused{1, Main.these(Main.minus(accepted, accept), "this path is not a contested attachment", "these paths are not contested attachments") ++ "; remove the unnecessary acceptance:" ++ Main.accept.lines(Main.minus(accepted, accept))}, Done{Sv.Planned{facts, refused, claimed, accept, emptied, None{}, obs, links}}, pl2, e6)
  %B.done_eq(Sv.Planned, Sv.Planned{facts, refused, claimed, accept, emptied, None{}, obs, links}, pl2, e7) : {Main.planned.settled(_, accepted) == True{} : Bool}
  B.and_tt(List.is_empty(&2, T.Split, claimed), Bool.and(List.is_empty(&2, T.Split, refused), Bool.and(List.is_empty(&2, T.Split, Sv.marked(obs)), Bool.and(List.is_empty(&2, String, emptied), Bool.and(True{}, Bool.and(List.is_empty(&2, String, Main.minus(accept, accepted)), List.is_empty(&2, String, Main.minus(accepted, accept))))))), h1,
    B.and_tt(List.is_empty(&2, T.Split, refused), Bool.and(List.is_empty(&2, T.Split, Sv.marked(obs)), Bool.and(List.is_empty(&2, String, emptied), Bool.and(True{}, Bool.and(List.is_empty(&2, String, Main.minus(accept, accepted)), List.is_empty(&2, String, Main.minus(accepted, accept)))))), h2,
      B.and_tt(List.is_empty(&2, T.Split, Sv.marked(obs)), Bool.and(List.is_empty(&2, String, emptied), Bool.and(True{}, Bool.and(List.is_empty(&2, String, Main.minus(accept, accepted)), List.is_empty(&2, String, Main.minus(accepted, accept))))), h3,
        B.and_tt(List.is_empty(&2, String, emptied), Bool.and(True{}, Bool.and(List.is_empty(&2, String, Main.minus(accept, accepted)), List.is_empty(&2, String, Main.minus(accepted, accept)))), h4,
          B.and_tt(True{}, Bool.and(List.is_empty(&2, String, Main.minus(accept, accepted)), List.is_empty(&2, String, Main.minus(accepted, accept))), {==},
            B.and_tt(List.is_empty(&2, String, Main.minus(accept, accepted)), List.is_empty(&2, String, Main.minus(accepted, accept)), h5, h6))))))

# What `record` goes on to write is a plan the survey settled.
def settled_ok(+looked: Tree.Tree(), pl: Sv.Planned, +accepted: List<&2, String>, -pl2: Sv.Planned, e: {Main.planned.r(looked, pl, accepted) == Done{pl2} : Result<&2, &2, Main.Refused, Sv.Planned>}) -> {Main.planned.settled(pl2, accepted) == True{} : Bool}:
  match pl:
    case Sv.Planned{facts, refused, claimed, accept, emptied, Some{m}, obs, links}:
      Empty.absurd({Main.planned.settled(pl2, accepted) == True{} : Bool}, B.fail_done(Sv.Planned, Main.Refused{1, m}, pl2, e))
    case Sv.Planned{+facts, +refused, +claimed, +accept, +emptied, None{}, +obs, +links}:
      settled_of(looked, facts, refused, claimed, accept, emptied, obs, links, accepted, pl2, e)

# It moves only files the position holds
# ---------------------------------------

def reloc_files(t: Tree.Tree(), +file: String, +to: String) -> {T.map(~Tree.Entry, ~String, ~(x => Tree.entry_file(x)), Sv.relocated(t, file, to)) == T.map(~Tree.Entry, ~String, ~(x => Tree.entry_file(x)), t) : List<&2, String>}:
  match t:
    case Nil{}:
      {==}
    case Tree.Entry{+f, p, k, y, g, m} <> rest:
      Equal.cong(List<&2, String>, List<&2, String>, l => f <> l, T.map(~Tree.Entry, ~String, ~(x => Tree.entry_file(x)), Sv.relocated(rest, file, to)), T.map(~Tree.Entry, ~String, ~(x => Tree.entry_file(x)), rest), reloc_files(rest, file, to))

def mem_head(+f: String, +rest: List<&2, String>) -> {Rev.member(f <> rest, f) == True{} : Bool}:
  %Equal.sym(Bool, String.eq(f, f), True{}, S.eq_refl(f)) : {Bool.or(_, Rev.member(rest, f)) == True{} : Bool}
  {==}

def or_true(a: Bool, -b: Bool, h: {b == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      h

def holds_step(b: Bool, +f: String, +e: Tree.Entry, +rest: Tree.Tree(), +g: String, eb: {String.eq(f, g) == b : Bool}, h: {Maybe.is_some(&2, Tree.Entry, Bool.pick(Maybe<&2, Tree.Entry>, b, Some{e}, Tree.lookup(rest, g))) == True{} : Bool}, ih: {Tree.holds(rest, g) == True{} : Bool} -> {Rev.member(T.map(~Tree.Entry, ~String, ~(x => Tree.entry_file(x)), rest), g) == True{} : Bool}) -> {Bool.or(b, Rev.member(T.map(~Tree.Entry, ~String, ~(x => Tree.entry_file(x)), rest), g)) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      ih(h)

# A file the tree holds is one of its files.
def holds_mem(t: Tree.Tree(), +g: String, h: {Tree.holds(t, g) == True{} : Bool}) -> {Rev.member(T.map(~Tree.Entry, ~String, ~(x => Tree.entry_file(x)), t), g) == True{} : Bool}:
  match t:
    case Nil{}:
      Empty.absurd({Rev.member(Nil{}, g) == True{} : Bool}, S.false_true(h))
    case Tree.Entry{+f, +p, +k, +y, +gg, +m} <> +rest:
      holds_step(String.eq(f, g), f, Tree.Entry{f, p, k, y, gg, m}, rest, g, {==}, h, hr => holds_mem(rest, g, hr))

def keep_held(b: Bool, +f: String, +fs: List<&2, String>, +xs: List<&2, String>, +h: {Main.all_held(fs, xs) == True{} : Bool}) -> {Main.all_held(f <> fs, Rev.keep(b, f, xs)) == True{} : Bool}:
  match b:
    case True{}:
      B.and_tt(Rev.member(f <> fs, f), Main.all_held(f <> fs, xs), mem_head(f, fs), StatusL.ah_weak(f, fs, xs, h))
    case False{}:
      StatusL.ah_weak(f, fs, xs, h)

# Every file the tree has at a path is one of its files.
def at_mem(t: Tree.Tree(), +p: String) -> {Main.all_held(T.map(~Tree.Entry, ~String, ~(x => Tree.entry_file(x)), t), Tree.at(t, p)) == True{} : Bool}:
  match t:
    case Nil{}:
      {==}
    case Tree.Entry{+f, +q, k, y, g, m} <> +rest:
      keep_held(String.eq(q, p), f, T.map(~Tree.Entry, ~String, ~(x => Tree.entry_file(x)), rest), Tree.at(rest, p), at_mem(rest, p))

def files_at_mem(+t: Tree.Tree(), +p: String) -> {Main.all_held(T.map(~Tree.Entry, ~String, ~(x => Tree.entry_file(x)), t), Main.files_at(t, p)) == True{} : Bool}:
  StatusL.ah_sort(~(a => b => String.is_le(a, b)), T.map(~Tree.Entry, ~String, ~(x => Tree.entry_file(x)), t), Tree.at(t, p), at_mem(t, p))

def mh_app(+files: List<&2, String>, xs: List<&2, T.Split>, +f: String, +to: String, +hx: {Main.moved.held(files, xs) == True{} : Bool}, hf: {Rev.member(files, f) == True{} : Bool}) -> {Main.moved.held(files, List.append(&2, T.Split, xs, [T.Split{f, to}])) == True{} : Bool}:
  match xs:
    case Nil{}:
      B.and_tt(Rev.member(files, f), True{}, hf, {==})
    case T.Split{+g, +w} <> +rest:
      B.and_tt(Rev.member(files, g), Main.moved.held(files, List.append(&2, T.Split, rest, [T.Split{f, to}])), SortL.band_l(Rev.member(files, g), Main.moved.held(files, rest), hx),
        mh_app(files, rest, f, to, SortL.band_r(Rev.member(files, g), Main.moved.held(files, rest), hx), hf))

def mem_moved(+t0: Tree.Tree(), +t: Tree.Tree(), +f: String, +ef: {T.map(~Tree.Entry, ~String, ~(x => Tree.entry_file(x)), t) == T.map(~Tree.Entry, ~String, ~(x => Tree.entry_file(x)), t0) : List<&2, String>}, h: {Rev.member(T.map(~Tree.Entry, ~String, ~(x => Tree.entry_file(x)), t), f) == True{} : Bool}) -> {Rev.member(T.map(~Tree.Entry, ~String, ~(x => Tree.entry_file(x)), t0), f) == True{} : Bool}:
  %ef : {Rev.member(_, f) == True{} : Bool}
  h

def placed_tree(p: Main.Placed) -> Tree.Tree():
  match p:
    case Main.Placed{t, m}:
      t

# `--at` moves files the position holds, and keeps its files.
def at_held(ats: List<&2, T.Split>, held: Bool, +t0: Tree.Tree(), +t: Tree.Tree(), +moved: List<&2, T.Split>, eh: {Main.placed.holds(t, ats) == held : Bool}, +ef: {T.map(~Tree.Entry, ~String, ~(x => Tree.entry_file(x)), t) == T.map(~Tree.Entry, ~String, ~(x => Tree.entry_file(x)), t0) : List<&2, String>}, +hm: {Main.moved.held(T.map(~Tree.Entry, ~String, ~(x => Tree.entry_file(x)), t0), moved) == True{} : Bool}, -p: Main.Placed, e: {Main.placed.at.r(ats, t, moved, held) == Done{p} : Result<&2, &2, Main.Refused, Main.Placed>}) -> {Main.moved.held(T.map(~Tree.Entry, ~String, ~(x => Tree.entry_file(x)), t0), Main.placed.moved(p)) == True{} : Bool}:
  match ats held:
    case Nil{} _:
      %B.done_eq(Main.Placed, Main.Placed{t, moved}, p, e) : {Main.moved.held(T.map(~Tree.Entry, ~String, ~(x => Tree.entry_file(x)), t0), Main.placed.moved(_)) == True{} : Bool}
      hm
    case T.Split{+f, to} <> rest False{}:
      Empty.absurd({Main.moved.held(T.map(~Tree.Entry, ~String, ~(x => Tree.entry_file(x)), t0), Main.placed.moved(p)) == True{} : Bool}, B.fail_done(Main.Placed, Main.Refused{1, "`" ++ f ++ "` is not a file this history holds, so nothing can be moved from it"}, p, e))
    case T.Split{+f, +to} <> +rest True{}:
      +m0 = mem_moved(t0, t, f, ef, holds_mem(t, f, eh))
      at_held(rest, Main.placed.holds(Sv.relocated(t, f, to), rest), t0, Sv.relocated(t, f, to), List.append(&2, T.Split, moved, [T.Split{f, to}]), {==},
        Equal.trans(List<&2, String>, T.map(~Tree.Entry, ~String, ~(x => Tree.entry_file(x)), Sv.relocated(t, f, to)), T.map(~Tree.Entry, ~String, ~(x => Tree.entry_file(x)), t), T.map(~Tree.Entry, ~String, ~(x => Tree.entry_file(x)), t0), reloc_files(t, f, to), ef), mh_app(T.map(~Tree.Entry, ~String, ~(x => Tree.entry_file(x)), t0), moved, f, to, hm, m0), p, e)

def at_files(ats: List<&2, T.Split>, held: Bool, +t0: Tree.Tree(), +t: Tree.Tree(), +moved: List<&2, T.Split>, +ef: {T.map(~Tree.Entry, ~String, ~(x => Tree.entry_file(x)), t) == T.map(~Tree.Entry, ~String, ~(x => Tree.entry_file(x)), t0) : List<&2, String>}, -p: Main.Placed, e: {Main.placed.at.r(ats, t, moved, held) == Done{p} : Result<&2, &2, Main.Refused, Main.Placed>}) -> {T.map(~Tree.Entry, ~String, ~(x => Tree.entry_file(x)), placed_tree(p)) == T.map(~Tree.Entry, ~String, ~(x => Tree.entry_file(x)), t0) : List<&2, String>}:
  match ats held:
    case Nil{} _:
      %B.done_eq(Main.Placed, Main.Placed{t, moved}, p, e) : {T.map(~Tree.Entry, ~String, ~(x => Tree.entry_file(x)), placed_tree(_)) == T.map(~Tree.Entry, ~String, ~(x => Tree.entry_file(x)), t0) : List<&2, String>}
      ef
    case T.Split{+f, to} <> rest False{}:
      Empty.absurd({T.map(~Tree.Entry, ~String, ~(x => Tree.entry_file(x)), placed_tree(p)) == T.map(~Tree.Entry, ~String, ~(x => Tree.entry_file(x)), t0) : List<&2, String>}, B.fail_done(Main.Placed, Main.Refused{1, "`" ++ f ++ "` is not a file this history holds, so nothing can be moved from it"}, p, e))
    case T.Split{+f, +to} <> +rest True{}:
      at_files(rest, Main.placed.holds(Sv.relocated(t, f, to), rest), t0, Sv.relocated(t, f, to), List.append(&2, T.Split, moved, [T.Split{f, to}]),
        Equal.trans(List<&2, String>, T.map(~Tree.Entry, ~String, ~(x => Tree.entry_file(x)), Sv.relocated(t, f, to)), T.map(~Tree.Entry, ~String, ~(x => Tree.entry_file(x)), t), T.map(~Tree.Entry, ~String, ~(x => Tree.entry_file(x)), t0), reloc_files(t, f, to), ef), p, e)

def one_held(+fs: List<&2, String>, +f: String, h: {Main.all_held(fs, [f]) == True{} : Bool}) -> {Rev.member(fs, f) == True{} : Bool}:
  SortL.band_l(Rev.member(fs, f), True{}, h)

# `--move` moves files the position holds.
def move_held(ms: List<&2, T.Split>, at: List<&2, String>, fault: Maybe<&2, String>, +t0: Tree.Tree(), +t: Tree.Tree(), +moved: List<&2, T.Split>, +eat: {Main.placed.head(t, ms) == at : List<&2, String>}, +ef: {T.map(~Tree.Entry, ~String, ~(x => Tree.entry_file(x)), t) == T.map(~Tree.Entry, ~String, ~(x => Tree.entry_file(x)), t0) : List<&2, String>}, +hm: {Main.moved.held(T.map(~Tree.Entry, ~String, ~(x => Tree.entry_file(x)), t0), moved) == True{} : Bool}, -p: Main.Placed, e: {Main.placed.move.r(ms, t, moved, at, fault) == Done{p} : Result<&2, &2, Main.Refused, Main.Placed>}) -> {Main.moved.held(T.map(~Tree.Entry, ~String, ~(x => Tree.entry_file(x)), t0), Main.placed.moved(p)) == True{} : Bool}:
  match ms at fault:
    case Nil{} _ _:
      %B.done_eq(Main.Placed, Main.Placed{t, moved}, p, e) : {Main.moved.held(T.map(~Tree.Entry, ~String, ~(x => Tree.entry_file(x)), t0), Main.placed.moved(_)) == True{} : Bool}
      hm
    case T.Split{+from, to} <> rest Nil{} _:
      Empty.absurd({Main.moved.held(T.map(~Tree.Entry, ~String, ~(x => Tree.entry_file(x)), t0), Main.placed.moved(p)) == True{} : Bool}, B.fail_done(Main.Placed, Main.Refused{1, "`" ++ from ++ "` is not a file this history holds, so nothing can be moved from it"}, p, e))
    case T.Split{+from, +to} <> +rest +f <> Nil{} None{}:
      +hall = Equal.trans(Bool, Main.all_held(T.map(~Tree.Entry, ~String, ~(x => Tree.entry_file(x)), t), [f]), Main.all_held(T.map(~Tree.Entry, ~String, ~(x => Tree.entry_file(x)), t), Main.files_at(t, from)), True{},
        Equal.cong(List<&2, String>, Bool, l => Main.all_held(T.map(~Tree.Entry, ~String, ~(x => Tree.entry_file(x)), t), l), [f], Main.files_at(t, from), Equal.sym(List<&2, String>, Main.files_at(t, from), [f], eat)),
        files_at_mem(t, from))
      +m0 = mem_moved(t0, t, f, ef, one_held(T.map(~Tree.Entry, ~String, ~(x => Tree.entry_file(x)), t), f, hall))
      move_held(rest, Main.placed.head(Sv.relocated(t, f, to), rest), Main.placed.fault(rest), t0, Sv.relocated(t, f, to), List.append(&2, T.Split, moved, [T.Split{f, to}]), {==},
        Equal.trans(List<&2, String>, T.map(~Tree.Entry, ~String, ~(x => Tree.entry_file(x)), Sv.relocated(t, f, to)), T.map(~Tree.Entry, ~String, ~(x => Tree.entry_file(x)), t), T.map(~Tree.Entry, ~String, ~(x => Tree.entry_file(x)), t0), reloc_files(t, f, to), ef), mh_app(T.map(~Tree.Entry, ~String, ~(x => Tree.entry_file(x)), t0), moved, f, to, hm, m0), p, e)
    case T.Split{from, +to} <> rest f <> Nil{} Some{+because}:
      Empty.absurd({Main.moved.held(T.map(~Tree.Entry, ~String, ~(x => Tree.entry_file(x)), t0), Main.placed.moved(p)) == True{} : Bool}, B.fail_done(Main.Placed, Main.Refused{1, "`" ++ to ++ "` cannot be a path here: " ++ because}, p, e))
    case T.Split{+from, to} <> rest +f <> +g <> +r None{}:
      Empty.absurd({Main.moved.held(T.map(~Tree.Entry, ~String, ~(x => Tree.entry_file(x)), t0), Main.placed.moved(p)) == True{} : Bool}, B.fail_done(Main.Placed, Main.Refused{1, Main.contested.msg(from, f <> g <> r)}, p, e))
    case T.Split{+from, to} <> rest +f <> +g <> +r Some{x}:
      Empty.absurd({Main.moved.held(T.map(~Tree.Entry, ~String, ~(x => Tree.entry_file(x)), t0), Main.placed.moved(p)) == True{} : Bool}, B.fail_done(Main.Placed, Main.Refused{1, Main.contested.msg(from, f <> g <> r)}, p, e))

def placed2(p1: Main.Placed, +t: Tree.Tree(), +ms: List<&2, T.Split>, +hm: {Main.moved.held(T.map(~Tree.Entry, ~String, ~(x => Tree.entry_file(x)), t), Main.placed.moved(p1)) == True{} : Bool}, +ef: {T.map(~Tree.Entry, ~String, ~(x => Tree.entry_file(x)), placed_tree(p1)) == T.map(~Tree.Entry, ~String, ~(x => Tree.entry_file(x)), t) : List<&2, String>}, -p: Main.Placed, e: {Main.placed.of.r(p1, ms) == Done{p} : Result<&2, &2, Main.Refused, Main.Placed>}) -> {Main.moved.held(T.map(~Tree.Entry, ~String, ~(x => Tree.entry_file(x)), t), Main.placed.moved(p)) == True{} : Bool}:
  match p1:
    case Main.Placed{+t1, +moved1}:
      move_held(ms, Main.placed.head(t1, ms), Main.placed.fault(ms), t, t1, moved1, {==}, ef, hm, p, e)

def placed1(+t: Tree.Tree(), +ats: List<&2, T.Split>, +ms: List<&2, T.Split>, r: Result<&2, &2, Main.Refused, Main.Placed>, +er: {Main.placed.at.r(ats, t, Nil{}, Main.placed.holds(t, ats)) == r : Result<&2, &2, Main.Refused, Main.Placed>}, -p: Main.Placed, e: {Result.bind(&2, &2, Main.Refused, Main.Placed, Main.Placed, r, p1 => Main.placed.of.r(p1, ms)) == Done{p} : Result<&2, &2, Main.Refused, Main.Placed>}) -> {Main.moved.held(T.map(~Tree.Entry, ~String, ~(x => Tree.entry_file(x)), t), Main.placed.moved(p)) == True{} : Bool}:
  match r:
    case Fail{x}:
      Empty.absurd({Main.moved.held(T.map(~Tree.Entry, ~String, ~(x => Tree.entry_file(x)), t), Main.placed.moved(p)) == True{} : Bool}, B.fail_done(Main.Placed, x, p, e))
    case Done{+p1}:
      placed2(p1, t, ms, at_held(ats, Main.placed.holds(t, ats), t, t, Nil{}, {==}, {==}, {==}, p1, er), at_files(ats, Main.placed.holds(t, ats), t, t, Nil{}, {==}, p1, er), p, e)

# Every file `record` moves by a stated rename is one the position holds.
def placed_held(+t: Tree.Tree(), +ats: List<&2, T.Split>, +ms: List<&2, T.Split>, -p: Main.Placed, e: {Main.placed.r(t, ats, ms) == Done{p} : Result<&2, &2, Main.Refused, Main.Placed>}) -> {Main.moved.held(T.map(~Tree.Entry, ~String, ~(x => Tree.entry_file(x)), t), Main.placed.moved(p)) == True{} : Bool}:
  placed1(t, ats, ms, Main.placed.at.r(ats, t, Nil{}, Main.placed.holds(t, ats)), {==}, p, e)

# It restricts no merge and no half of a rename
# ---------------------------------------------

def pick_yes(-A: Data, b: Bool, -r: Result<&2, &2, Main.Refused, A>, -x: Main.Refused, -y: A, e: {Bool.pick(Result<&2, &2, Main.Refused, A>, b, r, Fail{x}) == Done{y} : Result<&2, &2, Main.Refused, A>}) -> {b == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, B.fail_done(A, x, y, e))

def pick_keep(-A: Data, b: Bool, -r: Result<&2, &2, Main.Refused, A>, -x: Main.Refused, -y: A, e: {Bool.pick(Result<&2, &2, Main.Refused, A>, b, r, Fail{x}) == Done{y} : Result<&2, &2, Main.Refused, A>}) -> {r == Done{y} : Result<&2, &2, Main.Refused, A>}:
  match b:
    case True{}:
      e
    case False{}:
      Empty.absurd({r == Done{y} : Result<&2, &2, Main.Refused, A>}, B.fail_done(A, x, y, e))

def half_ok(+named: List<&2, String>, moves: List<&2, T.Split>, -u: Unit, +e: {Main.restricted.half.r(named, moves) == Done{u} : Result<&2, &2, Main.Refused, Unit>}) -> {Main.renames.covered(named, moves) == True{} : Bool}:
  match moves:
    case Nil{}:
      {==}
    case T.Split{+from, +to} <> +rest:
      +b = Bool.and(Sv.covers(named, from), Sv.covers(named, to))
      B.and_tt(b, Main.renames.covered(named, rest), pick_yes(Unit, b, Main.restricted.half.r(named, rest), Main.Refused{1, "`" ++ from ++ "` and `" ++ to ++ "` are one rename, and only one of them is among the paths this would record, which would spell the other end as a file appearing or disappearing; name both `" ++ from ++ "` and `" ++ to ++ "`, or record with no paths named"}, u, e),
        half_ok(named, rest, u, pick_keep(Unit, b, Main.restricted.half.r(named, rest), Main.Refused{1, "`" ++ from ++ "` and `" ++ to ++ "` are one rename, and only one of them is among the paths this would record, which would spell the other end as a file appearing or disappearing; name both `" ++ from ++ "` and `" ++ to ++ "`, or record with no paths named"}, u, e)))

def not_false(b: Bool, h: {b == False{} : Bool}) -> {Bool.not(b) == True{} : Bool}:
  %Equal.sym(Bool, b, False{}, h) : {Bool.not(_) == True{} : Bool}
  {==}

def whole_of(b0: Bool, +named: List<&2, String>, +ps: List<&2, String>, +moves: List<&2, T.Split>, -u: Unit, +e: {Bool.pick(Result<&2, &2, Main.Refused, Unit>, b0, Done{Unit{}}, Bool.pick(Result<&2, &2, Main.Refused, Unit>, Nat.is_gt(List.length(&2, String, ps), 1n), Fail{Main.Refused{1, "a merge states what every contested file is, and a merge of some of them would leave the rest joined and unstated; record the merge with no paths named, and restrict the record after it:" ++ Main.skips_held.lines(named)}}, Main.restricted.half.r(named, moves))) == Done{u} : Result<&2, &2, Main.Refused, Unit>}) -> {Bool.or(b0, Bool.and(Bool.not(Nat.is_gt(List.length(&2, String, ps), 1n)), Main.renames.covered(named, moves))) == True{} : Bool}:
  match b0:
    case True{}:
      {==}
    case False{}:
      +g = Nat.is_gt(List.length(&2, String, ps), 1n)
      B.and_tt(Bool.not(g), Main.renames.covered(named, moves), not_false(g, pick_no(Unit, g, Main.Refused{1, "a merge states what every contested file is, and a merge of some of them would leave the rest joined and unstated; record the merge with no paths named, and restrict the record after it:" ++ Main.skips_held.lines(named)}, Main.restricted.half.r(named, moves), u, e)),
        half_ok(named, moves, u, pick_rest(Unit, g, Main.Refused{1, "a merge states what every contested file is, and a merge of some of them would leave the rest joined and unstated; record the merge with no paths named, and restrict the record after it:" ++ Main.skips_held.lines(named)}, Main.restricted.half.r(named, moves), u, e)))

# A record restricted to some paths is no merge, and states no half of a
# rename.
def restriction_ok(+named: List<&2, String>, +ps: List<&2, String>, +moves: List<&2, T.Split>, -u: Unit, e: {Main.restricted.r(named, ps, moves) == Done{u} : Result<&2, &2, Main.Refused, Unit>}) -> {Main.restriction.whole(named, ps, moves) == True{} : Bool}:
  whole_of(List.is_empty(&2, String, named), named, ps, moves, u, e)

# It names only what is there
# ---------------------------

def skipped_either(sk: Bool, +rules: List<&2, Folder.Scope>, +n: String, +rest: List<&2, String>, h1: {List.is_empty(&2, String, Bool.pick(List<&2, String>, Bool.xor(sk, Bool.not(True{})), n <> Sv.kept_out(rules, rest, True{}), Sv.kept_out(rules, rest, True{}))) == True{} : Bool}, h2: {List.is_empty(&2, String, Bool.pick(List<&2, String>, Bool.xor(sk, Bool.not(False{})), n <> Sv.kept_out(rules, rest, False{}), Sv.kept_out(rules, rest, False{}))) == True{} : Bool}) -> Empty:
  match sk:
    case True{}:
      S.false_true(h1)
    case False{}:
      S.false_true(h2)

# A name neither kept out nor let through is no name at all.
def both_empty(+rules: List<&2, Folder.Scope>, u: List<&2, String>, h1: {List.is_empty(&2, String, Sv.kept_out(rules, u, True{})) == True{} : Bool}, h2: {List.is_empty(&2, String, Sv.kept_out(rules, u, False{})) == True{} : Bool}) -> {List.is_empty(&2, String, u) == True{} : Bool}:
  match u:
    case Nil{}:
      {==}
    case +n <> +rest:
      Empty.absurd({List.is_empty(&2, String, n <> rest) == True{} : Bool}, skipped_either(Bool.or(Folder.skips(rules, n), Folder.skips_directory(rules, n)), rules, n, rest, h1, h2))

# Every path `record` is asked to record answers to something: the
# folder, the history, or where the stated renames put a file.
def named_ok(+rules: List<&2, Folder.Scope>, +named: List<&2, String>, +folder: List<&2, String>, +was: List<&2, String>, +placed: List<&2, String>, -u: Unit, +e: {Main.named.r(rules, named, folder, was, placed) == Done{u} : Result<&2, &2, Main.Refused, Unit>}) -> {List.is_empty(&2, String, Sv.unknown(named, folder, was, placed)) == True{} : Bool}:
  +h1 = not_true(List.is_empty(&2, String, Sv.kept_out(rules, Sv.unknown(named, folder, was, placed), True{})), pick_no(Unit, Bool.not(List.is_empty(&2, String, Sv.kept_out(rules, Sv.unknown(named, folder, was, placed), True{}))), Main.Refused{1, "`history/skipped/` says history does not take " ++ Main.these(Sv.kept_out(rules, Sv.unknown(named, folder, was, placed), True{}), "this", "these") ++ ", and naming " ++ Main.these(Sv.kept_out(rules, Sv.unknown(named, folder, was, placed), True{}), "it", "them") ++ " here does not make " ++ Main.these(Sv.kept_out(rules, Sv.unknown(named, folder, was, placed), True{}), "it", "them") ++ " an exception; remove the rule if " ++ Main.these(Sv.kept_out(rules, Sv.unknown(named, folder, was, placed), True{}), "it is", "they are") ++ " to be recorded:" ++ Main.skips_held.lines(Sv.kept_out(rules, Sv.unknown(named, folder, was, placed), True{}))}, Bool.pick(Result<&2, &2, Main.Refused, Unit>, Bool.not(List.is_empty(&2, String, Sv.kept_out(rules, Sv.unknown(named, folder, was, placed), False{}))), Fail{Main.Refused{1, Main.these(Sv.kept_out(rules, Sv.unknown(named, folder, was, placed), False{}), "this path is", "these paths are") ++ " neither in the folder nor in this history, so there is nothing there to observe; check the spelling, or name no paths at all and record everything the folder says:" ++ Main.skips_held.lines(Sv.kept_out(rules, Sv.unknown(named, folder, was, placed), False{}))}}, Done{Unit{}}), u, e))
  +e2 = pick_rest(Unit, Bool.not(List.is_empty(&2, String, Sv.kept_out(rules, Sv.unknown(named, folder, was, placed), True{}))), Main.Refused{1, "`history/skipped/` says history does not take " ++ Main.these(Sv.kept_out(rules, Sv.unknown(named, folder, was, placed), True{}), "this", "these") ++ ", and naming " ++ Main.these(Sv.kept_out(rules, Sv.unknown(named, folder, was, placed), True{}), "it", "them") ++ " here does not make " ++ Main.these(Sv.kept_out(rules, Sv.unknown(named, folder, was, placed), True{}), "it", "them") ++ " an exception; remove the rule if " ++ Main.these(Sv.kept_out(rules, Sv.unknown(named, folder, was, placed), True{}), "it is", "they are") ++ " to be recorded:" ++ Main.skips_held.lines(Sv.kept_out(rules, Sv.unknown(named, folder, was, placed), True{}))}, Bool.pick(Result<&2, &2, Main.Refused, Unit>, Bool.not(List.is_empty(&2, String, Sv.kept_out(rules, Sv.unknown(named, folder, was, placed), False{}))), Fail{Main.Refused{1, Main.these(Sv.kept_out(rules, Sv.unknown(named, folder, was, placed), False{}), "this path is", "these paths are") ++ " neither in the folder nor in this history, so there is nothing there to observe; check the spelling, or name no paths at all and record everything the folder says:" ++ Main.skips_held.lines(Sv.kept_out(rules, Sv.unknown(named, folder, was, placed), False{}))}}, Done{Unit{}}), u, e)
  +h2 = not_true(List.is_empty(&2, String, Sv.kept_out(rules, Sv.unknown(named, folder, was, placed), False{})), pick_no(Unit, Bool.not(List.is_empty(&2, String, Sv.kept_out(rules, Sv.unknown(named, folder, was, placed), False{}))), Main.Refused{1, Main.these(Sv.kept_out(rules, Sv.unknown(named, folder, was, placed), False{}), "this path is", "these paths are") ++ " neither in the folder nor in this history, so there is nothing there to observe; check the spelling, or name no paths at all and record everything the folder says:" ++ Main.skips_held.lines(Sv.kept_out(rules, Sv.unknown(named, folder, was, placed), False{}))}, Done{Unit{}}, u, e2))
  both_empty(rules, Sv.unknown(named, folder, was, placed), h1, h2)

# Its dry run says an arrival once
# --------------------------------

def once_app(+a: Set(), xs: List<&2, T.Split>, +ys: List<&2, T.Split>, +hx: {Main.recorded.once(a, xs) == True{} : Bool}, hy: {Main.recorded.once(a, ys) == True{} : Bool}) -> {Main.recorded.once(a, List.append(&2, T.Split, xs, ys)) == True{} : Bool}:
  match xs:
    case Nil{}:
      hy
    case T.Split{+k, +p} <> +rest:
      +c = Bool.or(String.eq(k, "added"), Bool.or(String.eq(k, "moved"), Bool.or(String.eq(k, "dropped"), Bool.not(Sv.has(a, p)))))
      B.and_tt(c, Main.recorded.once(a, List.append(&2, T.Split, rest, ys)), SortL.band_l(c, Main.recorded.once(a, rest), hx),
        once_app(a, rest, ys, SortL.band_r(c, Main.recorded.once(a, rest), hx), hy))

def once_added(+a: Set(), ps: List<&2, String>) -> {Main.recorded.once(a, Sv.fact("added", ps)) == True{} : Bool}:
  match ps:
    case Nil{}:
      {==}
    case p <> rest:
      once_added(a, rest)

def once_moved(+a: Set(), ps: List<&2, String>) -> {Main.recorded.once(a, Sv.fact("moved", ps)) == True{} : Bool}:
  match ps:
    case Nil{}:
      {==}
    case p <> rest:
      once_moved(a, rest)

def once_dropped(+a: Set(), ps: List<&2, String>) -> {Main.recorded.once(a, Sv.fact("dropped", ps)) == True{} : Bool}:
  match ps:
    case Nil{}:
      {==}
    case p <> rest:
      once_dropped(a, rest)

def once_pick(b: Bool, +a: Set(), +k: String, +x: String, +later: List<&2, String>, eb: {Sv.has(a, x) == b : Bool}, h: {Main.recorded.once(a, Sv.fact(k, later)) == True{} : Bool}) -> {Main.recorded.once(a, Sv.fact(k, Sv.without.pick(b, x, later))) == True{} : Bool}:
  match b:
    case True{}:
      h
    case False{}:
      B.and_tt(Bool.or(String.eq(k, "added"), Bool.or(String.eq(k, "moved"), Bool.or(String.eq(k, "dropped"), Bool.not(Sv.has(a, x))))), Main.recorded.once(a, Sv.fact(k, later)),
        or_true(String.eq(k, "added"), Bool.or(String.eq(k, "moved"), Bool.or(String.eq(k, "dropped"), Bool.not(Sv.has(a, x)))),
        or_true(String.eq(k, "moved"), Bool.or(String.eq(k, "dropped"), Bool.not(Sv.has(a, x))),
        or_true(String.eq(k, "dropped"), Bool.not(Sv.has(a, x)), not_false(Sv.has(a, x), eb)))), h)

def once_without(+a: Set(), +k: String, xs: List<&2, String>) -> {Main.recorded.once(a, Sv.fact(k, Sv.without(xs, a))) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      once_pick(Sv.has(a, x), a, k, x, Sv.without(rest, a), {==}, once_without(a, k, rest))

# What `record --dry-run` says names an arriving file on its `added` line
# alone, whatever it observed.
def recorded_once(+a: Set(), +os: List<&2, Sv.Obs>, +ls: List<&2, String>, +mp: List<&2, String>) -> {Main.recorded.once(a, Sv.facts.recorded(a, os, ls, mp)) == True{} : Bool}:
  +ed = Sv.fact("edited", Sv.without(Sv.sorted(Sv.edited(os)), a))
  +md = Sv.fact("mode", Sv.without(Sv.sorted(Sv.modes(os)), a))
  +lk = Sv.fact("link", Sv.without(Sv.sorted(ls), a))
  +dr = Sv.fact("dropped", Sv.sorted(Sv.dropped_paths(os)))
  +mv = Sv.fact("moved", Sv.sorted(mp))
  once_app(a, Sv.fact("added", Sv.sorted(Sv.added(os))), List.append(&2, T.Split, mv, List.append(&2, T.Split, dr, List.append(&2, T.Split, ed, List.append(&2, T.Split, md, lk)))), once_added(a, Sv.sorted(Sv.added(os))),
    once_app(a, mv, List.append(&2, T.Split, dr, List.append(&2, T.Split, ed, List.append(&2, T.Split, md, lk))), once_moved(a, Sv.sorted(mp)),
    once_app(a, dr, List.append(&2, T.Split, ed, List.append(&2, T.Split, md, lk)), once_dropped(a, Sv.sorted(Sv.dropped_paths(os))),
    once_app(a, ed, List.append(&2, T.Split, md, lk), once_without(a, "edited", Sv.sorted(Sv.edited(os))),
    once_app(a, md, lk, once_without(a, "mode", Sv.sorted(Sv.modes(os))), once_without(a, "link", Sv.sorted(ls)))))))

# What `record` plans says an arriving file once.
def planned_once(+t: Tree.Tree(), +looked: Tree.Tree(), +held: Set(), +walked: List<&2, T.Split>, +ss: List<&2, Sv.Seen>, +moves: List<&2, T.Split>) -> {Main.recorded.once(Set.from_list(Sv.added(Main.planned.obs(Sv.planned(t, looked, held, walked, ss, moves)))), Main.planned.facts(Sv.planned(t, looked, held, walked, ss, moves))) == True{} : Bool}:
  +os = List.append(&2, Sv.Obs, Sv.seens(ss), Sv.claimed_drops(looked, Sv.claims(looked), held))
  +a = Set.from_list(Sv.added(os))
  recorded_once(a, os, Sv.links(t, Set.from_list(Sv.dropped_files(os)), a, os), Sv.moved.paths(moves, Set.from_list(Sv.dropped_files(os))))

# It reads as lines only what is text
# -----------------------------------

def msome(m: Maybe<&2, String>) -> Type:
  match m:
    case Some{x}:
      Unit
    case None{}:
      Empty

def none_some_m2(-x: String, h: {Some{x} == None{} : Maybe<&2, String>}) -> Empty:
  %h : {msome(_) : Type}
  Unit{}

def mnone_pick(b: Bool, -x: String, -r: Maybe<&2, String>, e: {Bool.pick(Maybe<&2, String>, b, Some{x}, r) == None{} : Maybe<&2, String>}) -> {b == False{} : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, none_some_m2(x, e))

def mnone_rest(b: Bool, -x: String, -r: Maybe<&2, String>, e: {Bool.pick(Maybe<&2, String>, b, Some{x}, r) == None{} : Maybe<&2, String>}) -> {r == None{} : Maybe<&2, String>}:
  match b:
    case False{}:
      e
    case True{}:
      Empty.absurd({r == None{} : Maybe<&2, String>}, none_some_m2(x, e))

def text_keep(ls: Bool, u: Bool, +reads: Map<&2, List<&2, U32>>, +p: String, +rest: List<&2, String>, eu: {Folder.is_utf8(Main.bytes_of(p, Map.get(List<&2, U32>, Nil{}, reads, p))) == u : Bool}, h: {Bool.and(ls, Bool.not(u)) == False{} : Bool}, ih: {Main.utf8.all(reads, rest) == True{} : Bool}) -> {Main.utf8.all(reads, Rev.keep(ls, p, rest)) == True{} : Bool}:
  match ls:
    case False{}:
      ih
    case True{}:
      match u:
        case True{}:
          B.and_tt(Folder.is_utf8(Main.bytes_of(p, Map.get(List<&2, U32>, Nil{}, reads, p))), Main.utf8.all(reads, rest), eu, ih)
        case False{}:
          Empty.absurd({Main.utf8.all(reads, Rev.keep(True{}, p, rest)) == True{} : Bool}, S.true_false(h))

# Where `record` goes on, every file a person said is lines is text.
def lines_text(+ks: List<&2, T.Split>, +reads: Map<&2, List<&2, U32>>, hs: List<&2, Main.Here>, +e: {Main.not_lines(ks, reads, hs) == None{} : Maybe<&2, String>}) -> {Main.utf8.all(reads, Main.lined_added(ks, hs)) == True{} : Bool}:
  match hs:
    case Nil{}:
      {==}
    case Main.Here{+p, None{}, Some{Folder.Found.File{q, r, n}}} <> +rest:
      +b = Bool.and(Main.lines.stated(ks, p), Bool.not(Folder.is_utf8(Main.bytes_of(p, Map.get(List<&2, U32>, Nil{}, reads, p)))))
      text_keep(Main.lines.stated(ks, p), Folder.is_utf8(Main.bytes_of(p, Map.get(List<&2, U32>, Nil{}, reads, p))), reads, p, Main.lined_added(ks, rest), {==}, mnone_pick(b, "`" ++ p ++ "` cannot be recorded as lines: its bytes are not UTF-8, and a line is text whoever says otherwise. Record it as bytes, or convert the file first", Main.not_lines(ks, reads, rest), e),
        lines_text(ks, reads, rest, mnone_rest(b, "`" ++ p ++ "` cannot be recorded as lines: its bytes are not UTF-8, and a line is text whoever says otherwise. Record it as bytes, or convert the file first", Main.not_lines(ks, reads, rest), e)))
    case Main.Here{p, None{}, Some{Folder.Found.Link{q, t}}} <> rest:
      lines_text(ks, reads, rest, e)
    case Main.Here{p, None{}, None{}} <> rest:
      lines_text(ks, reads, rest, e)
    case Main.Here{p, Some{x}, f} <> rest:
      lines_text(ks, reads, rest, e)

# It reads the position's content of what it edits
# ------------------------------------------------

def read2(+older: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +left: String, +f: String, +items: List<&2, Ops.Item>, +rest: List<&2, String>, r: Result<&2, &2, Main.Refused, List<&2, Main.Before>>, -bs: List<&2, Main.Before>, er: {Main.befores.r(older, ds, left, rest) == r : Result<&2, &2, Main.Refused, List<&2, Main.Before>>}, eg: {Main.content.in(older, ds, left, f) == Done{items} : Result<&2, &2, String, List<&2, Ops.Item>>}, e: {Result.bind(&2, &2, Main.Refused, List<&2, Main.Before>, List<&2, Main.Before>, r, later => Done{Main.Before{f, items} <> later}) == Done{bs} : Result<&2, &2, Main.Refused, List<&2, Main.Before>>}, ih: @more: List<&2, Main.Before> -> {Main.befores.r(older, ds, left, rest) == Done{more} : Result<&2, &2, Main.Refused, List<&2, Main.Before>>} -> {Main.befores.read(older, ds, left, rest, more) == True{} : Bool}) -> {Main.befores.read(older, ds, left, f <> rest, bs) == True{} : Bool}:
  match r:
    case Fail{x}:
      Empty.absurd({Main.befores.read(older, ds, left, f <> rest, bs) == True{} : Bool}, B.fail_done(List<&2, Main.Before>, x, bs, e))
    case Done{+later}:
      %B.done_eq(List<&2, Main.Before>, Main.Before{f, items} <> later, bs, e) : {Main.befores.read(older, ds, left, f <> rest, _) == True{} : Bool}
      %Equal.sym(Result<&2, &2, String, List<&2, Ops.Item>>, Main.content.in(older, ds, left, f), Done{items}, eg) : {Bool.and(String.eq(f, f), Bool.and(Main.content.applied(_, items), Main.befores.read(older, ds, left, rest, later))) == True{} : Bool}
      B.and_tt(String.eq(f, f), Bool.and(Main.content.applied(Done{items}, items), Main.befores.read(older, ds, left, rest, later)), S.eq_refl(f),
        B.and_tt(Main.content.applied(Done{items}, items), Main.befores.read(older, ds, left, rest, later), items_refl(items), ih(later, er)))

def read1(+older: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +left: String, +f: String, +rest: List<&2, String>, got: Result<&2, &2, String, List<&2, Ops.Item>>, -bs: List<&2, Main.Before>, eg: {Main.content.in(older, ds, left, f) == got : Result<&2, &2, String, List<&2, Ops.Item>>}, e: {Main.befores.of(f, got, Main.befores.r(older, ds, left, rest)) == Done{bs} : Result<&2, &2, Main.Refused, List<&2, Main.Before>>}, ih: @more: List<&2, Main.Before> -> {Main.befores.r(older, ds, left, rest) == Done{more} : Result<&2, &2, Main.Refused, List<&2, Main.Before>>} -> {Main.befores.read(older, ds, left, rest, more) == True{} : Bool}) -> {Main.befores.read(older, ds, left, f <> rest, bs) == True{} : Bool}:
  match got:
    case Fail{x}:
      Empty.absurd({Main.befores.read(older, ds, left, f <> rest, bs) == True{} : Bool}, B.fail_done(List<&2, Main.Before>, Main.Refused{1, x}, bs, e))
    case Done{+items}:
      read2(older, ds, left, f, items, rest, Main.befores.r(older, ds, left, rest), bs, {==}, eg, e, ih)

# What `record` reads of the position is the store's replay of each file
# it edits, one reading each, in order.
def befores_read(+older: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +left: String, files: List<&2, String>, -bs: List<&2, Main.Before>, e: {Main.befores.r(older, ds, left, files) == Done{bs} : Result<&2, &2, Main.Refused, List<&2, Main.Before>>}) -> {Main.befores.read(older, ds, left, files, bs) == True{} : Bool}:
  match files:
    case Nil{}:
      %B.done_eq(List<&2, Main.Before>, Nil{}, bs, e) : {Main.befores.read(older, ds, left, Nil{}, _) == True{} : Bool}
      {==}
    case +f <> +rest:
      read1(older, ds, left, f, rest, Main.content.in(older, ds, left, f), bs, {==}, e, more => h => befores_read(older, ds, left, rest, more, h))

# It gives kinds only to files
# ----------------------------

# Every path given a kind is a file the folder holds.
def kinds_found(ks: List<&2, T.Split>, +found: Set(), -u: Unit, +e: {Main.kinds.unheld.r(ks, found) == Done{u} : Result<&2, &2, Main.Refused, Unit>}) -> {Main.kinds.found(ks, found) == True{} : Bool}:
  match ks:
    case Nil{}:
      {==}
    case T.Split{+p, k} <> +rest:
      B.and_tt(Sv.has(found, p), Main.kinds.found(rest, found), pick_yes(Unit, Sv.has(found, p), Main.kinds.unheld.r(rest, found), Main.Refused{2, "`" ++ p ++ "` is not a file in this folder, so there is no kind for it to be"}, u, e),
        kinds_found(rest, found, u, pick_keep(Unit, Sv.has(found, p), Main.kinds.unheld.r(rest, found), Main.Refused{2, "`" ++ p ++ "` is not a file in this folder, so there is no kind for it to be"}, u, e)))

def once_list(+xs: List<&2, String>, fs: List<&2, T.Split>) -> {Main.recorded.once(Set.from_list(xs), fs) == Main.recorded.once.list(xs, fs) : Bool}:
  match fs:
    case Nil{}:
      {==}
    case T.Split{+k, +p} <> rest:
      %Equal.sym(Bool, Sv.has(Set.from_list(xs), p), Rev.member(xs, p), SurveyL.member_set(xs, p)) : {Bool.and(Bool.or(String.eq(k, "added"), Bool.or(String.eq(k, "moved"), Bool.or(String.eq(k, "dropped"), Bool.not(_)))), Main.recorded.once(Set.from_list(xs), rest)) == Bool.and(Bool.or(String.eq(k, "added"), Bool.or(String.eq(k, "moved"), Bool.or(String.eq(k, "dropped"), Bool.not(Rev.member(xs, p))))), Main.recorded.once.list(xs, rest)) : Bool}
      %Equal.sym(Bool, Main.recorded.once(Set.from_list(xs), rest), Main.recorded.once.list(xs, rest), once_list(xs, rest)) : {Bool.and(Bool.or(String.eq(k, "added"), Bool.or(String.eq(k, "moved"), Bool.or(String.eq(k, "dropped"), Bool.not(Rev.member(xs, p))))), _) == Bool.and(Bool.or(String.eq(k, "added"), Bool.or(String.eq(k, "moved"), Bool.or(String.eq(k, "dropped"), Bool.not(Rev.member(xs, p))))), Main.recorded.once.list(xs, rest)) : Bool}
      {==}

# `record --dry-run` names a path arriving only on an `added`, `moved` or
# `dropped` line, read against the list of what arrives.
def planned_once_list(+t: Tree.Tree(), +looked: Tree.Tree(), +held: Set(), +walked: List<&2, T.Split>, +ss: List<&2, Sv.Seen>, +moves: List<&2, T.Split>) -> {Main.recorded.once.list(Sv.added(Main.planned.obs(Sv.planned(t, looked, held, walked, ss, moves))), Main.planned.facts(Sv.planned(t, looked, held, walked, ss, moves))) == True{} : Bool}:
  +xs = Sv.added(Main.planned.obs(Sv.planned(t, looked, held, walked, ss, moves)))
  +fs = Main.planned.facts(Sv.planned(t, looked, held, walked, ss, moves))
  Equal.trans(Bool, Main.recorded.once.list(xs, fs), Main.recorded.once(Set.from_list(xs), fs), True{}, Equal.sym(Bool, Main.recorded.once(Set.from_list(xs), fs), Main.recorded.once.list(xs, fs), once_list(xs, fs)), planned_once(t, looked, held, walked, ss, moves))

