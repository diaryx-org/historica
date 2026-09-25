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
import ./store.bend as Store
import ./composition_lemmas.bend as Comp
import ./anchor_lemmas.bend as AL
import ./equality_lemmas.bend as Eq
import ./naming_lemmas.bend as NamingL

# Its words
# ---------

def done_rc(-a: Main.RecordCmd, -b: Main.RecordCmd, h: {Done{a} == Done{b} : Result<&2, &2, Main.Refused, Main.RecordCmd>}) -> {a == b : Main.RecordCmd}:
  B.done_eq(Main.RecordCmd, a, b, h)

# Where the words read so far end, the next are read afresh.
def kk(args: List<&2, String>, +more: List<&2, String>, k: Main.RWord) -> Main.RWord:
  match args:
    case Nil{}:
      Main.rword(more)
    case _:
      k

def kk_rw(args: List<&2, String>, +more: List<&2, String>) -> {kk(args, more, Main.rword(args)) == Main.rword(List.append(&2, String, args, more)) : Main.RWord}:
  match args:
    case Nil{}:
      {==}
    case w <> rest:
      {==}

def rstep(+rest: List<&2, String>, +more: List<&2, String>, -c1: Main.RecordCmd, -c2: Main.RecordCmd, ih: {Main.record.args.go(List.append(&2, String, rest, more), c1, kk(rest, more, Main.rword(rest))) == Main.record.args.go(more, c2, Main.rword(more)) : Result<&2, &2, Main.Refused, Main.RecordCmd>}) -> {Main.record.args.go(List.append(&2, String, rest, more), c1, Main.rword(List.append(&2, String, rest, more))) == Main.record.args.go(more, c2, Main.rword(more)) : Result<&2, &2, Main.Refused, Main.RecordCmd>}:
  %kk_rw(rest, more) : {Main.record.args.go(List.append(&2, String, rest, more), c1, _) == Main.record.args.go(more, c2, Main.rword(more)) : Result<&2, &2, Main.Refused, Main.RecordCmd>}
  ih

def rno(-args: List<&2, String>, -more: List<&2, String>, -c: Main.RecordCmd, -k: Main.RWord, -c2: Main.RecordCmd, -x: Main.Refused, h: {Fail{x} == Done{c2} : Result<&2, &2, Main.Refused, Main.RecordCmd>}) -> {Main.record.args.go(List.append(&2, String, args, more), c, kk(args, more, k)) == Main.record.args.go(more, c2, Main.rword(more)) : Result<&2, &2, Main.Refused, Main.RecordCmd>}:
  Empty.absurd({Main.record.args.go(List.append(&2, String, args, more), c, kk(args, more, k)) == Main.record.args.go(more, c2, Main.rword(more)) : Result<&2, &2, Main.Refused, Main.RecordCmd>}, B.fail_done(Main.RecordCmd, x, c2, h))

def rsplit(-rest: List<&2, String>, -more: List<&2, String>, -u: T.Split -> Main.RecordCmd, -c2: Main.RecordCmd, r: Result<&2, &2, Main.Refused, T.Split>, e: {Result.bind(&2, &2, Main.Refused, T.Split, Main.RecordCmd, r, s => Main.record.args.go(rest, u(s), Main.rword(rest))) == Done{c2} : Result<&2, &2, Main.Refused, Main.RecordCmd>}, ih: @s: T.Split -> {Main.record.args.go(rest, u(s), Main.rword(rest)) == Done{c2} : Result<&2, &2, Main.Refused, Main.RecordCmd>} -> {Main.record.args.go(List.append(&2, String, rest, more), u(s), Main.rword(List.append(&2, String, rest, more))) == Main.record.args.go(more, c2, Main.rword(more)) : Result<&2, &2, Main.Refused, Main.RecordCmd>}) -> {Result.bind(&2, &2, Main.Refused, T.Split, Main.RecordCmd, r, s => Main.record.args.go(List.append(&2, String, rest, more), u(s), Main.rword(List.append(&2, String, rest, more)))) == Main.record.args.go(more, c2, Main.rword(more)) : Result<&2, &2, Main.Refused, Main.RecordCmd>}:
  match r:
    case Fail{x}:
      Empty.absurd({Fail{x} == Main.record.args.go(more, c2, Main.rword(more)) : Result<&2, &2, Main.Refused, Main.RecordCmd>}, B.fail_done(Main.RecordCmd, x, c2, e))
    case Done{s}:
      ih(s, e)

def rpath(-rest: List<&2, String>, -more: List<&2, String>, -c2: Main.RecordCmd, r: Result<&2, &2, Main.Refused, Main.RecordCmd>, e: {Result.bind(&2, &2, Main.Refused, Main.RecordCmd, Main.RecordCmd, r, m => Main.record.args.go(rest, m, Main.rword(rest))) == Done{c2} : Result<&2, &2, Main.Refused, Main.RecordCmd>}, ih: @m: Main.RecordCmd -> {Main.record.args.go(rest, m, Main.rword(rest)) == Done{c2} : Result<&2, &2, Main.Refused, Main.RecordCmd>} -> {Main.record.args.go(List.append(&2, String, rest, more), m, Main.rword(List.append(&2, String, rest, more))) == Main.record.args.go(more, c2, Main.rword(more)) : Result<&2, &2, Main.Refused, Main.RecordCmd>}) -> {Result.bind(&2, &2, Main.Refused, Main.RecordCmd, Main.RecordCmd, r, m => Main.record.args.go(List.append(&2, String, rest, more), m, Main.rword(List.append(&2, String, rest, more)))) == Main.record.args.go(more, c2, Main.rword(more)) : Result<&2, &2, Main.Refused, Main.RecordCmd>}:
  match r:
    case Fail{x}:
      Empty.absurd({Fail{x} == Main.record.args.go(more, c2, Main.rword(more)) : Result<&2, &2, Main.Refused, Main.RecordCmd>}, B.fail_done(Main.RecordCmd, x, c2, e))
    case Done{m}:
      ih(m, e)

# A flag that takes no value, or a path, read before words not yet known.
def dry_cons(w: String, more: List<&2, String>, -c: Main.RecordCmd) -> {Main.record.args.go(w <> more, c, Main.RWord.Dry{}) == Main.record.args.go(more, Main.rc.dry(c), Main.rword(more)) : Result<&2, &2, Main.Refused, Main.RecordCmd>}:
  match more:
    case Nil{}:
      {==}
    case x <> y:
      {==}

def fields_cons(w: String, more: List<&2, String>, -c: Main.RecordCmd) -> {Main.record.args.go(w <> more, c, Main.RWord.Fields{}) == Main.record.args.go(more, Main.rc.fields(c), Main.rword(more)) : Result<&2, &2, Main.Refused, Main.RecordCmd>}:
  match more:
    case Nil{}:
      {==}
    case x <> y:
      {==}

def path_cons(w: String, more: List<&2, String>, -c: Main.RecordCmd) -> {Main.record.args.go(w <> more, c, Main.RWord.Path{}) == Result.bind(&2, &2, Main.Refused, Main.RecordCmd, Main.RecordCmd, Main.record.path(c, Main.trimmed(w)), m => Main.record.args.go(more, m, Main.rword(more))) : Result<&2, &2, Main.Refused, Main.RecordCmd>}:
  match more:
    case Nil{}:
      {==}
    case x <> y:
      {==}

# `record` reads its words one at a time: what words it has read say
# something, and the words after them are read from what they said.
def go_app(args: List<&2, String>, +more: List<&2, String>, +c: Main.RecordCmd, k: Main.RWord, -c2: Main.RecordCmd, e: {Main.record.args.go(args, c, k) == Done{c2} : Result<&2, &2, Main.Refused, Main.RecordCmd>}) -> {Main.record.args.go(List.append(&2, String, args, more), c, kk(args, more, k)) == Main.record.args.go(more, c2, Main.rword(more)) : Result<&2, &2, Main.Refused, Main.RecordCmd>}:
  match args k:
    case Nil{} _:
      %done_rc(c, c2, e) : {Main.record.args.go(more, c, Main.rword(more)) == Main.record.args.go(more, _, Main.rword(more)) : Result<&2, &2, Main.Refused, Main.RecordCmd>}
      {==}
    case w <> Nil{} Main.RWord.Message{}:
      rno([w], more, c, Main.RWord.Message{}, c2, Main.Refused{2, "`-m` wants a value"}, e)
    case w <> +v <> +rest Main.RWord.Message{}:
      rstep(rest, more, Main.rc.message(c, v), c2, go_app(rest, more, Main.rc.message(c, v), Main.rword(rest), c2, e))
    case w <> Nil{} Main.RWord.Onto{}:
      rno([w], more, c, Main.RWord.Onto{}, c2, Main.Refused{2, "`--onto` wants a value"}, e)
    case w <> +v <> +rest Main.RWord.Onto{}:
      rstep(rest, more, Main.rc.onto(c, v), c2, go_app(rest, more, Main.rc.onto(c, v), Main.rword(rest), c2, e))
    case w <> Nil{} Main.RWord.Merge{}:
      rno([w], more, c, Main.RWord.Merge{}, c2, Main.Refused{2, "`--merge` wants a value"}, e)
    case w <> +v <> +rest Main.RWord.Merge{}:
      rstep(rest, more, Main.rc.merge(c, v), c2, go_app(rest, more, Main.rc.merge(c, v), Main.rword(rest), c2, e))
    case w <> Nil{} Main.RWord.Accept{}:
      rno([w], more, c, Main.RWord.Accept{}, c2, Main.Refused{2, "`--accept` wants a value"}, e)
    case w <> +v <> +rest Main.RWord.Accept{}:
      rstep(rest, more, Main.rc.accept(c, v), c2, go_app(rest, more, Main.rc.accept(c, v), Main.rword(rest), c2, e))
    case w <> Nil{} Main.RWord.At{}:
      rno([w], more, c, Main.RWord.At{}, c2, Main.Refused{2, "`--at` wants a value"}, e)
    case w <> +v <> +rest Main.RWord.At{}:
      rsplit(rest, more, s => Main.rc.at(c, s), c2, Main.record.split(v, "`--at` is spelled `--at <file>=<path>`"), e, +s => h => rstep(rest, more, Main.rc.at(c, s), c2, go_app(rest, more, Main.rc.at(c, s), Main.rword(rest), c2, h)))
    case w <> Nil{} Main.RWord.Move{}:
      rno([w], more, c, Main.RWord.Move{}, c2, Main.Refused{2, "`--move` wants a value"}, e)
    case w <> +v <> +rest Main.RWord.Move{}:
      rsplit(rest, more, s => Main.rc.move(c, s), c2, Main.record.split(v, "`--move` is spelled `--move <old>=<new>`"), e, +s => h => rstep(rest, more, Main.rc.move(c, s), c2, go_app(rest, more, Main.rc.move(c, s), Main.rword(rest), c2, h)))
    case w <> Nil{} Main.RWord.Bytes{}:
      rno([w], more, c, Main.RWord.Bytes{}, c2, Main.Refused{2, "`--bytes` wants a value"}, e)
    case w <> +v <> +rest Main.RWord.Bytes{}:
      rstep(rest, more, Main.rc.kind(c, T.Split{v, "bytes"}), c2, go_app(rest, more, Main.rc.kind(c, T.Split{v, "bytes"}), Main.rword(rest), c2, e))
    case w <> Nil{} Main.RWord.Lines{}:
      rno([w], more, c, Main.RWord.Lines{}, c2, Main.Refused{2, "`--lines` wants a value"}, e)
    case w <> +v <> +rest Main.RWord.Lines{}:
      rstep(rest, more, Main.rc.kind(c, T.Split{v, "lines"}), c2, go_app(rest, more, Main.rc.kind(c, T.Split{v, "lines"}), Main.rword(rest), c2, e))
    case +w <> Nil{} Main.RWord.Dry{}:
      Equal.trans(Result<&2, &2, Main.Refused, Main.RecordCmd>, Main.record.args.go(w <> more, c, Main.RWord.Dry{}), Main.record.args.go(more, Main.rc.dry(c), Main.rword(more)), Main.record.args.go(more, c2, Main.rword(more)), dry_cons(w, more, c), Equal.cong(Main.RecordCmd, Result<&2, &2, Main.Refused, Main.RecordCmd>, x => Main.record.args.go(more, x, Main.rword(more)), Main.rc.dry(c), c2, done_rc(Main.rc.dry(c), c2, e)))
    case w <> +v <> +rest Main.RWord.Dry{}:
      rstep(v <> rest, more, Main.rc.dry(c), c2, go_app(v <> rest, more, Main.rc.dry(c), Main.rword(v <> rest), c2, e))
    case +w <> Nil{} Main.RWord.Fields{}:
      Equal.trans(Result<&2, &2, Main.Refused, Main.RecordCmd>, Main.record.args.go(w <> more, c, Main.RWord.Fields{}), Main.record.args.go(more, Main.rc.fields(c), Main.rword(more)), Main.record.args.go(more, c2, Main.rword(more)), fields_cons(w, more, c), Equal.cong(Main.RecordCmd, Result<&2, &2, Main.Refused, Main.RecordCmd>, x => Main.record.args.go(more, x, Main.rword(more)), Main.rc.fields(c), c2, done_rc(Main.rc.fields(c), c2, e)))
    case w <> +v <> +rest Main.RWord.Fields{}:
      rstep(v <> rest, more, Main.rc.fields(c), c2, go_app(v <> rest, more, Main.rc.fields(c), Main.rword(v <> rest), c2, e))
    case w <> Nil{} Main.RWord.Flag{}:
      rno([w], more, c, Main.RWord.Flag{}, c2, Main.Refused{2, "`" ++ w ++ "` is not an argument `record` takes"}, e)
    case w <> v <> rest Main.RWord.Flag{}:
      rno(w <> v <> rest, more, c, Main.RWord.Flag{}, c2, Main.Refused{2, "`" ++ w ++ "` is not an argument `record` takes"}, e)
    case +w <> Nil{} Main.RWord.Path{}:
      Equal.trans(Result<&2, &2, Main.Refused, Main.RecordCmd>, Main.record.args.go(w <> more, c, Main.RWord.Path{}), Result.bind(&2, &2, Main.Refused, Main.RecordCmd, Main.RecordCmd, Main.record.path(c, Main.trimmed(w)), m => Main.record.args.go(more, m, Main.rword(more))), Main.record.args.go(more, c2, Main.rword(more)), path_cons(w, more, c), rpath(Nil{}, more, c2, Main.record.path(c, Main.trimmed(w)), e, +m => h => rstep(Nil{}, more, m, c2, go_app(Nil{}, more, m, Main.rword(Nil{}), c2, h))))
    case +w <> +v <> +rest Main.RWord.Path{}:
      rpath(v <> rest, more, c2, Main.record.path(c, Main.trimmed(w)), e, +m => h => rstep(v <> rest, more, m, c2, go_app(v <> rest, more, m, Main.rword(v <> rest), c2, h)))

# So what follows words `record` reads is read from what they said.
def app_r(+args: List<&2, String>, +more: List<&2, String>, -c2: Main.RecordCmd, e: {Main.record.args.r(args) == Done{c2} : Result<&2, &2, Main.Refused, Main.RecordCmd>}) -> {Main.record.args.r(List.append(&2, String, args, more)) == Main.record.args.go(more, c2, Main.rword(more)) : Result<&2, &2, Main.Refused, Main.RecordCmd>}:
  rstep(args, more, Main.RecordCmd{None{}, Nil{}, Nil{}, Nil{}, Nil{}, Nil{}, Nil{}, False{}, False{}, None{}}, c2, go_app(args, more, Main.RecordCmd{None{}, Nil{}, Nil{}, Nil{}, Nil{}, Nil{}, Nil{}, False{}, False{}, None{}}, Main.rword(args), c2, e))

# The words read with each of `wss` after them, and what each of those
# says on its own after what the words said.
def after(+args: List<&2, String>, wss: List<&2, List<&2, String>>) -> List<&2, Result<&2, &2, Main.Refused, Main.RecordCmd>>:
  match wss:
    case Nil{}:
      Nil{}
    case +ws <> rest:
      Main.record.args.r(List.append(&2, String, args, ws)) <> after(args, rest)

def each(wss: List<&2, List<&2, String>>, +c: Main.RecordCmd) -> List<&2, Result<&2, &2, Main.Refused, Main.RecordCmd>>:
  match wss:
    case Nil{}:
      Nil{}
    case +ws <> rest:
      Main.record.args.go(ws, c, Main.rword(ws)) <> each(rest, c)

def each_app(+args: List<&2, String>, -c: Main.RecordCmd, +e: {Main.record.args.r(args) == Done{c} : Result<&2, &2, Main.Refused, Main.RecordCmd>}, wss: List<&2, List<&2, String>>) -> {after(args, wss) == each(wss, c) : List<&2, Result<&2, &2, Main.Refused, Main.RecordCmd>>}:
  match wss:
    case Nil{}:
      {==}
    case +ws <> +rest:
      %Equal.sym(Result<&2, &2, Main.Refused, Main.RecordCmd>, Main.record.args.r(List.append(&2, String, args, ws)), Main.record.args.go(ws, c, Main.rword(ws)), app_r(args, ws, c, e)) : {_ <> after(args, rest) == each(ws <> rest, c) : List<&2, Result<&2, &2, Main.Refused, Main.RecordCmd>>}
      %Equal.sym(List<&2, Result<&2, &2, Main.Refused, Main.RecordCmd>>, after(args, rest), each(rest, c), each_app(args, c, e, rest)) : {Main.record.args.go(ws, c, Main.rword(ws)) <> _ == each(ws <> rest, c) : List<&2, Result<&2, &2, Main.Refused, Main.RecordCmd>>}
      {==}

# Each flag after words `record` has read says one thing more.
def words_read(+args: List<&2, String>, +o: Maybe<&2, String>, +ms: List<&2, String>, +ac: List<&2, String>, +at: List<&2, T.Split>, +mv: List<&2, T.Split>, +ks: List<&2, T.Split>, +ns: List<&2, String>, +d: Bool, +f: Bool, +mg: Maybe<&2, String>, +e: {Main.record.args.r(args) == Done{Main.RecordCmd{o, ms, ac, at, mv, ks, ns, d, f, mg}} : Result<&2, &2, Main.Refused, Main.RecordCmd>}, +v: String) -> {[Main.record.args.r(List.append(&2, String, args, ["-m", v])), Main.record.args.r(List.append(&2, String, args, ["--message", v])), Main.record.args.r(List.append(&2, String, args, ["--onto", v])), Main.record.args.r(List.append(&2, String, args, ["--merge", v])), Main.record.args.r(List.append(&2, String, args, ["--accept", v])), Main.record.args.r(List.append(&2, String, args, ["--bytes", v])), Main.record.args.r(List.append(&2, String, args, ["--lines", v])), Main.record.args.r(List.append(&2, String, args, ["-n"])), Main.record.args.r(List.append(&2, String, args, ["--dry-run"])), Main.record.args.r(List.append(&2, String, args, ["--fields"])), Main.record.args.r(List.append(&2, String, args, ["-m"])), Main.record.args.r(List.append(&2, String, args, ["--onto"])), Main.record.args.r(List.append(&2, String, args, ["--merge"])), Main.record.args.r(List.append(&2, String, args, ["--accept"])), Main.record.args.r(List.append(&2, String, args, ["--at"])), Main.record.args.r(List.append(&2, String, args, ["--move"])), Main.record.args.r(List.append(&2, String, args, ["--bytes"])), Main.record.args.r(List.append(&2, String, args, ["--lines"]))] == [Done{Main.RecordCmd{o, ms, ac, at, mv, ks, ns, d, f, Some{v}}}, Done{Main.RecordCmd{o, ms, ac, at, mv, ks, ns, d, f, Some{v}}}, Done{Main.RecordCmd{Some{v}, ms, ac, at, mv, ks, ns, d, f, mg}}, Done{Main.RecordCmd{o, List.append(&2, String, ms, [v]), ac, at, mv, ks, ns, d, f, mg}}, Done{Main.RecordCmd{o, ms, v <> ac, at, mv, ks, ns, d, f, mg}}, Done{Main.RecordCmd{o, ms, ac, at, mv, List.append(&2, T.Split, ks, [T.Split{v, "bytes"}]), ns, d, f, mg}}, Done{Main.RecordCmd{o, ms, ac, at, mv, List.append(&2, T.Split, ks, [T.Split{v, "lines"}]), ns, d, f, mg}}, Done{Main.RecordCmd{o, ms, ac, at, mv, ks, ns, True{}, f, mg}}, Done{Main.RecordCmd{o, ms, ac, at, mv, ks, ns, True{}, f, mg}}, Done{Main.RecordCmd{o, ms, ac, at, mv, ks, ns, d, True{}, mg}}, Fail{Main.Refused{2, "`-m` wants a value"}}, Fail{Main.Refused{2, "`--onto` wants a value"}}, Fail{Main.Refused{2, "`--merge` wants a value"}}, Fail{Main.Refused{2, "`--accept` wants a value"}}, Fail{Main.Refused{2, "`--at` wants a value"}}, Fail{Main.Refused{2, "`--move` wants a value"}}, Fail{Main.Refused{2, "`--bytes` wants a value"}}, Fail{Main.Refused{2, "`--lines` wants a value"}}] : List<&2, Result<&2, &2, Main.Refused, Main.RecordCmd>>}:
  each_app(args, Main.RecordCmd{o, ms, ac, at, mv, ks, ns, d, f, mg}, e, [["-m", v], ["--message", v], ["--onto", v], ["--merge", v], ["--accept", v], ["--bytes", v], ["--lines", v], ["-n"], ["--dry-run"], ["--fields"], ["-m"], ["--onto"], ["--merge"], ["--accept"], ["--at"], ["--move"], ["--bytes"], ["--lines"]])

# A value cut at its first `=`
# --------------------------

def split_eq(a: String, -b: String, +h: {T.all_chars(~(c => Bool.not(Char.is_eq(c, '='))), a) == True{} : Bool}) -> {String.split(a ++ SCon{'=', b}, '=') == a <> String.split(b, '=') : List<&2, String>}:
  match a:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      Equal.trans(List<&2, String>, String.split.fin(c, String.split(t ++ SCon{'=', b}, '='), Char.is_eq(c, '=')), String.split.fin(c, String.split(t ++ SCon{'=', b}, '='), False{}), SCon{c, t} <> String.split(b, '='),
        Equal.cong(Bool, List<&2, String>, x => String.split.fin(c, String.split(t ++ SCon{'=', b}, '='), x), Char.is_eq(c, '='), False{}, AL.not_of_true(Char.is_eq(c, '='), Comp.and_left(Bool.not(Char.is_eq(c, '=')), T.all_chars(~(c => Bool.not(Char.is_eq(c, '='))), t), h))),
        Equal.cong(List<&2, String>, List<&2, String>, l => String.split.push(c, l), String.split(t ++ SCon{'=', b}, '='), t <> String.split(b, '='), split_eq(t, b, Comp.and_right(Bool.not(Char.is_eq(c, '=')), T.all_chars(~(c => Bool.not(Char.is_eq(c, '='))), t), h))))

def split_one(a: String, +h: {T.all_chars(~(c => Bool.not(Char.is_eq(c, '='))), a) == True{} : Bool}) -> {String.split(a, '=') == [a] : List<&2, String>}:
  match a:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      Equal.trans(List<&2, String>, String.split.fin(c, String.split(t, '='), Char.is_eq(c, '=')), String.split.fin(c, String.split(t, '='), False{}), [SCon{c, t}],
        Equal.cong(Bool, List<&2, String>, x => String.split.fin(c, String.split(t, '='), x), Char.is_eq(c, '='), False{}, AL.not_of_true(Char.is_eq(c, '='), Comp.and_left(Bool.not(Char.is_eq(c, '=')), T.all_chars(~(c => Bool.not(Char.is_eq(c, '='))), t), h))),
        Equal.cong(List<&2, String>, List<&2, String>, l => String.split.push(c, l), String.split(t, '='), [t], split_one(t, Comp.and_right(Bool.not(Char.is_eq(c, '=')), T.all_chars(~(c => Bool.not(Char.is_eq(c, '='))), t), h))))

def filled(xs: List<&2, String>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case h <> t:
      True{}

def split_filled.fin(c: Char, cut: Bool, r: List<&2, String>, -ne: {filled(r) == True{} : Bool}) -> {filled(String.split.fin(c, r, cut)) == True{} : Bool}:
  match cut:
    case True{}:
      {==}
    case False{}:
      match r:
        case Nil{}:
          {==}
        case h <> t:
          {==}

def split_filled(s: String) -> {filled(String.split(s, '=')) == True{} : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      split_filled.fin(h, Char.is_eq(h, '='), String.split(t, '='), split_filled(t))

def join_cut(r: List<&2, String>, ne: {filled(r) == True{} : Bool}) -> {String.join(SNil{} <> r, "=") == SCon{'=', String.join(r, "=")} : String}:
  match r:
    case Nil{}:
      Empty.absurd({String.join([SNil{}], "=") == SCon{'=', String.join(Nil{}, "=")} : String}, Comp.false_true(ne))
    case q <> more:
      {==}

def join_push(c: Char, r: List<&2, String>, ne: {filled(r) == True{} : Bool}) -> {String.join(String.split.push(c, r), "=") == SCon{c, String.join(r, "=")} : String}:
  match r:
    case Nil{}:
      Empty.absurd({String.join(String.split.push(c, Nil{}), "=") == SCon{c, String.join(Nil{}, "=")} : String}, Comp.false_true(ne))
    case p <> Nil{}:
      {==}
    case p <> q <> more:
      {==}

def join_split.fin(h: Char, +t: String, cut: Bool, eq: {Char.is_eq(h, '=') == cut : Bool}, ih: {String.join(String.split(t, '='), "=") == t : String}) -> {String.join(String.split.fin(h, String.split(t, '='), cut), "=") == SCon{h, t} : String}:
  match cut:
    case True{}:
      %Equal.sym(String, String.join(SNil{} <> String.split(t, '='), "="), SCon{'=', String.join(String.split(t, '='), "=")}, join_cut(String.split(t, '='), split_filled(t))) : {_ == SCon{h, t} : String}
      %Equal.sym(String, String.join(String.split(t, '='), "="), t, ih) : {SCon{'=', _} == SCon{h, t} : String}
      %Eq.char_eq(h, '=', eq) : {SCon{_, t} == SCon{h, t} : String}
      {==}
    case False{}:
      %Equal.sym(String, String.join(String.split.push(h, String.split(t, '=')), "="), SCon{h, String.join(String.split(t, '='), "=")}, join_push(h, String.split(t, '='), split_filled(t))) : {_ == SCon{h, t} : String}
      %Equal.sym(String, String.join(String.split(t, '='), "="), t, ih) : {SCon{h, _} == SCon{h, t} : String}
      {==}

# What a value splits into at each `=`, joined back at each, is the value.
def join_split(s: String) -> {String.join(String.split(s, '='), "=") == s : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      join_split.fin(h, t, Char.is_eq(h, '='), {==}, join_split(t))

def cut_cons(+a: String, +msg: String, xs: List<&2, String>, ne: {filled(xs) == True{} : Bool}) -> {Main.record.split.of(msg, a <> xs) == Done{T.Split{a, String.join(xs, "=")}} : Result<&2, &2, Main.Refused, T.Split>}:
  match xs:
    case Nil{}:
      Empty.absurd({Main.record.split.of(msg, [a]) == Done{T.Split{a, String.join(Nil{}, "=")}} : Result<&2, &2, Main.Refused, T.Split>}, Comp.false_true(ne))
    case q <> more:
      {==}

# A value with an `=` is cut at the first, whatever follows it.
def split_at(+a: String, +b: String, +msg: String, +ha: {T.all_chars(~(c => Bool.not(Char.is_eq(c, '='))), a) == True{} : Bool}) -> {Main.record.split(a ++ ("=" ++ b), msg) == Done{T.Split{a, b}} : Result<&2, &2, Main.Refused, T.Split>}:
  Equal.trans(Result<&2, &2, Main.Refused, T.Split>, Main.record.split.of(msg, String.split(a ++ SCon{'=', b}, '=')), Main.record.split.of(msg, a <> String.split(b, '=')), Done{T.Split{a, b}},
    Equal.cong(List<&2, String>, Result<&2, &2, Main.Refused, T.Split>, xs => Main.record.split.of(msg, xs), String.split(a ++ SCon{'=', b}, '='), a <> String.split(b, '='), split_eq(a, b, ha)),
    Equal.trans(Result<&2, &2, Main.Refused, T.Split>, Main.record.split.of(msg, a <> String.split(b, '=')), Done{T.Split{a, String.join(String.split(b, '='), "=")}}, Done{T.Split{a, b}},
      cut_cons(a, msg, String.split(b, '='), split_filled(b)),
      Equal.cong(String, Result<&2, &2, Main.Refused, T.Split>, x => Done{T.Split{a, x}}, String.join(String.split(b, '='), "="), b, join_split(b))))

# And one with none is refused.
def split_none(+a: String, +msg: String, +ha: {T.all_chars(~(c => Bool.not(Char.is_eq(c, '='))), a) == True{} : Bool}) -> {Main.record.split(a, msg) == Fail{Main.Refused{2, msg}} : Result<&2, &2, Main.Refused, T.Split>}:
  Equal.cong(List<&2, String>, Result<&2, &2, Main.Refused, T.Split>, xs => Main.record.split.of(msg, xs), String.split(a, '='), [a], split_one(a, ha))

# A word that is no flag
# ----------------------

def neq_dash.of(+p: String, +q: String, b: Bool, eb: {String.eq(p, q) == b : Bool}, hp: {String.starts_with(p, "-") == False{} : Bool}, hq: {String.starts_with(q, "-") == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      +pq = S.eq_true(p, q, eb)
      +hq2 = Equal.trans(Bool, String.starts_with(q, "-"), String.starts_with(p, "-"), False{}, Equal.cong(String, Bool, s => String.starts_with(s, "-"), q, p, Equal.sym(String, p, q, pq)), hp)
      Empty.absurd({True{} == False{} : Bool}, Comp.false_true(Equal.trans(Bool, False{}, String.starts_with(q, "-"), True{}, Equal.sym(Bool, String.starts_with(q, "-"), False{}, hq2), hq)))

# A word that does not begin with `-` is none of the flags, which all do.
def neq_dash(+p: String, +q: String, hp: {String.starts_with(p, "-") == False{} : Bool}, hq: {String.starts_with(q, "-") == True{} : Bool}) -> {String.eq(p, q) == False{} : Bool}:
  neq_dash.of(p, q, String.eq(p, q), {==}, hp, hq)

def dashed(qs: List<&2, String>) -> Bool:
  match qs:
    case Nil{}:
      True{}
    case +q <> rest:
      Bool.and(String.starts_with(q, "-"), dashed(rest))

def eqs(+p: String, qs: List<&2, String>, last: Bool) -> List<&2, Bool>:
  match qs:
    case Nil{}:
      [last]
    case +q <> rest:
      String.eq(p, q) <> eqs(p, rest, last)

def falses(qs: List<&2, String>) -> List<&2, Bool>:
  match qs:
    case Nil{}:
      [False{}]
    case q <> rest:
      False{} <> falses(rest)

def eqs_false(+p: String, qs: List<&2, String>, +hp: {String.starts_with(p, "-") == False{} : Bool}, +hq: {dashed(qs) == True{} : Bool}) -> {eqs(p, qs, String.starts_with(p, "-")) == falses(qs) : List<&2, Bool>}:
  match qs:
    case Nil{}:
      %Equal.sym(Bool, String.starts_with(p, "-"), False{}, hp) : {[_] == [False{}] : List<&2, Bool>}
      {==}
    case +q <> +rest:
      %Equal.sym(Bool, String.eq(p, q), False{}, neq_dash(p, q, hp, Comp.and_left(String.starts_with(q, "-"), dashed(rest), hq))) : {_ <> eqs(p, rest, String.starts_with(p, "-")) == falses(q <> rest) : List<&2, Bool>}
      %Equal.sym(List<&2, Bool>, eqs(p, rest, String.starts_with(p, "-")), falses(rest), eqs_false(p, rest, hp, Comp.and_right(String.starts_with(q, "-"), dashed(rest), hq))) : {False{} <> _ == falses(q <> rest) : List<&2, Bool>}
      {==}

# `rword.of`, over what each of its tests answers.
def rword_list(bs: List<&2, Bool>) -> Main.RWord:
  match bs:
    case m1 <> m2 <> o <> mg <> ac <> at <> mv <> by <> li <> n1 <> n2 <> fi <> fl <> Nil{}:
      Bool.pick(Main.RWord, Bool.or(m1, m2), Main.RWord.Message{},
      Bool.pick(Main.RWord, o, Main.RWord.Onto{},
      Bool.pick(Main.RWord, mg, Main.RWord.Merge{},
      Bool.pick(Main.RWord, ac, Main.RWord.Accept{},
      Bool.pick(Main.RWord, at, Main.RWord.At{},
      Bool.pick(Main.RWord, mv, Main.RWord.Move{},
      Bool.pick(Main.RWord, by, Main.RWord.Bytes{},
      Bool.pick(Main.RWord, li, Main.RWord.Lines{},
      Bool.pick(Main.RWord, Bool.or(n1, n2), Main.RWord.Dry{},
      Bool.pick(Main.RWord, fi, Main.RWord.Fields{},
      Bool.pick(Main.RWord, fl, Main.RWord.Flag{}, Main.RWord.Path{})))))))))))
    case _:
      Main.RWord.Path{}

def RFLAGS() -> List<&2, String>:
  ["-m", "--message", "--onto", "--merge", "--accept", "--at", "--move", "--bytes", "--lines", "-n", "--dry-run", "--fields"]

# So `record` reads such a word as a path.
def rword_path(+p: String, +hp: {String.starts_with(p, "-") == False{} : Bool}) -> {Main.rword.of(p) == Main.RWord.Path{} : Main.RWord}:
  Equal.cong(List<&2, Bool>, Main.RWord, bs => rword_list(bs), eqs(p, RFLAGS(), String.starts_with(p, "-")), falses(RFLAGS()), eqs_false(p, RFLAGS(), hp, {==}))

def swif(x: Bool, t: String) -> {String.starts_with.if(t ++ "/", SNil{}, x) == String.starts_with.if(t, SNil{}, x) : Bool}:
  match x:
    case False{}:
      {==}
    case True{}:
      match t:
        case SNil{}:
          {==}
        case SCon{h, r}:
          {==}

# A `/` after a path that does not begin with `-` leaves it one that does not.
def sw_slash(+p: String, hp: {String.starts_with(p, "-") == False{} : Bool}, hn: {String.is_empty(p) == False{} : Bool}) -> {String.starts_with(p ++ "/", "-") == False{} : Bool}:
  match p:
    case SNil{}:
      Empty.absurd({String.starts_with("/", "-") == False{} : Bool}, S.true_false(hn))
    case SCon{+c, +t}:
      Equal.trans(Bool, String.starts_with.if(t ++ "/", SNil{}, Char.is_eq(c, '-')), String.starts_with.if(t, SNil{}, Char.is_eq(c, '-')), False{}, swif(Char.is_eq(c, '-'), t), hp)

# The slashes a shell leaves are taken off, and a path with none is kept.
def trim_slash(+p: String) -> {Main.trimmed(p ++ "/") == Main.trimmed(p) : String}:
  Equal.cong(String, String, x => String.reverse(Main.drop_slashes(x, Main.heads_slash(x))), String.reverse(p ++ "/"), SCon{'/', String.reverse(p)}, B.rev_go_app(p, "/", SNil{}))

def keep_rev.of(+c: Char, +t: String, b: Bool, h: {String.starts_with.if(t, SNil{}, b) == False{} : Bool}) -> {Main.drop_slashes(SCon{c, t}, b) == SCon{c, t} : String}:
  match b:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({Main.drop_slashes(SCon{c, t}, True{}) == SCon{c, t} : String}, S.true_false(Equal.trans(Bool, True{}, String.starts_with(t, SNil{}), False{}, Equal.sym(Bool, String.starts_with(t, SNil{}), True{}, B.sw_nil(t)), h)))

def keep_rev(r: String, h: {String.starts_with(r, "/") == False{} : Bool}) -> {Main.drop_slashes(r, Main.heads_slash(r)) == r : String}:
  match r:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      keep_rev.of(c, t, Char.is_eq(c, '/'), h)

def trim_keep(+p: String, hs: {String.ends_with(p, "/") == False{} : Bool}) -> {Main.trimmed(p) == p : String}:
  Equal.trans(String, Main.trimmed(p), String.reverse(String.reverse(p)), p,
    Equal.cong(String, String, x => String.reverse(x), Main.drop_slashes(String.reverse(p), Main.heads_slash(String.reverse(p))), String.reverse(p), keep_rev(String.reverse(p), hs)),
    NamingL.rev_rev(p))

# A word read as a path, trimmed to one that is not empty, is kept.
def path_named(+c: Main.RecordCmd, +q: String, +p: String, ht: {Main.trimmed(q) == p : String}, hn: {String.is_empty(p) == False{} : Bool}) -> {Main.record.args.go([q], c, Main.RWord.Path{}) == Done{Main.rc.named(c, p)} : Result<&2, &2, Main.Refused, Main.RecordCmd>}:
  Equal.trans(Result<&2, &2, Main.Refused, Main.RecordCmd>, Result.bind(&2, &2, Main.Refused, Main.RecordCmd, Main.RecordCmd, Main.record.path(c, Main.trimmed(q)), m => Main.record.args.go(Nil{}, m, Main.rword(Nil{}))), Result.bind(&2, &2, Main.Refused, Main.RecordCmd, Main.RecordCmd, Main.record.path(c, p), m => Main.record.args.go(Nil{}, m, Main.rword(Nil{}))), Done{Main.rc.named(c, p)},
    Equal.cong(String, Result<&2, &2, Main.Refused, Main.RecordCmd>, x => Result.bind(&2, &2, Main.Refused, Main.RecordCmd, Main.RecordCmd, Main.record.path(c, x), m => Main.record.args.go(Nil{}, m, Main.rword(Nil{}))), Main.trimmed(q), p, ht),
    Equal.cong(Bool, Result<&2, &2, Main.Refused, Main.RecordCmd>, x => Result.bind(&2, &2, Main.Refused, Main.RecordCmd, Main.RecordCmd, Bool.pick(Result<&2, &2, Main.Refused, Main.RecordCmd>, x, Fail{Main.Refused{2, "`record` takes the paths to record, and an empty one names nothing"}}, Done{Main.rc.named(c, p)}), m => Main.record.args.go(Nil{}, m, Main.rword(Nil{}))), String.is_empty(p), False{}, hn))

def l6(-A: Data, -a1: A, -a2: A, -a3: A, -a4: A, -a5: A, -a6: A, -b1: A, -b2: A, -b3: A, -b4: A, -b5: A, -b6: A, h1: {a1 == b1 : A}, h2: {a2 == b2 : A}, h3: {a3 == b3 : A}, h4: {a4 == b4 : A}, h5: {a5 == b5 : A}, h6: {a6 == b6 : A}) -> {[a1, a2, a3, a4, a5, a6] == [b1, b2, b3, b4, b5, b6] : List<&2, A>}:
  %h1 : {[a1, a2, a3, a4, a5, a6] == [_, b2, b3, b4, b5, b6] : List<&2, A>}
  %h2 : {[a1, a2, a3, a4, a5, a6] == [a1, _, b3, b4, b5, b6] : List<&2, A>}
  %h3 : {[a1, a2, a3, a4, a5, a6] == [a1, a2, _, b4, b5, b6] : List<&2, A>}
  %h4 : {[a1, a2, a3, a4, a5, a6] == [a1, a2, a3, _, b5, b6] : List<&2, A>}
  %h5 : {[a1, a2, a3, a4, a5, a6] == [a1, a2, a3, a4, _, b6] : List<&2, A>}
  %h6 : {[a1, a2, a3, a4, a5, a6] == [a1, a2, a3, a4, a5, _] : List<&2, A>}
  {==}

# `--at` and `--move` are cut at their first `=`, and a word that is no
# flag is a path, with a `/` after it or not.
def renames_read(+args: List<&2, String>, +o: Maybe<&2, String>, +ms: List<&2, String>, +ac: List<&2, String>, +at: List<&2, T.Split>, +mv: List<&2, T.Split>, +ks: List<&2, T.Split>, +ns: List<&2, String>, +d: Bool, +f: Bool, +mg: Maybe<&2, String>, +e: {Main.record.args.r(args) == Done{Main.RecordCmd{o, ms, ac, at, mv, ks, ns, d, f, mg}} : Result<&2, &2, Main.Refused, Main.RecordCmd>}, +a: String, +b: String, +ha: {T.all_chars(~(c => Bool.not(Char.is_eq(c, '='))), a) == True{} : Bool}, +p: String, +hp: {String.starts_with(p, "-") == False{} : Bool}, +hn: {String.is_empty(p) == False{} : Bool}, +hs: {String.ends_with(p, "/") == False{} : Bool}) -> {after(args, [["--at", a ++ ("=" ++ b)], ["--move", a ++ ("=" ++ b)], ["--at", a], ["--move", a], [p], [p ++ "/"]]) == [Done{Main.RecordCmd{o, ms, ac, List.append(&2, T.Split, at, [T.Split{a, b}]), mv, ks, ns, d, f, mg}}, Done{Main.RecordCmd{o, ms, ac, at, List.append(&2, T.Split, mv, [T.Split{a, b}]), ks, ns, d, f, mg}}, Fail{Main.Refused{2, "`--at` is spelled `--at <file>=<path>`"}}, Fail{Main.Refused{2, "`--move` is spelled `--move <old>=<new>`"}}, Done{Main.RecordCmd{o, ms, ac, at, mv, ks, p <> ns, d, f, mg}}, Done{Main.RecordCmd{o, ms, ac, at, mv, ks, p <> ns, d, f, mg}}] : List<&2, Result<&2, &2, Main.Refused, Main.RecordCmd>>}:
  Equal.trans(List<&2, Result<&2, &2, Main.Refused, Main.RecordCmd>>, after(args, [["--at", a ++ ("=" ++ b)], ["--move", a ++ ("=" ++ b)], ["--at", a], ["--move", a], [p], [p ++ "/"]]), each([["--at", a ++ ("=" ++ b)], ["--move", a ++ ("=" ++ b)], ["--at", a], ["--move", a], [p], [p ++ "/"]], Main.RecordCmd{o, ms, ac, at, mv, ks, ns, d, f, mg}), [Done{Main.RecordCmd{o, ms, ac, List.append(&2, T.Split, at, [T.Split{a, b}]), mv, ks, ns, d, f, mg}}, Done{Main.RecordCmd{o, ms, ac, at, List.append(&2, T.Split, mv, [T.Split{a, b}]), ks, ns, d, f, mg}}, Fail{Main.Refused{2, "`--at` is spelled `--at <file>=<path>`"}}, Fail{Main.Refused{2, "`--move` is spelled `--move <old>=<new>`"}}, Done{Main.RecordCmd{o, ms, ac, at, mv, ks, p <> ns, d, f, mg}}, Done{Main.RecordCmd{o, ms, ac, at, mv, ks, p <> ns, d, f, mg}}],
    each_app(args, Main.RecordCmd{o, ms, ac, at, mv, ks, ns, d, f, mg}, e, [["--at", a ++ ("=" ++ b)], ["--move", a ++ ("=" ++ b)], ["--at", a], ["--move", a], [p], [p ++ "/"]]),
    l6(Result<&2, &2, Main.Refused, Main.RecordCmd>, Main.record.args.go(["--at", a ++ ("=" ++ b)], Main.RecordCmd{o, ms, ac, at, mv, ks, ns, d, f, mg}, Main.rword(["--at", a ++ ("=" ++ b)])), Main.record.args.go(["--move", a ++ ("=" ++ b)], Main.RecordCmd{o, ms, ac, at, mv, ks, ns, d, f, mg}, Main.rword(["--move", a ++ ("=" ++ b)])), Main.record.args.go(["--at", a], Main.RecordCmd{o, ms, ac, at, mv, ks, ns, d, f, mg}, Main.rword(["--at", a])), Main.record.args.go(["--move", a], Main.RecordCmd{o, ms, ac, at, mv, ks, ns, d, f, mg}, Main.rword(["--move", a])), Main.record.args.go([p], Main.RecordCmd{o, ms, ac, at, mv, ks, ns, d, f, mg}, Main.rword([p])), Main.record.args.go([p ++ "/"], Main.RecordCmd{o, ms, ac, at, mv, ks, ns, d, f, mg}, Main.rword([p ++ "/"])), Done{Main.RecordCmd{o, ms, ac, List.append(&2, T.Split, at, [T.Split{a, b}]), mv, ks, ns, d, f, mg}}, Done{Main.RecordCmd{o, ms, ac, at, List.append(&2, T.Split, mv, [T.Split{a, b}]), ks, ns, d, f, mg}}, Fail{Main.Refused{2, "`--at` is spelled `--at <file>=<path>`"}}, Fail{Main.Refused{2, "`--move` is spelled `--move <old>=<new>`"}}, Done{Main.RecordCmd{o, ms, ac, at, mv, ks, p <> ns, d, f, mg}}, Done{Main.RecordCmd{o, ms, ac, at, mv, ks, p <> ns, d, f, mg}},
      Equal.cong(Result<&2, &2, Main.Refused, T.Split>, Result<&2, &2, Main.Refused, Main.RecordCmd>, r => Result.bind(&2, &2, Main.Refused, T.Split, Main.RecordCmd, r, s => Main.record.args.go(Nil{}, Main.rc.at(Main.RecordCmd{o, ms, ac, at, mv, ks, ns, d, f, mg}, s), Main.rword(Nil{}))), Main.record.split(a ++ ("=" ++ b), "`--at` is spelled `--at <file>=<path>`"), Done{T.Split{a, b}}, split_at(a, b, "`--at` is spelled `--at <file>=<path>`", ha)),
      Equal.cong(Result<&2, &2, Main.Refused, T.Split>, Result<&2, &2, Main.Refused, Main.RecordCmd>, r => Result.bind(&2, &2, Main.Refused, T.Split, Main.RecordCmd, r, s => Main.record.args.go(Nil{}, Main.rc.move(Main.RecordCmd{o, ms, ac, at, mv, ks, ns, d, f, mg}, s), Main.rword(Nil{}))), Main.record.split(a ++ ("=" ++ b), "`--move` is spelled `--move <old>=<new>`"), Done{T.Split{a, b}}, split_at(a, b, "`--move` is spelled `--move <old>=<new>`", ha)),
      Equal.cong(Result<&2, &2, Main.Refused, T.Split>, Result<&2, &2, Main.Refused, Main.RecordCmd>, r => Result.bind(&2, &2, Main.Refused, T.Split, Main.RecordCmd, r, s => Main.record.args.go(Nil{}, Main.rc.at(Main.RecordCmd{o, ms, ac, at, mv, ks, ns, d, f, mg}, s), Main.rword(Nil{}))), Main.record.split(a, "`--at` is spelled `--at <file>=<path>`"), Fail{Main.Refused{2, "`--at` is spelled `--at <file>=<path>`"}}, split_none(a, "`--at` is spelled `--at <file>=<path>`", ha)),
      Equal.cong(Result<&2, &2, Main.Refused, T.Split>, Result<&2, &2, Main.Refused, Main.RecordCmd>, r => Result.bind(&2, &2, Main.Refused, T.Split, Main.RecordCmd, r, s => Main.record.args.go(Nil{}, Main.rc.move(Main.RecordCmd{o, ms, ac, at, mv, ks, ns, d, f, mg}, s), Main.rword(Nil{}))), Main.record.split(a, "`--move` is spelled `--move <old>=<new>`"), Fail{Main.Refused{2, "`--move` is spelled `--move <old>=<new>`"}}, split_none(a, "`--move` is spelled `--move <old>=<new>`", ha)),
      Equal.trans(Result<&2, &2, Main.Refused, Main.RecordCmd>, Main.record.args.go([p], Main.RecordCmd{o, ms, ac, at, mv, ks, ns, d, f, mg}, Main.rword.of(p)), Main.record.args.go([p], Main.RecordCmd{o, ms, ac, at, mv, ks, ns, d, f, mg}, Main.RWord.Path{}), Done{Main.rc.named(Main.RecordCmd{o, ms, ac, at, mv, ks, ns, d, f, mg}, p)}, Equal.cong(Main.RWord, Result<&2, &2, Main.Refused, Main.RecordCmd>, k => Main.record.args.go([p], Main.RecordCmd{o, ms, ac, at, mv, ks, ns, d, f, mg}, k), Main.rword.of(p), Main.RWord.Path{}, rword_path(p, hp)), path_named(Main.RecordCmd{o, ms, ac, at, mv, ks, ns, d, f, mg}, p, p, trim_keep(p, hs), hn)),
      Equal.trans(Result<&2, &2, Main.Refused, Main.RecordCmd>, Main.record.args.go([p ++ "/"], Main.RecordCmd{o, ms, ac, at, mv, ks, ns, d, f, mg}, Main.rword.of(p ++ "/")), Main.record.args.go([p ++ "/"], Main.RecordCmd{o, ms, ac, at, mv, ks, ns, d, f, mg}, Main.RWord.Path{}), Done{Main.rc.named(Main.RecordCmd{o, ms, ac, at, mv, ks, ns, d, f, mg}, p)}, Equal.cong(Main.RWord, Result<&2, &2, Main.Refused, Main.RecordCmd>, k => Main.record.args.go([p ++ "/"], Main.RecordCmd{o, ms, ac, at, mv, ks, ns, d, f, mg}, k), Main.rword.of(p ++ "/"), Main.RWord.Path{}, rword_path(p ++ "/", sw_slash(p, hp, hn))), path_named(Main.RecordCmd{o, ms, ac, at, mv, ks, ns, d, f, mg}, p ++ "/", p, Equal.trans(String, Main.trimmed(p ++ "/"), Main.trimmed(p), p, trim_slash(p), trim_keep(p, hs)), hn))))

# Rewriting's words
# -----------------

def done_rw(-a: Main.RwCmd, -b: Main.RwCmd, h: {Done{a} == Done{b} : Result<&2, &2, Main.Refused, Main.RwCmd>}) -> {a == b : Main.RwCmd}:
  B.done_eq(Main.RwCmd, a, b, h)

def wkk(+cmd: String, args: List<&2, String>, +more: List<&2, String>, k: Main.WWord) -> Main.WWord:
  match args:
    case Nil{}:
      Main.wword(cmd, more)
    case _:
      k

def wkk_rw(+cmd: String, args: List<&2, String>, +more: List<&2, String>) -> {wkk(cmd, args, more, Main.wword(cmd, args)) == Main.wword(cmd, List.append(&2, String, args, more)) : Main.WWord}:
  match args:
    case Nil{}:
      {==}
    case w <> rest:
      {==}

def wstep(+cmd: String, +rest: List<&2, String>, +more: List<&2, String>, -c1: Main.RwCmd, -c2: Main.RwCmd, ih: {Main.rw.args.go(cmd, List.append(&2, String, rest, more), c1, wkk(cmd, rest, more, Main.wword(cmd, rest))) == Main.rw.args.go(cmd, more, c2, Main.wword(cmd, more)) : Result<&2, &2, Main.Refused, Main.RwCmd>}) -> {Main.rw.args.go(cmd, List.append(&2, String, rest, more), c1, Main.wword(cmd, List.append(&2, String, rest, more))) == Main.rw.args.go(cmd, more, c2, Main.wword(cmd, more)) : Result<&2, &2, Main.Refused, Main.RwCmd>}:
  %wkk_rw(cmd, rest, more) : {Main.rw.args.go(cmd, List.append(&2, String, rest, more), c1, _) == Main.rw.args.go(cmd, more, c2, Main.wword(cmd, more)) : Result<&2, &2, Main.Refused, Main.RwCmd>}
  ih

def wno(-cmd: String, -args: List<&2, String>, -more: List<&2, String>, -c: Main.RwCmd, -k: Main.WWord, -c2: Main.RwCmd, -x: Main.Refused, h: {Fail{x} == Done{c2} : Result<&2, &2, Main.Refused, Main.RwCmd>}) -> {Main.rw.args.go(cmd, List.append(&2, String, args, more), c, wkk(cmd, args, more, k)) == Main.rw.args.go(cmd, more, c2, Main.wword(cmd, more)) : Result<&2, &2, Main.Refused, Main.RwCmd>}:
  Empty.absurd({Main.rw.args.go(cmd, List.append(&2, String, args, more), c, wkk(cmd, args, more, k)) == Main.rw.args.go(cmd, more, c2, Main.wword(cmd, more)) : Result<&2, &2, Main.Refused, Main.RwCmd>}, B.fail_done(Main.RwCmd, x, c2, h))

def wsplit(-cmd: String, -rest: List<&2, String>, -more: List<&2, String>, -u: T.Split -> Main.RwCmd, -c2: Main.RwCmd, r: Result<&2, &2, Main.Refused, T.Split>, e: {Result.bind(&2, &2, Main.Refused, T.Split, Main.RwCmd, r, s => Main.rw.args.go(cmd, rest, u(s), Main.wword(cmd, rest))) == Done{c2} : Result<&2, &2, Main.Refused, Main.RwCmd>}, ih: @s: T.Split -> {Main.rw.args.go(cmd, rest, u(s), Main.wword(cmd, rest)) == Done{c2} : Result<&2, &2, Main.Refused, Main.RwCmd>} -> {Main.rw.args.go(cmd, List.append(&2, String, rest, more), u(s), Main.wword(cmd, List.append(&2, String, rest, more))) == Main.rw.args.go(cmd, more, c2, Main.wword(cmd, more)) : Result<&2, &2, Main.Refused, Main.RwCmd>}) -> {Result.bind(&2, &2, Main.Refused, T.Split, Main.RwCmd, r, s => Main.rw.args.go(cmd, List.append(&2, String, rest, more), u(s), Main.wword(cmd, List.append(&2, String, rest, more)))) == Main.rw.args.go(cmd, more, c2, Main.wword(cmd, more)) : Result<&2, &2, Main.Refused, Main.RwCmd>}:
  match r:
    case Fail{x}:
      Empty.absurd({Fail{x} == Main.rw.args.go(cmd, more, c2, Main.wword(cmd, more)) : Result<&2, &2, Main.Refused, Main.RwCmd>}, B.fail_done(Main.RwCmd, x, c2, e))
    case Done{s}:
      ih(s, e)

def wtarget(-cmd: String, -rest: List<&2, String>, -more: List<&2, String>, -c2: Main.RwCmd, r: Result<&2, &2, Main.Refused, Main.RwCmd>, e: {Result.bind(&2, &2, Main.Refused, Main.RwCmd, Main.RwCmd, r, x => Main.rw.args.go(cmd, rest, x, Main.wword(cmd, rest))) == Done{c2} : Result<&2, &2, Main.Refused, Main.RwCmd>}, ih: @x: Main.RwCmd -> {Main.rw.args.go(cmd, rest, x, Main.wword(cmd, rest)) == Done{c2} : Result<&2, &2, Main.Refused, Main.RwCmd>} -> {Main.rw.args.go(cmd, List.append(&2, String, rest, more), x, Main.wword(cmd, List.append(&2, String, rest, more))) == Main.rw.args.go(cmd, more, c2, Main.wword(cmd, more)) : Result<&2, &2, Main.Refused, Main.RwCmd>}) -> {Result.bind(&2, &2, Main.Refused, Main.RwCmd, Main.RwCmd, r, x => Main.rw.args.go(cmd, List.append(&2, String, rest, more), x, Main.wword(cmd, List.append(&2, String, rest, more)))) == Main.rw.args.go(cmd, more, c2, Main.wword(cmd, more)) : Result<&2, &2, Main.Refused, Main.RwCmd>}:
  match r:
    case Fail{z}:
      Empty.absurd({Fail{z} == Main.rw.args.go(cmd, more, c2, Main.wword(cmd, more)) : Result<&2, &2, Main.Refused, Main.RwCmd>}, B.fail_done(Main.RwCmd, z, c2, e))
    case Done{x}:
      ih(x, e)

def l12(-A: Data, -a0: A, -a1: A, -a2: A, -a3: A, -a4: A, -a5: A, -a6: A, -a7: A, -a8: A, -a9: A, -a10: A, -a11: A, -b0: A, -b1: A, -b2: A, -b3: A, -b4: A, -b5: A, -b6: A, -b7: A, -b8: A, -b9: A, -b10: A, -b11: A, h0: {a0 == b0 : A}, h1: {a1 == b1 : A}, h2: {a2 == b2 : A}, h3: {a3 == b3 : A}, h4: {a4 == b4 : A}, h5: {a5 == b5 : A}, h6: {a6 == b6 : A}, h7: {a7 == b7 : A}, h8: {a8 == b8 : A}, h9: {a9 == b9 : A}, h10: {a10 == b10 : A}, h11: {a11 == b11 : A}) -> {[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11] == [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11] : List<&2, A>}:
  %h0 : {[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11] == [_, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11] : List<&2, A>}
  %h1 : {[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11] == [a0, _, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11] : List<&2, A>}
  %h2 : {[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11] == [a0, a1, _, b3, b4, b5, b6, b7, b8, b9, b10, b11] : List<&2, A>}
  %h3 : {[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11] == [a0, a1, a2, _, b4, b5, b6, b7, b8, b9, b10, b11] : List<&2, A>}
  %h4 : {[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11] == [a0, a1, a2, a3, _, b5, b6, b7, b8, b9, b10, b11] : List<&2, A>}
  %h5 : {[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11] == [a0, a1, a2, a3, a4, _, b6, b7, b8, b9, b10, b11] : List<&2, A>}
  %h6 : {[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11] == [a0, a1, a2, a3, a4, a5, _, b7, b8, b9, b10, b11] : List<&2, A>}
  %h7 : {[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11] == [a0, a1, a2, a3, a4, a5, a6, _, b8, b9, b10, b11] : List<&2, A>}
  %h8 : {[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11] == [a0, a1, a2, a3, a4, a5, a6, a7, _, b9, b10, b11] : List<&2, A>}
  %h9 : {[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11] == [a0, a1, a2, a3, a4, a5, a6, a7, a8, _, b10, b11] : List<&2, A>}
  %h10 : {[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11] == [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, _, b11] : List<&2, A>}
  %h11 : {[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11] == [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, _] : List<&2, A>}
  {==}

def l10(-A: Data, -a0: A, -a1: A, -a2: A, -a3: A, -a4: A, -a5: A, -a6: A, -a7: A, -a8: A, -a9: A, -b0: A, -b1: A, -b2: A, -b3: A, -b4: A, -b5: A, -b6: A, -b7: A, -b8: A, -b9: A, h0: {a0 == b0 : A}, h1: {a1 == b1 : A}, h2: {a2 == b2 : A}, h3: {a3 == b3 : A}, h4: {a4 == b4 : A}, h5: {a5 == b5 : A}, h6: {a6 == b6 : A}, h7: {a7 == b7 : A}, h8: {a8 == b8 : A}, h9: {a9 == b9 : A}) -> {[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9] == [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9] : List<&2, A>}:
  %h0 : {[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9] == [_, b1, b2, b3, b4, b5, b6, b7, b8, b9] : List<&2, A>}
  %h1 : {[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9] == [a0, _, b2, b3, b4, b5, b6, b7, b8, b9] : List<&2, A>}
  %h2 : {[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9] == [a0, a1, _, b3, b4, b5, b6, b7, b8, b9] : List<&2, A>}
  %h3 : {[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9] == [a0, a1, a2, _, b4, b5, b6, b7, b8, b9] : List<&2, A>}
  %h4 : {[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9] == [a0, a1, a2, a3, _, b5, b6, b7, b8, b9] : List<&2, A>}
  %h5 : {[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9] == [a0, a1, a2, a3, a4, _, b6, b7, b8, b9] : List<&2, A>}
  %h6 : {[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9] == [a0, a1, a2, a3, a4, a5, _, b7, b8, b9] : List<&2, A>}
  %h7 : {[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9] == [a0, a1, a2, a3, a4, a5, a6, _, b8, b9] : List<&2, A>}
  %h8 : {[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9] == [a0, a1, a2, a3, a4, a5, a6, a7, _, b9] : List<&2, A>}
  %h9 : {[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9] == [a0, a1, a2, a3, a4, a5, a6, a7, a8, _] : List<&2, A>}
  {==}

def wonly_cons(+cmd: String, w: String, more: List<&2, String>, -c: Main.RwCmd) -> {Main.rw.args.go(cmd, w <> more, c, Main.WWord.Only{}) == Main.rw.args.go(cmd, more, Main.rw.only(c), Main.wword(cmd, more)) : Result<&2, &2, Main.Refused, Main.RwCmd>}:
  match more:
    case Nil{}:
      {==}
    case x <> z:
      {==}

def wdry_cons(+cmd: String, w: String, more: List<&2, String>, -c: Main.RwCmd) -> {Main.rw.args.go(cmd, w <> more, c, Main.WWord.Dry{}) == Main.rw.args.go(cmd, more, Main.rw.dry(c), Main.wword(cmd, more)) : Result<&2, &2, Main.Refused, Main.RwCmd>}:
  match more:
    case Nil{}:
      {==}
    case x <> z:
      {==}

def wfields_cons(+cmd: String, w: String, more: List<&2, String>, -c: Main.RwCmd) -> {Main.rw.args.go(cmd, w <> more, c, Main.WWord.Fields{}) == Main.rw.args.go(cmd, more, Main.rw.fields(c), Main.wword(cmd, more)) : Result<&2, &2, Main.Refused, Main.RwCmd>}:
  match more:
    case Nil{}:
      {==}
    case x <> z:
      {==}

def wword_cons(+cmd: String, +w: String, more: List<&2, String>, -c: Main.RwCmd) -> {Main.rw.args.go(cmd, w <> more, c, Main.WWord.Word{}) == Result.bind(&2, &2, Main.Refused, Main.RwCmd, Main.RwCmd, Main.rw.word(cmd, c, w), x => Main.rw.args.go(cmd, more, x, Main.wword(cmd, more))) : Result<&2, &2, Main.Refused, Main.RwCmd>}:
  match more:
    case Nil{}:
      {==}
    case x <> z:
      {==}

# `amend`, `abandon` and `carry` read their words one at a time, as
# `record` does.
def rw_go_app(+cmd: String, args: List<&2, String>, +more: List<&2, String>, +c: Main.RwCmd, k: Main.WWord, -c2: Main.RwCmd, e: {Main.rw.args.go(cmd, args, c, k) == Done{c2} : Result<&2, &2, Main.Refused, Main.RwCmd>}) -> {Main.rw.args.go(cmd, List.append(&2, String, args, more), c, wkk(cmd, args, more, k)) == Main.rw.args.go(cmd, more, c2, Main.wword(cmd, more)) : Result<&2, &2, Main.Refused, Main.RwCmd>}:
  match args k:
    case Nil{} _:
      %done_rw(c, c2, e) : {Main.rw.args.go(cmd, more, c, Main.wword(cmd, more)) == Main.rw.args.go(cmd, more, _, Main.wword(cmd, more)) : Result<&2, &2, Main.Refused, Main.RwCmd>}
      {==}
    case w <> Nil{} Main.WWord.Message{}:
      wno(cmd, [w], more, c, Main.WWord.Message{}, c2, Main.Refused{2, "`-m` wants a value"}, e)
    case w <> +v <> +rest Main.WWord.Message{}:
      wstep(cmd, rest, more, Main.rw.message(c, v), c2, rw_go_app(cmd, rest, more, Main.rw.message(c, v), Main.wword(cmd, rest), c2, e))
    case w <> Nil{} Main.WWord.Move{}:
      wno(cmd, [w], more, c, Main.WWord.Move{}, c2, Main.Refused{2, "`--move` wants a value"}, e)
    case w <> +v <> +rest Main.WWord.Move{}:
      wsplit(cmd, rest, more, s => Main.rw.move(c, s), c2, Main.record.split(v, "`--move` is spelled `--move <old>=<new>`"), e, +s => h => wstep(cmd, rest, more, Main.rw.move(c, s), c2, rw_go_app(cmd, rest, more, Main.rw.move(c, s), Main.wword(cmd, rest), c2, h)))
    case w <> Nil{} Main.WWord.Onto{}:
      wno(cmd, [w], more, c, Main.WWord.Onto{}, c2, Main.Refused{2, "`--onto` wants a value"}, e)
    case w <> +v <> +rest Main.WWord.Onto{}:
      wstep(cmd, rest, more, Main.rw.onto(c, v), c2, rw_go_app(cmd, rest, more, Main.rw.onto(c, v), Main.wword(cmd, rest), c2, e))
    case +w <> Nil{} Main.WWord.Only{}:
      Equal.trans(Result<&2, &2, Main.Refused, Main.RwCmd>, Main.rw.args.go(cmd, w <> more, c, Main.WWord.Only{}), Main.rw.args.go(cmd, more, Main.rw.only(c), Main.wword(cmd, more)), Main.rw.args.go(cmd, more, c2, Main.wword(cmd, more)), wonly_cons(cmd, w, more, c), Equal.cong(Main.RwCmd, Result<&2, &2, Main.Refused, Main.RwCmd>, x => Main.rw.args.go(cmd, more, x, Main.wword(cmd, more)), Main.rw.only(c), c2, done_rw(Main.rw.only(c), c2, e)))
    case w <> +v <> +rest Main.WWord.Only{}:
      wstep(cmd, v <> rest, more, Main.rw.only(c), c2, rw_go_app(cmd, v <> rest, more, Main.rw.only(c), Main.wword(cmd, v <> rest), c2, e))
    case +w <> Nil{} Main.WWord.Dry{}:
      Equal.trans(Result<&2, &2, Main.Refused, Main.RwCmd>, Main.rw.args.go(cmd, w <> more, c, Main.WWord.Dry{}), Main.rw.args.go(cmd, more, Main.rw.dry(c), Main.wword(cmd, more)), Main.rw.args.go(cmd, more, c2, Main.wword(cmd, more)), wdry_cons(cmd, w, more, c), Equal.cong(Main.RwCmd, Result<&2, &2, Main.Refused, Main.RwCmd>, x => Main.rw.args.go(cmd, more, x, Main.wword(cmd, more)), Main.rw.dry(c), c2, done_rw(Main.rw.dry(c), c2, e)))
    case w <> +v <> +rest Main.WWord.Dry{}:
      wstep(cmd, v <> rest, more, Main.rw.dry(c), c2, rw_go_app(cmd, v <> rest, more, Main.rw.dry(c), Main.wword(cmd, v <> rest), c2, e))
    case +w <> Nil{} Main.WWord.Fields{}:
      Equal.trans(Result<&2, &2, Main.Refused, Main.RwCmd>, Main.rw.args.go(cmd, w <> more, c, Main.WWord.Fields{}), Main.rw.args.go(cmd, more, Main.rw.fields(c), Main.wword(cmd, more)), Main.rw.args.go(cmd, more, c2, Main.wword(cmd, more)), wfields_cons(cmd, w, more, c), Equal.cong(Main.RwCmd, Result<&2, &2, Main.Refused, Main.RwCmd>, x => Main.rw.args.go(cmd, more, x, Main.wword(cmd, more)), Main.rw.fields(c), c2, done_rw(Main.rw.fields(c), c2, e)))
    case w <> +v <> +rest Main.WWord.Fields{}:
      wstep(cmd, v <> rest, more, Main.rw.fields(c), c2, rw_go_app(cmd, v <> rest, more, Main.rw.fields(c), Main.wword(cmd, v <> rest), c2, e))
    case w <> Nil{} Main.WWord.Flag{}:
      wno(cmd, [w], more, c, Main.WWord.Flag{}, c2, Main.Refused{2, "`" ++ w ++ "` is not an argument `" ++ cmd ++ "` takes"}, e)
    case w <> v <> rest Main.WWord.Flag{}:
      wno(cmd, w <> v <> rest, more, c, Main.WWord.Flag{}, c2, Main.Refused{2, "`" ++ w ++ "` is not an argument `" ++ cmd ++ "` takes"}, e)
    case +w <> Nil{} Main.WWord.Word{}:
      Equal.trans(Result<&2, &2, Main.Refused, Main.RwCmd>, Main.rw.args.go(cmd, w <> more, c, Main.WWord.Word{}), Result.bind(&2, &2, Main.Refused, Main.RwCmd, Main.RwCmd, Main.rw.word(cmd, c, w), x => Main.rw.args.go(cmd, more, x, Main.wword(cmd, more))), Main.rw.args.go(cmd, more, c2, Main.wword(cmd, more)), wword_cons(cmd, w, more, c), wtarget(cmd, Nil{}, more, c2, Main.rw.word(cmd, c, w), e, +x => h => wstep(cmd, Nil{}, more, x, c2, rw_go_app(cmd, Nil{}, more, x, Main.wword(cmd, Nil{}), c2, h))))
    case +w <> +v <> +rest Main.WWord.Word{}:
      wtarget(cmd, v <> rest, more, c2, Main.rw.word(cmd, c, w), e, +x => h => wstep(cmd, v <> rest, more, x, c2, rw_go_app(cmd, v <> rest, more, x, Main.wword(cmd, v <> rest), c2, h)))

def app_w(+cmd: String, +args: List<&2, String>, +more: List<&2, String>, -c2: Main.RwCmd, e: {Main.rw.args.r(cmd, args) == Done{c2} : Result<&2, &2, Main.Refused, Main.RwCmd>}) -> {Main.rw.args.r(cmd, List.append(&2, String, args, more)) == Main.rw.args.go(cmd, more, c2, Main.wword(cmd, more)) : Result<&2, &2, Main.Refused, Main.RwCmd>}:
  wstep(cmd, args, more, Main.RwCmd{None{}, Nil{}, None{}, None{}, False{}, False{}, False{}}, c2, rw_go_app(cmd, args, more, Main.RwCmd{None{}, Nil{}, None{}, None{}, False{}, False{}, False{}}, Main.wword(cmd, args), c2, e))

def after_w(+cmd: String, +args: List<&2, String>, wss: List<&2, List<&2, String>>) -> List<&2, Result<&2, &2, Main.Refused, Main.RwCmd>>:
  match wss:
    case Nil{}:
      Nil{}
    case +ws <> rest:
      Main.rw.args.r(cmd, List.append(&2, String, args, ws)) <> after_w(cmd, args, rest)

def each_w(+cmd: String, wss: List<&2, List<&2, String>>, +c: Main.RwCmd) -> List<&2, Result<&2, &2, Main.Refused, Main.RwCmd>>:
  match wss:
    case Nil{}:
      Nil{}
    case +ws <> rest:
      Main.rw.args.go(cmd, ws, c, Main.wword(cmd, ws)) <> each_w(cmd, rest, c)

def each_app_w(+cmd: String, +args: List<&2, String>, -c: Main.RwCmd, +e: {Main.rw.args.r(cmd, args) == Done{c} : Result<&2, &2, Main.Refused, Main.RwCmd>}, wss: List<&2, List<&2, String>>) -> {after_w(cmd, args, wss) == each_w(cmd, wss, c) : List<&2, Result<&2, &2, Main.Refused, Main.RwCmd>>}:
  match wss:
    case Nil{}:
      {==}
    case +ws <> +rest:
      %Equal.sym(Result<&2, &2, Main.Refused, Main.RwCmd>, Main.rw.args.r(cmd, List.append(&2, String, args, ws)), Main.rw.args.go(cmd, ws, c, Main.wword(cmd, ws)), app_w(cmd, args, ws, c, e)) : {_ <> after_w(cmd, args, rest) == each_w(cmd, ws <> rest, c) : List<&2, Result<&2, &2, Main.Refused, Main.RwCmd>>}
      %Equal.sym(List<&2, Result<&2, &2, Main.Refused, Main.RwCmd>>, after_w(cmd, args, rest), each_w(cmd, rest, c), each_app_w(cmd, args, c, e, rest)) : {Main.rw.args.go(cmd, ws, c, Main.wword(cmd, ws)) <> _ == each_w(cmd, ws <> rest, c) : List<&2, Result<&2, &2, Main.Refused, Main.RwCmd>>}
      {==}

# `wword.of`, over what each of its tests of the word answers.
def wword_list(+cmd: String, bs: List<&2, Bool>) -> Main.WWord:
  match bs:
    case m1 <> m2 <> mv <> on <> ol <> n1 <> n2 <> fi <> fl <> Nil{}:
      Bool.pick(Main.WWord, Bool.and(Bool.not(String.eq(cmd, "carry")), Bool.or(m1, m2)), Main.WWord.Message{},
      Bool.pick(Main.WWord, Bool.and(String.eq(cmd, "amend"), mv), Main.WWord.Move{},
      Bool.pick(Main.WWord, Bool.and(String.eq(cmd, "carry"), on), Main.WWord.Onto{},
      Bool.pick(Main.WWord, Bool.and(String.eq(cmd, "abandon"), ol), Main.WWord.Only{},
      Bool.pick(Main.WWord, Bool.or(n1, n2), Main.WWord.Dry{},
      Bool.pick(Main.WWord, fi, Main.WWord.Fields{},
      Bool.pick(Main.WWord, fl, Main.WWord.Flag{}, Main.WWord.Word{})))))))
    case _:
      Main.WWord.Word{}

def WFLAGS() -> List<&2, String>:
  ["-m", "--message", "--move", "--onto", "--only", "-n", "--dry-run", "--fields"]

# A word that does not begin with `-` is no flag of any command.
def wword_word(+cmd: String, +w: String, +hw: {String.starts_with(w, "-") == False{} : Bool}) -> {Main.wword.of(cmd, w) == wword_list(cmd, falses(WFLAGS())) : Main.WWord}:
  Equal.cong(List<&2, Bool>, Main.WWord, bs => wword_list(cmd, bs), eqs(w, WFLAGS(), String.starts_with(w, "-")), falses(WFLAGS()), eqs_false(w, WFLAGS(), hw, {==}))

def word_n(+cmd: String, +m: Maybe<&2, String>, +mv: List<&2, T.Split>, +o: Maybe<&2, String>, n: Maybe<&2, String>, +d: Bool, +f: Bool, +y: Bool, +w: String) -> {Main.rw.args.go(cmd, [w], Main.RwCmd{m, mv, o, n, d, f, y}, Main.WWord.Word{}) == Bool.pick(Result<&2, &2, Main.Refused, Main.RwCmd>, Maybe.is_none(&2, String, n), Done{Main.RwCmd{m, mv, o, Some{w}, d, f, y}}, Fail{Main.Refused{2, Main.rw.second(cmd, w)}}) : Result<&2, &2, Main.Refused, Main.RwCmd>}:
  match n:
    case None{}:
      {==}
    case Some{x}:
      {==}

# The word is the target where none was named, and a second is refused.
def word_named(+cmd: String, +m: Maybe<&2, String>, +mv: List<&2, T.Split>, +o: Maybe<&2, String>, +n: Maybe<&2, String>, +d: Bool, +f: Bool, +y: Bool, +w: String, hk: {Main.wword.of(cmd, w) == Main.WWord.Word{} : Main.WWord}) -> {Main.rw.args.go(cmd, [w], Main.RwCmd{m, mv, o, n, d, f, y}, Main.wword(cmd, [w])) == Bool.pick(Result<&2, &2, Main.Refused, Main.RwCmd>, Maybe.is_none(&2, String, n), Done{Main.RwCmd{m, mv, o, Some{w}, d, f, y}}, Fail{Main.Refused{2, Main.rw.second(cmd, w)}}) : Result<&2, &2, Main.Refused, Main.RwCmd>}:
  Equal.trans(Result<&2, &2, Main.Refused, Main.RwCmd>, Main.rw.args.go(cmd, [w], Main.RwCmd{m, mv, o, n, d, f, y}, Main.wword.of(cmd, w)), Main.rw.args.go(cmd, [w], Main.RwCmd{m, mv, o, n, d, f, y}, Main.WWord.Word{}), Bool.pick(Result<&2, &2, Main.Refused, Main.RwCmd>, Maybe.is_none(&2, String, n), Done{Main.RwCmd{m, mv, o, Some{w}, d, f, y}}, Fail{Main.Refused{2, Main.rw.second(cmd, w)}}),
    Equal.cong(Main.WWord, Result<&2, &2, Main.Refused, Main.RwCmd>, k => Main.rw.args.go(cmd, [w], Main.RwCmd{m, mv, o, n, d, f, y}, k), Main.wword.of(cmd, w), Main.WWord.Word{}, hk),
    word_n(cmd, m, mv, o, n, d, f, y, w))

def amend_reads_its_words_ok(+args: List<&2, String>, +m: Maybe<&2, String>, +mv: List<&2, T.Split>, +o: Maybe<&2, String>, +n: Maybe<&2, String>, +d: Bool, +f: Bool, +y: Bool, +e: {Main.rw.args.r("amend", args) == Done{Main.RwCmd{m, mv, o, n, d, f, y}} : Result<&2, &2, Main.Refused, Main.RwCmd>}, +v: String, +a: String, +b: String, +ha: {T.all_chars(~(c => Bool.not(Char.is_eq(c, '='))), a) == True{} : Bool}, +w: String, +hw: {String.starts_with(w, "-") == False{} : Bool}) -> {after_w("amend", args, [["-m", v], ["--message", v], ["--move", a ++ ("=" ++ b)], ["--move", a], ["-n"], ["--dry-run"], ["--fields"], ["--onto", v], ["--only"], ["-m"], ["--move"], [w]]) == [Done{Main.RwCmd{Some{v}, mv, o, n, d, f, y}}, Done{Main.RwCmd{Some{v}, mv, o, n, d, f, y}}, Done{Main.RwCmd{m, List.append(&2, T.Split, mv, [T.Split{a, b}]), o, n, d, f, y}}, Fail{Main.Refused{2, "`--move` is spelled `--move <old>=<new>`"}}, Done{Main.RwCmd{m, mv, o, n, True{}, f, y}}, Done{Main.RwCmd{m, mv, o, n, True{}, f, y}}, Done{Main.RwCmd{m, mv, o, n, d, True{}, y}}, Fail{Main.Refused{2, "`--onto` is not an argument `amend` takes"}}, Fail{Main.Refused{2, "`--only` is not an argument `amend` takes"}}, Fail{Main.Refused{2, "`-m` wants a value"}}, Fail{Main.Refused{2, "`--move` wants a value"}}, Bool.pick(Result<&2, &2, Main.Refused, Main.RwCmd>, Maybe.is_none(&2, String, n), Done{Main.RwCmd{m, mv, o, Some{w}, d, f, y}}, Fail{Main.Refused{2, "`amend` rewrites one revision, and `" ++ w ++ "` is a second"}})] : List<&2, Result<&2, &2, Main.Refused, Main.RwCmd>>}:
  Equal.trans(List<&2, Result<&2, &2, Main.Refused, Main.RwCmd>>, after_w("amend", args, [["-m", v], ["--message", v], ["--move", a ++ ("=" ++ b)], ["--move", a], ["-n"], ["--dry-run"], ["--fields"], ["--onto", v], ["--only"], ["-m"], ["--move"], [w]]), each_w("amend", [["-m", v], ["--message", v], ["--move", a ++ ("=" ++ b)], ["--move", a], ["-n"], ["--dry-run"], ["--fields"], ["--onto", v], ["--only"], ["-m"], ["--move"], [w]], Main.RwCmd{m, mv, o, n, d, f, y}), [Done{Main.RwCmd{Some{v}, mv, o, n, d, f, y}}, Done{Main.RwCmd{Some{v}, mv, o, n, d, f, y}}, Done{Main.RwCmd{m, List.append(&2, T.Split, mv, [T.Split{a, b}]), o, n, d, f, y}}, Fail{Main.Refused{2, "`--move` is spelled `--move <old>=<new>`"}}, Done{Main.RwCmd{m, mv, o, n, True{}, f, y}}, Done{Main.RwCmd{m, mv, o, n, True{}, f, y}}, Done{Main.RwCmd{m, mv, o, n, d, True{}, y}}, Fail{Main.Refused{2, "`--onto` is not an argument `amend` takes"}}, Fail{Main.Refused{2, "`--only` is not an argument `amend` takes"}}, Fail{Main.Refused{2, "`-m` wants a value"}}, Fail{Main.Refused{2, "`--move` wants a value"}}, Bool.pick(Result<&2, &2, Main.Refused, Main.RwCmd>, Maybe.is_none(&2, String, n), Done{Main.RwCmd{m, mv, o, Some{w}, d, f, y}}, Fail{Main.Refused{2, "`amend` rewrites one revision, and `" ++ w ++ "` is a second"}})],
    each_app_w("amend", args, Main.RwCmd{m, mv, o, n, d, f, y}, e, [["-m", v], ["--message", v], ["--move", a ++ ("=" ++ b)], ["--move", a], ["-n"], ["--dry-run"], ["--fields"], ["--onto", v], ["--only"], ["-m"], ["--move"], [w]]),
    l12(Result<&2, &2, Main.Refused, Main.RwCmd>, Main.rw.args.go("amend", ["-m", v], Main.RwCmd{m, mv, o, n, d, f, y}, Main.wword("amend", ["-m", v])), Main.rw.args.go("amend", ["--message", v], Main.RwCmd{m, mv, o, n, d, f, y}, Main.wword("amend", ["--message", v])), Main.rw.args.go("amend", ["--move", a ++ ("=" ++ b)], Main.RwCmd{m, mv, o, n, d, f, y}, Main.wword("amend", ["--move", a ++ ("=" ++ b)])), Main.rw.args.go("amend", ["--move", a], Main.RwCmd{m, mv, o, n, d, f, y}, Main.wword("amend", ["--move", a])), Main.rw.args.go("amend", ["-n"], Main.RwCmd{m, mv, o, n, d, f, y}, Main.wword("amend", ["-n"])), Main.rw.args.go("amend", ["--dry-run"], Main.RwCmd{m, mv, o, n, d, f, y}, Main.wword("amend", ["--dry-run"])), Main.rw.args.go("amend", ["--fields"], Main.RwCmd{m, mv, o, n, d, f, y}, Main.wword("amend", ["--fields"])), Main.rw.args.go("amend", ["--onto", v], Main.RwCmd{m, mv, o, n, d, f, y}, Main.wword("amend", ["--onto", v])), Main.rw.args.go("amend", ["--only"], Main.RwCmd{m, mv, o, n, d, f, y}, Main.wword("amend", ["--only"])), Main.rw.args.go("amend", ["-m"], Main.RwCmd{m, mv, o, n, d, f, y}, Main.wword("amend", ["-m"])), Main.rw.args.go("amend", ["--move"], Main.RwCmd{m, mv, o, n, d, f, y}, Main.wword("amend", ["--move"])), Main.rw.args.go("amend", [w], Main.RwCmd{m, mv, o, n, d, f, y}, Main.wword("amend", [w])), Done{Main.RwCmd{Some{v}, mv, o, n, d, f, y}}, Done{Main.RwCmd{Some{v}, mv, o, n, d, f, y}}, Done{Main.RwCmd{m, List.append(&2, T.Split, mv, [T.Split{a, b}]), o, n, d, f, y}}, Fail{Main.Refused{2, "`--move` is spelled `--move <old>=<new>`"}}, Done{Main.RwCmd{m, mv, o, n, True{}, f, y}}, Done{Main.RwCmd{m, mv, o, n, True{}, f, y}}, Done{Main.RwCmd{m, mv, o, n, d, True{}, y}}, Fail{Main.Refused{2, "`--onto` is not an argument `amend` takes"}}, Fail{Main.Refused{2, "`--only` is not an argument `amend` takes"}}, Fail{Main.Refused{2, "`-m` wants a value"}}, Fail{Main.Refused{2, "`--move` wants a value"}}, Bool.pick(Result<&2, &2, Main.Refused, Main.RwCmd>, Maybe.is_none(&2, String, n), Done{Main.RwCmd{m, mv, o, Some{w}, d, f, y}}, Fail{Main.Refused{2, "`amend` rewrites one revision, and `" ++ w ++ "` is a second"}}),
      {==},
      {==},
      Equal.cong(Result<&2, &2, Main.Refused, T.Split>, Result<&2, &2, Main.Refused, Main.RwCmd>, r => Result.bind(&2, &2, Main.Refused, T.Split, Main.RwCmd, r, s => Main.rw.args.go("amend", Nil{}, Main.rw.move(Main.RwCmd{m, mv, o, n, d, f, y}, s), Main.wword("amend", Nil{}))), Main.record.split(a ++ ("=" ++ b), "`--move` is spelled `--move <old>=<new>`"), Done{T.Split{a, b}}, split_at(a, b, "`--move` is spelled `--move <old>=<new>`", ha)),
      Equal.cong(Result<&2, &2, Main.Refused, T.Split>, Result<&2, &2, Main.Refused, Main.RwCmd>, r => Result.bind(&2, &2, Main.Refused, T.Split, Main.RwCmd, r, s => Main.rw.args.go("amend", Nil{}, Main.rw.move(Main.RwCmd{m, mv, o, n, d, f, y}, s), Main.wword("amend", Nil{}))), Main.record.split(a, "`--move` is spelled `--move <old>=<new>`"), Fail{Main.Refused{2, "`--move` is spelled `--move <old>=<new>`"}}, split_none(a, "`--move` is spelled `--move <old>=<new>`", ha)),
      {==},
      {==},
      {==},
      {==},
      {==},
      {==},
      {==},
      word_named("amend", m, mv, o, n, d, f, y, w, wword_word("amend", w, hw))))

def abandon_reads_its_words_ok(+args: List<&2, String>, +m: Maybe<&2, String>, +mv: List<&2, T.Split>, +o: Maybe<&2, String>, +n: Maybe<&2, String>, +d: Bool, +f: Bool, +y: Bool, +e: {Main.rw.args.r("abandon", args) == Done{Main.RwCmd{m, mv, o, n, d, f, y}} : Result<&2, &2, Main.Refused, Main.RwCmd>}, +v: String, +a: String, +b: String, +ha: {T.all_chars(~(c => Bool.not(Char.is_eq(c, '='))), a) == True{} : Bool}, +w: String, +hw: {String.starts_with(w, "-") == False{} : Bool}) -> {after_w("abandon", args, [["-m", v], ["--message", v], ["--only"], ["-n"], ["--dry-run"], ["--fields"], ["--move", v], ["--onto", v], ["-m"], [w]]) == [Done{Main.RwCmd{Some{v}, mv, o, n, d, f, y}}, Done{Main.RwCmd{Some{v}, mv, o, n, d, f, y}}, Done{Main.RwCmd{m, mv, o, n, d, f, True{}}}, Done{Main.RwCmd{m, mv, o, n, True{}, f, y}}, Done{Main.RwCmd{m, mv, o, n, True{}, f, y}}, Done{Main.RwCmd{m, mv, o, n, d, True{}, y}}, Fail{Main.Refused{2, "`--move` is not an argument `abandon` takes"}}, Fail{Main.Refused{2, "`--onto` is not an argument `abandon` takes"}}, Fail{Main.Refused{2, "`-m` wants a value"}}, Bool.pick(Result<&2, &2, Main.Refused, Main.RwCmd>, Maybe.is_none(&2, String, n), Done{Main.RwCmd{m, mv, o, Some{w}, d, f, y}}, Fail{Main.Refused{2, "`abandon` abandons one run of work, and `" ++ w ++ "` is a second"}})] : List<&2, Result<&2, &2, Main.Refused, Main.RwCmd>>}:
  Equal.trans(List<&2, Result<&2, &2, Main.Refused, Main.RwCmd>>, after_w("abandon", args, [["-m", v], ["--message", v], ["--only"], ["-n"], ["--dry-run"], ["--fields"], ["--move", v], ["--onto", v], ["-m"], [w]]), each_w("abandon", [["-m", v], ["--message", v], ["--only"], ["-n"], ["--dry-run"], ["--fields"], ["--move", v], ["--onto", v], ["-m"], [w]], Main.RwCmd{m, mv, o, n, d, f, y}), [Done{Main.RwCmd{Some{v}, mv, o, n, d, f, y}}, Done{Main.RwCmd{Some{v}, mv, o, n, d, f, y}}, Done{Main.RwCmd{m, mv, o, n, d, f, True{}}}, Done{Main.RwCmd{m, mv, o, n, True{}, f, y}}, Done{Main.RwCmd{m, mv, o, n, True{}, f, y}}, Done{Main.RwCmd{m, mv, o, n, d, True{}, y}}, Fail{Main.Refused{2, "`--move` is not an argument `abandon` takes"}}, Fail{Main.Refused{2, "`--onto` is not an argument `abandon` takes"}}, Fail{Main.Refused{2, "`-m` wants a value"}}, Bool.pick(Result<&2, &2, Main.Refused, Main.RwCmd>, Maybe.is_none(&2, String, n), Done{Main.RwCmd{m, mv, o, Some{w}, d, f, y}}, Fail{Main.Refused{2, "`abandon` abandons one run of work, and `" ++ w ++ "` is a second"}})],
    each_app_w("abandon", args, Main.RwCmd{m, mv, o, n, d, f, y}, e, [["-m", v], ["--message", v], ["--only"], ["-n"], ["--dry-run"], ["--fields"], ["--move", v], ["--onto", v], ["-m"], [w]]),
    l10(Result<&2, &2, Main.Refused, Main.RwCmd>, Main.rw.args.go("abandon", ["-m", v], Main.RwCmd{m, mv, o, n, d, f, y}, Main.wword("abandon", ["-m", v])), Main.rw.args.go("abandon", ["--message", v], Main.RwCmd{m, mv, o, n, d, f, y}, Main.wword("abandon", ["--message", v])), Main.rw.args.go("abandon", ["--only"], Main.RwCmd{m, mv, o, n, d, f, y}, Main.wword("abandon", ["--only"])), Main.rw.args.go("abandon", ["-n"], Main.RwCmd{m, mv, o, n, d, f, y}, Main.wword("abandon", ["-n"])), Main.rw.args.go("abandon", ["--dry-run"], Main.RwCmd{m, mv, o, n, d, f, y}, Main.wword("abandon", ["--dry-run"])), Main.rw.args.go("abandon", ["--fields"], Main.RwCmd{m, mv, o, n, d, f, y}, Main.wword("abandon", ["--fields"])), Main.rw.args.go("abandon", ["--move", v], Main.RwCmd{m, mv, o, n, d, f, y}, Main.wword("abandon", ["--move", v])), Main.rw.args.go("abandon", ["--onto", v], Main.RwCmd{m, mv, o, n, d, f, y}, Main.wword("abandon", ["--onto", v])), Main.rw.args.go("abandon", ["-m"], Main.RwCmd{m, mv, o, n, d, f, y}, Main.wword("abandon", ["-m"])), Main.rw.args.go("abandon", [w], Main.RwCmd{m, mv, o, n, d, f, y}, Main.wword("abandon", [w])), Done{Main.RwCmd{Some{v}, mv, o, n, d, f, y}}, Done{Main.RwCmd{Some{v}, mv, o, n, d, f, y}}, Done{Main.RwCmd{m, mv, o, n, d, f, True{}}}, Done{Main.RwCmd{m, mv, o, n, True{}, f, y}}, Done{Main.RwCmd{m, mv, o, n, True{}, f, y}}, Done{Main.RwCmd{m, mv, o, n, d, True{}, y}}, Fail{Main.Refused{2, "`--move` is not an argument `abandon` takes"}}, Fail{Main.Refused{2, "`--onto` is not an argument `abandon` takes"}}, Fail{Main.Refused{2, "`-m` wants a value"}}, Bool.pick(Result<&2, &2, Main.Refused, Main.RwCmd>, Maybe.is_none(&2, String, n), Done{Main.RwCmd{m, mv, o, Some{w}, d, f, y}}, Fail{Main.Refused{2, "`abandon` abandons one run of work, and `" ++ w ++ "` is a second"}}),
      {==},
      {==},
      {==},
      {==},
      {==},
      {==},
      {==},
      {==},
      {==},
      word_named("abandon", m, mv, o, n, d, f, y, w, wword_word("abandon", w, hw))))

def carry_reads_its_words_ok(+args: List<&2, String>, +m: Maybe<&2, String>, +mv: List<&2, T.Split>, +o: Maybe<&2, String>, +n: Maybe<&2, String>, +d: Bool, +f: Bool, +y: Bool, +e: {Main.rw.args.r("carry", args) == Done{Main.RwCmd{m, mv, o, n, d, f, y}} : Result<&2, &2, Main.Refused, Main.RwCmd>}, +v: String, +a: String, +b: String, +ha: {T.all_chars(~(c => Bool.not(Char.is_eq(c, '='))), a) == True{} : Bool}, +w: String, +hw: {String.starts_with(w, "-") == False{} : Bool}) -> {after_w("carry", args, [["--onto", v], ["-n"], ["--dry-run"], ["--fields"], ["-m", v], ["--message", v], ["--move", v], ["--only"], ["--onto"], [w]]) == [Done{Main.RwCmd{m, mv, Some{v}, n, d, f, y}}, Done{Main.RwCmd{m, mv, o, n, True{}, f, y}}, Done{Main.RwCmd{m, mv, o, n, True{}, f, y}}, Done{Main.RwCmd{m, mv, o, n, d, True{}, y}}, Fail{Main.Refused{2, "`-m` is not an argument `carry` takes"}}, Fail{Main.Refused{2, "`--message` is not an argument `carry` takes"}}, Fail{Main.Refused{2, "`--move` is not an argument `carry` takes"}}, Fail{Main.Refused{2, "`--only` is not an argument `carry` takes"}}, Fail{Main.Refused{2, "`--onto` wants a value"}}, Bool.pick(Result<&2, &2, Main.Refused, Main.RwCmd>, Maybe.is_none(&2, String, n), Done{Main.RwCmd{m, mv, o, Some{w}, d, f, y}}, Fail{Main.Refused{2, "`carry` carries one line of work, and `" ++ w ++ "` is a second"}})] : List<&2, Result<&2, &2, Main.Refused, Main.RwCmd>>}:
  Equal.trans(List<&2, Result<&2, &2, Main.Refused, Main.RwCmd>>, after_w("carry", args, [["--onto", v], ["-n"], ["--dry-run"], ["--fields"], ["-m", v], ["--message", v], ["--move", v], ["--only"], ["--onto"], [w]]), each_w("carry", [["--onto", v], ["-n"], ["--dry-run"], ["--fields"], ["-m", v], ["--message", v], ["--move", v], ["--only"], ["--onto"], [w]], Main.RwCmd{m, mv, o, n, d, f, y}), [Done{Main.RwCmd{m, mv, Some{v}, n, d, f, y}}, Done{Main.RwCmd{m, mv, o, n, True{}, f, y}}, Done{Main.RwCmd{m, mv, o, n, True{}, f, y}}, Done{Main.RwCmd{m, mv, o, n, d, True{}, y}}, Fail{Main.Refused{2, "`-m` is not an argument `carry` takes"}}, Fail{Main.Refused{2, "`--message` is not an argument `carry` takes"}}, Fail{Main.Refused{2, "`--move` is not an argument `carry` takes"}}, Fail{Main.Refused{2, "`--only` is not an argument `carry` takes"}}, Fail{Main.Refused{2, "`--onto` wants a value"}}, Bool.pick(Result<&2, &2, Main.Refused, Main.RwCmd>, Maybe.is_none(&2, String, n), Done{Main.RwCmd{m, mv, o, Some{w}, d, f, y}}, Fail{Main.Refused{2, "`carry` carries one line of work, and `" ++ w ++ "` is a second"}})],
    each_app_w("carry", args, Main.RwCmd{m, mv, o, n, d, f, y}, e, [["--onto", v], ["-n"], ["--dry-run"], ["--fields"], ["-m", v], ["--message", v], ["--move", v], ["--only"], ["--onto"], [w]]),
    l10(Result<&2, &2, Main.Refused, Main.RwCmd>, Main.rw.args.go("carry", ["--onto", v], Main.RwCmd{m, mv, o, n, d, f, y}, Main.wword("carry", ["--onto", v])), Main.rw.args.go("carry", ["-n"], Main.RwCmd{m, mv, o, n, d, f, y}, Main.wword("carry", ["-n"])), Main.rw.args.go("carry", ["--dry-run"], Main.RwCmd{m, mv, o, n, d, f, y}, Main.wword("carry", ["--dry-run"])), Main.rw.args.go("carry", ["--fields"], Main.RwCmd{m, mv, o, n, d, f, y}, Main.wword("carry", ["--fields"])), Main.rw.args.go("carry", ["-m", v], Main.RwCmd{m, mv, o, n, d, f, y}, Main.wword("carry", ["-m", v])), Main.rw.args.go("carry", ["--message", v], Main.RwCmd{m, mv, o, n, d, f, y}, Main.wword("carry", ["--message", v])), Main.rw.args.go("carry", ["--move", v], Main.RwCmd{m, mv, o, n, d, f, y}, Main.wword("carry", ["--move", v])), Main.rw.args.go("carry", ["--only"], Main.RwCmd{m, mv, o, n, d, f, y}, Main.wword("carry", ["--only"])), Main.rw.args.go("carry", ["--onto"], Main.RwCmd{m, mv, o, n, d, f, y}, Main.wword("carry", ["--onto"])), Main.rw.args.go("carry", [w], Main.RwCmd{m, mv, o, n, d, f, y}, Main.wword("carry", [w])), Done{Main.RwCmd{m, mv, Some{v}, n, d, f, y}}, Done{Main.RwCmd{m, mv, o, n, True{}, f, y}}, Done{Main.RwCmd{m, mv, o, n, True{}, f, y}}, Done{Main.RwCmd{m, mv, o, n, d, True{}, y}}, Fail{Main.Refused{2, "`-m` is not an argument `carry` takes"}}, Fail{Main.Refused{2, "`--message` is not an argument `carry` takes"}}, Fail{Main.Refused{2, "`--move` is not an argument `carry` takes"}}, Fail{Main.Refused{2, "`--only` is not an argument `carry` takes"}}, Fail{Main.Refused{2, "`--onto` wants a value"}}, Bool.pick(Result<&2, &2, Main.Refused, Main.RwCmd>, Maybe.is_none(&2, String, n), Done{Main.RwCmd{m, mv, o, Some{w}, d, f, y}}, Fail{Main.Refused{2, "`carry` carries one line of work, and `" ++ w ++ "` is a second"}}),
      {==},
      {==},
      {==},
      {==},
      {==},
      {==},
      {==},
      {==},
      {==},
      word_named("carry", m, mv, o, n, d, f, y, w, wword_word("carry", w, hw))))

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

def held_state(~da: @parent: List<&2, Ops.Item> -> @child: List<&2, Ops.Item> -> {Ops.terminated_but_last(child) == True{} : Bool} -> @doc: Ops.Doc -> {Ops.diff(parent, child) == Some{doc} : Maybe<&2, Ops.Doc>} -> {Ops.apply(parent, doc) == Done{child} : Result<&2, &2, String, List<&2, Ops.Item>>}, +befores: List<&2, Main.Before>, +dg: Map<&2, String>, +reads: Map<&2, List<&2, U32>>, e: Maybe<&2, Tree.Entry>, +edited: List<&2, String>, +p: String) -> {Main.contents.state(befores, dg, reads, Main.stating.contents(Main.stating.held(edited, befores, p, e, Main.status.folder_digest(dg, p), Main.bytes_of(p, Map.get(List<&2, U32>, Nil{}, reads, p))))) == True{} : Bool}:
  match e:
    case Some{Tree.Entry{+f, q, Tree.Whole{}, y, g, m}}:
      pick_state(befores, dg, reads, Rev.member(edited, p), [Main.Content.Whole{f, p, Main.status.folder_digest(dg, p)}], whole_state(befores, dg, reads, f, p))
    case Some{Tree.Entry{+f, q, Tree.Lines{}, y, g, m}}:
      pick_state(befores, dg, reads, Rev.member(edited, p), Main.edited.content(f, p, Ops.diff(Main.before_of(befores, f), Ops.from_text(Utf8.decode(Main.bytes_of(p, Map.get(List<&2, U32>, Nil{}, reads, p)))))), edited_state(~da, befores, dg, reads, Ops.diff(Main.before_of(befores, f), Ops.from_text(Utf8.decode(Main.bytes_of(p, Map.get(List<&2, U32>, Nil{}, reads, p))))), f, p, {==}))
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

def settled_of(+looked: Tree.Tree(), +facts: List<&2, T.Split>, +refused: List<&2, T.Split>, +claimed: List<&2, T.Split>, +accept: List<&2, String>, +emptied: List<&2, String>, +obs: List<&2, Sv.Obs>, +links: List<&2, String>, +accepted: List<&2, String>, -pl2: Sv.Planned, +e: {Bool.pick(Result<&2, &2, Main.Refused, Sv.Planned>, Bool.not(List.is_empty(&2, T.Split, claimed)), Fail{Main.Refused{1, Main.claimed.msg(looked, claimed)}}, Bool.pick(Result<&2, &2, Main.Refused, Sv.Planned>, Bool.not(List.is_empty(&2, T.Split, refused)), Fail{Main.Refused{1, Main.refused.msg(refused)}}, Bool.pick(Result<&2, &2, Main.Refused, Sv.Planned>, Bool.not(List.is_empty(&2, String, emptied)), Fail{Main.Refused{1, "a merge states what each contested file is, and there is no way to state that one is empty; leave " ++ Main.these(emptied, "it", "them") ++ " something and remove it in the revision after, or drop it here:" ++ Main.skips_held.lines(emptied)}}, Bool.pick(Result<&2, &2, Main.Refused, Sv.Planned>, Bool.not(List.is_empty(&2, String, Main.minus(accept, accepted))), Fail{Main.Refused{1, "concurrent work states different bytes for " ++ Main.these(Main.minus(accept, accepted), "one attachment", "these attachments") ++ "; inspect " ++ Main.these(Main.minus(accept, accepted), "it", "them") ++ " and explicitly accept what the folder holds:" ++ Main.accept.lines(Main.minus(accept, accepted))}}, Bool.pick(Result<&2, &2, Main.Refused, Sv.Planned>, Bool.not(List.is_empty(&2, String, Main.minus(accepted, accept))), Fail{Main.Refused{1, Main.these(Main.minus(accepted, accept), "this path is not a contested attachment", "these paths are not contested attachments") ++ "; remove the unnecessary acceptance:" ++ Main.accept.lines(Main.minus(accepted, accept))}}, Done{Sv.Planned{facts, refused, claimed, accept, emptied, None{}, obs, links}}))))) == Done{pl2} : Result<&2, &2, Main.Refused, Sv.Planned>}) -> {Main.planned.settled(pl2, accepted) == True{} : Bool}:
  +h1 = not_true(List.is_empty(&2, T.Split, claimed), pick_no(Sv.Planned, Bool.not(List.is_empty(&2, T.Split, claimed)), Main.Refused{1, Main.claimed.msg(looked, claimed)}, Bool.pick(Result<&2, &2, Main.Refused, Sv.Planned>, Bool.not(List.is_empty(&2, T.Split, refused)), Fail{Main.Refused{1, Main.refused.msg(refused)}}, Bool.pick(Result<&2, &2, Main.Refused, Sv.Planned>, Bool.not(List.is_empty(&2, String, emptied)), Fail{Main.Refused{1, "a merge states what each contested file is, and there is no way to state that one is empty; leave " ++ Main.these(emptied, "it", "them") ++ " something and remove it in the revision after, or drop it here:" ++ Main.skips_held.lines(emptied)}}, Bool.pick(Result<&2, &2, Main.Refused, Sv.Planned>, Bool.not(List.is_empty(&2, String, Main.minus(accept, accepted))), Fail{Main.Refused{1, "concurrent work states different bytes for " ++ Main.these(Main.minus(accept, accepted), "one attachment", "these attachments") ++ "; inspect " ++ Main.these(Main.minus(accept, accepted), "it", "them") ++ " and explicitly accept what the folder holds:" ++ Main.accept.lines(Main.minus(accept, accepted))}}, Bool.pick(Result<&2, &2, Main.Refused, Sv.Planned>, Bool.not(List.is_empty(&2, String, Main.minus(accepted, accept))), Fail{Main.Refused{1, Main.these(Main.minus(accepted, accept), "this path is not a contested attachment", "these paths are not contested attachments") ++ "; remove the unnecessary acceptance:" ++ Main.accept.lines(Main.minus(accepted, accept))}}, Done{Sv.Planned{facts, refused, claimed, accept, emptied, None{}, obs, links}})))), pl2, e))
  +e2 = pick_rest(Sv.Planned, Bool.not(List.is_empty(&2, T.Split, claimed)), Main.Refused{1, Main.claimed.msg(looked, claimed)}, Bool.pick(Result<&2, &2, Main.Refused, Sv.Planned>, Bool.not(List.is_empty(&2, T.Split, refused)), Fail{Main.Refused{1, Main.refused.msg(refused)}}, Bool.pick(Result<&2, &2, Main.Refused, Sv.Planned>, Bool.not(List.is_empty(&2, String, emptied)), Fail{Main.Refused{1, "a merge states what each contested file is, and there is no way to state that one is empty; leave " ++ Main.these(emptied, "it", "them") ++ " something and remove it in the revision after, or drop it here:" ++ Main.skips_held.lines(emptied)}}, Bool.pick(Result<&2, &2, Main.Refused, Sv.Planned>, Bool.not(List.is_empty(&2, String, Main.minus(accept, accepted))), Fail{Main.Refused{1, "concurrent work states different bytes for " ++ Main.these(Main.minus(accept, accepted), "one attachment", "these attachments") ++ "; inspect " ++ Main.these(Main.minus(accept, accepted), "it", "them") ++ " and explicitly accept what the folder holds:" ++ Main.accept.lines(Main.minus(accept, accepted))}}, Bool.pick(Result<&2, &2, Main.Refused, Sv.Planned>, Bool.not(List.is_empty(&2, String, Main.minus(accepted, accept))), Fail{Main.Refused{1, Main.these(Main.minus(accepted, accept), "this path is not a contested attachment", "these paths are not contested attachments") ++ "; remove the unnecessary acceptance:" ++ Main.accept.lines(Main.minus(accepted, accept))}}, Done{Sv.Planned{facts, refused, claimed, accept, emptied, None{}, obs, links}})))), pl2, e)
  +h2 = not_true(List.is_empty(&2, T.Split, refused), pick_no(Sv.Planned, Bool.not(List.is_empty(&2, T.Split, refused)), Main.Refused{1, Main.refused.msg(refused)}, Bool.pick(Result<&2, &2, Main.Refused, Sv.Planned>, Bool.not(List.is_empty(&2, String, emptied)), Fail{Main.Refused{1, "a merge states what each contested file is, and there is no way to state that one is empty; leave " ++ Main.these(emptied, "it", "them") ++ " something and remove it in the revision after, or drop it here:" ++ Main.skips_held.lines(emptied)}}, Bool.pick(Result<&2, &2, Main.Refused, Sv.Planned>, Bool.not(List.is_empty(&2, String, Main.minus(accept, accepted))), Fail{Main.Refused{1, "concurrent work states different bytes for " ++ Main.these(Main.minus(accept, accepted), "one attachment", "these attachments") ++ "; inspect " ++ Main.these(Main.minus(accept, accepted), "it", "them") ++ " and explicitly accept what the folder holds:" ++ Main.accept.lines(Main.minus(accept, accepted))}}, Bool.pick(Result<&2, &2, Main.Refused, Sv.Planned>, Bool.not(List.is_empty(&2, String, Main.minus(accepted, accept))), Fail{Main.Refused{1, Main.these(Main.minus(accepted, accept), "this path is not a contested attachment", "these paths are not contested attachments") ++ "; remove the unnecessary acceptance:" ++ Main.accept.lines(Main.minus(accepted, accept))}}, Done{Sv.Planned{facts, refused, claimed, accept, emptied, None{}, obs, links}}))), pl2, e2))
  +e3 = pick_rest(Sv.Planned, Bool.not(List.is_empty(&2, T.Split, refused)), Main.Refused{1, Main.refused.msg(refused)}, Bool.pick(Result<&2, &2, Main.Refused, Sv.Planned>, Bool.not(List.is_empty(&2, String, emptied)), Fail{Main.Refused{1, "a merge states what each contested file is, and there is no way to state that one is empty; leave " ++ Main.these(emptied, "it", "them") ++ " something and remove it in the revision after, or drop it here:" ++ Main.skips_held.lines(emptied)}}, Bool.pick(Result<&2, &2, Main.Refused, Sv.Planned>, Bool.not(List.is_empty(&2, String, Main.minus(accept, accepted))), Fail{Main.Refused{1, "concurrent work states different bytes for " ++ Main.these(Main.minus(accept, accepted), "one attachment", "these attachments") ++ "; inspect " ++ Main.these(Main.minus(accept, accepted), "it", "them") ++ " and explicitly accept what the folder holds:" ++ Main.accept.lines(Main.minus(accept, accepted))}}, Bool.pick(Result<&2, &2, Main.Refused, Sv.Planned>, Bool.not(List.is_empty(&2, String, Main.minus(accepted, accept))), Fail{Main.Refused{1, Main.these(Main.minus(accepted, accept), "this path is not a contested attachment", "these paths are not contested attachments") ++ "; remove the unnecessary acceptance:" ++ Main.accept.lines(Main.minus(accepted, accept))}}, Done{Sv.Planned{facts, refused, claimed, accept, emptied, None{}, obs, links}}))), pl2, e2)
  +h3 = not_true(List.is_empty(&2, String, emptied), pick_no(Sv.Planned, Bool.not(List.is_empty(&2, String, emptied)), Main.Refused{1, "a merge states what each contested file is, and there is no way to state that one is empty; leave " ++ Main.these(emptied, "it", "them") ++ " something and remove it in the revision after, or drop it here:" ++ Main.skips_held.lines(emptied)}, Bool.pick(Result<&2, &2, Main.Refused, Sv.Planned>, Bool.not(List.is_empty(&2, String, Main.minus(accept, accepted))), Fail{Main.Refused{1, "concurrent work states different bytes for " ++ Main.these(Main.minus(accept, accepted), "one attachment", "these attachments") ++ "; inspect " ++ Main.these(Main.minus(accept, accepted), "it", "them") ++ " and explicitly accept what the folder holds:" ++ Main.accept.lines(Main.minus(accept, accepted))}}, Bool.pick(Result<&2, &2, Main.Refused, Sv.Planned>, Bool.not(List.is_empty(&2, String, Main.minus(accepted, accept))), Fail{Main.Refused{1, Main.these(Main.minus(accepted, accept), "this path is not a contested attachment", "these paths are not contested attachments") ++ "; remove the unnecessary acceptance:" ++ Main.accept.lines(Main.minus(accepted, accept))}}, Done{Sv.Planned{facts, refused, claimed, accept, emptied, None{}, obs, links}})), pl2, e3))
  +e4 = pick_rest(Sv.Planned, Bool.not(List.is_empty(&2, String, emptied)), Main.Refused{1, "a merge states what each contested file is, and there is no way to state that one is empty; leave " ++ Main.these(emptied, "it", "them") ++ " something and remove it in the revision after, or drop it here:" ++ Main.skips_held.lines(emptied)}, Bool.pick(Result<&2, &2, Main.Refused, Sv.Planned>, Bool.not(List.is_empty(&2, String, Main.minus(accept, accepted))), Fail{Main.Refused{1, "concurrent work states different bytes for " ++ Main.these(Main.minus(accept, accepted), "one attachment", "these attachments") ++ "; inspect " ++ Main.these(Main.minus(accept, accepted), "it", "them") ++ " and explicitly accept what the folder holds:" ++ Main.accept.lines(Main.minus(accept, accepted))}}, Bool.pick(Result<&2, &2, Main.Refused, Sv.Planned>, Bool.not(List.is_empty(&2, String, Main.minus(accepted, accept))), Fail{Main.Refused{1, Main.these(Main.minus(accepted, accept), "this path is not a contested attachment", "these paths are not contested attachments") ++ "; remove the unnecessary acceptance:" ++ Main.accept.lines(Main.minus(accepted, accept))}}, Done{Sv.Planned{facts, refused, claimed, accept, emptied, None{}, obs, links}})), pl2, e3)
  +h4 = not_true(List.is_empty(&2, String, Main.minus(accept, accepted)), pick_no(Sv.Planned, Bool.not(List.is_empty(&2, String, Main.minus(accept, accepted))), Main.Refused{1, "concurrent work states different bytes for " ++ Main.these(Main.minus(accept, accepted), "one attachment", "these attachments") ++ "; inspect " ++ Main.these(Main.minus(accept, accepted), "it", "them") ++ " and explicitly accept what the folder holds:" ++ Main.accept.lines(Main.minus(accept, accepted))}, Bool.pick(Result<&2, &2, Main.Refused, Sv.Planned>, Bool.not(List.is_empty(&2, String, Main.minus(accepted, accept))), Fail{Main.Refused{1, Main.these(Main.minus(accepted, accept), "this path is not a contested attachment", "these paths are not contested attachments") ++ "; remove the unnecessary acceptance:" ++ Main.accept.lines(Main.minus(accepted, accept))}}, Done{Sv.Planned{facts, refused, claimed, accept, emptied, None{}, obs, links}}), pl2, e4))
  +e5 = pick_rest(Sv.Planned, Bool.not(List.is_empty(&2, String, Main.minus(accept, accepted))), Main.Refused{1, "concurrent work states different bytes for " ++ Main.these(Main.minus(accept, accepted), "one attachment", "these attachments") ++ "; inspect " ++ Main.these(Main.minus(accept, accepted), "it", "them") ++ " and explicitly accept what the folder holds:" ++ Main.accept.lines(Main.minus(accept, accepted))}, Bool.pick(Result<&2, &2, Main.Refused, Sv.Planned>, Bool.not(List.is_empty(&2, String, Main.minus(accepted, accept))), Fail{Main.Refused{1, Main.these(Main.minus(accepted, accept), "this path is not a contested attachment", "these paths are not contested attachments") ++ "; remove the unnecessary acceptance:" ++ Main.accept.lines(Main.minus(accepted, accept))}}, Done{Sv.Planned{facts, refused, claimed, accept, emptied, None{}, obs, links}}), pl2, e4)
  +h5 = not_true(List.is_empty(&2, String, Main.minus(accepted, accept)), pick_no(Sv.Planned, Bool.not(List.is_empty(&2, String, Main.minus(accepted, accept))), Main.Refused{1, Main.these(Main.minus(accepted, accept), "this path is not a contested attachment", "these paths are not contested attachments") ++ "; remove the unnecessary acceptance:" ++ Main.accept.lines(Main.minus(accepted, accept))}, Done{Sv.Planned{facts, refused, claimed, accept, emptied, None{}, obs, links}}, pl2, e5))
  +e6 = pick_rest(Sv.Planned, Bool.not(List.is_empty(&2, String, Main.minus(accepted, accept))), Main.Refused{1, Main.these(Main.minus(accepted, accept), "this path is not a contested attachment", "these paths are not contested attachments") ++ "; remove the unnecessary acceptance:" ++ Main.accept.lines(Main.minus(accepted, accept))}, Done{Sv.Planned{facts, refused, claimed, accept, emptied, None{}, obs, links}}, pl2, e5)
  %B.done_eq(Sv.Planned, Sv.Planned{facts, refused, claimed, accept, emptied, None{}, obs, links}, pl2, e6) : {Main.planned.settled(_, accepted) == True{} : Bool}
  B.and_tt(List.is_empty(&2, T.Split, claimed), Bool.and(List.is_empty(&2, T.Split, refused), Bool.and(List.is_empty(&2, String, emptied), Bool.and(True{}, Bool.and(List.is_empty(&2, String, Main.minus(accept, accepted)), List.is_empty(&2, String, Main.minus(accepted, accept)))))), h1,
    B.and_tt(List.is_empty(&2, T.Split, refused), Bool.and(List.is_empty(&2, String, emptied), Bool.and(True{}, Bool.and(List.is_empty(&2, String, Main.minus(accept, accepted)), List.is_empty(&2, String, Main.minus(accepted, accept))))), h2,
    B.and_tt(List.is_empty(&2, String, emptied), Bool.and(True{}, Bool.and(List.is_empty(&2, String, Main.minus(accept, accepted)), List.is_empty(&2, String, Main.minus(accepted, accept)))), h3,
    B.and_tt(True{}, Bool.and(List.is_empty(&2, String, Main.minus(accept, accepted)), List.is_empty(&2, String, Main.minus(accepted, accept))), {==},
    B.and_tt(List.is_empty(&2, String, Main.minus(accept, accepted)), List.is_empty(&2, String, Main.minus(accepted, accept)), h4, h5)))))

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
