# `diff` reads its arguments as their plain reading says: `--onto` and
# `--color` take the word after them, `--color=` spells a colour in the word,
# the last of each counting, and every other word is the target or the path.
import Base
import ./commands.bend as Main
import ./text.bend as T
import ./bookmark.bend as Bm
import ./string_lemmas.bend as S
import ./blamed_lemmas.bend as B
import ./tree.bend as Tree
import ./revision.bend as Rev
import ./fileat_lemmas.bend as FileAt
import ./store.bend as Store
import ./folder.bend as Folder

def done_eq_d(-a: Main.DiffAsked, -b: Main.DiffAsked, h: {Done{a} == Done{b} : Result<&2, &2, String, Main.DiffAsked>}) -> {a == b : Main.DiffAsked}:
  Equal.cong(Result<&2, &2, String, Main.DiffAsked>, Main.DiffAsked, r => Result.default(&2, &2, String, Main.DiffAsked, r, a), Done{a}, Done{b}, h)

def run_fail(args: List<&2, String>, +e: String, +want: Main.DWant) -> {Main.dasked.run(args, Main.DRead{Fail{e}, want}) == Main.DRead{Fail{e}, want} : Main.DRead}:
  match args:
    case Nil{}:
      {==}
    case w <> rest:
      run_fail(rest, e, want)

# A colour after `--color` or `--color=`: refused unless it is one.
def run_color(ok: Bool, +v: String, rest: List<&2, String>, +o: Maybe<&2, String>, +c: String, +acc: List<&2, String>, +fin: Main.DiffAsked, e: {Main.dasked.end(Main.dasked.run(rest, Main.DRead{Main.dasked.color(Main.DiffAsked{o, c, acc}, v, ok), Main.DWant.No{}})) == Done{fin} : Result<&2, &2, String, Main.DiffAsked>}, ih: {Main.dasked.end(Main.dasked.run(rest, Main.DRead{Done{Main.DiffAsked{o, v, acc}}, Main.DWant.No{}})) == Done{fin} : Result<&2, &2, String, Main.DiffAsked>} -> {fin == Main.DiffAsked{Main.dargs.onto(rest, Main.DWant.No{}, o), Main.dargs.color(rest, Main.DWant.No{}, v), List.append(&2, String, acc, Main.dargs.words(rest, Main.DWant.No{}))} : Main.DiffAsked}) -> {fin == Main.DiffAsked{Main.dargs.onto(rest, Main.DWant.No{}, o), Main.dargs.color(rest, Main.DWant.No{}, v), List.append(&2, String, acc, Main.dargs.words(rest, Main.DWant.No{}))} : Main.DiffAsked}:
  match ok:
    case True{}:
      ih(e)
    case False{}:
      Empty.absurd({fin == Main.DiffAsked{Main.dargs.onto(rest, Main.DWant.No{}, o), Main.dargs.color(rest, Main.DWant.No{}, v), List.append(&2, String, acc, Main.dargs.words(rest, Main.DWant.No{}))} : Main.DiffAsked}, B.fail_done_s(Main.DiffAsked, "`" ++ v ++ "` is not a `--color` setting; it is `auto`, which decorates a terminal and nothing else, `always`, or `never`", fin, Equal.trans(Result<&2, &2, String, Main.DiffAsked>, Fail{"`" ++ v ++ "` is not a `--color` setting; it is `auto`, which decorates a terminal and nothing else, `always`, or `never`"}, Main.dasked.end(Main.dasked.run(rest, Main.DRead{Fail{"`" ++ v ++ "` is not a `--color` setting; it is `auto`, which decorates a terminal and nothing else, `always`, or `never`"}, Main.DWant.No{}})), Done{fin},
          Equal.cong(Main.DRead, Result<&2, &2, String, Main.DiffAsked>, r => Main.dasked.end(r), Main.DRead{Fail{"`" ++ v ++ "` is not a `--color` setting; it is `auto`, which decorates a terminal and nothing else, `always`, or `never`"}, Main.DWant.No{}}, Main.dasked.run(rest, Main.DRead{Fail{"`" ++ v ++ "` is not a `--color` setting; it is `auto`, which decorates a terminal and nothing else, `always`, or `never`"}, Main.DWant.No{}}), Equal.sym(Main.DRead, Main.dasked.run(rest, Main.DRead{Fail{"`" ++ v ++ "` is not a `--color` setting; it is `auto`, which decorates a terminal and nothing else, `always`, or `never`"}, Main.DWant.No{}}), Main.DRead{Fail{"`" ++ v ++ "` is not a `--color` setting; it is `auto`, which decorates a terminal and nothing else, `always`, or `never`"}, Main.DWant.No{}}, run_fail(rest, "`" ++ v ++ "` is not a `--color` setting; it is `auto`, which decorates a terminal and nothing else, `always`, or `never`", Main.DWant.No{}))), e)))

def run_other(m: Maybe<&2, String>, +w: String, rest: List<&2, String>, +o: Maybe<&2, String>, +c: String, +acc: List<&2, String>, +fin: Main.DiffAsked, e: {Main.dasked.end(Main.dasked.run(rest, Main.DRead{Main.dasked.other(Main.DiffAsked{o, c, acc}, w, m), Main.DWant.No{}})) == Done{fin} : Result<&2, &2, String, Main.DiffAsked>}, hc: @v: String -> {Main.dasked.end(Main.dasked.run(rest, Main.DRead{Done{Main.DiffAsked{o, v, acc}}, Main.DWant.No{}})) == Done{fin} : Result<&2, &2, String, Main.DiffAsked>} -> {fin == Main.DiffAsked{Main.dargs.onto(rest, Main.DWant.No{}, o), Main.dargs.color(rest, Main.DWant.No{}, v), List.append(&2, String, acc, Main.dargs.words(rest, Main.DWant.No{}))} : Main.DiffAsked}, hw: {Main.dasked.end(Main.dasked.run(rest, Main.DRead{Done{Main.DiffAsked{o, c, List.append(&2, String, acc, [w])}}, Main.DWant.No{}})) == Done{fin} : Result<&2, &2, String, Main.DiffAsked>} -> {fin == Main.DiffAsked{Main.dargs.onto(rest, Main.DWant.No{}, o), Main.dargs.color(rest, Main.DWant.No{}, c), List.append(&2, String, List.append(&2, String, acc, [w]), Main.dargs.words(rest, Main.DWant.No{}))} : Main.DiffAsked}) -> {fin == Main.DiffAsked{Main.dargs.onto(rest, Main.DWant.No{}, o), Main.dargs.color(rest, Main.DWant.No{}, Maybe.default(&2, String, m, c)), List.append(&2, String, acc, Main.dargs.other(m, w, Main.dargs.words(rest, Main.DWant.No{})))} : Main.DiffAsked}:
  match m:
    case Some{+v}:
      run_color(Main.color_ok(v), v, rest, o, c, acc, fin, e, hc(v))
    case None{}:
      Equal.trans(Main.DiffAsked, fin, Main.DiffAsked{Main.dargs.onto(rest, Main.DWant.No{}, o), Main.dargs.color(rest, Main.DWant.No{}, c), List.append(&2, String, List.append(&2, String, acc, [w]), Main.dargs.words(rest, Main.DWant.No{}))}, Main.DiffAsked{Main.dargs.onto(rest, Main.DWant.No{}, o), Main.dargs.color(rest, Main.DWant.No{}, c), List.append(&2, String, acc, w <> Main.dargs.words(rest, Main.DWant.No{}))},
        hw(e),
        Equal.cong(List<&2, String>, Main.DiffAsked, x => Main.DiffAsked{Main.dargs.onto(rest, Main.DWant.No{}, o), Main.dargs.color(rest, Main.DWant.No{}, c), x}, List.append(&2, String, List.append(&2, String, acc, [w]), Main.dargs.words(rest, Main.DWant.No{})), List.append(&2, String, acc, w <> Main.dargs.words(rest, Main.DWant.No{})), B.lapp_assoc(acc, [w], Main.dargs.words(rest, Main.DWant.No{}))))

def run_plain(b1: Bool, b2: Bool, +w: String, rest: List<&2, String>, +o: Maybe<&2, String>, +c: String, +acc: List<&2, String>, +fin: Main.DiffAsked, e: {Main.dasked.end(Main.dasked.run(rest, Main.dasked.plain(Main.DiffAsked{o, c, acc}, w, b1, b2))) == Done{fin} : Result<&2, &2, String, Main.DiffAsked>}, ho: {Main.dasked.end(Main.dasked.run(rest, Main.DRead{Done{Main.DiffAsked{o, c, acc}}, Main.DWant.Onto{}})) == Done{fin} : Result<&2, &2, String, Main.DiffAsked>} -> {fin == Main.DiffAsked{Main.dargs.onto(rest, Main.DWant.Onto{}, o), Main.dargs.color(rest, Main.DWant.Onto{}, c), List.append(&2, String, acc, Main.dargs.words(rest, Main.DWant.Onto{}))} : Main.DiffAsked}, hk: {Main.dasked.end(Main.dasked.run(rest, Main.DRead{Done{Main.DiffAsked{o, c, acc}}, Main.DWant.Color{}})) == Done{fin} : Result<&2, &2, String, Main.DiffAsked>} -> {fin == Main.DiffAsked{Main.dargs.onto(rest, Main.DWant.Color{}, o), Main.dargs.color(rest, Main.DWant.Color{}, c), List.append(&2, String, acc, Main.dargs.words(rest, Main.DWant.Color{}))} : Main.DiffAsked}, hc: @v: String -> {Main.dasked.end(Main.dasked.run(rest, Main.DRead{Done{Main.DiffAsked{o, v, acc}}, Main.DWant.No{}})) == Done{fin} : Result<&2, &2, String, Main.DiffAsked>} -> {fin == Main.DiffAsked{Main.dargs.onto(rest, Main.DWant.No{}, o), Main.dargs.color(rest, Main.DWant.No{}, v), List.append(&2, String, acc, Main.dargs.words(rest, Main.DWant.No{}))} : Main.DiffAsked}, hw: {Main.dasked.end(Main.dasked.run(rest, Main.DRead{Done{Main.DiffAsked{o, c, List.append(&2, String, acc, [w])}}, Main.DWant.No{}})) == Done{fin} : Result<&2, &2, String, Main.DiffAsked>} -> {fin == Main.DiffAsked{Main.dargs.onto(rest, Main.DWant.No{}, o), Main.dargs.color(rest, Main.DWant.No{}, c), List.append(&2, String, List.append(&2, String, acc, [w]), Main.dargs.words(rest, Main.DWant.No{}))} : Main.DiffAsked}) -> {fin == Main.DiffAsked{Bool.pick(Maybe<&2, String>, b1, Main.dargs.onto(rest, Main.DWant.Onto{}, o), Bool.pick(Maybe<&2, String>, b2, Main.dargs.onto(rest, Main.DWant.Color{}, o), Main.dargs.onto(rest, Main.DWant.No{}, o))), Bool.pick(String, b1, Main.dargs.color(rest, Main.DWant.Onto{}, c), Bool.pick(String, b2, Main.dargs.color(rest, Main.DWant.Color{}, c), Main.dargs.color(rest, Main.DWant.No{}, Maybe.default(&2, String, T.strip_prefix(w, "--color="), c)))), List.append(&2, String, acc, Bool.pick(List<&2, String>, b1, Main.dargs.words(rest, Main.DWant.Onto{}), Bool.pick(List<&2, String>, b2, Main.dargs.words(rest, Main.DWant.Color{}), Main.dargs.other(T.strip_prefix(w, "--color="), w, Main.dargs.words(rest, Main.DWant.No{})))))} : Main.DiffAsked}:
  match b1:
    case True{}:
      ho(e)
    case False{}:
      match b2:
        case True{}:
          hk(e)
        case False{}:
          run_other(T.strip_prefix(w, "--color="), w, rest, o, c, acc, fin, e, hc, hw)

# One pass over the arguments reads what their plain reading says.
def run_ok(args: List<&2, String>, want: Main.DWant, +o: Maybe<&2, String>, +c: String, +acc: List<&2, String>, +fin: Main.DiffAsked, e: {Main.dasked.end(Main.dasked.run(args, Main.DRead{Done{Main.DiffAsked{o, c, acc}}, want})) == Done{fin} : Result<&2, &2, String, Main.DiffAsked>}) -> {fin == Main.DiffAsked{Main.dargs.onto(args, want, o), Main.dargs.color(args, want, c), List.append(&2, String, acc, Main.dargs.words(args, want))} : Main.DiffAsked}:
  match args:
    case Nil{}:
      match want:
        case Main.DWant.No{}:
          Equal.trans(Main.DiffAsked, fin, Main.DiffAsked{o, c, acc}, Main.DiffAsked{Main.dargs.onto(Nil{}, Main.DWant.No{}, o), Main.dargs.color(Nil{}, Main.DWant.No{}, c), List.append(&2, String, acc, Main.dargs.words(Nil{}, Main.DWant.No{}))},
            Equal.sym(Main.DiffAsked, Main.DiffAsked{o, c, acc}, fin, done_eq_d(Main.DiffAsked{o, c, acc}, fin, e)),
            Equal.cong(List<&2, String>, Main.DiffAsked, x => Main.DiffAsked{o, c, x}, acc, List.append(&2, String, acc, Nil{}), Equal.sym(List<&2, String>, List.append(&2, String, acc, Nil{}), acc, B.lapp_nil(acc))))
        case Main.DWant.Onto{}:
          Empty.absurd({fin == Main.DiffAsked{Main.dargs.onto(Nil{}, Main.DWant.Onto{}, o), Main.dargs.color(Nil{}, Main.DWant.Onto{}, c), List.append(&2, String, acc, Main.dargs.words(Nil{}, Main.DWant.Onto{}))} : Main.DiffAsked}, B.fail_done_s(Main.DiffAsked, "`--onto` wants a value", fin, e))
        case Main.DWant.Color{}:
          Empty.absurd({fin == Main.DiffAsked{Main.dargs.onto(Nil{}, Main.DWant.Color{}, o), Main.dargs.color(Nil{}, Main.DWant.Color{}, c), List.append(&2, String, acc, Main.dargs.words(Nil{}, Main.DWant.Color{}))} : Main.DiffAsked}, B.fail_done_s(Main.DiffAsked, "`--color` wants `auto`, `always`, or `never`", fin, e))
    case +w <> +rest:
      match want:
        case Main.DWant.No{}:
          run_plain(String.eq(w, "--onto"), String.eq(w, "--color"), w, rest, o, c, acc, fin, e,
            h => run_ok(rest, Main.DWant.Onto{}, o, c, acc, fin, h),
            h => run_ok(rest, Main.DWant.Color{}, o, c, acc, fin, h),
            v => h => run_ok(rest, Main.DWant.No{}, o, v, acc, fin, h),
            h => run_ok(rest, Main.DWant.No{}, o, c, List.append(&2, String, acc, [w]), fin, h))
        case Main.DWant.Onto{}:
          run_ok(rest, Main.DWant.No{}, Some{w}, c, acc, fin, e)
        case Main.DWant.Color{}:
          run_color(Main.color_ok(w), w, rest, o, c, acc, fin, e, h => run_ok(rest, Main.DWant.No{}, o, w, acc, fin, h))

def cmd_said(+c: Main.DiffCmd, +cmd: Main.DiffCmd, e: {Done{c} == Done{cmd} : Result<&2, &2, Main.Refused, Main.DiffCmd>}) -> {Main.diff.said(c) == Main.diff.said(cmd) : Main.DSaid}:
  Equal.cong(Main.DiffCmd, Main.DSaid, x => Main.diff.said(x), c, cmd, B.done_eq(Main.DiffCmd, c, cmd, e))

def first_d(+x: String, +onto: Maybe<&2, String>, +color: String, t: Bool, +cmd: Main.DiffCmd, e: {Main.diff.first.r(x, onto, color, t) == Done{cmd} : Result<&2, &2, Main.Refused, Main.DiffCmd>}) -> {Main.DSaid{[x], onto, color} == Main.diff.said(cmd) : Main.DSaid}:
  match t:
    case True{}:
      cmd_said(Main.DiffCmd{Some{x}, None{}, onto, color}, cmd, e)
    case False{}:
      cmd_said(Main.DiffCmd{None{}, Some{x}, onto, color}, cmd, e)

# What is left once the flags are read is the target and the path, in order.
def split_said(+bs: List<&2, Bm.Bookmark>, +onto: Maybe<&2, String>, +color: String, rest: List<&2, String>, +cmd: Main.DiffCmd, e: {Main.diff.split.r(bs, onto, color, rest) == Done{cmd} : Result<&2, &2, Main.Refused, Main.DiffCmd>}) -> {Main.DSaid{rest, onto, color} == Main.diff.said(cmd) : Main.DSaid}:
  match rest:
    case Nil{}:
      cmd_said(Main.DiffCmd{None{}, None{}, onto, color}, cmd, e)
    case +x <> r1:
      match r1:
        case Nil{}:
          first_d(x, onto, color, Main.could_be_target(bs, x), cmd, e)
        case +y <> r2:
          match r2:
            case Nil{}:
              cmd_said(Main.DiffCmd{Some{x}, Some{y}, onto, color}, cmd, e)
            case +z <> +r3:
              Empty.absurd({Main.DSaid{x <> y <> z <> r3, onto, color} == Main.diff.said(cmd) : Main.DSaid}, B.refuse(Main.DiffCmd, Main.diff.split.r(bs, onto, color, x <> y <> z <> r3), cmd, {==}, e))

def da_onto(a: Main.DiffAsked) -> Maybe<&2, String>:
  match a:
    case Main.DiffAsked{o, c, r}:
      o

def da_color(a: Main.DiffAsked) -> String:
  match a:
    case Main.DiffAsked{o, c, r}:
      c

def da_rest(a: Main.DiffAsked) -> List<&2, String>:
  match a:
    case Main.DiffAsked{o, c, r}:
      r

def asked_said(+bs: List<&2, Bm.Bookmark>, +args: List<&2, String>, r: Result<&2, &2, String, Main.DiffAsked>, +er: {Main.dasked.go(args) == r : Result<&2, &2, String, Main.DiffAsked>}, +cmd: Main.DiffCmd, e: {Main.diff.asked.r(bs, r) == Done{cmd} : Result<&2, &2, Main.Refused, Main.DiffCmd>}) -> {Main.dargs.said(args) == Main.diff.said(cmd) : Main.DSaid}:
  match r:
    case Fail{x}:
      Empty.absurd({Main.dargs.said(args) == Main.diff.said(cmd) : Main.DSaid}, B.fail_done(Main.DiffCmd, Main.Refused{2, x}, cmd, e))
    case Done{a}:
      match a:
        case Main.DiffAsked{+onto, +color, +rest}:
          +ro = run_ok(args, Main.DWant.No{}, None{}, "auto", Nil{}, Main.DiffAsked{onto, color, rest}, er)
          +eo = Equal.cong(Main.DiffAsked, Maybe<&2, String>, x => da_onto(x), Main.DiffAsked{onto, color, rest}, Main.DiffAsked{Main.dargs.onto(args, Main.DWant.No{}, None{}), Main.dargs.color(args, Main.DWant.No{}, "auto"), Main.dargs.words(args, Main.DWant.No{})}, ro)
          +ec = Equal.cong(Main.DiffAsked, String, x => da_color(x), Main.DiffAsked{onto, color, rest}, Main.DiffAsked{Main.dargs.onto(args, Main.DWant.No{}, None{}), Main.dargs.color(args, Main.DWant.No{}, "auto"), Main.dargs.words(args, Main.DWant.No{})}, ro)
          +ew = Equal.cong(Main.DiffAsked, List<&2, String>, x => da_rest(x), Main.DiffAsked{onto, color, rest}, Main.DiffAsked{Main.dargs.onto(args, Main.DWant.No{}, None{}), Main.dargs.color(args, Main.DWant.No{}, "auto"), Main.dargs.words(args, Main.DWant.No{})}, ro)
          %eo : {Main.DSaid{Main.dargs.words(args, Main.DWant.No{}), _, Main.dargs.color(args, Main.DWant.No{}, "auto")} == Main.diff.said(cmd) : Main.DSaid}
          %ec : {Main.DSaid{Main.dargs.words(args, Main.DWant.No{}), onto, _} == Main.diff.said(cmd) : Main.DSaid}
          %ew : {Main.DSaid{_, onto, color} == Main.diff.said(cmd) : Main.DSaid}
          split_said(bs, onto, color, rest, cmd, e)

# `diff` reads its arguments as their plain reading says.
def args_said(+bs: List<&2, Bm.Bookmark>, +args: List<&2, String>, +cmd: Main.DiffCmd, e: {Main.diff.args.r(bs, args) == Done{cmd} : Result<&2, &2, Main.Refused, Main.DiffCmd>}) -> {Main.dargs.said(args) == Main.diff.said(cmd) : Main.DSaid}:
  asked_said(bs, args, Main.dasked.go(args), {==}, cmd, e)

# The other side
# --------------

def AL_and_right(a: Bool, -b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      Empty.absurd({b == True{} : Bool}, S.false_true(h))

def onto_bind(+fs: List<&2, Main.Full>, +bs: List<&2, Bm.Bookmark>, +t: String, r: Result<&2, &2, Main.Refused, Main.Full>, +er: {Main.resolved.r(fs, bs, t) == r : Result<&2, &2, Main.Refused, Main.Full>}, +l: Maybe<&2, String>, e: {Result.bind(&2, &2, Main.Refused, Main.Full, Maybe<&2, String>, r, f => Done{Some{Main.id_of(f)}}) == Done{l} : Result<&2, &2, Main.Refused, Maybe<&2, String>>}) -> {Bool.and(Maybe.is_some(&2, String, l), Main.left.ok(fs, l)) == True{} : Bool}:
  match r:
    case Fail{x}:
      Empty.absurd({Bool.and(Maybe.is_some(&2, String, l), Main.left.ok(fs, l)) == True{} : Bool}, B.fail_done(Maybe<&2, String>, x, l, e))
    case Done{+f}:
      +d = B.done_eq(Maybe<&2, String>, Some{Main.id_of(f)}, l, e)
      %d : {Bool.and(Maybe.is_some(&2, String, _), Main.left.ok(fs, _)) == True{} : Bool}
      B.resolved_mem(fs, bs, t, f, er)

# What `--onto` names is a revision the store holds.
def onto_ok(+fs: List<&2, Main.Full>, +bs: List<&2, Bm.Bookmark>, +t: String, +l: Maybe<&2, String>, e: {Main.onto.r(fs, bs, t) == Done{l} : Result<&2, &2, Main.Refused, Maybe<&2, String>>}) -> {Bool.and(Maybe.is_some(&2, String, l), Main.left.ok(fs, l)) == True{} : Bool}:
  onto_bind(fs, bs, t, Main.resolved.r(fs, bs, t), {==}, l, e)

def parent_ok(+id: String, ps: List<&2, String>, +l: Maybe<&2, String>, e: {Main.sole_parent.r(id, ps) == Done{l} : Result<&2, &2, Main.Refused, Maybe<&2, String>>}) -> {Main.same_list(Main.maybe.list(l), ps) == True{} : Bool}:
  match ps:
    case Nil{}:
      +d = B.done_eq(Maybe<&2, String>, None{}, l, e)
      %d : {Main.same_list(Main.maybe.list(_), Nil{}) == True{} : Bool}
      {==}
    case +p <> rest:
      match rest:
        case Nil{}:
          +d = B.done_eq(Maybe<&2, String>, Some{p}, l, e)
          %d : {Main.same_list(Main.maybe.list(_), [p]) == True{} : Bool}
          B.and_tt(String.eq(p, p), True{}, S.eq_refl(p), {==})
        case +q <> +more:
          Empty.absurd({Main.same_list(Main.maybe.list(l), p <> q <> more) == True{} : Bool}, B.refuse(Maybe<&2, String>, Main.sole_parent.r(id, p <> q <> more), l, {==}, e))

# `diff <target>` compares the target with what `--onto` names, a revision
# the store holds, or else with its one parent.
def left_ok(+fs: List<&2, Main.Full>, +bs: List<&2, Bm.Bookmark>, right: Main.Full, onto: Maybe<&2, String>, +l: Maybe<&2, String>, e: {Main.diff.left.r(fs, bs, right, onto) == Done{l} : Result<&2, &2, Main.Refused, Maybe<&2, String>>}) -> {Main.diff.left.ok(fs, right, onto, l) == True{} : Bool}:
  match right:
    case Main.Full{+i, +change, ps, +supersedes, +author, +when, +revised_by, +revised, +facts, +message}:
      match onto:
        case Some{+t}:
          onto_ok(fs, bs, t, l, e)
        case None{}:
          parent_ok(i, ps, l, e)

# `diff` over the folder compares it with what `--onto` names or the head,
# a revision the store holds either way.
def wc_left_ok(+fs: List<&2, Main.Full>, +bs: List<&2, Bm.Bookmark>, onto: Maybe<&2, String>, +l: Maybe<&2, String>, e: {Main.wc.left.r(fs, bs, onto) == Done{l} : Result<&2, &2, Main.Refused, Maybe<&2, String>>}) -> {Main.left.ok(fs, l) == True{} : Bool}:
  match onto:
    case Some{+t}:
      AL_and_right(Maybe.is_some(&2, String, l), Main.left.ok(fs, l), onto_ok(fs, bs, t, l, e))
    case None{}:
      B.head_left(fs, bs, Main.current_heads(Main.history(fs)), l, e, x => m => B.cur_held(fs, x, m))

# The limit
# ---------

def lim_tree(+bs: List<&2, Bm.Bookmark>, +fs: List<&2, Main.Full>, +id: String, +sp: String, +t: Tree.Tree(), +et: {Main.tree.r(fs, id) == Done{t} : Result<&2, &2, Main.Refused, Tree.Tree()>}, r: Result<&2, &2, Main.Refused, String>, +er: {Main.file_in.r(id, bs, sp, t) == r : Result<&2, &2, Main.Refused, String>}, +lim: Main.Limit, e: {Result.bind(&2, &2, Main.Refused, String, Main.Limit, r, f => Done{Main.Limit.File{f}}) == Done{lim} : Result<&2, &2, Main.Refused, Main.Limit>}) -> {Main.limit.held(fs, lim, Some{id}) == True{} : Bool}:
  match r:
    case Fail{x}:
      Empty.absurd({Main.limit.held(fs, lim, Some{id}) == True{} : Bool}, B.fail_done(Main.Limit, x, lim, e))
    case Done{+f}:
      +d = B.done_eq(Main.Limit, Main.Limit.File{f}, lim, e)
      %d : {Main.limit.held(fs, _, Some{id}) == True{} : Bool}
      +es = Equal.sym(Result<&2, &2, Main.Refused, Tree.Tree()>, Main.tree.r(fs, id), Done{t}, et)
      %es : {Main.tree.holds.r(_, f) == True{} : Bool}
      FileAt.file_ok(id, bs, sp, t, f, er)

def lim_file_bind(+fs: List<&2, Main.Full>, +bs: List<&2, Bm.Bookmark>, +id: String, +sp: String, r: Result<&2, &2, Main.Refused, Tree.Tree()>, +er: {Main.tree.r(fs, id) == r : Result<&2, &2, Main.Refused, Tree.Tree()>}, +lim: Main.Limit, e: {Result.bind(&2, &2, Main.Refused, Tree.Tree(), Main.Limit, r, t => Main.diff.limit.tree(bs, id, sp, t)) == Done{lim} : Result<&2, &2, Main.Refused, Main.Limit>}) -> {Main.limit.held(fs, lim, Some{id}) == True{} : Bool}:
  match r:
    case Fail{x}:
      Empty.absurd({Main.limit.held(fs, lim, Some{id}) == True{} : Bool}, B.fail_done(Main.Limit, x, lim, e))
    case Done{+t}:
      lim_tree(bs, fs, id, sp, t, er, Main.file_in.r(id, bs, sp, t), {==}, lim, e)

def lim_file(+fs: List<&2, Main.Full>, +bs: List<&2, Bm.Bookmark>, +id: String, +sp: String, +lim: Main.Limit, e: {Main.diff.limit.file.r(fs, bs, id, sp) == Done{lim} : Result<&2, &2, Main.Refused, Main.Limit>}) -> {Main.limit.held(fs, lim, Some{id}) == True{} : Bool}:
  lim_file_bind(fs, bs, id, sp, Main.tree.r(fs, id), {==}, lim, e)

def path_held(+fs: List<&2, Main.Full>, +p: String, at: Maybe<&2, String>) -> {Main.limit.held(fs, Main.Limit.Path{p}, at) == True{} : Bool}:
  {==}

def lim_spelled(+fs: List<&2, Main.Full>, +bs: List<&2, Bm.Bookmark>, +id: String, +sp: String, b: Bool, +lim: Main.Limit, e: {Main.diff.limit.spelled(fs, bs, id, sp, b) == Done{lim} : Result<&2, &2, Main.Refused, Main.Limit>}) -> {Main.limit.held(fs, lim, Some{id}) == True{} : Bool}:
  match b:
    case True{}:
      lim_file(fs, bs, id, sp, lim, e)
    case False{}:
      +d = B.done_eq(Main.Limit, Main.Limit.Path{Main.path.spelled(sp)}, lim, e)
      %d : {Main.limit.held(fs, _, Some{id}) == True{} : Bool}
      {==}

# A file `diff <target>` is limited to is one the target's tree holds.
def limit_ok(+fs: List<&2, Main.Full>, +bs: List<&2, Bm.Bookmark>, +right: String, only: Maybe<&2, String>, +lim: Main.Limit, e: {Main.diff.limit.r(fs, bs, right, only) == Done{lim} : Result<&2, &2, Main.Refused, Main.Limit>}) -> {Main.limit.held(fs, lim, Some{right}) == True{} : Bool}:
  match only:
    case None{}:
      +d = B.done_eq(Main.Limit, Main.Limit.None{}, lim, e)
      %d : {Main.limit.held(fs, _, Some{right}) == True{} : Bool}
      {==}
    case Some{+sp}:
      lim_spelled(fs, bs, right, sp, String.starts_with(sp, "file:"), lim, e)

def wc_lim_file(+fs: List<&2, Main.Full>, +bs: List<&2, Bm.Bookmark>, +sp: String, left: Maybe<&2, String>, +lim: Main.Limit, e: {Main.wc.limit.file.r(fs, bs, sp, left) == Done{lim} : Result<&2, &2, Main.Refused, Main.Limit>}) -> {Main.limit.held(fs, lim, left) == True{} : Bool}:
  match left:
    case None{}:
      Empty.absurd({Main.limit.held(fs, lim, None{}) == True{} : Bool}, B.refuse(Main.Limit, Main.wc.limit.file.r(fs, bs, sp, None{}), lim, {==}, e))
    case Some{+id}:
      lim_file(fs, bs, id, sp, lim, e)

def wc_lim_spelled(+fs: List<&2, Main.Full>, +bs: List<&2, Bm.Bookmark>, +left: Maybe<&2, String>, +sp: String, b: Bool, +lim: Main.Limit, e: {Main.wc.limit.spelled(fs, bs, left, sp, b) == Done{lim} : Result<&2, &2, Main.Refused, Main.Limit>}) -> {Main.limit.held(fs, lim, left) == True{} : Bool}:
  match b:
    case True{}:
      wc_lim_file(fs, bs, sp, left, lim, e)
    case False{}:
      +d = B.done_eq(Main.Limit, Main.Limit.Path{Main.path.spelled(sp)}, lim, e)
      %d : {Main.limit.held(fs, _, left) == True{} : Bool}
      path_held(fs, Main.path.spelled(sp), left)

# A file `diff` over the folder is limited to is one the position holds.
def wc_limit_ok(+fs: List<&2, Main.Full>, +bs: List<&2, Bm.Bookmark>, +left: Maybe<&2, String>, only: Maybe<&2, String>, +lim: Main.Limit, e: {Main.wc.limit.r(fs, bs, left, only) == Done{lim} : Result<&2, &2, Main.Refused, Main.Limit>}) -> {Main.limit.held(fs, lim, left) == True{} : Bool}:
  match only:
    case None{}:
      +d = B.done_eq(Main.Limit, Main.Limit.None{}, lim, e)
      %d : {Main.limit.held(fs, _, left) == True{} : Bool}
      {==}
    case Some{+sp}:
      wc_lim_spelled(fs, bs, left, sp, String.starts_with(sp, "file:"), lim, e)

# What is shown
# -------------

def shows_m(l: Main.Limit, m: Maybe<&2, Main.Compared>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{+c}:
      Bool.and(Main.pair.differs(c), Main.limit.shows(l, c))

def rdisc_str(-A: Data, r: Result<&2, &2, String, A>) -> Type:
  match r:
    case Done{x}:
      Empty
    case Fail{e}:
      Unit

def fail_done_str(-A: Data, -e: String, -x: A, h: {Fail{e} == Done{x} : Result<&2, &2, String, A>}) -> Empty:
  %h : {rdisc_str(A, _) : Type}
  Unit{}

def done_eq_str(-A: Data, -a: A, -b: A, h: {Done{a} == Done{b} : Result<&2, &2, String, A>}) -> {a == b : A}:
  Equal.cong(Result<&2, &2, String, A>, A, r => Result.default(&2, &2, String, A, r, a), Done{a}, Done{b}, h)

def built_at(+l: Main.Limit, +c: Main.Compared, d: Bool, +ed: {Main.pair.differs(c) == d : Bool}, +hs: {Main.limit.shows(l, c) == True{} : Bool}) -> {shows_m(l, Bool.pick(Maybe<&2, Main.Compared>, d, Some{c}, None{})) == True{} : Bool}:
  match d:
    case True{}:
      B.and_tt(Main.pair.differs(c), Main.limit.shows(l, c), ed, hs)
    case False{}:
      {==}

# A comparison is kept only where its sides differ.
def built_ok(+l: Main.Limit, +c: Main.Compared, +hs: {Main.limit.shows(l, c) == True{} : Bool}) -> {shows_m(l, Main.compare.built(c)) == True{} : Bool}:
  built_at(l, c, Main.pair.differs(c), {==}, hs)

# A path limit wants a file at that path on one side, which is where the
# comparison says it is.
def wants_shows(l: Main.Limit, +file: String, +was: Maybe<&2, Tree.Entry>, +now: Maybe<&2, Tree.Entry>, -b: Maybe<&2, Main.Side>, -a: Maybe<&2, Main.Side>, -md: Maybe<&2, T.Split>, -rt: Maybe<&2, Main.Retarget>, h: {Main.limit.wants(l, file, Main.entry.path(was), Main.entry.path(now)) == True{} : Bool}) -> {Main.limit.shows(l, Main.Compared{Main.entry.path(was), Main.entry.path(now), b, a, md, rt}) == True{} : Bool}:
  match l:
    case Main.Limit.None{}:
      {==}
    case Main.Limit.File{f}:
      {==}
    case Main.Limit.Path{p}:
      h

def sides_after(+l: Main.Limit, +file: String, +was: Maybe<&2, Tree.Entry>, +now: Maybe<&2, Tree.Entry>, +before: Tree.Tree(), +after: Tree.Tree(), +b: Maybe<&2, Main.Side>, +hw: {Main.limit.wants(l, file, Main.entry.path(was), Main.entry.path(now)) == True{} : Bool}, r: Result<&2, &2, String, Maybe<&2, Main.Side>>, +m: Maybe<&2, Main.Compared>, e: {Result.bind(&2, &2, String, Maybe<&2, Main.Side>, Maybe<&2, Main.Compared>, r, a => Done{Main.compare.built(Main.Compared{Main.entry.path(was), Main.entry.path(now), b, a, Main.modes(was, now), Main.retargeting(Main.shown(before, was), Main.shown(after, now))})}) == Done{m} : Result<&2, &2, String, Maybe<&2, Main.Compared>>}) -> {shows_m(l, m) == True{} : Bool}:
  match r:
    case Fail{x}:
      Empty.absurd({shows_m(l, m) == True{} : Bool}, fail_done_str(Maybe<&2, Main.Compared>, x, m, e))
    case Done{+a}:
      +d = done_eq_str(Maybe<&2, Main.Compared>, Main.compare.built(Main.Compared{Main.entry.path(was), Main.entry.path(now), b, a, Main.modes(was, now), Main.retargeting(Main.shown(before, was), Main.shown(after, now))}), m, e)
      %d : {shows_m(l, _) == True{} : Bool}
      built_ok(l, Main.Compared{Main.entry.path(was), Main.entry.path(now), b, a, Main.modes(was, now), Main.retargeting(Main.shown(before, was), Main.shown(after, now))}, wants_shows(l, file, was, now, b, a, Main.modes(was, now), Main.retargeting(Main.shown(before, was), Main.shown(after, now)), hw))

def sides_before(+l: Main.Limit, +file: String, +was: Maybe<&2, Tree.Entry>, +now: Maybe<&2, Tree.Entry>, +before: Tree.Tree(), +after: Tree.Tree(), +newer: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +right: String, +needed: Bool, +hw: {Main.limit.wants(l, file, Main.entry.path(was), Main.entry.path(now)) == True{} : Bool}, r: Result<&2, &2, String, Maybe<&2, Main.Side>>, +m: Maybe<&2, Main.Compared>, e: {Result.bind(&2, &2, String, Maybe<&2, Main.Side>, Maybe<&2, Main.Compared>, r, b => Result.bind(&2, &2, String, Maybe<&2, Main.Side>, Maybe<&2, Main.Compared>, Main.side(newer, ds, right, file, needed, now), a => Done{Main.compare.built(Main.Compared{Main.entry.path(was), Main.entry.path(now), b, a, Main.modes(was, now), Main.retargeting(Main.shown(before, was), Main.shown(after, now))})})) == Done{m} : Result<&2, &2, String, Maybe<&2, Main.Compared>>}) -> {shows_m(l, m) == True{} : Bool}:
  match r:
    case Fail{x}:
      Empty.absurd({shows_m(l, m) == True{} : Bool}, fail_done_str(Maybe<&2, Main.Compared>, x, m, e))
    case Done{+b}:
      sides_after(l, file, was, now, before, after, b, hw, Main.side(newer, ds, right, file, needed, now), m, e)

def sides_ok(sd: Main.Sides, +l: Main.Limit, +file: String, +was: Maybe<&2, Tree.Entry>, +now: Maybe<&2, Tree.Entry>, +hw: {Main.limit.wants(l, file, Main.entry.path(was), Main.entry.path(now)) == True{} : Bool}, +m: Maybe<&2, Main.Compared>, e: {Main.compare.sides(sd, file, was, now) == Done{m} : Result<&2, &2, String, Maybe<&2, Main.Compared>>}) -> {shows_m(l, m) == True{} : Bool}:
  match sd:
    case Main.Sides{+before, +after, +older, +newer, +ds, +left, +right, +ws, +ns}:
      sides_before(l, file, was, now, before, after, newer, ds, right, Main.compare.needed(ws, ns, file, was, now), hw, Main.side(older, ds, left, file, Main.compare.needed(ws, ns, file, was, now), was), m, e)

def wanted_ok(+sd: Main.Sides, +l: Main.Limit, +file: String, +was: Maybe<&2, Tree.Entry>, +now: Maybe<&2, Tree.Entry>, w: Bool, +ew: {Main.limit.wants(l, file, Main.entry.path(was), Main.entry.path(now)) == w : Bool}, +m: Maybe<&2, Main.Compared>, e: {Main.compare.wanted(sd, file, was, now, w) == Done{m} : Result<&2, &2, String, Maybe<&2, Main.Compared>>}) -> {shows_m(l, m) == True{} : Bool}:
  match w:
    case True{}:
      sides_ok(sd, l, file, was, now, ew, m, e)
    case False{}:
      +d = done_eq_str(Maybe<&2, Main.Compared>, None{}, m, e)
      %d : {shows_m(l, _) == True{} : Bool}
      {==}

def one_ok(+sd: Main.Sides, +l: Main.Limit, b: Main.Both, +m: Maybe<&2, Main.Compared>, e: {Main.compare.one(sd, l, b) == Done{m} : Result<&2, &2, String, Maybe<&2, Main.Compared>>}) -> {shows_m(l, m) == True{} : Bool}:
  match b:
    case Main.Both{+file, +was, +now}:
      wanted_ok(sd, l, file, was, now, Main.limit.wants(l, file, Main.entry.path(was), Main.entry.path(now)), {==}, m, e)

def push_ok(+l: Main.Limit, here: Maybe<&2, Main.Compared>, +later: List<&2, Main.Compared>, h1: {shows_m(l, here) == True{} : Bool}, h2: {Main.all.shown(l, later) == True{} : Bool}) -> {Main.all.shown(l, Main.compare.push(here, later)) == True{} : Bool}:
  match here:
    case None{}:
      h2
    case Some{+c}:
      B.and_tt(Bool.and(Main.pair.differs(c), Main.limit.shows(l, c)), Main.all.shown(l, later), h1, h2)

def later_ok(+l: Main.Limit, +here: Maybe<&2, Main.Compared>, +h1: {shows_m(l, here) == True{} : Bool}, r: Result<&2, &2, String, List<&2, Main.Compared>>, ih: @xs: List<&2, Main.Compared> -> {r == Done{xs} : Result<&2, &2, String, List<&2, Main.Compared>>} -> {Main.all.shown(l, xs) == True{} : Bool}, +cs: List<&2, Main.Compared>, e: {Result.bind(&2, &2, String, List<&2, Main.Compared>, List<&2, Main.Compared>, r, later => Done{Main.compare.push(here, later)}) == Done{cs} : Result<&2, &2, String, List<&2, Main.Compared>>}) -> {Main.all.shown(l, cs) == True{} : Bool}:
  match r:
    case Fail{x}:
      Empty.absurd({Main.all.shown(l, cs) == True{} : Bool}, fail_done_str(List<&2, Main.Compared>, x, cs, e))
    case Done{+later}:
      +d = done_eq_str(List<&2, Main.Compared>, Main.compare.push(here, later), cs, e)
      %d : {Main.all.shown(l, _) == True{} : Bool}
      push_ok(l, here, later, h1, ih(later, {==}))

def here_ok(+sd: Main.Sides, +l: Main.Limit, +f: Main.Both, +rest: List<&2, Main.Both>, r: Result<&2, &2, String, Maybe<&2, Main.Compared>>, +er: {Main.compare.one(sd, l, f) == r : Result<&2, &2, String, Maybe<&2, Main.Compared>>}, ih: @xs: List<&2, Main.Compared> -> {Main.compare(sd, l, rest) == Done{xs} : Result<&2, &2, String, List<&2, Main.Compared>>} -> {Main.all.shown(l, xs) == True{} : Bool}, +cs: List<&2, Main.Compared>, e: {Result.bind(&2, &2, String, Maybe<&2, Main.Compared>, List<&2, Main.Compared>, r, here => Result.bind(&2, &2, String, List<&2, Main.Compared>, List<&2, Main.Compared>, Main.compare(sd, l, rest), later => Done{Main.compare.push(here, later)})) == Done{cs} : Result<&2, &2, String, List<&2, Main.Compared>>}) -> {Main.all.shown(l, cs) == True{} : Bool}:
  match r:
    case Fail{x}:
      Empty.absurd({Main.all.shown(l, cs) == True{} : Bool}, fail_done_str(List<&2, Main.Compared>, x, cs, e))
    case Done{+here}:
      later_ok(l, here, one_ok(sd, l, f, here, er), Main.compare(sd, l, rest), ih, cs, e)

# `diff` shows only files whose two sides differ, and under a path limit
# only a file at that path on one side.
def compare_ok(+sd: Main.Sides, +l: Main.Limit, files: List<&2, Main.Both>, +cs: List<&2, Main.Compared>, e: {Main.compare(sd, l, files) == Done{cs} : Result<&2, &2, String, List<&2, Main.Compared>>}) -> {Main.all.shown(l, cs) == True{} : Bool}:
  match files:
    case Nil{}:
      +d = done_eq_str(List<&2, Main.Compared>, Nil{}, cs, e)
      %d : {Main.all.shown(l, _) == True{} : Bool}
      {==}
    case +f <> +rest:
      here_ok(sd, l, f, rest, Main.compare.one(sd, l, f), {==}, xs => h => compare_ok(sd, l, rest, xs, h), cs, e)

# The folder
# ----------

def keep_w(+l: Main.Limit, +h: Main.Here, +later: List<&2, Main.Here>, b: Bool, +eb: {Main.here.wanted(l, h) == b : Bool}, ih: {Main.all.wanted(l, later) == True{} : Bool}) -> {Main.all.wanted(l, Bool.pick(List<&2, Main.Here>, b, h <> later, later)) == True{} : Bool}:
  match b:
    case True{}:
      B.and_tt(Main.here.wanted(l, h), Main.all.wanted(l, later), eb, ih)
    case False{}:
      ih

def limited_ok(+l: Main.Limit, hs: List<&2, Main.Here>) -> {Main.all.wanted(l, Main.heres.limited(l, hs)) == True{} : Bool}:
  match hs:
    case Nil{}:
      {==}
    case +h <> +rest:
      keep_w(l, h, Main.heres.limited(l, rest), Main.here.wanted(l, h), {==}, limited_ok(l, rest))

# Every path `diff` over the folder goes on with is one the limit wants.
def heres_ok(+t: Tree.Tree(), +found: List<&2, Folder.Found>, +l: Main.Limit) -> {Main.all.wanted(l, Main.heres(t, found, l)) == True{} : Bool}:
  limited_ok(l, Main.here.go(1n+Nat.add(List.length(&2, Tree.Entry, List.sort(~Tree.Entry, ~(a => b => Main.by_path(a, b)), t)), List.length(&2, Folder.Found, found)), List.sort(~Tree.Entry, ~(a => b => Main.by_path(a, b)), t), found, Main.here.cmp(List.sort(~Tree.Entry, ~(a => b => Main.by_path(a, b)), t), found)))

def bind_built(-A: Data, r: Result<&2, &2, String, A>, -k: A -> Result<&2, &2, String, Maybe<&2, Main.Compared>>, +m: Maybe<&2, Main.Compared>, e: {Result.bind(&2, &2, String, A, Maybe<&2, Main.Compared>, r, k) == Done{m} : Result<&2, &2, String, Maybe<&2, Main.Compared>>}, ok: @x: A -> {k(x) == Done{m} : Result<&2, &2, String, Maybe<&2, Main.Compared>>} -> {shows_m(Main.Limit.None{}, m) == True{} : Bool}) -> {shows_m(Main.Limit.None{}, m) == True{} : Bool}:
  match r:
    case Fail{x}:
      Empty.absurd({shows_m(Main.Limit.None{}, m) == True{} : Bool}, fail_done_str(Maybe<&2, Main.Compared>, x, m, e))
    case Done{x}:
      ok(x, e)


def built_done(+c: Main.Compared, +m: Maybe<&2, Main.Compared>, e: {Done{Main.compare.built(c)} == Done{m} : Result<&2, &2, String, Maybe<&2, Main.Compared>>}) -> {shows_m(Main.Limit.None{}, m) == True{} : Bool}:
  +d = done_eq_str(Maybe<&2, Main.Compared>, Main.compare.built(c), m, e)
  %d : {shows_m(Main.Limit.None{}, _) == True{} : Bool}
  built_ok(Main.Limit.None{}, c, {==})

def wc_one_ok(+t: Tree.Tree(), +older: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +left: String, +reads: Map<&2, List<&2, U32>>, p: Main.Planned, +m: Maybe<&2, Main.Compared>, e: {Main.wc.compare.one(t, older, ds, left, reads, p) == Done{m} : Result<&2, &2, String, Maybe<&2, Main.Compared>>}) -> {shows_m(Main.Limit.None{}, m) == True{} : Bool}:
  match p:
    case Main.Planned{Main.Here{+path, +en, +found}, +digest, replay, read}:
      bind_built(Maybe<&2, Main.Side>, Main.wc.before(en, Main.wc.content(older, ds, left, Maybe.default(&2, String, Maybe.map(&2, Tree.Entry, String, x => Tree.entry_file(x), en), SNil{}), replay)), b => Result.bind(&2, &2, String, Maybe<&2, Main.Side>, Maybe<&2, Main.Compared>, Main.wc.after(path, en, found, Main.bytes_of(path, Map.get(List<&2, U32>, Nil{}, reads, path)), digest, read), a => Done{Main.compare.built(Main.Compared{Main.entry.path(en), Maybe.map(&2, Folder.Found, String, x => Folder.found.path(x), found), b, a, Main.wc.mode(en, found), Main.retargeting(Main.shown(t, en), Main.wc.target(found))})}), m, e,
        b => h => bind_built(Maybe<&2, Main.Side>, Main.wc.after(path, en, found, Main.bytes_of(path, Map.get(List<&2, U32>, Nil{}, reads, path)), digest, read), a => Done{Main.compare.built(Main.Compared{Main.entry.path(en), Maybe.map(&2, Folder.Found, String, x => Folder.found.path(x), found), b, a, Main.wc.mode(en, found), Main.retargeting(Main.shown(t, en), Main.wc.target(found))})}, m, h,
          a => h2 => built_done(Main.Compared{Main.entry.path(en), Maybe.map(&2, Folder.Found, String, x => Folder.found.path(x), found), b, a, Main.wc.mode(en, found), Main.retargeting(Main.shown(t, en), Main.wc.target(found))}, m, h2)))

def wc_here_ok(+t: Tree.Tree(), +older: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +left: String, +reads: Map<&2, List<&2, U32>>, +p: Main.Planned, +rest: List<&2, Main.Planned>, r: Result<&2, &2, String, Maybe<&2, Main.Compared>>, +er: {Main.wc.compare.one(t, older, ds, left, reads, p) == r : Result<&2, &2, String, Maybe<&2, Main.Compared>>}, ih: @xs: List<&2, Main.Compared> -> {Main.wc.compare(t, older, ds, left, reads, rest) == Done{xs} : Result<&2, &2, String, List<&2, Main.Compared>>} -> {Main.all.shown(Main.Limit.None{}, xs) == True{} : Bool}, +cs: List<&2, Main.Compared>, e: {Result.bind(&2, &2, String, Maybe<&2, Main.Compared>, List<&2, Main.Compared>, r, here => Result.bind(&2, &2, String, List<&2, Main.Compared>, List<&2, Main.Compared>, Main.wc.compare(t, older, ds, left, reads, rest), later => Done{Main.compare.push(here, later)})) == Done{cs} : Result<&2, &2, String, List<&2, Main.Compared>>}) -> {Main.all.shown(Main.Limit.None{}, cs) == True{} : Bool}:
  match r:
    case Fail{x}:
      Empty.absurd({Main.all.shown(Main.Limit.None{}, cs) == True{} : Bool}, fail_done_str(List<&2, Main.Compared>, x, cs, e))
    case Done{+here}:
      later_ok(Main.Limit.None{}, here, wc_one_ok(t, older, ds, left, reads, p, here, er), Main.wc.compare(t, older, ds, left, reads, rest), ih, cs, e)

# `diff` over the folder shows only paths whose two sides differ.
def wc_compare_ok(+t: Tree.Tree(), +older: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +left: String, +reads: Map<&2, List<&2, U32>>, ps: List<&2, Main.Planned>, +cs: List<&2, Main.Compared>, e: {Main.wc.compare(t, older, ds, left, reads, ps) == Done{cs} : Result<&2, &2, String, List<&2, Main.Compared>>}) -> {Main.all.shown(Main.Limit.None{}, cs) == True{} : Bool}:
  match ps:
    case Nil{}:
      +d = done_eq_str(List<&2, Main.Compared>, Nil{}, cs, e)
      %d : {Main.all.shown(Main.Limit.None{}, _) == True{} : Bool}
      {==}
    case +p <> +rest:
      wc_here_ok(t, older, ds, left, reads, p, rest, Main.wc.compare.one(t, older, ds, left, reads, p), {==}, xs => h => wc_compare_ok(t, older, ds, left, reads, rest, xs, h), cs, e)
