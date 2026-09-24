# `diff` reads its arguments as their plain reading says: `--onto` and
# `--color` take the word after them, `--color=` spells a colour in the word,
# the last of each counting, and every other word is the target or the path.
import Base
import ./main.bend as Main
import ./text.bend as T
import ./bookmark.bend as Bm
import ./string_lemmas.bend as S
import ./blamed_lemmas.bend as B

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
