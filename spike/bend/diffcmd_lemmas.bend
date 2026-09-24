# `diff` reads its arguments as their plain reading says: `--onto` and
# `--color` take the word after them, `--color=` spells a colour in the word,
# the last of each counting, and every other word is the target or the path.
import Base
import ./main.bend as Main
import ./text.bend as T
import ./bookmark.bend as Bm
import ./string_lemmas.bend as S
import ./blamed_lemmas.bend as B
import ./tree.bend as Tree
import ./revision.bend as Rev
import ./fileat_lemmas.bend as FileAt

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
      +d = B.done_eq(Main.Limit, Main.Limit.Path{Maybe.default(&2, String, T.strip_prefix(sp, "path:"), sp)}, lim, e)
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
      +d = B.done_eq(Main.Limit, Main.Limit.Path{Maybe.default(&2, String, T.strip_prefix(sp, "path:"), sp)}, lim, e)
      %d : {Main.limit.held(fs, _, left) == True{} : Bool}
      path_held(fs, Maybe.default(&2, String, T.strip_prefix(sp, "path:"), sp), left)

# A file `diff` over the folder is limited to is one the position holds.
def wc_limit_ok(+fs: List<&2, Main.Full>, +bs: List<&2, Bm.Bookmark>, +left: Maybe<&2, String>, only: Maybe<&2, String>, +lim: Main.Limit, e: {Main.wc.limit.r(fs, bs, left, only) == Done{lim} : Result<&2, &2, Main.Refused, Main.Limit>}) -> {Main.limit.held(fs, lim, left) == True{} : Bool}:
  match only:
    case None{}:
      +d = B.done_eq(Main.Limit, Main.Limit.None{}, lim, e)
      %d : {Main.limit.held(fs, _, left) == True{} : Bool}
      {==}
    case Some{+sp}:
      wc_lim_spelled(fs, bs, left, sp, String.starts_with(sp, "file:"), lim, e)
