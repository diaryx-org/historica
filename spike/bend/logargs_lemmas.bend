# `log` reads its arguments as their plain reading says: the word after a
# flag that takes a value is that flag's value, the last counting; `--fields`
# is asked for if it is there; every other word is the target.
import Base
import ./commands.bend as Main
import ./string_lemmas.bend as S
import ./blamed_lemmas.bend as B

def run_fail(args: List<&2, String>, +e: String, +want: Maybe<&2, Main.LFlag>) -> {Main.raw.run(args, Main.LRead{Fail{e}, want}) == Main.LRead{Fail{e}, want} : Main.LRead}:
  match args:
    case Nil{}:
      {==}
    case w <> rest:
      run_fail(rest, e, want)

def done_eq_r(-a: Main.LRaw, -b: Main.LRaw, h: {Done{a} == Done{b} : Result<&2, &2, String, Main.LRaw>}) -> {a == b : Main.LRaw}:
  Equal.cong(Result<&2, &2, String, Main.LRaw>, Main.LRaw, r => Result.default(&2, &2, String, Main.LRaw, r, a), Done{a}, Done{b}, h)

def valued_limit(c: Result<&2, &2, String, Unit>, +w: String, rest: List<&2, String>, +ws: List<&2, String>, +p: Maybe<&2, String>, +fi: Bool, +l: Maybe<&2, String>, +au: Maybe<&2, String>, +g: Maybe<&2, String>, +si: Maybe<&2, String>, +u: Maybe<&2, String>, +fin: Main.LRaw, e: {Main.raw.end(Main.raw.run(rest, Main.LRead{Main.raw.valued(Main.LRaw{ws, p, fi, l, au, g, si, u}, Main.LFlag.Limit{}, w, c), None{}})) == Done{fin} : Result<&2, &2, String, Main.LRaw>}, ih: @w2: Maybe<&2, Main.LFlag> -> @ws2: List<&2, String> -> @p2: Maybe<&2, String> -> @fi2: Bool -> @l2: Maybe<&2, String> -> @au2: Maybe<&2, String> -> @g2: Maybe<&2, String> -> @si2: Maybe<&2, String> -> @u2: Maybe<&2, String> -> {Main.raw.end(Main.raw.run(rest, Main.LRead{Done{Main.LRaw{ws2, p2, fi2, l2, au2, g2, si2, u2}}, w2})) == Done{fin} : Result<&2, &2, String, Main.LRaw>} -> {fin == Main.LRaw{List.append(&2, String, ws2, Main.largs.words(rest, w2)), Main.largs.last(rest, w2, Main.LFlag.Path{}, p2), Main.largs.fields(rest, w2, fi2), Main.largs.last(rest, w2, Main.LFlag.Limit{}, l2), Main.largs.last(rest, w2, Main.LFlag.Author{}, au2), Main.largs.last(rest, w2, Main.LFlag.Grep{}, g2), Main.largs.last(rest, w2, Main.LFlag.Since{}, si2), Main.largs.last(rest, w2, Main.LFlag.Until{}, u2)} : Main.LRaw}) -> {fin == Main.LRaw{List.append(&2, String, ws, Main.largs.words(rest, None{})), Main.largs.last(rest, None{}, Main.LFlag.Path{}, p), Main.largs.fields(rest, None{}, fi), Main.largs.last(rest, None{}, Main.LFlag.Limit{}, Some{w}), Main.largs.last(rest, None{}, Main.LFlag.Author{}, au), Main.largs.last(rest, None{}, Main.LFlag.Grep{}, g), Main.largs.last(rest, None{}, Main.LFlag.Since{}, si), Main.largs.last(rest, None{}, Main.LFlag.Until{}, u)} : Main.LRaw}:
  match c:
    case Fail{x}:
      Empty.absurd({fin == Main.LRaw{List.append(&2, String, ws, Main.largs.words(rest, None{})), Main.largs.last(rest, None{}, Main.LFlag.Path{}, p), Main.largs.fields(rest, None{}, fi), Main.largs.last(rest, None{}, Main.LFlag.Limit{}, Some{w}), Main.largs.last(rest, None{}, Main.LFlag.Author{}, au), Main.largs.last(rest, None{}, Main.LFlag.Grep{}, g), Main.largs.last(rest, None{}, Main.LFlag.Since{}, si), Main.largs.last(rest, None{}, Main.LFlag.Until{}, u)} : Main.LRaw}, B.fail_done_s(Main.LRaw, x, fin, Equal.trans(Result<&2, &2, String, Main.LRaw>, Fail{x}, Main.raw.end(Main.raw.run(rest, Main.LRead{Fail{x}, None{}})), Done{fin},
          Equal.cong(Main.LRead, Result<&2, &2, String, Main.LRaw>, r => Main.raw.end(r), Main.LRead{Fail{x}, None{}}, Main.raw.run(rest, Main.LRead{Fail{x}, None{}}), Equal.sym(Main.LRead, Main.raw.run(rest, Main.LRead{Fail{x}, None{}}), Main.LRead{Fail{x}, None{}}, run_fail(rest, x, None{}))), e)))
    case Done{uu}:
      ih(None{}, ws, p, fi, Some{w}, au, g, si, u, e)

def valued_since(c: Result<&2, &2, String, Unit>, +w: String, rest: List<&2, String>, +ws: List<&2, String>, +p: Maybe<&2, String>, +fi: Bool, +l: Maybe<&2, String>, +au: Maybe<&2, String>, +g: Maybe<&2, String>, +si: Maybe<&2, String>, +u: Maybe<&2, String>, +fin: Main.LRaw, e: {Main.raw.end(Main.raw.run(rest, Main.LRead{Main.raw.valued(Main.LRaw{ws, p, fi, l, au, g, si, u}, Main.LFlag.Since{}, w, c), None{}})) == Done{fin} : Result<&2, &2, String, Main.LRaw>}, ih: @w2: Maybe<&2, Main.LFlag> -> @ws2: List<&2, String> -> @p2: Maybe<&2, String> -> @fi2: Bool -> @l2: Maybe<&2, String> -> @au2: Maybe<&2, String> -> @g2: Maybe<&2, String> -> @si2: Maybe<&2, String> -> @u2: Maybe<&2, String> -> {Main.raw.end(Main.raw.run(rest, Main.LRead{Done{Main.LRaw{ws2, p2, fi2, l2, au2, g2, si2, u2}}, w2})) == Done{fin} : Result<&2, &2, String, Main.LRaw>} -> {fin == Main.LRaw{List.append(&2, String, ws2, Main.largs.words(rest, w2)), Main.largs.last(rest, w2, Main.LFlag.Path{}, p2), Main.largs.fields(rest, w2, fi2), Main.largs.last(rest, w2, Main.LFlag.Limit{}, l2), Main.largs.last(rest, w2, Main.LFlag.Author{}, au2), Main.largs.last(rest, w2, Main.LFlag.Grep{}, g2), Main.largs.last(rest, w2, Main.LFlag.Since{}, si2), Main.largs.last(rest, w2, Main.LFlag.Until{}, u2)} : Main.LRaw}) -> {fin == Main.LRaw{List.append(&2, String, ws, Main.largs.words(rest, None{})), Main.largs.last(rest, None{}, Main.LFlag.Path{}, p), Main.largs.fields(rest, None{}, fi), Main.largs.last(rest, None{}, Main.LFlag.Limit{}, l), Main.largs.last(rest, None{}, Main.LFlag.Author{}, au), Main.largs.last(rest, None{}, Main.LFlag.Grep{}, g), Main.largs.last(rest, None{}, Main.LFlag.Since{}, Some{w}), Main.largs.last(rest, None{}, Main.LFlag.Until{}, u)} : Main.LRaw}:
  match c:
    case Fail{x}:
      Empty.absurd({fin == Main.LRaw{List.append(&2, String, ws, Main.largs.words(rest, None{})), Main.largs.last(rest, None{}, Main.LFlag.Path{}, p), Main.largs.fields(rest, None{}, fi), Main.largs.last(rest, None{}, Main.LFlag.Limit{}, l), Main.largs.last(rest, None{}, Main.LFlag.Author{}, au), Main.largs.last(rest, None{}, Main.LFlag.Grep{}, g), Main.largs.last(rest, None{}, Main.LFlag.Since{}, Some{w}), Main.largs.last(rest, None{}, Main.LFlag.Until{}, u)} : Main.LRaw}, B.fail_done_s(Main.LRaw, x, fin, Equal.trans(Result<&2, &2, String, Main.LRaw>, Fail{x}, Main.raw.end(Main.raw.run(rest, Main.LRead{Fail{x}, None{}})), Done{fin},
          Equal.cong(Main.LRead, Result<&2, &2, String, Main.LRaw>, r => Main.raw.end(r), Main.LRead{Fail{x}, None{}}, Main.raw.run(rest, Main.LRead{Fail{x}, None{}}), Equal.sym(Main.LRead, Main.raw.run(rest, Main.LRead{Fail{x}, None{}}), Main.LRead{Fail{x}, None{}}, run_fail(rest, x, None{}))), e)))
    case Done{uu}:
      ih(None{}, ws, p, fi, l, au, g, Some{w}, u, e)

def valued_until(c: Result<&2, &2, String, Unit>, +w: String, rest: List<&2, String>, +ws: List<&2, String>, +p: Maybe<&2, String>, +fi: Bool, +l: Maybe<&2, String>, +au: Maybe<&2, String>, +g: Maybe<&2, String>, +si: Maybe<&2, String>, +u: Maybe<&2, String>, +fin: Main.LRaw, e: {Main.raw.end(Main.raw.run(rest, Main.LRead{Main.raw.valued(Main.LRaw{ws, p, fi, l, au, g, si, u}, Main.LFlag.Until{}, w, c), None{}})) == Done{fin} : Result<&2, &2, String, Main.LRaw>}, ih: @w2: Maybe<&2, Main.LFlag> -> @ws2: List<&2, String> -> @p2: Maybe<&2, String> -> @fi2: Bool -> @l2: Maybe<&2, String> -> @au2: Maybe<&2, String> -> @g2: Maybe<&2, String> -> @si2: Maybe<&2, String> -> @u2: Maybe<&2, String> -> {Main.raw.end(Main.raw.run(rest, Main.LRead{Done{Main.LRaw{ws2, p2, fi2, l2, au2, g2, si2, u2}}, w2})) == Done{fin} : Result<&2, &2, String, Main.LRaw>} -> {fin == Main.LRaw{List.append(&2, String, ws2, Main.largs.words(rest, w2)), Main.largs.last(rest, w2, Main.LFlag.Path{}, p2), Main.largs.fields(rest, w2, fi2), Main.largs.last(rest, w2, Main.LFlag.Limit{}, l2), Main.largs.last(rest, w2, Main.LFlag.Author{}, au2), Main.largs.last(rest, w2, Main.LFlag.Grep{}, g2), Main.largs.last(rest, w2, Main.LFlag.Since{}, si2), Main.largs.last(rest, w2, Main.LFlag.Until{}, u2)} : Main.LRaw}) -> {fin == Main.LRaw{List.append(&2, String, ws, Main.largs.words(rest, None{})), Main.largs.last(rest, None{}, Main.LFlag.Path{}, p), Main.largs.fields(rest, None{}, fi), Main.largs.last(rest, None{}, Main.LFlag.Limit{}, l), Main.largs.last(rest, None{}, Main.LFlag.Author{}, au), Main.largs.last(rest, None{}, Main.LFlag.Grep{}, g), Main.largs.last(rest, None{}, Main.LFlag.Since{}, si), Main.largs.last(rest, None{}, Main.LFlag.Until{}, Some{w})} : Main.LRaw}:
  match c:
    case Fail{x}:
      Empty.absurd({fin == Main.LRaw{List.append(&2, String, ws, Main.largs.words(rest, None{})), Main.largs.last(rest, None{}, Main.LFlag.Path{}, p), Main.largs.fields(rest, None{}, fi), Main.largs.last(rest, None{}, Main.LFlag.Limit{}, l), Main.largs.last(rest, None{}, Main.LFlag.Author{}, au), Main.largs.last(rest, None{}, Main.LFlag.Grep{}, g), Main.largs.last(rest, None{}, Main.LFlag.Since{}, si), Main.largs.last(rest, None{}, Main.LFlag.Until{}, Some{w})} : Main.LRaw}, B.fail_done_s(Main.LRaw, x, fin, Equal.trans(Result<&2, &2, String, Main.LRaw>, Fail{x}, Main.raw.end(Main.raw.run(rest, Main.LRead{Fail{x}, None{}})), Done{fin},
          Equal.cong(Main.LRead, Result<&2, &2, String, Main.LRaw>, r => Main.raw.end(r), Main.LRead{Fail{x}, None{}}, Main.raw.run(rest, Main.LRead{Fail{x}, None{}}), Equal.sym(Main.LRead, Main.raw.run(rest, Main.LRead{Fail{x}, None{}}), Main.LRead{Fail{x}, None{}}, run_fail(rest, x, None{}))), e)))
    case Done{uu}:
      ih(None{}, ws, p, fi, l, au, g, si, Some{w}, e)

def flagged(fl: Main.LFlag, ws: List<&2, String>, +w: String, rest: List<&2, String>, +p: Maybe<&2, String>, +fi: Bool, +l: Maybe<&2, String>, +au: Maybe<&2, String>, +g: Maybe<&2, String>, +si: Maybe<&2, String>, +u: Maybe<&2, String>, +fin: Main.LRaw, e: {Main.raw.end(Main.raw.run(rest, Main.raw.flagged(Main.LRaw{ws, p, fi, l, au, g, si, u}, w, fl))) == Done{fin} : Result<&2, &2, String, Main.LRaw>}, ih: @w2: Maybe<&2, Main.LFlag> -> @ws2: List<&2, String> -> @p2: Maybe<&2, String> -> @fi2: Bool -> @l2: Maybe<&2, String> -> @au2: Maybe<&2, String> -> @g2: Maybe<&2, String> -> @si2: Maybe<&2, String> -> @u2: Maybe<&2, String> -> {Main.raw.end(Main.raw.run(rest, Main.LRead{Done{Main.LRaw{ws2, p2, fi2, l2, au2, g2, si2, u2}}, w2})) == Done{fin} : Result<&2, &2, String, Main.LRaw>} -> {fin == Main.LRaw{List.append(&2, String, ws2, Main.largs.words(rest, w2)), Main.largs.last(rest, w2, Main.LFlag.Path{}, p2), Main.largs.fields(rest, w2, fi2), Main.largs.last(rest, w2, Main.LFlag.Limit{}, l2), Main.largs.last(rest, w2, Main.LFlag.Author{}, au2), Main.largs.last(rest, w2, Main.LFlag.Grep{}, g2), Main.largs.last(rest, w2, Main.LFlag.Since{}, si2), Main.largs.last(rest, w2, Main.LFlag.Until{}, u2)} : Main.LRaw}) -> {fin == Main.LRaw{List.append(&2, String, ws, Main.flag.word(fl, w, Main.largs.words(rest, Main.flag.want(fl)))), Main.largs.last(rest, Main.flag.want(fl), Main.LFlag.Path{}, p), Main.largs.fields(rest, Main.flag.want(fl), Main.flag.fields(fl, fi)), Main.largs.last(rest, Main.flag.want(fl), Main.LFlag.Limit{}, l), Main.largs.last(rest, Main.flag.want(fl), Main.LFlag.Author{}, au), Main.largs.last(rest, Main.flag.want(fl), Main.LFlag.Grep{}, g), Main.largs.last(rest, Main.flag.want(fl), Main.LFlag.Since{}, si), Main.largs.last(rest, Main.flag.want(fl), Main.LFlag.Until{}, u)} : Main.LRaw}:
  match fl:
    case Main.LFlag.Limit{}:
      ih(Some{Main.LFlag.Limit{}}, ws, p, fi, l, au, g, si, u, e)
    case Main.LFlag.Author{}:
      ih(Some{Main.LFlag.Author{}}, ws, p, fi, l, au, g, si, u, e)
    case Main.LFlag.Grep{}:
      ih(Some{Main.LFlag.Grep{}}, ws, p, fi, l, au, g, si, u, e)
    case Main.LFlag.Since{}:
      ih(Some{Main.LFlag.Since{}}, ws, p, fi, l, au, g, si, u, e)
    case Main.LFlag.Until{}:
      ih(Some{Main.LFlag.Until{}}, ws, p, fi, l, au, g, si, u, e)
    case Main.LFlag.Path{}:
      ih(Some{Main.LFlag.Path{}}, ws, p, fi, l, au, g, si, u, e)
    case Main.LFlag.Fields{}:
      ih(None{}, ws, p, True{}, l, au, g, si, u, e)
    case Main.LFlag.Other{}:
      Empty.absurd({fin == Main.LRaw{List.append(&2, String, ws, Main.flag.word(Main.LFlag.Other{}, w, Main.largs.words(rest, Main.flag.want(Main.LFlag.Other{})))), Main.largs.last(rest, Main.flag.want(Main.LFlag.Other{}), Main.LFlag.Path{}, p), Main.largs.fields(rest, Main.flag.want(Main.LFlag.Other{}), Main.flag.fields(Main.LFlag.Other{}, fi)), Main.largs.last(rest, Main.flag.want(Main.LFlag.Other{}), Main.LFlag.Limit{}, l), Main.largs.last(rest, Main.flag.want(Main.LFlag.Other{}), Main.LFlag.Author{}, au), Main.largs.last(rest, Main.flag.want(Main.LFlag.Other{}), Main.LFlag.Grep{}, g), Main.largs.last(rest, Main.flag.want(Main.LFlag.Other{}), Main.LFlag.Since{}, si), Main.largs.last(rest, Main.flag.want(Main.LFlag.Other{}), Main.LFlag.Until{}, u)} : Main.LRaw}, B.fail_done_s(Main.LRaw, "`" ++ w ++ "` is not an argument `log` takes", fin, Equal.trans(Result<&2, &2, String, Main.LRaw>, Fail{"`" ++ w ++ "` is not an argument `log` takes"}, Main.raw.end(Main.raw.run(rest, Main.LRead{Fail{"`" ++ w ++ "` is not an argument `log` takes"}, None{}})), Done{fin},
          Equal.cong(Main.LRead, Result<&2, &2, String, Main.LRaw>, r => Main.raw.end(r), Main.LRead{Fail{"`" ++ w ++ "` is not an argument `log` takes"}, None{}}, Main.raw.run(rest, Main.LRead{Fail{"`" ++ w ++ "` is not an argument `log` takes"}, None{}}), Equal.sym(Main.LRead, Main.raw.run(rest, Main.LRead{Fail{"`" ++ w ++ "` is not an argument `log` takes"}, None{}}), Main.LRead{Fail{"`" ++ w ++ "` is not an argument `log` takes"}, None{}}, run_fail(rest, "`" ++ w ++ "` is not an argument `log` takes", None{}))), e)))
    case Main.LFlag.Word{}:
      match ws:
        case Nil{}:
          ih(None{}, [w], p, fi, l, au, g, si, u, e)
        case +x <> +more:
          Empty.absurd({fin == Main.LRaw{List.append(&2, String, x <> more, Main.flag.word(Main.LFlag.Word{}, w, Main.largs.words(rest, Main.flag.want(Main.LFlag.Word{})))), Main.largs.last(rest, Main.flag.want(Main.LFlag.Word{}), Main.LFlag.Path{}, p), Main.largs.fields(rest, Main.flag.want(Main.LFlag.Word{}), Main.flag.fields(Main.LFlag.Word{}, fi)), Main.largs.last(rest, Main.flag.want(Main.LFlag.Word{}), Main.LFlag.Limit{}, l), Main.largs.last(rest, Main.flag.want(Main.LFlag.Word{}), Main.LFlag.Author{}, au), Main.largs.last(rest, Main.flag.want(Main.LFlag.Word{}), Main.LFlag.Grep{}, g), Main.largs.last(rest, Main.flag.want(Main.LFlag.Word{}), Main.LFlag.Since{}, si), Main.largs.last(rest, Main.flag.want(Main.LFlag.Word{}), Main.LFlag.Until{}, u)} : Main.LRaw}, B.fail_done_s(Main.LRaw, "`log` takes one target or one range, and `" ++ w ++ "` is a second", fin, Equal.trans(Result<&2, &2, String, Main.LRaw>, Fail{"`log` takes one target or one range, and `" ++ w ++ "` is a second"}, Main.raw.end(Main.raw.run(rest, Main.LRead{Fail{"`log` takes one target or one range, and `" ++ w ++ "` is a second"}, None{}})), Done{fin},
          Equal.cong(Main.LRead, Result<&2, &2, String, Main.LRaw>, r => Main.raw.end(r), Main.LRead{Fail{"`log` takes one target or one range, and `" ++ w ++ "` is a second"}, None{}}, Main.raw.run(rest, Main.LRead{Fail{"`log` takes one target or one range, and `" ++ w ++ "` is a second"}, None{}}), Equal.sym(Main.LRead, Main.raw.run(rest, Main.LRead{Fail{"`log` takes one target or one range, and `" ++ w ++ "` is a second"}, None{}}), Main.LRead{Fail{"`log` takes one target or one range, and `" ++ w ++ "` is a second"}, None{}}, run_fail(rest, "`log` takes one target or one range, and `" ++ w ++ "` is a second", None{}))), e)))

# One pass over the arguments reads what their plain reading says.
def run_ok(args: List<&2, String>, want: Maybe<&2, Main.LFlag>, +ws: List<&2, String>, +p: Maybe<&2, String>, +fi: Bool, +l: Maybe<&2, String>, +au: Maybe<&2, String>, +g: Maybe<&2, String>, +si: Maybe<&2, String>, +u: Maybe<&2, String>, +fin: Main.LRaw, e: {Main.raw.end(Main.raw.run(args, Main.LRead{Done{Main.LRaw{ws, p, fi, l, au, g, si, u}}, want})) == Done{fin} : Result<&2, &2, String, Main.LRaw>}) -> {fin == Main.LRaw{List.append(&2, String, ws, Main.largs.words(args, want)), Main.largs.last(args, want, Main.LFlag.Path{}, p), Main.largs.fields(args, want, fi), Main.largs.last(args, want, Main.LFlag.Limit{}, l), Main.largs.last(args, want, Main.LFlag.Author{}, au), Main.largs.last(args, want, Main.LFlag.Grep{}, g), Main.largs.last(args, want, Main.LFlag.Since{}, si), Main.largs.last(args, want, Main.LFlag.Until{}, u)} : Main.LRaw}:
  match args:
    case Nil{}:
      match want:
        case None{}:
          Equal.trans(Main.LRaw, fin, Main.LRaw{ws, p, fi, l, au, g, si, u}, Main.LRaw{List.append(&2, String, ws, Main.largs.words(Nil{}, None{})), Main.largs.last(Nil{}, None{}, Main.LFlag.Path{}, p), Main.largs.fields(Nil{}, None{}, fi), Main.largs.last(Nil{}, None{}, Main.LFlag.Limit{}, l), Main.largs.last(Nil{}, None{}, Main.LFlag.Author{}, au), Main.largs.last(Nil{}, None{}, Main.LFlag.Grep{}, g), Main.largs.last(Nil{}, None{}, Main.LFlag.Since{}, si), Main.largs.last(Nil{}, None{}, Main.LFlag.Until{}, u)},
            Equal.sym(Main.LRaw, Main.LRaw{ws, p, fi, l, au, g, si, u}, fin, done_eq_r(Main.LRaw{ws, p, fi, l, au, g, si, u}, fin, e)),
            Equal.cong(List<&2, String>, Main.LRaw, x => Main.LRaw{x, p, fi, l, au, g, si, u}, ws, List.append(&2, String, ws, Nil{}), Equal.sym(List<&2, String>, List.append(&2, String, ws, Nil{}), ws, B.lapp_nil(ws))))
        case Some{f}:
          Empty.absurd({fin == Main.LRaw{List.append(&2, String, ws, Main.largs.words(Nil{}, Some{f})), Main.largs.last(Nil{}, Some{f}, Main.LFlag.Path{}, p), Main.largs.fields(Nil{}, Some{f}, fi), Main.largs.last(Nil{}, Some{f}, Main.LFlag.Limit{}, l), Main.largs.last(Nil{}, Some{f}, Main.LFlag.Author{}, au), Main.largs.last(Nil{}, Some{f}, Main.LFlag.Grep{}, g), Main.largs.last(Nil{}, Some{f}, Main.LFlag.Since{}, si), Main.largs.last(Nil{}, Some{f}, Main.LFlag.Until{}, u)} : Main.LRaw}, B.fail_done_s(Main.LRaw, "`" ++ Main.flag.name(f) ++ "` wants a value", fin, e))
    case +w <> +rest:
      match want:
        case None{}:
          flagged(Main.log.flag(w), ws, w, rest, p, fi, l, au, g, si, u, fin, e, w2 => ws2 => p2 => fi2 => l2 => au2 => g2 => si2 => u2 => h => run_ok(rest, w2, ws2, p2, fi2, l2, au2, g2, si2, u2, fin, h))
        case Some{gf}:
          match gf:
            case Main.LFlag.Limit{}:
              valued_limit(Main.value.check(Main.LFlag.Limit{}, w), w, rest, ws, p, fi, l, au, g, si, u, fin, e, w2 => ws2 => p2 => fi2 => l2 => au2 => g2 => si2 => u2 => h => run_ok(rest, w2, ws2, p2, fi2, l2, au2, g2, si2, u2, fin, h))
            case Main.LFlag.Author{}:
              run_ok(rest, None{}, ws, p, fi, l, Some{w}, g, si, u, fin, e)
            case Main.LFlag.Grep{}:
              run_ok(rest, None{}, ws, p, fi, l, au, Some{w}, si, u, fin, e)
            case Main.LFlag.Since{}:
              valued_since(Main.value.check(Main.LFlag.Since{}, w), w, rest, ws, p, fi, l, au, g, si, u, fin, e, w2 => ws2 => p2 => fi2 => l2 => au2 => g2 => si2 => u2 => h => run_ok(rest, w2, ws2, p2, fi2, l2, au2, g2, si2, u2, fin, h))
            case Main.LFlag.Until{}:
              valued_until(Main.value.check(Main.LFlag.Until{}, w), w, rest, ws, p, fi, l, au, g, si, u, fin, e, w2 => ws2 => p2 => fi2 => l2 => au2 => g2 => si2 => u2 => h => run_ok(rest, w2, ws2, p2, fi2, l2, au2, g2, si2, u2, fin, h))
            case Main.LFlag.Path{}:
              run_ok(rest, None{}, ws, Some{w}, fi, l, au, g, si, u, fin, e)
            case Main.LFlag.Fields{}:
              run_ok(rest, None{}, ws, p, fi, l, au, g, si, u, fin, e)
            case Main.LFlag.Other{}:
              run_ok(rest, None{}, ws, p, fi, l, au, g, si, u, fin, e)
            case Main.LFlag.Word{}:
              run_ok(rest, None{}, ws, p, fi, l, au, g, si, u, fin, e)

def asked_bind(+args: List<&2, String>, r: Result<&2, &2, String, Main.LRaw>, +er: {Main.raw.end(Main.raw.run(args, Main.LRead{Done{Main.LRaw{Nil{}, None{}, False{}, None{}, None{}, None{}, None{}, None{}}}, None{}})) == r : Result<&2, &2, String, Main.LRaw>}, +a: Main.Asked, e: {Result.bind(&2, &2, String, Main.LRaw, Main.Asked, r, x => Main.asked.of(x)) == Done{a} : Result<&2, &2, String, Main.Asked>}) -> {Main.asked.of(Main.largs.raw(args)) == Done{a} : Result<&2, &2, String, Main.Asked>}:
  match r:
    case Fail{x}:
      Empty.absurd({Main.asked.of(Main.largs.raw(args)) == Done{a} : Result<&2, &2, String, Main.Asked>}, B.fail_done_s(Main.Asked, x, a, e))
    case Done{+x}:
      +rr = run_ok(args, None{}, Nil{}, None{}, False{}, None{}, None{}, None{}, None{}, None{}, x, er)
      %rr : {Main.asked.of(_) == Done{a} : Result<&2, &2, String, Main.Asked>}
      e

# `log` reads its arguments as their plain reading says.
def args_said(+args: List<&2, String>, +a: Main.Asked, e: {Main.asked(args) == Done{a} : Result<&2, &2, String, Main.Asked>}) -> {Main.asked.of(Main.largs.raw(args)) == Done{a} : Result<&2, &2, String, Main.Asked>}:
  asked_bind(args, Main.raw.end(Main.raw.run(args, Main.LRead{Done{Main.LRaw{Nil{}, None{}, False{}, None{}, None{}, None{}, None{}, None{}}}, None{}})), {==}, a, e)
