# What `status` asks of the store. It reads its words as they say — the
# word after a flag its value, the last `--onto` counting, each `--merge`
# in order — and every revision it joins is one the store holds: what
# `--onto` and each `--merge` resolve to, and the head where it is taken,
# sorted and each once.
import Base
import ./commands.bend as Main
import ./sort_lemmas.bend as SortL
import ./blamed_lemmas.bend as B
import ./revision.bend as Rev
import ./bookmark.bend as Bm
import ./anchor_lemmas.bend as AL
import ./composition_lemmas.bend as Comp

# Its words
# ---------

def done_cmd(-a: Main.StatusCmd, -b: Main.StatusCmd, h: {Done{a} == Done{b} : Result<&2, &2, Main.Refused, Main.StatusCmd>}) -> {a == b : Main.StatusCmd}:
  B.done_eq(Main.StatusCmd, a, b, h)

def args_go(args: List<&2, String>, +onto: Maybe<&2, String>, +acc: List<&2, String>, k: Main.SWord, +cmd: Main.StatusCmd, e: {Main.status.args.go(args, onto, acc, k) == Done{cmd} : Result<&2, &2, Main.Refused, Main.StatusCmd>}) -> {cmd == Main.StatusCmd{Main.sargs.onto(args, onto, k), List.append(&2, String, acc, Main.sargs.merges(args, k))} : Main.StatusCmd}:
  match args k:
    case Nil{} _:
      %done_cmd(Main.StatusCmd{onto, acc}, cmd, e) : {_ == Main.StatusCmd{onto, List.append(&2, String, acc, Nil{})} : Main.StatusCmd}
      %Equal.sym(List<&2, String>, List.append(&2, String, acc, Nil{}), acc, SortL.lapp_nil(String, acc)) : {Main.StatusCmd{onto, acc} == Main.StatusCmd{onto, _} : Main.StatusCmd}
      {==}
    case +w <> Nil{} Main.SWord.Onto{}:
      Empty.absurd({cmd == Main.StatusCmd{Main.sargs.onto([w], onto, Main.SWord.Onto{}), List.append(&2, String, acc, Main.sargs.merges([w], Main.SWord.Onto{}))} : Main.StatusCmd}, B.fail_done(Main.StatusCmd, Main.Refused{2, "`--onto` wants a value"}, cmd, e))
    case w <> +v <> +rest Main.SWord.Onto{}:
      args_go(rest, Some{v}, acc, Main.sword(rest), cmd, e)
    case +w <> Nil{} Main.SWord.Merge{}:
      Empty.absurd({cmd == Main.StatusCmd{Main.sargs.onto([w], onto, Main.SWord.Merge{}), List.append(&2, String, acc, Main.sargs.merges([w], Main.SWord.Merge{}))} : Main.StatusCmd}, B.fail_done(Main.StatusCmd, Main.Refused{2, "`--merge` wants a value"}, cmd, e))
    case w <> +v <> +rest Main.SWord.Merge{}:
      Equal.trans(Main.StatusCmd, cmd, Main.StatusCmd{Main.sargs.onto(rest, onto, Main.sword(rest)), List.append(&2, String, List.append(&2, String, acc, [v]), Main.sargs.merges(rest, Main.sword(rest)))}, Main.StatusCmd{Main.sargs.onto(rest, onto, Main.sword(rest)), List.append(&2, String, acc, v <> Main.sargs.merges(rest, Main.sword(rest)))},
        args_go(rest, onto, List.append(&2, String, acc, [v]), Main.sword(rest), cmd, e),
        Equal.cong(List<&2, String>, Main.StatusCmd, x => Main.StatusCmd{Main.sargs.onto(rest, onto, Main.sword(rest)), x}, List.append(&2, String, List.append(&2, String, acc, [v]), Main.sargs.merges(rest, Main.sword(rest))), List.append(&2, String, acc, v <> Main.sargs.merges(rest, Main.sword(rest))), SortL.app_assoc(String, acc, [v], Main.sargs.merges(rest, Main.sword(rest)))))
    case +w <> Nil{} Main.SWord.Other{}:
      Empty.absurd({cmd == Main.StatusCmd{Main.sargs.onto([w], onto, Main.SWord.Other{}), List.append(&2, String, acc, Main.sargs.merges([w], Main.SWord.Other{}))} : Main.StatusCmd}, B.fail_done(Main.StatusCmd, Main.Refused{2, "`" ++ w ++ "` is not an argument `status` takes"}, cmd, e))
    case +w <> +v <> +rest Main.SWord.Other{}:
      Empty.absurd({cmd == Main.StatusCmd{Main.sargs.onto(w <> v <> rest, onto, Main.SWord.Other{}), List.append(&2, String, acc, Main.sargs.merges(w <> v <> rest, Main.SWord.Other{}))} : Main.StatusCmd}, B.fail_done(Main.StatusCmd, Main.Refused{2, "`" ++ w ++ "` is not an argument `status` takes"}, cmd, e))

# `status` reads its words as they say.
def args_said(+args: List<&2, String>, +cmd: Main.StatusCmd, e: {Main.status.args.r(args) == Done{cmd} : Result<&2, &2, Main.Refused, Main.StatusCmd>}) -> {cmd == Main.StatusCmd{Main.sargs.onto(args, None{}, Main.sword(args)), Main.sargs.merges(args, Main.sword(args))} : Main.StatusCmd}:
  args_go(args, None{}, Nil{}, Main.sword(args), cmd, e)

# Sorting keeps what every item has
# ---------------------------------

def ah_app(+ids: List<&2, String>, +xs: List<&2, String>, +ys: List<&2, String>, +hx: {Main.all_held(ids, xs) == True{} : Bool}, hy: {Main.all_held(ids, ys) == True{} : Bool}) -> {Main.all_held(ids, List.append(&2, String, xs, ys)) == True{} : Bool}:
  match xs:
    case Nil{}:
      hy
    case +x <> +rest:
      AL.and_intro(Rev.member(ids, x), Main.all_held(ids, List.append(&2, String, rest, ys)), Comp.and_left(Rev.member(ids, x), Main.all_held(ids, rest), hx),
        ah_app(ids, rest, ys, Comp.and_right(Rev.member(ids, x), Main.all_held(ids, rest), hx), hy))

def ah_rev(+ids: List<&2, String>, +xs: List<&2, String>, +acc: List<&2, String>, +hx: {Main.all_held(ids, xs) == True{} : Bool}, hacc: {Main.all_held(ids, acc) == True{} : Bool}) -> {Main.all_held(ids, List.reverse.go(&2, String, xs, acc)) == True{} : Bool}:
  match xs:
    case Nil{}:
      hacc
    case +x <> +rest:
      ah_rev(ids, rest, x <> acc, Comp.and_right(Rev.member(ids, x), Main.all_held(ids, rest), hx),
        AL.and_intro(Rev.member(ids, x), Main.all_held(ids, acc), Comp.and_left(Rev.member(ids, x), Main.all_held(ids, rest), hx), hacc))

def ah_step(~le: String -> String -> Bool, +ids: List<&2, String>, b: Bool, +x: String, +xt: List<&2, String>, +y: String, +yt: List<&2, String>, +acc: List<&2, String>, +f: Nat, +hx: {Main.all_held(ids, x <> xt) == True{} : Bool}, +hy: {Main.all_held(ids, y <> yt) == True{} : Bool}, +hacc: {Main.all_held(ids, acc) == True{} : Bool}, ih: @acc2: List<&2, String> -> @xs2: List<&2, String> -> @ys2: List<&2, String> -> {Main.all_held(ids, acc2) == True{} : Bool} -> {Main.all_held(ids, xs2) == True{} : Bool} -> {Main.all_held(ids, ys2) == True{} : Bool} -> {Main.all_held(ids, List.merge.go(~String, ~le, f, (acc2, xs2, ys2))) == True{} : Bool}) -> {Main.all_held(ids, List.merge.go(~String, ~le, f, List.merge.step(String, acc, x, xt, y, yt, b))) == True{} : Bool}:
  match b:
    case True{}:
      ih(x <> acc, xt, y <> yt, AL.and_intro(Rev.member(ids, x), Main.all_held(ids, acc), Comp.and_left(Rev.member(ids, x), Main.all_held(ids, xt), hx), hacc), Comp.and_right(Rev.member(ids, x), Main.all_held(ids, xt), hx), hy)
    case False{}:
      ih(y <> acc, x <> xt, yt, AL.and_intro(Rev.member(ids, y), Main.all_held(ids, acc), Comp.and_left(Rev.member(ids, y), Main.all_held(ids, yt), hy), hacc), hx, Comp.and_right(Rev.member(ids, y), Main.all_held(ids, yt), hy))

def ah_merge(~le: String -> String -> Bool, +ids: List<&2, String>, fuel: Nat, +acc: List<&2, String>, +xs: List<&2, String>, +ys: List<&2, String>, +hacc: {Main.all_held(ids, acc) == True{} : Bool}, +hx: {Main.all_held(ids, xs) == True{} : Bool}, +hy: {Main.all_held(ids, ys) == True{} : Bool}) -> {Main.all_held(ids, List.merge.go(~String, ~le, fuel, (acc, xs, ys))) == True{} : Bool}:
  match fuel:
    case 0n:
      ah_rev(ids, acc, List.append(&2, String, xs, ys), hacc, ah_app(ids, xs, ys, hx, hy))
    case 1n++f:
      match xs ys:
        case Nil{} Nil{}:
          ah_rev(ids, acc, Nil{}, hacc, {==})
        case Nil{} +y <> +yt:
          ah_rev(ids, acc, y <> yt, hacc, hy)
        case +x <> +xt Nil{}:
          ah_rev(ids, acc, x <> xt, hacc, hx)
        case +x <> +xt +y <> +yt:
          ah_step(~le, ids, le(x, y), x, xt, y, yt, acc, f, hx, hy, hacc, a2 => x2 => y2 => h1 => h2 => h3 => ah_merge(~le, ids, f, a2, x2, y2, h1, h2, h3))

def allruns(+ids: List<&2, String>, +runs: List<&2, List<&2, String>>) -> Bool:
  match runs:
    case Nil{}:
      True{}
    case r <> rest:
      Bool.and(Main.all_held(ids, r), allruns(ids, rest))

def ah_concat(+ids: List<&2, String>, +runs: List<&2, List<&2, String>>, +h: {allruns(ids, runs) == True{} : Bool}) -> {Main.all_held(ids, List.concat(&2, String, runs)) == True{} : Bool}:
  match runs:
    case Nil{}:
      {==}
    case +r <> +rest:
      ah_app(ids, r, List.concat(&2, String, rest), Comp.and_left(Main.all_held(ids, r), allruns(ids, rest), h), ah_concat(ids, rest, Comp.and_right(Main.all_held(ids, r), allruns(ids, rest), h)))

def ah_pass(~le: String -> String -> Bool, +ids: List<&2, String>, +n: Nat, +runs: List<&2, List<&2, String>>, +h: {allruns(ids, runs) == True{} : Bool}) -> {allruns(ids, List.sort.pass(~String, ~le, n, runs)) == True{} : Bool}:
  match runs:
    case Nil{}:
      {==}
    case r <> Nil{}:
      h
    case +r1 <> +r2 <> +rest:
      AL.and_intro(Main.all_held(ids, List.merge.go(~String, ~le, n, (Nil{}, r1, r2))), allruns(ids, List.sort.pass(~String, ~le, n, rest)),
        ah_merge(~le, ids, n, Nil{}, r1, r2, {==}, Comp.and_left(Main.all_held(ids, r1), allruns(ids, r2 <> rest), h), Comp.and_left(Main.all_held(ids, r2), allruns(ids, rest), Comp.and_right(Main.all_held(ids, r1), allruns(ids, r2 <> rest), h))),
        ah_pass(~le, ids, n, rest, Comp.and_right(Main.all_held(ids, r2), allruns(ids, rest), Comp.and_right(Main.all_held(ids, r1), allruns(ids, r2 <> rest), h))))

def ah_go(~le: String -> String -> Bool, +ids: List<&2, String>, fuel: Nat, +n: Nat, +runs: List<&2, List<&2, String>>, +h: {allruns(ids, runs) == True{} : Bool}) -> {Main.all_held(ids, List.sort.go(~String, ~le, fuel, n, runs)) == True{} : Bool}:
  match fuel:
    case 0n:
      ah_concat(ids, runs, h)
    case 1n+f:
      match runs:
        case Nil{}:
          {==}
        case +r <> Nil{}:
          Comp.and_left(Main.all_held(ids, r), True{}, h)
        case +r1 <> +r2 <> +rest:
          ah_go(~le, ids, f, n, List.sort.pass(~String, ~le, n, r1 <> r2 <> rest), ah_pass(~le, ids, n, r1 <> r2 <> rest, h))

def ah_runs(+ids: List<&2, String>, +xs: List<&2, String>, +h: {Main.all_held(ids, xs) == True{} : Bool}) -> {allruns(ids, List.sort.runs(String, xs)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      AL.and_intro(Main.all_held(ids, [x]), allruns(ids, List.sort.runs(String, rest)),
        AL.and_intro(Rev.member(ids, x), True{}, Comp.and_left(Rev.member(ids, x), Main.all_held(ids, rest), h), {==}),
        ah_runs(ids, rest, Comp.and_right(Rev.member(ids, x), Main.all_held(ids, rest), h)))

# A sort by any order returns only what it was given.
def ah_sort(~le: String -> String -> Bool, +ids: List<&2, String>, +xs: List<&2, String>, +h: {Main.all_held(ids, xs) == True{} : Bool}) -> {Main.all_held(ids, List.sort(~String, ~le, xs)) == True{} : Bool}:
  ah_go(~le, ids, List.length(&2, String, xs), List.length(&2, String, xs), List.sort.runs(String, xs), ah_runs(ids, xs, h))

def keep_ok(+ids: List<&2, String>, +a: String, +rest: List<&2, String>, same: Bool, ha: {Rev.member(ids, a) == True{} : Bool}, hr: {Main.all_held(ids, rest) == True{} : Bool}) -> {Main.all_held(ids, Main.distinct.keep(a, rest, same)) == True{} : Bool}:
  match same:
    case True{}:
      hr
    case False{}:
      AL.and_intro(Rev.member(ids, a), Main.all_held(ids, rest), ha, hr)

def ah_distinct(+ids: List<&2, String>, +xs: List<&2, String>, +h: {Main.all_held(ids, xs) == True{} : Bool}) -> {Main.all_held(ids, Main.distinct(xs)) == True{} : Bool}:
  match xs:
    case Nil{}:
      h
    case a <> Nil{}:
      h
    case +a <> +b <> +rest:
      keep_ok(ids, a, Main.distinct(b <> rest), String.eq(a, b), Comp.and_left(Rev.member(ids, a), Main.all_held(ids, b <> rest), h),
        ah_distinct(ids, b <> rest, Comp.and_right(Rev.member(ids, a), Main.all_held(ids, b <> rest), h)))

# What it joins
# -------------

def done_list(-a: List<&2, String>, -b: List<&2, String>, h: {Done{a} == Done{b} : Result<&2, &2, Main.Refused, List<&2, String>>}) -> {a == b : List<&2, String>}:
  B.done_eq(List<&2, String>, a, b, h)

def one_held(+ids: List<&2, String>, +id: String, h: {Rev.member(ids, id) == True{} : Bool}) -> {Main.all_held(ids, [id]) == True{} : Bool}:
  AL.and_intro(Rev.member(ids, id), True{}, h, {==})

def onto_bind(+fs: List<&2, Main.Full>, +bs: List<&2, Bm.Bookmark>, +t: String, r: Result<&2, &2, Main.Refused, Main.Full>, +er: {Main.resolved.r(fs, bs, t) == r : Result<&2, &2, Main.Refused, Main.Full>}, +first: List<&2, String>, e: {Result.bind(&2, &2, Main.Refused, Main.Full, List<&2, String>, r, f => Done{[Main.id_of(f)]}) == Done{first} : Result<&2, &2, Main.Refused, List<&2, String>>}) -> {Main.all_held(Main.ids(fs), first) == True{} : Bool}:
  match r:
    case Fail{x}:
      Empty.absurd({Main.all_held(Main.ids(fs), first) == True{} : Bool}, B.fail_done(List<&2, String>, x, first, e))
    case Done{+f}:
      %done_list([Main.id_of(f)], first, e) : {Main.all_held(Main.ids(fs), _) == True{} : Bool}
      one_held(Main.ids(fs), Main.id_of(f), B.resolved_mem(fs, bs, t, f, er))

# What `--onto` names is held.
def onto_held(+fs: List<&2, Main.Full>, +bs: List<&2, Bm.Bookmark>, onto: Maybe<&2, String>, +first: List<&2, String>, e: {Main.status.onto.r(fs, bs, onto) == Done{first} : Result<&2, &2, Main.Refused, List<&2, String>>}) -> {Main.all_held(Main.ids(fs), first) == True{} : Bool}:
  match onto:
    case None{}:
      %done_list(Nil{}, first, e) : {Main.all_held(Main.ids(fs), _) == True{} : Bool}
      {==}
    case Some{+t}:
      onto_bind(fs, bs, t, Main.resolved.r(fs, bs, t), {==}, first, e)

def named_held(+ids: List<&2, String>, +m: String, +id: String, +ps: List<&2, String>, twice: Bool, +hps: {Main.all_held(ids, ps) == True{} : Bool}, +hid: {Rev.member(ids, id) == True{} : Bool}, +more: List<&2, String>, e: {Main.status.named(m, id, ps, twice) == Done{more} : Result<&2, &2, Main.Refused, List<&2, String>>}) -> {Main.all_held(ids, more) == True{} : Bool}:
  match twice:
    case True{}:
      Empty.absurd({Main.all_held(ids, more) == True{} : Bool}, B.fail_done(List<&2, String>, Main.Refused{1, "`" ++ m ++ "` is named twice, and a revision is its own parent exactly never"}, more, e))
    case False{}:
      %done_list(List.append(&2, String, ps, [id]), more, e) : {Main.all_held(ids, _) == True{} : Bool}
      ah_app(ids, ps, [id], hps, one_held(ids, id, hid))

def merged_bind2(+fs: List<&2, Main.Full>, +bs: List<&2, Bm.Bookmark>, +rest: List<&2, String>, +m: String, +f: Main.Full, +ps: List<&2, String>, +hps: {Main.all_held(Main.ids(fs), ps) == True{} : Bool}, r: Result<&2, &2, Main.Refused, List<&2, String>>, +er: {Main.status.named.of(m, f, ps) == r : Result<&2, &2, Main.Refused, List<&2, String>>}, +named: List<&2, String>, e: {Result.bind(&2, &2, Main.Refused, List<&2, String>, List<&2, String>, r, more => Main.status.merged.r(fs, bs, rest, more)) == Done{named} : Result<&2, &2, Main.Refused, List<&2, String>>}, +hf: {Rev.member(Main.ids(fs), Main.id_of(f)) == True{} : Bool}, ih: @more: List<&2, String> -> {Main.all_held(Main.ids(fs), more) == True{} : Bool} -> {Main.status.merged.r(fs, bs, rest, more) == Done{named} : Result<&2, &2, Main.Refused, List<&2, String>>} -> {Main.all_held(Main.ids(fs), named) == True{} : Bool}) -> {Main.all_held(Main.ids(fs), named) == True{} : Bool}:
  match r:
    case Fail{x}:
      Empty.absurd({Main.all_held(Main.ids(fs), named) == True{} : Bool}, B.fail_done(List<&2, String>, x, named, e))
    case Done{+more}:
      ih(more, named_held(Main.ids(fs), m, Main.id_of(f), ps, Rev.member(ps, Main.id_of(f)), hps, hf, more, er), e)

def merged_bind1(+fs: List<&2, Main.Full>, +bs: List<&2, Bm.Bookmark>, +m: String, +rest: List<&2, String>, +ps: List<&2, String>, +hps: {Main.all_held(Main.ids(fs), ps) == True{} : Bool}, r: Result<&2, &2, Main.Refused, Main.Full>, +er: {Main.resolved.r(fs, bs, m) == r : Result<&2, &2, Main.Refused, Main.Full>}, +named: List<&2, String>, e: {Result.bind(&2, &2, Main.Refused, Main.Full, List<&2, String>, r, f => Result.bind(&2, &2, Main.Refused, List<&2, String>, List<&2, String>, Main.status.named.of(m, f, ps), more => Main.status.merged.r(fs, bs, rest, more))) == Done{named} : Result<&2, &2, Main.Refused, List<&2, String>>}, ih: @more: List<&2, String> -> {Main.all_held(Main.ids(fs), more) == True{} : Bool} -> {Main.status.merged.r(fs, bs, rest, more) == Done{named} : Result<&2, &2, Main.Refused, List<&2, String>>} -> {Main.all_held(Main.ids(fs), named) == True{} : Bool}) -> {Main.all_held(Main.ids(fs), named) == True{} : Bool}:
  match r:
    case Fail{x}:
      Empty.absurd({Main.all_held(Main.ids(fs), named) == True{} : Bool}, B.fail_done(List<&2, String>, x, named, e))
    case Done{+f}:
      merged_bind2(fs, bs, rest, m, f, ps, hps, Main.status.named.of(m, f, ps), {==}, named, e, B.resolved_mem(fs, bs, m, f, er), ih)

# Each `--merge` names a held revision, onto held ones.
def merged_held(+fs: List<&2, Main.Full>, +bs: List<&2, Bm.Bookmark>, ms: List<&2, String>, +ps: List<&2, String>, +hps: {Main.all_held(Main.ids(fs), ps) == True{} : Bool}, +named: List<&2, String>, e: {Main.status.merged.r(fs, bs, ms, ps) == Done{named} : Result<&2, &2, Main.Refused, List<&2, String>>}) -> {Main.all_held(Main.ids(fs), named) == True{} : Bool}:
  match ms:
    case Nil{}:
      %done_list(ps, named, e) : {Main.all_held(Main.ids(fs), _) == True{} : Bool}
      hps
    case +m <> +rest:
      merged_bind1(fs, bs, m, rest, ps, hps, Main.resolved.r(fs, bs, m), {==}, named, e, mo => h => e2 => merged_held(fs, bs, rest, mo, h, named, e2))

def with_pick(+ids: List<&2, String>, +n: List<&2, String>, +id: String, b: Bool, +hn: {Main.all_held(ids, n) == True{} : Bool}, +hid: {Rev.member(ids, id) == True{} : Bool}) -> {Main.all_held(ids, Bool.pick(List<&2, String>, b, n, List.append(&2, String, n, [id]))) == True{} : Bool}:
  match b:
    case True{}:
      hn
    case False{}:
      ah_app(ids, n, [id], hn, one_held(ids, id, hid))

def with_held(+fs: List<&2, Main.Full>, h: Maybe<&2, String>, +n: List<&2, String>, +hn: {Main.all_held(Main.ids(fs), n) == True{} : Bool}, hl: {Main.left.ok(fs, h) == True{} : Bool}) -> {Main.all_held(Main.ids(fs), Main.status.with_head(h, n)) == True{} : Bool}:
  match h:
    case None{}:
      hn
    case Some{+id}:
      with_pick(Main.ids(fs), n, id, Rev.member(n, id), hn, hl)

def head_bind(+fs: List<&2, Main.Full>, +bs: List<&2, Bm.Bookmark>, +n: List<&2, String>, +hn: {Main.all_held(Main.ids(fs), n) == True{} : Bool}, r: Result<&2, &2, Main.Refused, Maybe<&2, String>>, +er: {Main.the_head.r(fs, bs, Main.current_heads(Main.history(fs))) == r : Result<&2, &2, Main.Refused, Maybe<&2, String>>}, +all: List<&2, String>, e: {Result.bind(&2, &2, Main.Refused, Maybe<&2, String>, List<&2, String>, r, h => Done{Main.status.with_head(h, n)}) == Done{all} : Result<&2, &2, Main.Refused, List<&2, String>>}) -> {Main.all_held(Main.ids(fs), all) == True{} : Bool}:
  match r:
    case Fail{x}:
      Empty.absurd({Main.all_held(Main.ids(fs), all) == True{} : Bool}, B.fail_done(List<&2, String>, x, all, e))
    case Done{+h}:
      %done_list(Main.status.with_head(h, n), all, e) : {Main.all_held(Main.ids(fs), _) == True{} : Bool}
      with_held(fs, h, n, hn, B.head_left(fs, bs, Main.current_heads(Main.history(fs)), h, er, x => m => B.cur_held(fs, x, m)))

# The head, where it is taken, is held.
def head_held(+fs: List<&2, Main.Full>, +bs: List<&2, Bm.Bookmark>, +n: List<&2, String>, wants: Bool, +hn: {Main.all_held(Main.ids(fs), n) == True{} : Bool}, +all: List<&2, String>, e: {Main.status.head.r(fs, bs, n, wants) == Done{all} : Result<&2, &2, Main.Refused, List<&2, String>>}) -> {Main.all_held(Main.ids(fs), all) == True{} : Bool}:
  match wants:
    case False{}:
      %done_list(n, all, e) : {Main.all_held(Main.ids(fs), _) == True{} : Bool}
      hn
    case True{}:
      head_bind(fs, bs, n, hn, Main.the_head.r(fs, bs, Main.current_heads(Main.history(fs))), {==}, all, e)

def top3(+fs: List<&2, Main.Full>, +bs: List<&2, Bm.Bookmark>, +onto: Maybe<&2, String>, +ms: List<&2, String>, +named: List<&2, String>, +hn: {Main.all_held(Main.ids(fs), named) == True{} : Bool}, r: Result<&2, &2, Main.Refused, List<&2, String>>, +er: {Main.status.head.of(fs, bs, named, ms, onto) == r : Result<&2, &2, Main.Refused, List<&2, String>>}, +ps: List<&2, String>, e: {Result.bind(&2, &2, Main.Refused, List<&2, String>, List<&2, String>, r, all => Done{Main.status.sorted(all)}) == Done{ps} : Result<&2, &2, Main.Refused, List<&2, String>>}) -> {Main.all_held(Main.ids(fs), ps) == True{} : Bool}:
  match r:
    case Fail{x}:
      Empty.absurd({Main.all_held(Main.ids(fs), ps) == True{} : Bool}, B.fail_done(List<&2, String>, x, ps, e))
    case Done{+all}:
      %done_list(Main.status.sorted(all), ps, e) : {Main.all_held(Main.ids(fs), _) == True{} : Bool}
      ah_distinct(Main.ids(fs), List.sort(~String, ~(a => b => String.is_le(a, b)), all),
        ah_sort(~(a => b => String.is_le(a, b)), Main.ids(fs), all, head_held(fs, bs, named, Main.status.wants(named, ms, onto), hn, all, er)))

def top2(+fs: List<&2, Main.Full>, +bs: List<&2, Bm.Bookmark>, +onto: Maybe<&2, String>, +ms: List<&2, String>, +first: List<&2, String>, +hfirst: {Main.all_held(Main.ids(fs), first) == True{} : Bool}, r: Result<&2, &2, Main.Refused, List<&2, String>>, +er: {Main.status.merged.r(fs, bs, ms, first) == r : Result<&2, &2, Main.Refused, List<&2, String>>}, +ps: List<&2, String>, e: {Result.bind(&2, &2, Main.Refused, List<&2, String>, List<&2, String>, r, named => Result.bind(&2, &2, Main.Refused, List<&2, String>, List<&2, String>, Main.status.head.of(fs, bs, named, ms, onto), all => Done{Main.status.sorted(all)})) == Done{ps} : Result<&2, &2, Main.Refused, List<&2, String>>}) -> {Main.all_held(Main.ids(fs), ps) == True{} : Bool}:
  match r:
    case Fail{x}:
      Empty.absurd({Main.all_held(Main.ids(fs), ps) == True{} : Bool}, B.fail_done(List<&2, String>, x, ps, e))
    case Done{+named}:
      top3(fs, bs, onto, ms, named, merged_held(fs, bs, ms, first, hfirst, named, er), Main.status.head.of(fs, bs, named, ms, onto), {==}, ps, e)

def top1(+fs: List<&2, Main.Full>, +bs: List<&2, Bm.Bookmark>, +onto: Maybe<&2, String>, +ms: List<&2, String>, r: Result<&2, &2, Main.Refused, List<&2, String>>, +er: {Main.status.onto.r(fs, bs, onto) == r : Result<&2, &2, Main.Refused, List<&2, String>>}, +ps: List<&2, String>, e: {Result.bind(&2, &2, Main.Refused, List<&2, String>, List<&2, String>, r, first => Result.bind(&2, &2, Main.Refused, List<&2, String>, List<&2, String>, Main.status.merged.r(fs, bs, ms, first), named => Result.bind(&2, &2, Main.Refused, List<&2, String>, List<&2, String>, Main.status.head.of(fs, bs, named, ms, onto), all => Done{Main.status.sorted(all)}))) == Done{ps} : Result<&2, &2, Main.Refused, List<&2, String>>}) -> {Main.all_held(Main.ids(fs), ps) == True{} : Bool}:
  match r:
    case Fail{x}:
      Empty.absurd({Main.all_held(Main.ids(fs), ps) == True{} : Bool}, B.fail_done(List<&2, String>, x, ps, e))
    case Done{+first}:
      top2(fs, bs, onto, ms, first, onto_held(fs, bs, onto, first, er), Main.status.merged.r(fs, bs, ms, first), {==}, ps, e)

# Every revision `status` joins is one the store holds.
def parents_held(+fs: List<&2, Main.Full>, +bs: List<&2, Bm.Bookmark>, +onto: Maybe<&2, String>, +ms: List<&2, String>, +ps: List<&2, String>, e: {Main.status.parents.r(fs, bs, onto, ms) == Done{ps} : Result<&2, &2, Main.Refused, List<&2, String>>}) -> {Main.all_held(Main.ids(fs), ps) == True{} : Bool}:
  top1(fs, bs, onto, ms, Main.status.onto.r(fs, bs, onto), {==}, ps, e)
