# What `status` asks of the store. It reads its words as they say — the
# word after a flag its value, the last `--onto` counting, each `--merge`
# in order — and every revision it joins is one the store holds: what
# `--onto` and each `--merge` resolve to, and the head where it is taken,
# sorted and each once.
#
# And what it says: everything the survey found, in order, each fact,
# refusal, claim and accept on a line of its own naming it; and where work
# is joined, each contest the merge found but a claimed path, once, naming
# its file; against one revision, the tree `files` reads there; it reads
# and replays only files of lines, and believes a digest a statement gives,
# so that only a replay can refuse it; and joining, it compares each file
# with what the parents' readings of it join to, and leaves a file they
# read differently unsettled, whatever the folder holds.
import Base
import ./commands.bend as Main
import ./sort_lemmas.bend as SortL
import ./blamed_lemmas.bend as B
import ./revision.bend as Rev
import ./bookmark.bend as Bm
import ./anchor_lemmas.bend as AL
import ./composition_lemmas.bend as Comp
import ./string_lemmas.bend as S
import ./text.bend as T
import ./survey.bend as Sv
import ./tree.bend as Tree
import ./listing_lemmas.bend as ListL
import ./graph_lemmas.bend as GL
import ./folder.bend as Folder
import ./store.bend as Store
import ./ops.bend as Ops

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

# What it says
# ------------

# A line looked for is found among later lines too: one more line in front
# loses no match, and one expectation fewer is met wherever more were.
def prepend_at(m: Bool, +x: String, +lr: List<&2, String>, +e: Main.Expect, +er: List<&2, Main.Expect>, h: {Main.expect.in(lr, e <> er) == True{} : Bool}, suf: @e2: Main.Expect -> @er2: List<&2, Main.Expect> -> {Main.expect.in(lr, e2 <> er2) == True{} : Bool} -> {Main.expect.in(lr, er2) == True{} : Bool}) -> {Main.expect.go(x <> lr, e <> er, m) == True{} : Bool}:
  match m:
    case True{}:
      suf(e, er, h)
    case False{}:
      h

def prepend(+x: String, +lr: List<&2, String>, es: List<&2, Main.Expect>, h: {Main.expect.in(lr, es) == True{} : Bool}, suf: @e2: Main.Expect -> @er2: List<&2, Main.Expect> -> {Main.expect.in(lr, e2 <> er2) == True{} : Bool} -> {Main.expect.in(lr, er2) == True{} : Bool}) -> {Main.expect.in(x <> lr, es) == True{} : Bool}:
  match es:
    case Nil{}:
      {==}
    case +e <> +er:
      prepend_at(Main.expect.met(x, e), x, lr, e, er, h, suf)

def suffix_at(m: Bool, +l: String, +lr: List<&2, String>, +e: Main.Expect, +er: List<&2, Main.Expect>, h: {Main.expect.go(l <> lr, e <> er, m) == True{} : Bool}, suf: @e2: Main.Expect -> @er2: List<&2, Main.Expect> -> {Main.expect.in(lr, e2 <> er2) == True{} : Bool} -> {Main.expect.in(lr, er2) == True{} : Bool}, suf2: @e2: Main.Expect -> @er2: List<&2, Main.Expect> -> {Main.expect.in(lr, e2 <> er2) == True{} : Bool} -> {Main.expect.in(lr, er2) == True{} : Bool}) -> {Main.expect.in(l <> lr, er) == True{} : Bool}:
  match m:
    case True{}:
      prepend(l, lr, er, h, suf)
    case False{}:
      prepend(l, lr, er, suf2(e, er, h), suf)

def suffix(ls: List<&2, String>, +e: Main.Expect, +er: List<&2, Main.Expect>, h: {Main.expect.in(ls, e <> er) == True{} : Bool}) -> {Main.expect.in(ls, er) == True{} : Bool}:
  match ls:
    case Nil{}:
      Empty.absurd({Main.expect.in(Nil{}, er) == True{} : Bool}, S.false_true(h))
    case +l <> +lr:
      suffix_at(Main.expect.met(l, e), l, lr, e, er, h, e2 => er2 => h2 => suffix(lr, e2, er2, h2), e3 => er3 => h3 => suffix(lr, e3, er3, h3))

# Lines before those that meet every expectation leave them met.
def skip(xs: List<&2, String>, +ls: List<&2, String>, +es: List<&2, Main.Expect>, h: {Main.expect.in(ls, es) == True{} : Bool}) -> {Main.expect.in(List.append(&2, String, xs, ls), es) == True{} : Bool}:
  match xs:
    case Nil{}:
      h
    case +x <> +xr:
      prepend(x, List.append(&2, String, xr, ls), es, skip(xr, ls, es, h), e2 => er2 => h2 => suffix(List.append(&2, String, xr, ls), e2, er2, h2))

def in_nil(ls: List<&2, String>) -> {Main.expect.in(ls, Nil{}) == True{} : Bool}:
  match ls:
    case Nil{}:
      {==}
    case l <> lr:
      {==}

def fact_met(+k: String, +p: String) -> {Main.expect.met(Main.pad(k, 7n) ++ " " ++ p, Main.Expect{k, p}) == True{} : Bool}:
  AL.and_intro(String.starts_with(Main.pad(k, 7n) ++ " " ++ p, k), String.ends_with(Main.pad(k, 7n) ++ " " ++ p, p),
    B.sw_ext(Main.pad(k, 7n), k, " " ++ p, B.sw_ext(k, k, String.repeat(" ", Nat.sub(7n, String.length(k))), B.sw_refl(k))),
    B.ends_pre(Main.pad(k, 7n), " " ++ p, p, B.ends_pre(" ", p, p, B.ends_refl(p))))

# Each fact is said on the line its turn comes to, beginning with its kind
# and ending with its path.
def facts_exact(xs: List<&2, T.Split>, +ls: List<&2, String>, +es: List<&2, Main.Expect>, h: {Main.expect.in(ls, es) == True{} : Bool}) -> {Main.expect.in(List.append(&2, String, Main.facts.said(xs), ls), List.append(&2, Main.Expect, Main.facts.expect(xs), es)) == True{} : Bool}:
  match xs:
    case Nil{}:
      h
    case T.Split{+k, +p} <> +rest:
      %Equal.sym(Bool, Main.expect.met(Main.pad(k, 7n) ++ " " ++ p, Main.Expect{k, p}), True{}, fact_met(k, p)) : {Main.expect.go((Main.pad(k, 7n) ++ " " ++ p) <> List.append(&2, String, Main.facts.said(rest), ls), Main.Expect{k, p} <> List.append(&2, Main.Expect, Main.facts.expect(rest), es), _) == True{} : Bool}
      facts_exact(rest, ls, es, h)

def split_met(+pre: String, +a: String, +mid: String, +b: String, +post: String) -> {Main.expect.met(pre ++ a ++ mid ++ b ++ post, Main.Expect{pre ++ a, SNil{}}) == True{} : Bool}:
  AL.and_intro(String.starts_with(pre ++ a ++ mid ++ b ++ post, pre ++ a), String.ends_with(pre ++ a ++ mid ++ b ++ post, SNil{}),
    ListL.sw_prefix(pre, a ++ mid ++ b ++ post, a, B.sw_ext(a, a, mid ++ b ++ post, B.sw_refl(a))),
    B.sw_nil(String.reverse(pre ++ a ++ mid ++ b ++ post)))

# Each refusal or claim is said on the line its turn comes to, beginning
# with its word and its path.
def splits_exact(+pre: String, +mid: String, +post: String, xs: List<&2, T.Split>, +ls: List<&2, String>, +es: List<&2, Main.Expect>, h: {Main.expect.in(ls, es) == True{} : Bool}) -> {Main.expect.in(List.append(&2, String, Main.splits.said(pre, mid, post, xs), ls), List.append(&2, Main.Expect, Main.splits.expect(pre, xs), es)) == True{} : Bool}:
  match xs:
    case Nil{}:
      h
    case T.Split{+a, +b} <> +rest:
      %Equal.sym(Bool, Main.expect.met(pre ++ a ++ mid ++ b ++ post, Main.Expect{pre ++ a, SNil{}}), True{}, split_met(pre, a, mid, b, post)) : {Main.expect.go((pre ++ a ++ mid ++ b ++ post) <> List.append(&2, String, Main.splits.said(pre, mid, post, rest), ls), Main.Expect{pre ++ a, SNil{}} <> List.append(&2, Main.Expect, Main.splits.expect(pre, rest), es), _) == True{} : Bool}
      splits_exact(pre, mid, post, rest, ls, es, h)

def accept_met(+p: String) -> {Main.expect.met("accept  " ++ p ++ ": selected revisions state different bytes; record with --accept " ++ p, Main.Expect{"accept  " ++ p, p}) == True{} : Bool}:
  AL.and_intro(String.starts_with("accept  " ++ p ++ ": selected revisions state different bytes; record with --accept " ++ p, "accept  " ++ p), String.ends_with("accept  " ++ p ++ ": selected revisions state different bytes; record with --accept " ++ p, p),
    ListL.sw_prefix("accept  ", p ++ ": selected revisions state different bytes; record with --accept " ++ p, p, B.sw_ext(p, p, ": selected revisions state different bytes; record with --accept " ++ p, B.sw_refl(p))),
    B.ends_pre("accept  ", p ++ ": selected revisions state different bytes; record with --accept " ++ p, p, B.ends_pre(p, ": selected revisions state different bytes; record with --accept " ++ p, p, B.ends_pre(": selected revisions state different bytes; record with --accept ", p, p, B.ends_refl(p)))))

# Each accept is said on the line its turn comes to, beginning `accept` and
# its path, and ending with the path again.
def accepts_exact(xs: List<&2, String>, +ls: List<&2, String>, +es: List<&2, Main.Expect>, h: {Main.expect.in(ls, es) == True{} : Bool}) -> {Main.expect.in(List.append(&2, String, Main.accepts.said(xs), ls), List.append(&2, Main.Expect, Main.accepts.expect(xs), es)) == True{} : Bool}:
  match xs:
    case Nil{}:
      h
    case +p <> +rest:
      %Equal.sym(Bool, Main.expect.met("accept  " ++ p ++ ": selected revisions state different bytes; record with --accept " ++ p, Main.Expect{"accept  " ++ p, p}), True{}, accept_met(p)) : {Main.expect.go(("accept  " ++ p ++ ": selected revisions state different bytes; record with --accept " ++ p) <> List.append(&2, String, Main.accepts.said(rest), ls), Main.Expect{"accept  " ++ p, p} <> List.append(&2, Main.Expect, Main.accepts.expect(rest), es), _) == True{} : Bool}
      accepts_exact(rest, ls, es, h)

def accepts_all(+xs: List<&2, String>, +tail: List<&2, String>) -> {Main.expect.in(List.append(&2, String, Main.accepts.said(xs), tail), Main.accepts.expect(xs)) == True{} : Bool}:
  %SortL.lapp_nil(Main.Expect, Main.accepts.expect(xs)) : {Main.expect.in(List.append(&2, String, Main.accepts.said(xs), tail), _) == True{} : Bool}
  accepts_exact(xs, tail, Nil{}, in_nil(tail))

# Everything the survey found is in the report, in order: after the
# revisions the folder is compared with, each fact on a line beginning with
# its kind and ending with its path, then each refusal, claim and accept on
# a line beginning with its word and its path.
def report_says(+fs: List<&2, Main.Full>, +bs: List<&2, Bm.Bookmark>, +ps: List<&2, String>, +cs: List<&2, Tree.Contest>, sv: Sv.Survey) -> {Main.expect.in(Main.status.report(fs, bs, ps, cs, sv), Main.status.expects(sv)) == True{} : Bool}:
  match sv:
    case Sv.Survey{+facts, +refused, +claimed, +accept, +renames}:
      skip(Main.status.position(fs, bs, ps), List.append(&2, String, Main.facts.said(facts), List.append(&2, String, Main.splits.said("refused ", ": ", SNil{}, refused), List.append(&2, String, Main.splits.said("claimed ", ": ", " files claim it; say where each goes with --at", claimed), List.append(&2, String, Main.accepts.said(accept), List.append(&2, String, Main.contests.said(ps, cs), List.append(&2, String, Bool.pick(List<&2, String>, Sv.is_quiet(Sv.Survey{facts, refused, claimed, accept, renames}), ["nothing here differs from what is recorded"], Nil{}), Main.renames.said(renames))))))), List.append(&2, Main.Expect, Main.facts.expect(facts), List.append(&2, Main.Expect, Main.splits.expect("refused ", refused), List.append(&2, Main.Expect, Main.splits.expect("claimed ", claimed), Main.accepts.expect(accept)))),
        facts_exact(facts, List.append(&2, String, Main.splits.said("refused ", ": ", SNil{}, refused), List.append(&2, String, Main.splits.said("claimed ", ": ", " files claim it; say where each goes with --at", claimed), List.append(&2, String, Main.accepts.said(accept), List.append(&2, String, Main.contests.said(ps, cs), List.append(&2, String, Bool.pick(List<&2, String>, Sv.is_quiet(Sv.Survey{facts, refused, claimed, accept, renames}), ["nothing here differs from what is recorded"], Nil{}), Main.renames.said(renames)))))), List.append(&2, Main.Expect, Main.splits.expect("refused ", refused), List.append(&2, Main.Expect, Main.splits.expect("claimed ", claimed), Main.accepts.expect(accept))),
          splits_exact("refused ", ": ", SNil{}, refused, List.append(&2, String, Main.splits.said("claimed ", ": ", " files claim it; say where each goes with --at", claimed), List.append(&2, String, Main.accepts.said(accept), List.append(&2, String, Main.contests.said(ps, cs), List.append(&2, String, Bool.pick(List<&2, String>, Sv.is_quiet(Sv.Survey{facts, refused, claimed, accept, renames}), ["nothing here differs from what is recorded"], Nil{}), Main.renames.said(renames))))), List.append(&2, Main.Expect, Main.splits.expect("claimed ", claimed), Main.accepts.expect(accept)),
            splits_exact("claimed ", ": ", " files claim it; say where each goes with --at", claimed, List.append(&2, String, Main.accepts.said(accept), List.append(&2, String, Main.contests.said(ps, cs), List.append(&2, String, Bool.pick(List<&2, String>, Sv.is_quiet(Sv.Survey{facts, refused, claimed, accept, renames}), ["nothing here differs from what is recorded"], Nil{}), Main.renames.said(renames)))), Main.accepts.expect(accept),
              accepts_all(accept, List.append(&2, String, Main.contests.said(ps, cs), List.append(&2, String, Bool.pick(List<&2, String>, Sv.is_quiet(Sv.Survey{facts, refused, claimed, accept, renames}), ["nothing here differs from what is recorded"], Nil{}), Main.renames.said(renames))))))))

# The contests
# ------------

# A string holds what a string it ends with begins with.
def contains_sw(s: String, p: String, h: {String.starts_with(s, p) == True{} : Bool}) -> {String.contains(s, p) == True{} : Bool}:
  match s p:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{x, xt}:
      Empty.absurd({String.contains(SNil{}, SCon{x, xt}) == True{} : Bool}, S.false_true(h))
    case SCon{c, t} _:
      %Equal.sym(Bool, String.starts_with(SCon{c, t}, p), True{}, h) : {String.contains.if(t, p, _) == True{} : Bool}
      {==}

def contains_if(b: Bool, -t: String, -p: String, ih: {String.contains(t, p) == True{} : Bool}) -> {String.contains.if(t, p, b) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      ih

# What a string holds, anything in front of it holds too.
def contains_after(+a: String, +s: String, +p: String, h: {String.contains(s, p) == True{} : Bool}) -> {String.contains(String.append(a, s), p) == True{} : Bool}:
  match a:
    case SNil{}:
      h
    case SCon{c, t}:
      contains_if(String.starts_with(SCon{c, String.append(t, s)}, p), String.append(t, s), p, contains_after(t, s, p, h))

# A line with the file's abbreviation in it, after `pre`, names it.
def names_at(+pre: String, +k: String, +rest: String) -> {String.contains(String.append(pre, String.append(String.take(k, 8n), rest)), String.take(k, 8n)) == True{} : Bool}:
  contains_after(pre, String.append(String.take(k, 8n), rest), String.take(k, 8n), contains_sw(String.append(String.take(k, 8n), rest), String.take(k, 8n), B.sw_ext(String.take(k, 8n), String.take(k, 8n), rest, B.sw_refl(String.take(k, 8n)))))

# Each contest but a claimed path has a line, in order, naming its file.
def lines_named(cs: List<&2, Tree.Contest>) -> {Main.contests.named(Main.contest.lines(cs), Main.contests.unclaimed(cs)) == True{} : Bool}:
  match cs:
    case Nil{}:
      {==}
    case Tree.Dropped{+f, +by} <> +rest:
      B.and_tt(String.contains("kept " ++ String.take(f, 8n) ++ " : " ++ String.join(Main.ab8(by), ", ") ++ " dropped it, and concurrent work did not", String.take(f, 8n)), Main.contests.named(Main.contest.lines(rest), Main.contests.unclaimed(rest)), names_at("kept ", f, " : " ++ String.join(Main.ab8(by), ", ") ++ " dropped it, and concurrent work did not"), lines_named(rest))
    case Tree.Moved{+f, +cl} <> +rest:
      B.and_tt(String.contains("moved " ++ String.take(f, 8n) ++ Main.lower_of(" to ", cl), String.take(f, 8n)), Main.contests.named(Main.contest.lines(rest), Main.contests.unclaimed(rest)), names_at("moved ", f, Main.lower_of(" to ", cl)), lines_named(rest))
    case Tree.Content{+f, +cl} <> +rest:
      B.and_tt(String.contains(String.take(f, 8n) ++ " was stated whole by " ++ Nat.show(List.length(&2, Tree.Claim, cl)) ++ " concurrent revisions, and bytes do not merge; put the version you mean in the folder", String.take(f, 8n)), Main.contests.named(Main.contest.lines(rest), Main.contests.unclaimed(rest)), names_at("", f, " was stated whole by " ++ Nat.show(List.length(&2, Tree.Claim, cl)) ++ " concurrent revisions, and bytes do not merge; put the version you mean in the folder"), lines_named(rest))
    case Tree.ModeOf{+f, +cl} <> +rest:
      B.and_tt(String.contains(String.take(f, 8n) ++ Main.lower_of(" is ", cl), String.take(f, 8n)), Main.contests.named(Main.contest.lines(rest), Main.contests.unclaimed(rest)), names_at("", f, Main.lower_of(" is ", cl)), lines_named(rest))
    case Tree.TargetOf{+f, +cl} <> +rest:
      B.and_tt(String.contains(String.take(f, 8n) ++ Main.lower_of(" points at ", cl), String.take(f, 8n)), Main.contests.named(Main.contest.lines(rest), Main.contests.unclaimed(rest)), names_at("", f, Main.lower_of(" points at ", cl)), lines_named(rest))
    case Tree.Referenced{+f, +by, +links} <> +rest:
      B.and_tt(String.contains("kept " ++ String.take(f, 8n) ++ " : " ++ String.join(Main.ab8(by), ", ") ++ " dropped it, and " ++ String.join(Main.ab8(links), ", ") ++ " still " ++ Bool.pick(String, Nat.is_eq(List.length(&2, String, links), 1n), "points", "point") ++ " at it", String.take(f, 8n)), Main.contests.named(Main.contest.lines(rest), Main.contests.unclaimed(rest)), names_at("kept ", f, " : " ++ String.join(Main.ab8(by), ", ") ++ " dropped it, and " ++ String.join(Main.ab8(links), ", ") ++ " still " ++ Bool.pick(String, Nat.is_eq(List.length(&2, String, links), 1n), "points", "point") ++ " at it"), lines_named(rest))
    case Tree.Path{p, fs} <> +rest:
      lines_named(rest)

# Where work is joined, `status` says each contest the merge found but a
# claimed path once, in its order, naming the file contested; where one
# revision or none is the position, none.
def contests_said(ps: List<&2, String>, +cs: List<&2, Tree.Contest>) -> {Main.contests.shown(ps, cs, Main.contests.said(ps, cs)) == True{} : Bool}:
  match ps:
    case Nil{}:
      {==}
    case p <> Nil{}:
      {==}
    case p <> q <> rest:
      lines_named(cs)

# The tree it compares with
# -------------------------

def tree_of(+p: String, r: Result<&2, &2, Tree.Fault, Tree.Merged>) -> {Result.map(&2, &2, Main.Refused, Tree.Merged, Tree.Tree(), m => Tree.merged_tree(m), Main.status.tree.of.r(p, r)) == Main.tree.of.r(p, r) : Result<&2, &2, Main.Refused, Tree.Tree()>}:
  match r:
    case Fail{e}:
      {==}
    case Done{m}:
      {==}

# Against one revision, `status` compares the folder with the tree `files`,
# `cat` and `diff` read there, or refuses as they do.
def one_tree(+fs: List<&2, Main.Full>, +p: String) -> {Result.map(&2, &2, Main.Refused, Tree.Merged, Tree.Tree(), m => Tree.merged_tree(m), Main.status.tree.r(fs, [p])) == Main.tree.r(fs, p) : Result<&2, &2, Main.Refused, Tree.Tree()>}:
  tree_of(p, Tree.merge(Main.events_of(Main.ancestry.oldest(fs, p))))

# What it reads
# -------------

# A path is read from the folder only where the position holds a file of
# lines there.
def read_lines(+dg: Map<&2, String>, +bf: Map<&2, String>, h: Main.Here, e: {Main.status.read(dg, bf, h) == True{} : Bool}) -> {Main.status.lines(h) == True{} : Bool}:
  match h:
    case Main.Here{+p, None{}, None{}}:
      Empty.absurd({Main.status.lines(Main.Here{p, None{}, None{}}) == True{} : Bool}, S.false_true(e))
    case Main.Here{+p, None{}, Some{Folder.Found.File{+r, +x, +n}}}:
      Empty.absurd({Main.status.lines(Main.Here{p, None{}, Some{Folder.Found.File{r, x, n}}}) == True{} : Bool}, S.false_true(e))
    case Main.Here{+p, None{}, Some{Folder.Found.Link{+r, +x}}}:
      Empty.absurd({Main.status.lines(Main.Here{p, None{}, Some{Folder.Found.Link{r, x}}}) == True{} : Bool}, S.false_true(e))
    case Main.Here{+p, Some{Tree.Entry{+f, +q, Tree.Lines{}, +y, +g, +m}}, None{}}:
      {==}
    case Main.Here{+p, Some{Tree.Entry{+f, +q, Tree.Lines{}, +y, +g, +m}}, Some{Folder.Found.File{+r, +x, +n}}}:
      {==}
    case Main.Here{+p, Some{Tree.Entry{+f, +q, Tree.Lines{}, +y, +g, +m}}, Some{Folder.Found.Link{+r, +x}}}:
      Empty.absurd({Main.status.lines(Main.Here{p, Some{Tree.Entry{f, q, Tree.Lines{}, y, g, m}}, Some{Folder.Found.Link{r, x}}}) == True{} : Bool}, S.false_true(e))
    case Main.Here{+p, Some{Tree.Entry{+f, +q, Tree.Whole{}, +y, +g, +m}}, None{}}:
      Empty.absurd({Main.status.lines(Main.Here{p, Some{Tree.Entry{f, q, Tree.Whole{}, y, g, m}}, None{}}) == True{} : Bool}, S.false_true(e))
    case Main.Here{+p, Some{Tree.Entry{+f, +q, Tree.Whole{}, +y, +g, +m}}, Some{Folder.Found.File{+r, +x, +n}}}:
      Empty.absurd({Main.status.lines(Main.Here{p, Some{Tree.Entry{f, q, Tree.Whole{}, y, g, m}}, Some{Folder.Found.File{r, x, n}}}) == True{} : Bool}, S.false_true(e))
    case Main.Here{+p, Some{Tree.Entry{+f, +q, Tree.Whole{}, +y, +g, +m}}, Some{Folder.Found.Link{+r, +x}}}:
      Empty.absurd({Main.status.lines(Main.Here{p, Some{Tree.Entry{f, q, Tree.Whole{}, y, g, m}}, Some{Folder.Found.Link{r, x}}}) == True{} : Bool}, S.false_true(e))
    case Main.Here{+p, Some{Tree.Entry{+f, +q, Tree.Link{}, +y, +g, +m}}, None{}}:
      Empty.absurd({Main.status.lines(Main.Here{p, Some{Tree.Entry{f, q, Tree.Link{}, y, g, m}}, None{}}) == True{} : Bool}, S.false_true(e))
    case Main.Here{+p, Some{Tree.Entry{+f, +q, Tree.Link{}, +y, +g, +m}}, Some{Folder.Found.File{+r, +x, +n}}}:
      Empty.absurd({Main.status.lines(Main.Here{p, Some{Tree.Entry{f, q, Tree.Link{}, y, g, m}}, Some{Folder.Found.File{r, x, n}}}) == True{} : Bool}, S.false_true(e))
    case Main.Here{+p, Some{Tree.Entry{+f, +q, Tree.Link{}, +y, +g, +m}}, Some{Folder.Found.Link{+r, +x}}}:
      Empty.absurd({Main.status.lines(Main.Here{p, Some{Tree.Entry{f, q, Tree.Link{}, y, g, m}}, Some{Folder.Found.Link{r, x}}}) == True{} : Bool}, S.false_true(e))

def ah_weak(+y: String, +ys: List<&2, String>, xs: List<&2, String>, +h: {Main.all_held(ys, xs) == True{} : Bool}) -> {Main.all_held(y <> ys, xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      AL.and_intro(Rev.member(y <> ys, x), Main.all_held(y <> ys, rest), GL.member_tail(y, ys, x, Comp.and_left(Rev.member(ys, x), Main.all_held(ys, rest), h)),
        ah_weak(y, ys, rest, Comp.and_right(Rev.member(ys, x), Main.all_held(ys, rest), h)))

def reads_step(r: Bool, l: Bool, +dg: Map<&2, String>, +bf: Map<&2, String>, +h: Main.Here, +rest: List<&2, Main.Here>, er: {Main.status.read(dg, bf, h) == r : Bool}, el: {Main.status.lines(h) == l : Bool}, ih: {Main.all_held(T.map(~Main.Here, ~String, ~(x => Main.here.path(x)), Main.status.lined(rest)), Main.status.reads(dg, bf, rest)) == True{} : Bool}) -> {Main.all_held(T.map(~Main.Here, ~String, ~(x => Main.here.path(x)), Bool.pick(List<&2, Main.Here>, l, h <> Main.status.lined(rest), Main.status.lined(rest))), Rev.keep(r, Main.here.path(h), Main.status.reads(dg, bf, rest))) == True{} : Bool}:
  match r l:
    case True{} True{}:
      AL.and_intro(Rev.member(Main.here.path(h) <> T.map(~Main.Here, ~String, ~(x => Main.here.path(x)), Main.status.lined(rest)), Main.here.path(h)), Main.all_held(Main.here.path(h) <> T.map(~Main.Here, ~String, ~(x => Main.here.path(x)), Main.status.lined(rest)), Main.status.reads(dg, bf, rest)),
        GL.member_head(Main.here.path(h), T.map(~Main.Here, ~String, ~(x => Main.here.path(x)), Main.status.lined(rest))), ah_weak(Main.here.path(h), T.map(~Main.Here, ~String, ~(x => Main.here.path(x)), Main.status.lined(rest)), Main.status.reads(dg, bf, rest), ih))
    case True{} False{}:
      Empty.absurd({Main.all_held(T.map(~Main.Here, ~String, ~(x => Main.here.path(x)), Bool.pick(List<&2, Main.Here>, False{}, h <> Main.status.lined(rest), Main.status.lined(rest))), Main.here.path(h) <> Main.status.reads(dg, bf, rest)) == True{} : Bool}, S.true_false(Equal.trans(Bool, True{}, Main.status.lines(h), False{}, Equal.sym(Bool, Main.status.lines(h), True{}, read_lines(dg, bf, h, er)), el)))
    case False{} True{}:
      ah_weak(Main.here.path(h), T.map(~Main.Here, ~String, ~(x => Main.here.path(x)), Main.status.lined(rest)), Main.status.reads(dg, bf, rest), ih)
    case False{} False{}:
      ih

def reads_lined(+dg: Map<&2, String>, +bf: Map<&2, String>, hs: List<&2, Main.Here>) -> {Main.all_held(T.map(~Main.Here, ~String, ~(x => Main.here.path(x)), Main.status.lined(hs)), Main.status.reads(dg, bf, hs)) == True{} : Bool}:
  match hs:
    case Nil{}:
      {==}
    case +h <> +rest:
      reads_step(Main.status.read(dg, bf, h), Main.status.lines(h), dg, bf, h, rest, {==}, {==}, reads_lined(dg, bf, rest))

def unknown_step(l: Bool, u: Bool, +h: Main.Here, +rest: List<&2, Main.Here>, +eds: List<&2, Store.Doc>, +os: Map<&2, T.Split>, ih: {Main.all_held(T.map(~Main.Here, ~String, ~(x => Main.here.file(x)), Main.status.lined(rest)), Main.status.unknown(eds, os, rest)) == True{} : Bool}) -> {Main.all_held(T.map(~Main.Here, ~String, ~(x => Main.here.file(x)), Bool.pick(List<&2, Main.Here>, l, h <> Main.status.lined(rest), Main.status.lined(rest))), Bool.pick(List<&2, String>, Bool.and(l, u), Main.here.file(h) <> Main.status.unknown(eds, os, rest), Main.status.unknown(eds, os, rest))) == True{} : Bool}:
  match l u:
    case True{} True{}:
      AL.and_intro(Rev.member(Main.here.file(h) <> T.map(~Main.Here, ~String, ~(x => Main.here.file(x)), Main.status.lined(rest)), Main.here.file(h)), Main.all_held(Main.here.file(h) <> T.map(~Main.Here, ~String, ~(x => Main.here.file(x)), Main.status.lined(rest)), Main.status.unknown(eds, os, rest)),
        GL.member_head(Main.here.file(h), T.map(~Main.Here, ~String, ~(x => Main.here.file(x)), Main.status.lined(rest))), ah_weak(Main.here.file(h), T.map(~Main.Here, ~String, ~(x => Main.here.file(x)), Main.status.lined(rest)), Main.status.unknown(eds, os, rest), ih))
    case True{} False{}:
      ah_weak(Main.here.file(h), T.map(~Main.Here, ~String, ~(x => Main.here.file(x)), Main.status.lined(rest)), Main.status.unknown(eds, os, rest), ih)
    case False{} _:
      ih

def unknown_lined(+eds: List<&2, Store.Doc>, +os: Map<&2, T.Split>, hs: List<&2, Main.Here>) -> {Main.all_held(T.map(~Main.Here, ~String, ~(x => Main.here.file(x)), Main.status.lined(hs)), Main.status.unknown(eds, os, hs)) == True{} : Bool}:
  match hs:
    case Nil{}:
      {==}
    case +h <> +rest:
      unknown_step(Main.status.lines(h), Maybe.is_none(&2, String, Main.stated_digest(eds, Main.origin(os, Main.here.file(h)))), h, rest, eds, os, unknown_lined(eds, os, rest))

# `status` reads from the folder, and replays at the position, only files
# of lines the position holds: never a file of bytes or a link.
def reads_only_lines(+dg: Map<&2, String>, +bf: Map<&2, String>, +eds: List<&2, Store.Doc>, +os: Map<&2, T.Split>, +hs: List<&2, Main.Here>) -> {Bool.and(Main.all_held(T.map(~Main.Here, ~String, ~(x => Main.here.path(x)), Main.status.lined(hs)), Main.status.reads(dg, bf, hs)), Main.all_held(T.map(~Main.Here, ~String, ~(x => Main.here.file(x)), Main.status.lined(hs)), Main.status.unknown(eds, os, hs))) == True{} : Bool}:
  AL.and_intro(Main.all_held(T.map(~Main.Here, ~String, ~(x => Main.here.path(x)), Main.status.lined(hs)), Main.status.reads(dg, bf, hs)), Main.all_held(T.map(~Main.Here, ~String, ~(x => Main.here.file(x)), Main.status.lined(hs)), Main.status.unknown(eds, os, hs)), reads_lined(dg, bf, hs), unknown_lined(eds, os, hs))

# What the survey is told
# -----------------------

def or_l(a: Bool, -b: Bool, e: {a == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({Bool.or(False{}, b) == True{} : Bool}, S.false_true(e))

def or_r(a: Bool, -b: Bool, e: {b == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      e

def unsettles_after(xs: List<&2, Sv.Obs>, +ys: List<&2, Sv.Obs>, +path: String, h: {Main.obs.any_unsettles(path, ys) == True{} : Bool}) -> {Main.obs.any_unsettles(path, List.append(&2, Sv.Obs, xs, ys)) == True{} : Bool}:
  match xs:
    case Nil{}:
      h
    case x <> rest:
      or_r(Main.obs.unsettles(path, x), Main.obs.any_unsettles(path, List.append(&2, Sv.Obs, rest, ys)), unsettles_after(rest, ys, path, h))

# After what a mode change says, one observation: what it says is all
# there is to say of an edit or of emptying.
def edits_after_mode(b: Bool, +path: String, +o: Sv.Obs, h: {Main.obs.edits(path, o) == False{} : Bool}) -> {Main.obs.any_edits(path, List.append(&2, Sv.Obs, Bool.pick(List<&2, Sv.Obs>, b, Nil{}, [Sv.Obs.Mode{path}]), [o])) == False{} : Bool}:
  match b:
    case True{}:
      AL.or_false(Main.obs.edits(path, o), False{}, h, {==})
    case False{}:
      AL.or_false(Main.obs.edits(path, o), False{}, h, {==})

def empties_after_mode(b: Bool, +path: String, +o: Sv.Obs, h: {Main.obs.empties(path, o) == False{} : Bool}) -> {Main.obs.any_empties(path, List.append(&2, Sv.Obs, Bool.pick(List<&2, Sv.Obs>, b, Nil{}, [Sv.Obs.Mode{path}]), [o])) == False{} : Bool}:
  match b:
    case True{}:
      AL.or_false(Main.obs.empties(path, o), False{}, h, {==})
    case False{}:
      AL.or_false(Main.obs.empties(path, o), False{}, h, {==})

# A file of lines the parents dispute, with a file in the folder at its
# path, is edited, emptied or refused, whatever its bytes: emptied only
# where it holds none, and edited only where it holds some.
def disputed_file(+path: String, +f: String, +q: String, +y: Maybe<&2, String>, +g: Maybe<&2, Tree.Target>, +m: Tree.Mode, +runs: Bool, text: Bool, empty: Bool) -> {Bool.and(Main.obs.any_unsettles(path, Sv.lines.proposed(path, Tree.Entry{f, q, Tree.Lines{}, y, g, m}, runs, text, empty)), Bool.not(Bool.pick(Bool, empty, Main.obs.any_edits(path, Sv.lines.proposed(path, Tree.Entry{f, q, Tree.Lines{}, y, g, m}, runs, text, empty)), Main.obs.any_empties(path, Sv.lines.proposed(path, Tree.Entry{f, q, Tree.Lines{}, y, g, m}, runs, text, empty))))) == True{} : Bool}:
  match text empty:
    case False{} True{}:
      AL.and_intro(Bool.or(String.eq(path, path), False{}), True{}, or_l(String.eq(path, path), False{}, S.eq_refl(path)), {==})
    case False{} False{}:
      AL.and_intro(Bool.or(String.eq(path, path), False{}), True{}, or_l(String.eq(path, path), False{}, S.eq_refl(path)), {==})
    case True{} True{}:
      AL.and_intro(Main.obs.any_unsettles(path, List.append(&2, Sv.Obs, Sv.mode(path, Tree.Entry{f, q, Tree.Lines{}, y, g, m}, runs), [Sv.Obs.Emptied{path}])), Bool.not(Main.obs.any_edits(path, List.append(&2, Sv.Obs, Sv.mode(path, Tree.Entry{f, q, Tree.Lines{}, y, g, m}, runs), [Sv.Obs.Emptied{path}]))),
        unsettles_after(Sv.mode(path, Tree.Entry{f, q, Tree.Lines{}, y, g, m}, runs), [Sv.Obs.Emptied{path}], path, or_l(String.eq(path, path), False{}, S.eq_refl(path))),
        AL.not_true(Main.obs.any_edits(path, List.append(&2, Sv.Obs, Sv.mode(path, Tree.Entry{f, q, Tree.Lines{}, y, g, m}, runs), [Sv.Obs.Emptied{path}])), edits_after_mode(Tree.mode_eq(Tree.entry_mode(Tree.Entry{f, q, Tree.Lines{}, y, g, m}), Bool.pick(Tree.Mode, runs, Tree.Executable{}, Tree.Plain{})), path, Sv.Obs.Emptied{path}, {==})))
    case True{} False{}:
      AL.and_intro(Main.obs.any_unsettles(path, List.append(&2, Sv.Obs, Sv.mode(path, Tree.Entry{f, q, Tree.Lines{}, y, g, m}, runs), [Sv.Obs.Edited{path}])), Bool.not(Main.obs.any_empties(path, List.append(&2, Sv.Obs, Sv.mode(path, Tree.Entry{f, q, Tree.Lines{}, y, g, m}, runs), [Sv.Obs.Edited{path}]))),
        unsettles_after(Sv.mode(path, Tree.Entry{f, q, Tree.Lines{}, y, g, m}, runs), [Sv.Obs.Edited{path}], path, or_l(String.eq(path, path), False{}, S.eq_refl(path))),
        AL.not_true(Main.obs.any_empties(path, List.append(&2, Sv.Obs, Sv.mode(path, Tree.Entry{f, q, Tree.Lines{}, y, g, m}, runs), [Sv.Obs.Edited{path}])), empties_after_mode(Tree.mode_eq(Tree.entry_mode(Tree.Entry{f, q, Tree.Lines{}, y, g, m}), Bool.pick(Tree.Mode, runs, Tree.Executable{}, Tree.Plain{})), path, Sv.Obs.Edited{path}, {==})))

def disputed_said(b: Bool, eb: {b == True{} : Bool}, +path: String, +f: String, +q: String, +y: Maybe<&2, String>, +g: Maybe<&2, Tree.Target>, +m: Tree.Mode, found: Maybe<&2, Folder.Found>, +dig: String, -bef: Maybe<&2, String>, text: Bool, -shown: Maybe<&2, String>) -> {Main.disputed.said(path, f, found, Sv.seen(Sv.Seen{path, Some{Tree.Entry{f, q, Tree.Lines{}, y, g, m}}, found, dig, Bool.pick(Maybe<&2, String>, b, None{}, bef), text, shown, b})) == True{} : Bool}:
  match b:
    case False{}:
      Empty.absurd({Main.disputed.said(path, f, found, Sv.seen(Sv.Seen{path, Some{Tree.Entry{f, q, Tree.Lines{}, y, g, m}}, found, dig, bef, text, shown, False{}})) == True{} : Bool}, S.false_true(eb))
    case True{}:
      match found:
        case None{}:
          or_l(Bool.and(String.eq(path, path), String.eq(f, f)), False{}, B.and_tt(String.eq(path, path), String.eq(f, f), S.eq_refl(path), S.eq_refl(f)))
        case Some{Folder.Found.Link{q2, +target}}:
          or_l(Bool.and(String.eq(path, path), String.eq(f, f)), Main.obs.any_drops_bare(path, f, Sv.link(path, target, None{}, None{}, True{})), B.and_tt(String.eq(path, path), String.eq(f, f), S.eq_refl(path), S.eq_refl(f)))
        case Some{Folder.Found.File{q2, +runs, n}}:
          disputed_file(path, f, q, y, g, m, runs, text, Nat.is_eq(n, 0n))

# The map gives the file `-`, so the parents are read as disputing it.
def dash(+f: String, +bf: Map<&2, String>, -bf2: Map<&2, String>, h: {Map.get(String, SNil{}, bf, f) == (bf2, "-") : Map<&2, String> & String}) -> {String.eq(Main.stat_of(f, Map.get(String, SNil{}, bf, f)), "-") == True{} : Bool}:
  %Equal.sym(Map<&2, String> & String, Map.get(String, SNil{}, bf, f), (bf2, "-"), h) : {String.eq(Main.stat_of(f, _), "-") == True{} : Bool}
  {==}

# Where the parents leave a file of lines differently, the survey is given
# no digest to settle it by: whatever the folder holds, a file there is
# edited, emptied or refused, emptied only where it holds no bytes and
# edited only where it holds some, and anything else drops it with no
# content.
def disputed(+t: Tree.Tree(), +dg: Map<&2, String>, +bf: Map<&2, String>, -bf2: Map<&2, String>, +reads: Map<&2, List<&2, U32>>, +path: String, +f: String, +q: String, +y: Maybe<&2, String>, +g: Maybe<&2, Tree.Target>, +m: Tree.Mode, found: Maybe<&2, Folder.Found>, h: {Map.get(String, SNil{}, bf, f) == (bf2, "-") : Map<&2, String> & String}) -> {Main.disputed.said(path, f, found, Sv.seen(Main.status.seen(t, dg, bf, reads, Main.Here{path, Some{Tree.Entry{f, q, Tree.Lines{}, y, g, m}}, found}))) == True{} : Bool}:
  disputed_said(String.eq(Main.stat_of(f, Map.get(String, SNil{}, bf, f)), "-"), dash(f, bf, bf2, h), path, f, q, y, g, m, found, Main.status.folder_digest(dg, path), Main.status.before(bf, Some{Tree.Entry{f, q, Tree.Lines{}, y, g, m}}), Folder.is_utf8(Main.bytes_of(path, Map.get(List<&2, U32>, Nil{}, reads, path))), Main.status.shown(t, Some{Tree.Entry{f, q, Tree.Lines{}, y, g, m}}))

# What it believes
# ----------------

def err_of(r: Result<&2, &2, String, Map<&2, String>>, d: String) -> String:
  match r:
    case Fail{x}:
      x
    case Done{m}:
      d

def fail_eq(-x: String, -e: String, h: {Fail{x} == Fail{e} : Result<&2, &2, String, Map<&2, String>>}) -> {x == e : String}:
  Equal.cong(Result<&2, &2, String, Map<&2, String>>, String, r => err_of(r, x), Fail{x}, Fail{e}, h)

def fails_replay(+older: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +left: String, +eds: List<&2, Store.Doc>, +os: Map<&2, T.Split>, +file: String, +rest: List<&2, Main.Here>, +m: Map<&2, String>, +e: String, r: Result<&2, &2, String, List<&2, Ops.Item>>, +er: {Main.content.in(older, ds, left, file) == r : Result<&2, &2, String, List<&2, Ops.Item>>}, e1: {Result.bind(&2, &2, String, String, Map<&2, String>, Result.map(&2, &2, String, List<&2, Ops.Item>, String, items => Ops.state_digest(items), r), d => Main.status.befores.go(older, ds, left, eds, os, rest, Map.set(&2, String, m, file, d))) == Fail{e} : Result<&2, &2, String, Map<&2, String>>}, ih: @m2: Map<&2, String> -> {Main.status.befores.go(older, ds, left, eds, os, rest, m2) == Fail{e} : Result<&2, &2, String, Map<&2, String>>} -> {Main.status.replay_fails(older, ds, left, eds, os, rest, e) == True{} : Bool}) -> {Bool.or(Main.status.fails_as(Main.content.in(older, ds, left, file), e), Main.status.replay_fails(older, ds, left, eds, os, rest, e)) == True{} : Bool}:
  match r:
    case Fail{+x}:
      AL.or_left(Main.status.fails_as(Main.content.in(older, ds, left, file), e), Main.status.replay_fails(older, ds, left, eds, os, rest, e),
        (%Equal.sym(Result<&2, &2, String, List<&2, Ops.Item>>, Main.content.in(older, ds, left, file), Fail{x}, er) : {Main.status.fails_as(_, e) == True{} : Bool}
          (%Equal.sym(String, x, e, fail_eq(x, e, e1)) : {String.eq(_, e) == True{} : Bool}
            S.eq_refl(e))))
    case Done{+items}:
      AL.or_right(Main.status.fails_as(Main.content.in(older, ds, left, file), e), Main.status.replay_fails(older, ds, left, eds, os, rest, e), ih(Map.set(&2, String, m, file, Ops.state_digest(items)), e1))

def fails_digest(st: Maybe<&2, String>, +older: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +left: String, +eds: List<&2, Store.Doc>, +os: Map<&2, T.Split>, +file: String, +rest: List<&2, Main.Here>, +m: Map<&2, String>, +e: String, e1: {Result.bind(&2, &2, String, String, Map<&2, String>, Main.status.digest.of(st, older, ds, left, file), d => Main.status.befores.go(older, ds, left, eds, os, rest, Map.set(&2, String, m, file, d))) == Fail{e} : Result<&2, &2, String, Map<&2, String>>}, ih: @m2: Map<&2, String> -> {Main.status.befores.go(older, ds, left, eds, os, rest, m2) == Fail{e} : Result<&2, &2, String, Map<&2, String>>} -> {Main.status.replay_fails(older, ds, left, eds, os, rest, e) == True{} : Bool}) -> {Bool.or(Main.status.replay_fails.one(older, ds, left, e, st, file), Main.status.replay_fails(older, ds, left, eds, os, rest, e)) == True{} : Bool}:
  match st:
    case Some{+d}:
      AL.or_right(False{}, Main.status.replay_fails(older, ds, left, eds, os, rest, e), ih(Map.set(&2, String, m, file, d), e1))
    case None{}:
      fails_replay(older, ds, left, eds, os, file, rest, m, e, Main.content.in(older, ds, left, file), {==}, e1, ih)

def go_fails(hs: List<&2, Main.Here>, +older: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +left: String, +eds: List<&2, Store.Doc>, +os: Map<&2, T.Split>, +m: Map<&2, String>, +e: String, h: {Main.status.befores.go(older, ds, left, eds, os, hs, m) == Fail{e} : Result<&2, &2, String, Map<&2, String>>}) -> {Main.status.replay_fails(older, ds, left, eds, os, hs, e) == True{} : Bool}:
  match hs:
    case Nil{}:
      Empty.absurd({Main.status.replay_fails(older, ds, left, eds, os, Nil{}, e) == True{} : Bool}, B.fail_done_s(Map<&2, String>, e, m, Equal.sym(Result<&2, &2, String, Map<&2, String>>, Done{m}, Fail{e}, h)))
    case +x <> +rest:
      fails_digest(Main.stated_digest(eds, Main.origin(os, Main.here.file(x))), older, ds, left, eds, os, Main.here.file(x), rest, m, e, h, m2 => h2 => go_fails(rest, older, ds, left, eds, os, m2, e, h2))

# Against one revision, `status` believes a digest a statement gives and
# replays only where none does, so it is refused only where a file of lines
# no statement settles cannot be replayed, and with that refusal.
def believes(+older: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +left: String, +eds: List<&2, Store.Doc>, +os: Map<&2, T.Split>, +hs: List<&2, Main.Here>, +m: Map<&2, String>, +e: String, h: {Main.status.befores(older, ds, left, eds, os, hs, m) == Fail{e} : Result<&2, &2, String, Map<&2, String>>}) -> {Main.status.replay_fails(older, ds, left, eds, os, Main.status.lined(hs), e) == True{} : Bool}:
  go_fails(Main.status.lined(hs), older, ds, left, eds, os, m, e, h)

# Joining
# -------

def done_eq_g(-A: Data, -a: A, -b: A, h: {Done{a} == Done{b} : Result<&2, &2, String, A>}) -> {a == b : A}:
  Equal.cong(Result<&2, &2, String, A>, A, r => Result.default(&2, &2, String, A, r, a), Done{a}, Done{b}, h)

def and_l(a: Bool, -b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      h

def and_r(a: Bool, -b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      Empty.absurd({b == True{} : Bool}, S.false_true(h))

# What the parents mention, read as the plain list of digests mentioned.
def none_somes(rs: List<&2, Maybe<&2, String>>) -> {Main.mentions.none(rs) == List.is_empty(&2, String, Main.somes(rs)) : Bool}:
  match rs:
    case Nil{}:
      {==}
    case None{} <> rest:
      none_somes(rest)
    case Some{x} <> rest:
      {==}

def all_somes(rs: List<&2, Maybe<&2, String>>, +d: String) -> {Main.mentions.all(rs, d) == Main.all_eq(Main.somes(rs), d) : Bool}:
  match rs:
    case Nil{}:
      {==}
    case None{} <> rest:
      all_somes(rest, d)
    case Some{x} <> rest:
      %all_somes(rest, d) : {Bool.and(String.eq(x, d), Main.mentions.all(rest, d)) == Bool.and(String.eq(x, d), _) : Bool}
      {==}

def differ_s(xs: List<&2, String>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case +x <> +rest:
      Bool.or(Bool.not(Main.all_eq(rest, x)), differ_s(rest))

def differ_somes(rs: List<&2, Maybe<&2, String>>) -> {Main.mentions.differ(rs) == differ_s(Main.somes(rs)) : Bool}:
  match rs:
    case Nil{}:
      {==}
    case None{} <> rest:
      differ_somes(rest)
    case Some{+x} <> +rest:
      %all_somes(rest, x) : {Bool.or(Bool.not(Main.mentions.all(rest, x)), Main.mentions.differ(rest)) == Bool.or(Bool.not(_), differ_s(Main.somes(rest))) : Bool}
      %differ_somes(rest) : {Bool.or(Bool.not(Main.mentions.all(rest, x)), Main.mentions.differ(rest)) == Bool.or(Bool.not(Main.mentions.all(rest, x)), _) : Bool}
      {==}

# Digests that all equal one digest do not differ among themselves.
def same_no_differ(xs: List<&2, String>, +d: String, +h: {Main.all_eq(xs, d) == True{} : Bool}) -> {differ_s(xs) == False{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      +hx = and_l(String.eq(x, d), Main.all_eq(rest, d), h)
      +hr = and_r(String.eq(x, d), Main.all_eq(rest, d), h)
      %Equal.sym(String, x, d, S.eq_true(x, d, hx)) : {Bool.or(Bool.not(Main.all_eq(rest, _)), differ_s(rest)) == False{} : Bool}
      %Equal.sym(Bool, Main.all_eq(rest, d), True{}, hr) : {Bool.or(Bool.not(_), differ_s(rest)) == False{} : Bool}
      same_no_differ(rest, d, hr)

def joins_at(b: Bool, +d: String, +rest: List<&2, String>, +eb: {Main.all_eq(rest, d) == b : Bool}) -> {Bool.pick(Bool, Bool.or(Bool.not(b), differ_s(rest)), String.eq(Bool.pick(String, b, d, "-"), "-"), Main.all_eq(d <> rest, Bool.pick(String, b, d, "-"))) == True{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(Bool, differ_s(rest), False{}, same_no_differ(rest, d, eb)) : {Bool.pick(Bool, _, String.eq(d, "-"), Main.all_eq(d <> rest, d)) == True{} : Bool}
      B.and_tt(String.eq(d, d), Main.all_eq(rest, d), S.eq_refl(d), eb)
    case False{}:
      {==}

# The join of a plain list of digests: the empty digest of none, `-` where
# two differ, and otherwise the digest every one is.
def joins_s(s: List<&2, String>) -> {Bool.pick(Bool, List.is_empty(&2, String, s), String.eq(Main.status.agree(s), Sv.EMPTY()), Bool.pick(Bool, differ_s(s), String.eq(Main.status.agree(s), "-"), Main.all_eq(s, Main.status.agree(s)))) == True{} : Bool}:
  match s:
    case Nil{}:
      S.eq_refl(Sv.EMPTY())
    case +d <> +rest:
      joins_at(Main.all_eq(rest, d), d, rest, {==})

# What the parents' readings of a file join to, as the law reads a join.
def joins(+rs: List<&2, Maybe<&2, String>>) -> {Main.joined.as(rs, Main.status.agree(Main.somes(rs))) == True{} : Bool}:
  %Equal.sym(Bool, Main.mentions.none(rs), List.is_empty(&2, String, Main.somes(rs)), none_somes(rs)) : {Bool.pick(Bool, _, String.eq(Main.status.agree(Main.somes(rs)), Sv.EMPTY()), Bool.pick(Bool, Main.mentions.differ(rs), String.eq(Main.status.agree(Main.somes(rs)), "-"), Main.mentions.all(rs, Main.status.agree(Main.somes(rs))))) == True{} : Bool}
  %Equal.sym(Bool, Main.mentions.differ(rs), differ_s(Main.somes(rs)), differ_somes(rs)) : {Bool.pick(Bool, List.is_empty(&2, String, Main.somes(rs)), String.eq(Main.status.agree(Main.somes(rs)), Sv.EMPTY()), Bool.pick(Bool, _, String.eq(Main.status.agree(Main.somes(rs)), "-"), Main.mentions.all(rs, Main.status.agree(Main.somes(rs))))) == True{} : Bool}
  %Equal.sym(Bool, Main.mentions.all(rs, Main.status.agree(Main.somes(rs))), Main.all_eq(Main.somes(rs), Main.status.agree(Main.somes(rs))), all_somes(rs, Main.status.agree(Main.somes(rs)))) : {Bool.pick(Bool, List.is_empty(&2, String, Main.somes(rs)), String.eq(Main.status.agree(Main.somes(rs)), Sv.EMPTY()), Bool.pick(Bool, differ_s(Main.somes(rs)), String.eq(Main.status.agree(Main.somes(rs)), "-"), _)) == True{} : Bool}
  joins_s(Main.somes(rs))

def each_rest_r(+fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +file: String, +x: Maybe<&2, String>, +rest: List<&2, String>, +rs: List<&2, Maybe<&2, String>>, r: Result<&2, &2, String, List<&2, Maybe<&2, String>>>, +er: {Main.status.joined.each(fs, ds, file, rest) == r : Result<&2, &2, String, List<&2, Maybe<&2, String>>>}, h: {Result.bind(&2, &2, String, List<&2, Maybe<&2, String>>, List<&2, Maybe<&2, String>>, r, xs => Done{x <> xs}) == Done{rs} : Result<&2, &2, String, List<&2, Maybe<&2, String>>>}, ih: @r2: List<&2, Maybe<&2, String>> -> {Main.status.joined.each(fs, ds, file, rest) == Done{r2} : Result<&2, &2, String, List<&2, Maybe<&2, String>>>} -> {Main.status.readings(fs, ds, file, rest) == r2 : List<&2, Maybe<&2, String>>}) -> {x <> Main.status.readings(fs, ds, file, rest) == rs : List<&2, Maybe<&2, String>>}:
  match r:
    case Fail{y}:
      Empty.absurd({x <> Main.status.readings(fs, ds, file, rest) == rs : List<&2, Maybe<&2, String>>}, B.fail_done_s(List<&2, Maybe<&2, String>>, y, rs, h))
    case Done{+xs}:
      %Equal.sym(List<&2, Maybe<&2, String>>, Main.status.readings(fs, ds, file, rest), xs, ih(xs, er)) : {x <> _ == rs : List<&2, Maybe<&2, String>>}
      done_eq_g(List<&2, Maybe<&2, String>>, x <> xs, rs, h)

def each_one_r(+fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +file: String, +p: String, +rest: List<&2, String>, +rs: List<&2, Maybe<&2, String>>, r: Result<&2, &2, String, Maybe<&2, String>>, +er: {Main.status.joined.one(fs, ds, file, p) == r : Result<&2, &2, String, Maybe<&2, String>>}, h: {Result.bind(&2, &2, String, Maybe<&2, String>, List<&2, Maybe<&2, String>>, r, x => Result.bind(&2, &2, String, List<&2, Maybe<&2, String>>, List<&2, Maybe<&2, String>>, Main.status.joined.each(fs, ds, file, rest), xs => Done{x <> xs})) == Done{rs} : Result<&2, &2, String, List<&2, Maybe<&2, String>>>}, ih: @r2: List<&2, Maybe<&2, String>> -> {Main.status.joined.each(fs, ds, file, rest) == Done{r2} : Result<&2, &2, String, List<&2, Maybe<&2, String>>>} -> {Main.status.readings(fs, ds, file, rest) == r2 : List<&2, Maybe<&2, String>>}) -> {Main.reading.of(Main.status.joined.one(fs, ds, file, p)) <> Main.status.readings(fs, ds, file, rest) == rs : List<&2, Maybe<&2, String>>}:
  match r:
    case Fail{y}:
      Empty.absurd({Main.reading.of(Main.status.joined.one(fs, ds, file, p)) <> Main.status.readings(fs, ds, file, rest) == rs : List<&2, Maybe<&2, String>>}, B.fail_done_s(List<&2, Maybe<&2, String>>, y, rs, h))
    case Done{+x}:
      %Equal.sym(Result<&2, &2, String, Maybe<&2, String>>, Main.status.joined.one(fs, ds, file, p), Done{x}, er) : {Main.reading.of(_) <> Main.status.readings(fs, ds, file, rest) == rs : List<&2, Maybe<&2, String>>}
      each_rest_r(fs, ds, file, x, rest, rs, Main.status.joined.each(fs, ds, file, rest), {==}, h, ih)

# Reading a file at every parent, where no reading is refused, is reading
# it at each.
def each_readings(ps: List<&2, String>, +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +file: String, +rs: List<&2, Maybe<&2, String>>, h: {Main.status.joined.each(fs, ds, file, ps) == Done{rs} : Result<&2, &2, String, List<&2, Maybe<&2, String>>>}) -> {Main.status.readings(fs, ds, file, ps) == rs : List<&2, Maybe<&2, String>>}:
  match ps:
    case Nil{}:
      done_eq_g(List<&2, Maybe<&2, String>>, Nil{}, rs, h)
    case +p <> +rest:
      each_one_r(fs, ds, file, p, rest, rs, Main.status.joined.one(fs, ds, file, p), {==}, h, r2 => h2 => each_readings(rest, fs, ds, file, r2, h2))

def pairs_later(+fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +ps: List<&2, String>, +x: Main.Here, +rest: List<&2, Main.Here>, +xs: List<&2, T.Split>, +rs: List<&2, Maybe<&2, String>>, r: Result<&2, &2, String, List<&2, T.Split>>, +er2: {Main.status.joined.pairs(fs, ds, ps, rest) == r : Result<&2, &2, String, List<&2, T.Split>>}, +er: {Main.status.joined.each(fs, ds, Main.here.file(x), ps) == Done{rs} : Result<&2, &2, String, List<&2, Maybe<&2, String>>>}, h: {Result.bind(&2, &2, String, List<&2, T.Split>, List<&2, T.Split>, r, later => Done{T.Split{Main.here.file(x), Main.status.agree(Main.somes(rs))} <> later}) == Done{xs} : Result<&2, &2, String, List<&2, T.Split>>}, ih: @ys: List<&2, T.Split> -> {Main.status.joined.pairs(fs, ds, ps, rest) == Done{ys} : Result<&2, &2, String, List<&2, T.Split>>} -> {Main.joined.files(fs, ds, ps, rest, ys) == True{} : Bool}) -> {Main.joined.files(fs, ds, ps, x <> rest, xs) == True{} : Bool}:
  match r:
    case Fail{y}:
      Empty.absurd({Main.joined.files(fs, ds, ps, x <> rest, xs) == True{} : Bool}, B.fail_done_s(List<&2, T.Split>, y, xs, h))
    case Done{+later}:
      %done_eq_g(List<&2, T.Split>, T.Split{Main.here.file(x), Main.status.agree(Main.somes(rs))} <> later, xs, h) : {Main.joined.files(fs, ds, ps, x <> rest, _) == True{} : Bool}
      %Equal.sym(List<&2, Maybe<&2, String>>, Main.status.readings(fs, ds, Main.here.file(x), ps), rs, each_readings(ps, fs, ds, Main.here.file(x), rs, er)) : {Bool.and(String.eq(Main.here.file(x), Main.here.file(x)), Bool.and(Main.joined.as(_, Main.status.agree(Main.somes(rs))), Main.joined.files(fs, ds, ps, rest, later))) == True{} : Bool}
      B.and_tt(String.eq(Main.here.file(x), Main.here.file(x)), Bool.and(Main.joined.as(rs, Main.status.agree(Main.somes(rs))), Main.joined.files(fs, ds, ps, rest, later)), S.eq_refl(Main.here.file(x)),
        B.and_tt(Main.joined.as(rs, Main.status.agree(Main.somes(rs))), Main.joined.files(fs, ds, ps, rest, later), joins(rs), ih(later, er2)))

def pairs_step(+fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +ps: List<&2, String>, +x: Main.Here, +rest: List<&2, Main.Here>, +xs: List<&2, T.Split>, r: Result<&2, &2, String, List<&2, Maybe<&2, String>>>, +er: {Main.status.joined.each(fs, ds, Main.here.file(x), ps) == r : Result<&2, &2, String, List<&2, Maybe<&2, String>>>}, h: {Result.bind(&2, &2, String, List<&2, Maybe<&2, String>>, List<&2, T.Split>, r, ys => Result.bind(&2, &2, String, List<&2, T.Split>, List<&2, T.Split>, Main.status.joined.pairs(fs, ds, ps, rest), later => Done{T.Split{Main.here.file(x), Main.status.agree(Main.somes(ys))} <> later})) == Done{xs} : Result<&2, &2, String, List<&2, T.Split>>}, ih: @ys: List<&2, T.Split> -> {Main.status.joined.pairs(fs, ds, ps, rest) == Done{ys} : Result<&2, &2, String, List<&2, T.Split>>} -> {Main.joined.files(fs, ds, ps, rest, ys) == True{} : Bool}) -> {Main.joined.files(fs, ds, ps, x <> rest, xs) == True{} : Bool}:
  match r:
    case Fail{y}:
      Empty.absurd({Main.joined.files(fs, ds, ps, x <> rest, xs) == True{} : Bool}, B.fail_done_s(List<&2, T.Split>, y, xs, h))
    case Done{+rs}:
      pairs_later(fs, ds, ps, x, rest, xs, rs, Main.status.joined.pairs(fs, ds, ps, rest), {==}, er, h, ih)

# Where several parents are joined, each file compared is paired, in order,
# with what the parents' readings of it join to.
def pairs_files(hs: List<&2, Main.Here>, +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +ps: List<&2, String>, +xs: List<&2, T.Split>, h: {Main.status.joined.pairs(fs, ds, ps, hs) == Done{xs} : Result<&2, &2, String, List<&2, T.Split>>}) -> {Main.joined.files(fs, ds, ps, hs, xs) == True{} : Bool}:
  match hs:
    case Nil{}:
      %done_eq_g(List<&2, T.Split>, Nil{}, xs, h) : {Main.joined.files(fs, ds, ps, Nil{}, _) == True{} : Bool}
      {==}
    case +x <> +rest:
      pairs_step(fs, ds, ps, x, rest, xs, Main.status.joined.each(fs, ds, Main.here.file(x), ps), {==}, h, ys => h2 => pairs_files(rest, fs, ds, ps, ys, h2))
