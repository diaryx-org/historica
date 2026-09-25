# What the host hashed, read back. `Store.digests` answers the paths it is
# asked a line each, in order: `<digest> <size>`, or `- 0` for a file that
# will not read, as the adapter writes it. `forget` pairs each file of
# `operations/` with its line, and `arrange` each payload with its digest;
# this writes the answer and holds both to reading back what was written.
import Base
import ./store.bend as Store
import ./text.bend as T
import ./forget.bend as Fg
import ./arrange.bend as Arrange
import ./string_lemmas.bend as S
import ./bookmark_lemmas.bend as BmL
import ./composition_lemmas.bend as Comp
import ./anchor_lemmas.bend as AL
import ./host_lemmas.bend as HostL
import ./listed_lemmas.bend as ListedL

# What the host found for one file: its digest and its size, spelled.
def digests.line(s: T.Split) -> String:
  match s:
    case T.Split{d, n}:
      d ++ " " ++ n

def digests.lines(ss: List<&2, T.Split>) -> List<&2, String>:
  match ss:
    case Nil{}:
      Nil{}
    case s <> rest:
      digests.line(s) <> digests.lines(rest)

# The answer, the lines joined as `.join("\n")` joins them.
def digests.answer(ss: List<&2, T.Split>) -> String:
  String.join(digests.lines(ss), "\n")

# A digest is one word, and neither it nor the size holds a newline.
def stats_ok(ss: List<&2, T.Split>) -> Bool:
  match ss:
    case Nil{}:
      True{}
    case T.Split{+d, +n} <> rest:
      Bool.and(Bool.and(Bool.and(HostL.nosep(d, ' '), BmL.nonl(d)), BmL.nonl(n)), stats_ok(rest))

# Each path with the digest and size found for it, in order.
def filed(ps: List<&2, String>, ss: List<&2, T.Split>) -> List<&2, Fg.FgFiled>:
  match ps ss:
    case p <> pr T.Split{d, n} <> sr:
      Fg.Fg.Filed{p, d, n} <> filed(pr, sr)
    case _ _:
      Nil{}

# Each path with the digest found for it, in order.
def digested(ps: List<&2, String>, ss: List<&2, T.Split>) -> List<&2, T.Split>:
  match ps ss:
    case p <> pr T.Split{d, n} <> sr:
      T.Split{p, d} <> digested(pr, sr)
    case _ _:
      Nil{}

def lines_nonl(ss: List<&2, T.Split>, +h: {stats_ok(ss) == True{} : Bool}) -> {HostL.all_nonl(digests.lines(ss)) == True{} : Bool}:
  match ss:
    case Nil{}:
      {==}
    case T.Split{+d, +n} <> +rest:
      +he = Comp.and_left(Bool.and(Bool.and(HostL.nosep(d, ' '), BmL.nonl(d)), BmL.nonl(n)), stats_ok(rest), h)
      AL.and_intro(BmL.nonl(d ++ " " ++ n), HostL.all_nonl(digests.lines(rest)),
        HostL.nonl_app(d, " " ++ n, Comp.and_right(HostL.nosep(d, ' '), BmL.nonl(d), Comp.and_left(Bool.and(HostL.nosep(d, ' '), BmL.nonl(d)), BmL.nonl(n), he)), Comp.and_right(Bool.and(HostL.nosep(d, ' '), BmL.nonl(d)), BmL.nonl(n), he)),
        lines_nonl(rest, Comp.and_right(Bool.and(Bool.and(HostL.nosep(d, ' '), BmL.nonl(d)), BmL.nonl(n)), stats_ok(rest), h)))

def word_of(+d: String, +n: String, +h: {Bool.and(Bool.and(HostL.nosep(d, ' '), BmL.nonl(d)), BmL.nonl(n)) == True{} : Bool}) -> {T.split_once(d ++ " " ++ n) == Some{T.Split{d, n}} : Maybe<&2, T.Split>}:
  ListedL.split_word(d, n, Comp.and_left(HostL.nosep(d, ' '), BmL.nonl(d), Comp.and_left(Bool.and(HostL.nosep(d, ' '), BmL.nonl(d)), BmL.nonl(n), h)))

# `forget` pairs each path with what its line says.
def filed_lines(ps: List<&2, String>, ss: List<&2, T.Split>, +h: {stats_ok(ss) == True{} : Bool}) -> {Fg.filed(ps, digests.lines(ss)) == filed(ps, ss) : List<&2, Fg.FgFiled>}:
  match ps ss:
    case Nil{} _:
      {==}
    case p <> pr Nil{}:
      {==}
    case +p <> +pr T.Split{+d, +n} <> +sr:
      +he = Comp.and_left(Bool.and(Bool.and(HostL.nosep(d, ' '), BmL.nonl(d)), BmL.nonl(n)), stats_ok(sr), h)
      %Equal.sym(Maybe<&2, T.Split>, T.split_once(d ++ " " ++ n), Some{T.Split{d, n}}, word_of(d, n, he)) : {Fg.filed.one(p, _) <> Fg.filed(pr, digests.lines(sr)) == Fg.Fg.Filed{p, d, n} <> filed(pr, sr) : List<&2, Fg.FgFiled>}
      Equal.cong(List<&2, Fg.FgFiled>, List<&2, Fg.FgFiled>, l => Fg.Fg.Filed{p, d, n} <> l, Fg.filed(pr, digests.lines(sr)), filed(pr, sr), filed_lines(pr, sr, Comp.and_right(Bool.and(Bool.and(HostL.nosep(d, ' '), BmL.nonl(d)), BmL.nonl(n)), stats_ok(sr), h)))

# `arrange` takes each payload's digest from its line.
def digested_lines(ps: List<&2, String>, ss: List<&2, T.Split>, +h: {stats_ok(ss) == True{} : Bool}) -> {Arrange.zip.stats(ps, digests.lines(ss)) == digested(ps, ss) : List<&2, T.Split>}:
  match ps ss:
    case Nil{} _:
      {==}
    case p <> pr Nil{}:
      {==}
    case +p <> +pr T.Split{+d, +n} <> +sr:
      +he = Comp.and_left(Bool.and(Bool.and(HostL.nosep(d, ' '), BmL.nonl(d)), BmL.nonl(n)), stats_ok(sr), h)
      %Equal.sym(Maybe<&2, T.Split>, T.split_once(d ++ " " ++ n), Some{T.Split{d, n}}, word_of(d, n, he)) : {T.Split{p, T.word.of(d ++ " " ++ n, _)} <> Arrange.zip.stats(pr, digests.lines(sr)) == T.Split{p, d} <> digested(pr, sr) : List<&2, T.Split>}
      Equal.cong(List<&2, T.Split>, List<&2, T.Split>, l => T.Split{p, d} <> l, Arrange.zip.stats(pr, digests.lines(sr)), digested(pr, sr), digested_lines(pr, sr, Comp.and_right(Bool.and(Bool.and(HostL.nosep(d, ' '), BmL.nonl(d)), BmL.nonl(n)), stats_ok(sr), h)))

# The answer, split into its lines: a line for each file.
def answer_lines(s: T.Split, +rest: List<&2, T.Split>, +h: {stats_ok(s <> rest) == True{} : Bool}) -> {Store.stats.read(digests.answer(s <> rest)) == digests.lines(s <> rest) : List<&2, String>}:
  match s:
    case T.Split{+d, +n}:
      HostL.split_join(d ++ " " ++ n, digests.lines(rest), lines_nonl(T.Split{d, n} <> rest, h))

# `forget_reads_what_the_host_hashed`.
def forget_reads(ss: List<&2, T.Split>, ps: List<&2, String>, +hl: {Nat.is_eq(List.length(&2, String, ps), List.length(&2, T.Split, ss)) == True{} : Bool}, +h: {stats_ok(ss) == True{} : Bool}) -> {Fg.filed(ps, Store.stats.read(digests.answer(ss))) == filed(ps, ss) : List<&2, Fg.FgFiled>}:
  match ss ps:
    case Nil{} Nil{}:
      {==}
    case Nil{} p <> pr:
      Empty.absurd({Fg.filed(p <> pr, Store.stats.read(digests.answer(Nil{}))) == filed(p <> pr, Nil{}) : List<&2, Fg.FgFiled>}, S.false_true(hl))
    case +s <> +rest +ps2:
      %Equal.sym(List<&2, String>, Store.stats.read(digests.answer(s <> rest)), digests.lines(s <> rest), answer_lines(s, rest, h)) : {Fg.filed(ps2, _) == filed(ps2, s <> rest) : List<&2, Fg.FgFiled>}
      filed_lines(ps2, s <> rest, h)

# `arrange_reads_what_the_host_hashed`.
def arrange_reads(ss: List<&2, T.Split>, ps: List<&2, String>, +hl: {Nat.is_eq(List.length(&2, String, ps), List.length(&2, T.Split, ss)) == True{} : Bool}, +h: {stats_ok(ss) == True{} : Bool}) -> {Arrange.zip.stats(ps, Store.stats.read(digests.answer(ss))) == digested(ps, ss) : List<&2, T.Split>}:
  match ss ps:
    case Nil{} Nil{}:
      {==}
    case Nil{} p <> pr:
      Empty.absurd({Arrange.zip.stats(p <> pr, Store.stats.read(digests.answer(Nil{}))) == digested(p <> pr, Nil{}) : List<&2, T.Split>}, S.false_true(hl))
    case +s <> +rest +ps2:
      %Equal.sym(List<&2, String>, Store.stats.read(digests.answer(s <> rest)), digests.lines(s <> rest), answer_lines(s, rest, h)) : {Arrange.zip.stats(ps2, _) == digested(ps2, s <> rest) : List<&2, T.Split>}
      digested_lines(ps2, s <> rest, h)
