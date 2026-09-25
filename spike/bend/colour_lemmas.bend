# Colour changes no character of what `diff` prints. Every line is its
# runs; where there is colour, a line replaced one for one has the runs
# that differ marked, and every mark reads as its own line
# (`LAWS.emphasis_marks_its_own_line`), so each line, read as it is printed
# without colour, is the line `diff` prints without colour.
import Base
import ./ops.bend as Ops
import ./text.bend as T
import ./similar.bend as Sim
import ./commands.bend as Main
import ./mark_lemmas.bend as MarkL
import ./composition_lemmas.bend as Comp
import ./string_lemmas.bend as S
import ./blamed_lemmas.bend as B

# The lines as printed without colour.
def plain(ls: List<&2, Main.Painted>) -> List<&2, String>:
  match ls:
    case Nil{}:
      Nil{}
    case l <> rest:
      Main.painted(False{}, l) <> plain(rest)

def map_plain(ls: List<&2, Main.Painted>) -> {T.map(~Main.Painted, ~String, ~(p => Main.painted(False{}, p)), ls) == plain(ls) : List<&2, String>}:
  match ls:
    case Nil{}:
      {==}
    case l <> rest:
      Equal.cong(List<&2, String>, List<&2, String>, x => Main.painted(False{}, l) <> x, T.map(~Main.Painted, ~String, ~(p => Main.painted(False{}, p)), rest), plain(rest), map_plain(rest))

def plain_app(xs: List<&2, Main.Painted>, -ys: List<&2, Main.Painted>) -> {plain(List.append(&2, Main.Painted, xs, ys)) == List.append(&2, String, plain(xs), plain(ys)) : List<&2, String>}:
  match xs:
    case Nil{}:
      {==}
    case x <> rest:
      Equal.cong(List<&2, String>, List<&2, String>, l => Main.painted(False{}, x) <> l, plain(List.append(&2, Main.Painted, rest, ys)), List.append(&2, String, plain(rest), plain(ys)), plain_app(rest, ys))

def app2(-a1: List<&2, String>, -a2: List<&2, String>, -b1: List<&2, String>, -b2: List<&2, String>, ea: {a1 == a2 : List<&2, String>}, eb: {b1 == b2 : List<&2, String>}) -> {List.append(&2, String, a1, b1) == List.append(&2, String, a2, b2) : List<&2, String>}:
  %ea : {List.append(&2, String, a1, b1) == List.append(&2, String, _, b2) : List<&2, String>}
  %eb : {List.append(&2, String, a1, b1) == List.append(&2, String, a1, _) : List<&2, String>}
  {==}

# Two renderings that read alike, each followed by two more that do, read
# alike.
def plain_app2(xs1: List<&2, Main.Painted>, xs2: List<&2, Main.Painted>, -ys1: List<&2, Main.Painted>, -ys2: List<&2, Main.Painted>, ex: {plain(xs1) == plain(xs2) : List<&2, String>}, ey: {plain(ys1) == plain(ys2) : List<&2, String>}) -> {plain(List.append(&2, Main.Painted, xs1, ys1)) == plain(List.append(&2, Main.Painted, xs2, ys2)) : List<&2, String>}:
  Equal.trans(List<&2, String>, plain(List.append(&2, Main.Painted, xs1, ys1)), List.append(&2, String, plain(xs1), plain(ys1)), plain(List.append(&2, Main.Painted, xs2, ys2)),
    plain_app(xs1, ys1),
    Equal.trans(List<&2, String>, List.append(&2, String, plain(xs1), plain(ys1)), List.append(&2, String, plain(xs2), plain(ys2)), plain(List.append(&2, Main.Painted, xs2, ys2)),
      app2(plain(xs1), plain(xs2), plain(ys1), plain(ys2), ex, ey),
      Equal.sym(List<&2, String>, plain(List.append(&2, Main.Painted, xs2, ys2)), List.append(&2, String, plain(xs2), plain(ys2)), plain_app(xs2, ys2))))

# The same lines in front leave two renderings that read alike reading
# alike.
def same_front(xs: List<&2, Main.Painted>, -ys1: List<&2, Main.Painted>, -ys2: List<&2, Main.Painted>, ey: {plain(ys1) == plain(ys2) : List<&2, String>}) -> {plain(List.append(&2, Main.Painted, xs, ys1)) == plain(List.append(&2, Main.Painted, xs, ys2)) : List<&2, String>}:
  match xs:
    case Nil{}:
      ey
    case x <> rest:
      Equal.cong(List<&2, String>, List<&2, String>, l => Main.painted(False{}, x) <> l, plain(List.append(&2, Main.Painted, rest, ys1)), plain(List.append(&2, Main.Painted, rest, ys2)), same_front(rest, ys1, ys2, ey))

def cons_plain(+p: Main.Painted, -l1: List<&2, Main.Painted>, -l2: List<&2, Main.Painted>, e: {plain(l1) == plain(l2) : List<&2, String>}) -> {plain(p <> l1) == plain(p <> l2) : List<&2, String>}:
  Equal.cong(List<&2, String>, List<&2, String>, l => Main.painted(False{}, p) <> l, plain(l1), plain(l2), e)

# One line
# --------

# A line whose mark reads as the line itself reads, without colour, as the
# line unmarked: its sign and its runs are its sign and its text.
def marked_some(+sign: String, +it: Ops.Item, +ps: List<&2, Main.Piece>, h: {Bool.and(String.eq(Main.pieces.text(ps), Ops.shown(it)), Main.laid.changed(sign)) == True{} : Bool}) -> {plain(Main.laid.marked.of(sign, it, ps)) == plain(Main.laid.text(sign, it)) : List<&2, String>}:
  match it:
    case Ops.Item{+x, True{}, +f}:
      Equal.trans(List<&2, String>, [sign ++ Main.pieces.text(ps)], [sign ++ Ops.shown(Ops.Item{x, True{}, f})], [(sign ++ Ops.shown(Ops.Item{x, True{}, f})) ++ SNil{}],
        Equal.cong(String, List<&2, String>, s => [sign ++ s], Main.pieces.text(ps), Ops.shown(Ops.Item{x, True{}, f}),
          S.eq_true(Main.pieces.text(ps), Ops.shown(Ops.Item{x, True{}, f}), Comp.and_left(String.eq(Main.pieces.text(ps), Ops.shown(Ops.Item{x, True{}, f})), Main.laid.changed(sign), h))),
        Equal.cong(String, List<&2, String>, s => [s], sign ++ Ops.shown(Ops.Item{x, True{}, f}), (sign ++ Ops.shown(Ops.Item{x, True{}, f})) ++ SNil{},
          Equal.sym(String, (sign ++ Ops.shown(Ops.Item{x, True{}, f})) ++ SNil{}, sign ++ Ops.shown(Ops.Item{x, True{}, f}), B.app_nil(sign ++ Ops.shown(Ops.Item{x, True{}, f})))))
    case Ops.Item{+x, False{}, +f}:
      Equal.trans(List<&2, String>, [sign ++ Main.pieces.text(ps), "\\ no newline at end of file"], [sign ++ Ops.shown(Ops.Item{x, False{}, f}), "\\ no newline at end of file"], [(sign ++ Ops.shown(Ops.Item{x, False{}, f})) ++ SNil{}, "\\ no newline at end of file"],
        Equal.cong(String, List<&2, String>, s => [sign ++ s, "\\ no newline at end of file"], Main.pieces.text(ps), Ops.shown(Ops.Item{x, False{}, f}),
          S.eq_true(Main.pieces.text(ps), Ops.shown(Ops.Item{x, False{}, f}), Comp.and_left(String.eq(Main.pieces.text(ps), Ops.shown(Ops.Item{x, False{}, f})), Main.laid.changed(sign), h))),
        Equal.cong(String, List<&2, String>, s => [s, "\\ no newline at end of file"], sign ++ Ops.shown(Ops.Item{x, False{}, f}), (sign ++ Ops.shown(Ops.Item{x, False{}, f})) ++ SNil{},
          Equal.sym(String, (sign ++ Ops.shown(Ops.Item{x, False{}, f})) ++ SNil{}, sign ++ Ops.shown(Ops.Item{x, False{}, f}), B.app_nil(sign ++ Ops.shown(Ops.Item{x, False{}, f})))))

# A line whose mark reads as the line itself reads, without colour, as the
# line unmarked: its sign and its runs are its sign and its text.
def marked_fit(+sign: String, +it: Ops.Item, +m: Maybe<&2, List<&2, Main.Piece>>, -b: Nat, -a: Nat, h: {Main.mark.fits(Main.Numbered{Main.Laid{sign, it}, b, a}, m) == True{} : Bool}) -> {plain(Main.laid.marked(sign, it, m)) == plain(Main.laid.text(sign, it)) : List<&2, String>}:
  match m:
    case None{}:
      {==}
    case Some{+ps}:
      marked_some(sign, it, ps, h)

# A hunk's lines
# --------------

# Lines whose marks fit them read, without colour, as the lines unmarked.
def lines_fit(ns: List<&2, Main.Numbered>, ms: List<&2, Maybe<&2, List<&2, Main.Piece>>>, +h: {Main.marks.fit(ns, ms) == True{} : Bool}) -> {plain(Main.hunk.lines(ns, ms)) == plain(Main.hunk.lines(ns, Nil{})) : List<&2, String>}:
  match ns ms:
    case Nil{} Nil{}:
      {==}
    case Nil{} m <> mr:
      {==}
    case Main.Numbered{Main.Laid{+sign, +it}, +b, +a} <> +rest +m <> +mr:
      plain_app2(Main.laid.marked(sign, it, m), Main.laid.text(sign, it), Main.hunk.lines(rest, mr), Main.hunk.lines(rest, Nil{}),
        marked_fit(sign, it, m, b, a, Comp.and_left(Main.mark.fits(Main.Numbered{Main.Laid{sign, it}, b, a}, m), Main.marks.fit(rest, mr), h)),
        lines_fit(rest, mr, Comp.and_right(Main.mark.fits(Main.Numbered{Main.Laid{sign, it}, b, a}, m), Main.marks.fit(rest, mr), h)))
    case n <> rest Nil{}:
      {==}

def hunk_fit(h: Main.Hunk) -> {plain(Main.hunk.shown(True{}, h)) == plain(Main.hunk.shown(False{}, h)) : List<&2, String>}:
  match h:
    case Main.Hunk{+o, +oc, +n, +nc, +ns}:
      cons_plain(Main.hunk.header(o, oc, n, nc), Main.hunk.lines(ns, Main.emph(ns, True{})), Main.hunk.lines(ns, Nil{}),
        lines_fit(ns, Main.emph(ns, True{}), MarkL.emph_fit(ns, True{})))

def hunks_fit(hs: List<&2, Main.Hunk>) -> {plain(Main.hunks.shown(True{}, hs)) == plain(Main.hunks.shown(False{}, hs)) : List<&2, String>}:
  match hs:
    case Nil{}:
      {==}
    case +h <> +rest:
      plain_app2(Main.hunk.shown(True{}, h), Main.hunk.shown(False{}, h), Main.hunks.shown(True{}, rest), Main.hunks.shown(False{}, rest), hunk_fit(h), hunks_fit(rest))

# A file
# ------

def hunks_d(+left: String, +right: String, +before: List<&2, Ops.Item>, d: Maybe<&2, Ops.Doc>) -> {plain(Main.render.hunks(True{}, left, right, before, d)) == plain(Main.render.hunks(False{}, left, right, before, d)) : List<&2, String>}:
  match d:
    case None{}:
      {==}
    case Some{+doc}:
      cons_plain(Main.meta("--- " ++ left), Main.meta("+++ " ++ right) <> Main.hunks(True{}, Main.laid(before, doc)), Main.meta("+++ " ++ right) <> Main.hunks(False{}, Main.laid(before, doc)),
        cons_plain(Main.meta("+++ " ++ right), Main.hunks(True{}, Main.laid(before, doc)), Main.hunks(False{}, Main.laid(before, doc)),
          hunks_fit(Main.hunks.made(Main.laid(before, doc)))))

def content_fit(+left: String, +right: String, before: Maybe<&2, List<&2, Ops.Item>>, after: Maybe<&2, List<&2, Ops.Item>>, +whole: String) -> {plain(Main.render.content(True{}, left, right, before, after, whole)) == plain(Main.render.content(False{}, left, right, before, after, whole)) : List<&2, String>}:
  match before after:
    case Some{+b} Some{+a}:
      hunks_d(left, right, b, Sim.diff(b, a))
    case Some{b} None{}:
      {==}
    case None{} Some{a}:
      {==}
    case None{} None{}:
      {==}

# What `diff` prints of one file reads, without colour, as it does with.
def render_fit(c: Main.Compared) -> {plain(Main.render(True{}, c)) == plain(Main.render(False{}, c)) : List<&2, String>}:
  match c:
    case Main.Compared{+from, +to, +before, +after, +modes, +targets}:
      same_front(Main.render.facts(from, to),
        List.append(&2, Main.Painted, Main.render.mode(Maybe.default(&2, String, Maybe.or(&2, String, to, from), "?"), modes), List.append(&2, Main.Painted, Main.render.link(Maybe.default(&2, String, Maybe.or(&2, String, to, from), "?"), targets),
          Main.render.content(True{}, Maybe.default(&2, String, Maybe.map(&2, String, String, x => "a/" ++ x, from), "/dev/null"), Maybe.default(&2, String, Maybe.map(&2, String, String, x => "b/" ++ x, to), "/dev/null"),
            Main.side.lines(before), Main.side.lines(after), Main.binary.side(before) ++ " ->" ++ Main.binary.side(after)))),
        List.append(&2, Main.Painted, Main.render.mode(Maybe.default(&2, String, Maybe.or(&2, String, to, from), "?"), modes), List.append(&2, Main.Painted, Main.render.link(Maybe.default(&2, String, Maybe.or(&2, String, to, from), "?"), targets),
          Main.render.content(False{}, Maybe.default(&2, String, Maybe.map(&2, String, String, x => "a/" ++ x, from), "/dev/null"), Maybe.default(&2, String, Maybe.map(&2, String, String, x => "b/" ++ x, to), "/dev/null"),
            Main.side.lines(before), Main.side.lines(after), Main.binary.side(before) ++ " ->" ++ Main.binary.side(after)))),
        same_front(Main.render.mode(Maybe.default(&2, String, Maybe.or(&2, String, to, from), "?"), modes),
          List.append(&2, Main.Painted, Main.render.link(Maybe.default(&2, String, Maybe.or(&2, String, to, from), "?"), targets),
            Main.render.content(True{}, Maybe.default(&2, String, Maybe.map(&2, String, String, x => "a/" ++ x, from), "/dev/null"), Maybe.default(&2, String, Maybe.map(&2, String, String, x => "b/" ++ x, to), "/dev/null"),
              Main.side.lines(before), Main.side.lines(after), Main.binary.side(before) ++ " ->" ++ Main.binary.side(after))),
          List.append(&2, Main.Painted, Main.render.link(Maybe.default(&2, String, Maybe.or(&2, String, to, from), "?"), targets),
            Main.render.content(False{}, Maybe.default(&2, String, Maybe.map(&2, String, String, x => "a/" ++ x, from), "/dev/null"), Maybe.default(&2, String, Maybe.map(&2, String, String, x => "b/" ++ x, to), "/dev/null"),
              Main.side.lines(before), Main.side.lines(after), Main.binary.side(before) ++ " ->" ++ Main.binary.side(after))),
          same_front(Main.render.link(Maybe.default(&2, String, Maybe.or(&2, String, to, from), "?"), targets),
            Main.render.content(True{}, Maybe.default(&2, String, Maybe.map(&2, String, String, x => "a/" ++ x, from), "/dev/null"), Maybe.default(&2, String, Maybe.map(&2, String, String, x => "b/" ++ x, to), "/dev/null"),
              Main.side.lines(before), Main.side.lines(after), Main.binary.side(before) ++ " ->" ++ Main.binary.side(after)),
            Main.render.content(False{}, Maybe.default(&2, String, Maybe.map(&2, String, String, x => "a/" ++ x, from), "/dev/null"), Maybe.default(&2, String, Maybe.map(&2, String, String, x => "b/" ++ x, to), "/dev/null"),
              Main.side.lines(before), Main.side.lines(after), Main.binary.side(before) ++ " ->" ++ Main.binary.side(after)),
            content_fit(Maybe.default(&2, String, Maybe.map(&2, String, String, x => "a/" ++ x, from), "/dev/null"), Maybe.default(&2, String, Maybe.map(&2, String, String, x => "b/" ++ x, to), "/dev/null"),
              Main.side.lines(before), Main.side.lines(after), Main.binary.side(before) ++ " ->" ++ Main.binary.side(after)))))

def rendered_fit(cs: List<&2, Main.Compared>) -> {plain(Main.diff.rendered(True{}, cs)) == plain(Main.diff.rendered(False{}, cs)) : List<&2, String>}:
  match cs:
    case Nil{}:
      {==}
    case +c <> +rest:
      plain_app2(Main.render(True{}, c), Main.render(False{}, c), Main.diff.rendered(True{}, rest), Main.diff.rendered(False{}, rest), render_fit(c), rendered_fit(rest))

# Colour changes no character of what `diff` prints.
def colour_fit(+cs: List<&2, Main.Compared>) -> {T.map(~Main.Painted, ~String, ~(p => Main.painted(False{}, p)), Main.diff.rendered(True{}, cs)) == T.map(~Main.Painted, ~String, ~(p => Main.painted(False{}, p)), Main.diff.rendered(False{}, cs)) : List<&2, String>}:
  Equal.trans(List<&2, String>, T.map(~Main.Painted, ~String, ~(p => Main.painted(False{}, p)), Main.diff.rendered(True{}, cs)), plain(Main.diff.rendered(True{}, cs)), T.map(~Main.Painted, ~String, ~(p => Main.painted(False{}, p)), Main.diff.rendered(False{}, cs)),
    map_plain(Main.diff.rendered(True{}, cs)),
    Equal.trans(List<&2, String>, plain(Main.diff.rendered(True{}, cs)), plain(Main.diff.rendered(False{}, cs)), T.map(~Main.Painted, ~String, ~(p => Main.painted(False{}, p)), Main.diff.rendered(False{}, cs)),
      rendered_fit(cs),
      Equal.sym(List<&2, String>, T.map(~Main.Painted, ~String, ~(p => Main.painted(False{}, p)), Main.diff.rendered(False{}, cs)), plain(Main.diff.rendered(False{}, cs)), map_plain(Main.diff.rendered(False{}, cs)))))
