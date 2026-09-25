# A stand-in stands for the digest it forgets, and for no other. Decision
# 0014's documents say what they forget in their first header, in each of
# the three grammars; `Store.standing` keeps, of the documents it reads,
# those that forget a digest asked. This writes the stand-ins as the port
# writes them — an operation document or a resolution forgetting a digest,
# and a payload's stand-in — and holds the scan to keeping exactly those
# whose digest was asked.
import Base
import ./store.bend as Store
import ./ops.bend as Ops
import ./resolution.bend as Res
import ./standin.bend as Stand
import ./revision.bend as Rev
import ./string_lemmas.bend as S
import ./bookmark_lemmas.bend as BmL
import ./skip_lemmas.bend as SkipL
import ./composition_lemmas.bend as Comp
import ./anchor_lemmas.bend as AL
import ./host_lemmas.bend as HostL
import ./pattern_lemmas.bend as PatL

# The stand-ins
# -------------

# A forgetting document as the port writes one, where the store holds it:
# an operation document forgetting a digest, a resolution forgetting one,
# or a payload's two headers.
type Standing is Data:
  Standing.Ops{path: String, id: String, size: Nat, forgets: String, result: Maybe<&2, String>, ops: List<&2, Ops.Op>}
  Standing.Res{path: String, id: String, size: Nat, forgets: String, result: Maybe<&2, String>, pieces: List<&2, Res.Piece>}
  Standing.Payload{path: String, id: String, size: Nat, forgets: String, length: String}

def doc(s: Standing) -> Store.Doc:
  match s:
    case Standing.Ops{p, i, n, d, r, os}:
      Store.Doc{p, i, n, Ops.write(Ops.Doc{Some{d}, r, os})}
    case Standing.Res{p, i, n, d, r, ps}:
      Store.Doc{p, i, n, Res.write(Res.Doc{Some{d}, r, ps})}
    case Standing.Payload{p, i, n, d, k}:
      Store.Doc{p, i, n, Stand.payload.write(Stand.Payload{d, k})}

def docs(ss: List<&2, Standing>) -> List<&2, Store.Doc>:
  match ss:
    case Nil{}:
      Nil{}
    case s <> rest:
      doc(s) <> docs(rest)

def forgets(s: Standing) -> String:
  match s:
    case Standing.Ops{p, i, n, d, r, os}:
      d
    case Standing.Res{p, i, n, d, r, ps}:
      d
    case Standing.Payload{p, i, n, d, k}:
      d

# Those that forget a digest among `ds`, in order.
def kept(+ds: List<&2, String>, ss: List<&2, Standing>) -> List<&2, Standing>:
  match ss:
    case Nil{}:
      Nil{}
    case +s <> rest:
      List.filter.put(Standing, s, kept(ds, rest), Rev.member(ds, forgets(s)))

# A digest is one line.
def standing_ok(ss: List<&2, Standing>) -> Bool:
  match ss:
    case Nil{}:
      True{}
    case s <> rest:
      Bool.and(BmL.nonl(forgets(s)), standing_ok(rest))

# The first header
# ----------------

def char_ne(+c: Char, +d: Char, e: {Char.is_eq(c, d) == False{} : Bool}, b: Bool, eb: {Char.is_eq(d, c) == b : Bool}) -> {b == False{} : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, S.true_false(Equal.trans(Bool, True{}, Char.is_eq(c, c), False{}, Equal.sym(Bool, Char.is_eq(c, c), True{}, HostL.char_refl(c)),
        (%BmL.chr_eq(d, c, eb) : {Char.is_eq(c, _) == False{} : Bool}
          e))))

def sw_eq.at(b: Bool, +c1: Char, +c2: Char, +t1: String, +t2: String, +u1: String, +u2: String, eb: {Char.is_eq(c1, c2) == b : Bool}, h: {String.starts_with.if(u1, u2, b) == True{} : Bool}, ih: {String.starts_with(u1, u2) == True{} : Bool} -> {t2 == t1 : String}) -> {SCon{c2, t2} == SCon{c1, t1} : String}:
  match b:
    case True{}:
      %BmL.chr_eq(c1, c2, eb) : {SCon{_, t2} == SCon{c1, t1} : String}
      Equal.cong(String, String, v => SCon{c1, v}, t2, t1, ih(h))
    case False{}:
      Empty.absurd({SCon{c2, t2} == SCon{c1, t1} : String}, S.false_true(h))

# A line that opens with another and a newline, neither holding one, is
# that line.
def sw_eq(d: String, e: String, +r: String, +hd: {BmL.nonl(d) == True{} : Bool}, +he: {BmL.nonl(e) == True{} : Bool}, h: {String.starts_with(d ++ SCon{'\n', r}, e ++ "\n") == True{} : Bool}) -> {e == d : String}:
  match d e:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{+c, +t}:
      +ne = char_ne(c, '\n', AL.not_of_true(Char.is_eq(c, '\n'), Comp.and_left(Bool.not(Char.is_eq(c, '\n')), BmL.nonl(t), he)), Char.is_eq('\n', c), {==})
      Empty.absurd({SCon{c, t} == SNil{} : String}, S.false_true(Equal.trans(Bool, False{}, String.starts_with.if(r, t ++ "\n", Char.is_eq('\n', c)), True{},
        (%Equal.sym(Bool, Char.is_eq('\n', c), False{}, ne) : {False{} == String.starts_with.if(r, t ++ "\n", _) : Bool}
          {==}), h)))
    case SCon{+c, +t} SNil{}:
      Empty.absurd({SNil{} == SCon{c, t} : String}, S.false_true(Equal.trans(Bool, False{}, String.starts_with.if(t ++ SCon{'\n', r}, SNil{}, Char.is_eq(c, '\n')), True{},
        (%Equal.sym(Bool, Char.is_eq(c, '\n'), False{}, AL.not_of_true(Char.is_eq(c, '\n'), Comp.and_left(Bool.not(Char.is_eq(c, '\n')), BmL.nonl(t), hd))) : {False{} == String.starts_with.if(t ++ SCon{'\n', r}, SNil{}, _) : Bool}
          {==}), h)))
    case SCon{+c1, +t1} SCon{+c2, +t2}:
      sw_eq.at(Char.is_eq(c1, c2), c1, c2, t1, t2, t1 ++ SCon{'\n', r}, t2 ++ "\n", {==}, h, h2 => sw_eq(t1, t2, r, Comp.and_right(Bool.not(Char.is_eq(c1, '\n')), BmL.nonl(t1), hd), Comp.and_right(Bool.not(Char.is_eq(c2, '\n')), BmL.nonl(t2), he), h2))

def sw_nl.at(b: Bool, +d: String, +e: String, +r: String, +hd: {BmL.nonl(d) == True{} : Bool}, +he: {BmL.nonl(e) == True{} : Bool}, eb: {String.eq(e, d) == b : Bool}) -> {String.starts_with(d ++ SCon{'\n', r}, e ++ "\n") == b : Bool}:
  match b:
    case True{}:
      %Equal.sym(String, e, d, S.eq_true(e, d, eb)) : {String.starts_with(d ++ SCon{'\n', r}, _ ++ "\n") == True{} : Bool}
      %PatL.app_assoc(d, "\n", r) : {String.starts_with(_, d ++ "\n") == True{} : Bool}
      PatL.sw_app(d ++ "\n", r)
    case False{}:
      AL.bool_cases({String.starts_with(d ++ SCon{'\n', r}, e ++ "\n") == False{} : Bool}, String.starts_with(d ++ SCon{'\n', r}, e ++ "\n"),
        t => Empty.absurd({String.starts_with(d ++ SCon{'\n', r}, e ++ "\n") == False{} : Bool}, S.true_false(Equal.trans(Bool, True{}, String.eq(e, d), False{},
          (%Equal.sym(String, e, d, sw_eq(d, e, r, hd, he, t)) : {True{} == String.eq(_, d) : Bool}
            Equal.sym(Bool, String.eq(d, d), True{}, S.eq_refl(d))), eb))),
        f => f)

# A document whose first header forgets `d` opens with `d` and a newline
# after the preamble; it is taken for the digest `e` exactly where `e` is
# `d`.
def sw_nl(+d: String, +e: String, +r: String, +hd: {BmL.nonl(d) == True{} : Bool}, +he: {BmL.nonl(e) == True{} : Bool}) -> {String.starts_with(d ++ SCon{'\n', r}, e ++ "\n") == String.eq(e, d) : Bool}:
  sw_nl.at(String.eq(e, d), d, e, r, hd, he, {==})

# The scan asks each digest; it holds the document for one of them exactly
# where the digest it forgets is among them.
def stands(ds: List<&2, String>, +d: String, +r: String, +hd: {BmL.nonl(d) == True{} : Bool}, +h: {HostL.all_nonl(ds) == True{} : Bool}) -> {Store.stands_for("historica\nforgets " ++ (d ++ SCon{'\n', r}), ds) == Rev.member(ds, d) : Bool}:
  match ds:
    case Nil{}:
      {==}
    case +e <> +rest:
      %Equal.sym(Bool, String.starts_with(d ++ SCon{'\n', r}, e ++ "\n"), String.eq(e, d), sw_nl(d, e, r, hd, Comp.and_left(BmL.nonl(e), HostL.all_nonl(rest), h))) : {Bool.or(_, Store.stands_for("historica\nforgets " ++ (d ++ SCon{'\n', r}), rest)) == Rev.member(e <> rest, d) : Bool}
      Equal.cong(Bool, Bool, x => Bool.or(String.eq(e, d), x), Store.stands_for("historica\nforgets " ++ (d ++ SCon{'\n', r}), rest), Rev.member(rest, d), stands(rest, d, r, hd, Comp.and_right(BmL.nonl(e), HostL.all_nonl(rest), h)))

# Each of the three grammars forgets in its first header.
def text_stands(s: Standing, +ds: List<&2, String>, +hd: {BmL.nonl(forgets(s)) == True{} : Bool}, +h: {HostL.all_nonl(ds) == True{} : Bool}) -> {Store.stands_for(Store.text_of(doc(s)), ds) == Rev.member(ds, forgets(s)) : Bool}:
  match s:
    case Standing.Ops{p, i, n, +d, +r, +os}:
      %Equal.sym(String, (d ++ "\n") ++ (Ops.header_line("result", r) ++ ("\n" ++ Ops.write_ops(os))), d ++ ("\n" ++ (Ops.header_line("result", r) ++ ("\n" ++ Ops.write_ops(os)))), PatL.app_assoc(d, "\n", Ops.header_line("result", r) ++ ("\n" ++ Ops.write_ops(os)))) : {Store.stands_for("historica\nforgets " ++ _, ds) == Rev.member(ds, d) : Bool}
      stands(ds, d, Ops.header_line("result", r) ++ ("\n" ++ Ops.write_ops(os)), hd, h)
    case Standing.Res{p, i, n, +d, +r, +ps}:
      %Equal.sym(String, (d ++ "\n") ++ (Ops.header_line("result", r) ++ ("\n" ++ Res.write.pieces(ps))), d ++ ("\n" ++ (Ops.header_line("result", r) ++ ("\n" ++ Res.write.pieces(ps)))), PatL.app_assoc(d, "\n", Ops.header_line("result", r) ++ ("\n" ++ Res.write.pieces(ps)))) : {Store.stands_for("historica\nforgets " ++ _, ds) == Rev.member(ds, d) : Bool}
      stands(ds, d, Ops.header_line("result", r) ++ ("\n" ++ Res.write.pieces(ps)), hd, h)
    case Standing.Payload{p, i, n, +d, +k}:
      stands(ds, d, "length " ++ (k ++ "\n"), hd, h)

def docs_put(+s: Standing, -xs: List<&2, Standing>, b: Bool) -> {docs(List.filter.put(Standing, s, xs, b)) == List.filter.put(Store.Doc, doc(s), docs(xs), b) : List<&2, Store.Doc>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# `a_stand_in_stands_for_what_it_forgets`.
def standing_of(ss: List<&2, Standing>, +ds: List<&2, String>, +h: {Bool.and(HostL.all_nonl(ds), standing_ok(ss)) == True{} : Bool}) -> {Store.standing.of(ds, docs(ss)) == docs(kept(ds, ss)) : List<&2, Store.Doc>}:
  match ss:
    case Nil{}:
      {==}
    case +s <> +rest:
      +hs = Comp.and_right(HostL.all_nonl(ds), standing_ok(s <> rest), h)
      +hn = Comp.and_left(HostL.all_nonl(ds), standing_ok(s <> rest), h)
      %Equal.sym(Bool, Store.stands_for(Store.text_of(doc(s)), ds), Rev.member(ds, forgets(s)), text_stands(s, ds, Comp.and_left(BmL.nonl(forgets(s)), standing_ok(rest), hs), hn)) : {List.filter.put(Store.Doc, doc(s), Store.standing.of(ds, docs(rest)), _) == docs(kept(ds, s <> rest)) : List<&2, Store.Doc>}
      %Equal.sym(List<&2, Store.Doc>, docs(List.filter.put(Standing, s, kept(ds, rest), Rev.member(ds, forgets(s)))), List.filter.put(Store.Doc, doc(s), docs(kept(ds, rest)), Rev.member(ds, forgets(s))), docs_put(s, kept(ds, rest), Rev.member(ds, forgets(s)))) : {List.filter.put(Store.Doc, doc(s), Store.standing.of(ds, docs(rest)), Rev.member(ds, forgets(s))) == _ : List<&2, Store.Doc>}
      Equal.cong(List<&2, Store.Doc>, List<&2, Store.Doc>, l => List.filter.put(Store.Doc, doc(s), l, Rev.member(ds, forgets(s))), Store.standing.of(ds, docs(rest)), docs(kept(ds, rest)), standing_of(rest, ds, AL.and_intro(HostL.all_nonl(ds), standing_ok(rest), hn, Comp.and_right(BmL.nonl(forgets(s)), standing_ok(rest), hs))))
