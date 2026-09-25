# What `forget` says, where it files what it writes, what it sweeps, and
# which documents it rewrites: the output read back as a person or a script
# would read it, the paths it writes to held apart from what the store
# already has, and the documents a span's forgetting reaches.
import Base
import ./text.bend as T
import ./revision.bend as Rev
import ./commands.bend as Main
import ./forget.bend as Fg
import ./ops.bend as Ops
import ./store.bend as Store
import ./sha256.bend as Sha
import ./utf8.bend as Utf8
import ./composition_lemmas.bend as Comp
import ./anchor_lemmas.bend as AL
import ./string_lemmas.bend as S
import ./graph_lemmas.bend as GL
import ./fetch_lemmas.bend as FetchL
import ./forget_lemmas.bend as ForgetL

def sw_nil(str: String) -> {String.starts_with(str, SNil{}) == True{} : Bool}:
  match str:
    case SNil{}:
      {==}
    case SCon{x, u}:
      {==}

def drop_zero(str: String) -> {String.drop(str, 0n) == str : String}:
  match str:
    case SNil{}:
      {==}
    case SCon{x, u}:
      {==}

def plan.targets(p: Fg.FgPlan) -> List<&2, String>:
  ForgetL.plan.targets(p)

# What is said
# ------------

# Decision 0074's `gone` lines read back: the digest after each, or nothing
# where a line is not one.
def gone.read(ls: List<&2, String>) -> Maybe<&2, List<&2, String>>:
  match ls:
    case Nil{}:
      Some{Nil{}}
    case +l <> rest:
      Bool.pick(Maybe<&2, List<&2, String>>, String.starts_with(l, "gone "), Maybe.map(&2, List<&2, String>, List<&2, String>, more => String.drop(l, 5n) <> more, gone.read(rest)), None{})

def gone_reads(ts: List<&2, String>) -> {gone.read(Fg.said.gone(ts)) == Some{ts} : Maybe<&2, List<&2, String>>}:
  match ts:
    case Nil{}:
      {==}
    case +t <> rest:
      %Equal.sym(Bool, String.starts_with(t, SNil{}), True{}, sw_nil(t)) : {Bool.pick(Maybe<&2, List<&2, String>>, _, Maybe.map(&2, List<&2, String>, List<&2, String>, more => String.drop(t, 0n) <> more, gone.read(Fg.said.gone(rest))), None{}) == Some{t <> rest} : Maybe<&2, List<&2, String>>}
      %Equal.sym(String, String.drop(t, 0n), t, drop_zero(t)) : {Maybe.map(&2, List<&2, String>, List<&2, String>, more => _ <> more, gone.read(Fg.said.gone(rest))) == Some{t <> rest} : Maybe<&2, List<&2, String>>}
      %Equal.sym(Maybe<&2, List<&2, String>>, gone.read(Fg.said.gone(rest)), Some{rest}, gone_reads(rest)) : {Maybe.map(&2, List<&2, String>, List<&2, String>, more => t <> more, _) == Some{t <> rest} : Maybe<&2, List<&2, String>>}
      {==}

# Asked for `--fields`, what `forget` prints reads back as the digests the
# plan made unreadable, each in its `gone` line and nothing else.
def says_gone(p: Fg.FgPlan, -ds: List<&2, String>, -lines: Bool, -dry: Bool) -> {gone.read(Fg.said(p, True{}, ds, lines, dry)) == Some{plan.targets(p)} : Maybe<&2, List<&2, String>>}:
  match p:
    case Fg.Fg.Plan{ts, ws, a, n}:
      gone_reads(ts)

# The files a line says were destroyed, after the verb and `history/`.
def destroyed.read(ls: List<&2, String>, +verb: String) -> List<&2, String>:
  match ls:
    case Nil{}:
      Nil{}
    case +l <> rest:
      +more = destroyed.read(rest, verb)
      Bool.pick(List<&2, String>, String.starts_with(l, verb ++ " history/"), String.drop(l, String.length(verb ++ " history/")) <> more, more)

def pick_app(b: Bool, -x: String, -r: List<&2, String>, -q: List<&2, String>) -> {Bool.pick(List<&2, String>, b, x <> List.append(&2, String, r, q), List.append(&2, String, r, q)) == List.append(&2, String, Bool.pick(List<&2, String>, b, x <> r, r), q) : List<&2, String>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def read_app(xs: List<&2, String>, -ys: List<&2, String>, +verb: String) -> {destroyed.read(List.append(&2, String, xs, ys), verb) == List.append(&2, String, destroyed.read(xs, verb), destroyed.read(ys, verb)) : List<&2, String>}:
  match xs:
    case Nil{}:
      {==}
    case +l <> rest:
      %Equal.sym(List<&2, String>, destroyed.read(List.append(&2, String, rest, ys), verb), List.append(&2, String, destroyed.read(rest, verb), destroyed.read(ys, verb)), read_app(rest, ys, verb)) : {Bool.pick(List<&2, String>, String.starts_with(l, verb ++ " history/"), String.drop(l, String.length(verb ++ " history/")) <> _, _) == List.append(&2, String, Bool.pick(List<&2, String>, String.starts_with(l, verb ++ " history/"), String.drop(l, String.length(verb ++ " history/")) <> destroyed.read(rest, verb), destroyed.read(rest, verb)), destroyed.read(ys, verb)) : List<&2, String>}
      pick_app(String.starts_with(l, verb ++ " history/"), String.drop(l, String.length(verb ++ " history/")), destroyed.read(rest, verb), destroyed.read(ys, verb))

def lapp_nil(xs: List<&2, String>) -> {List.append(&2, String, xs, Nil{}) == xs : List<&2, String>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> rest:
      Equal.cong(List<&2, String>, List<&2, String>, l => x <> l, List.append(&2, String, rest, Nil{}), rest, lapp_nil(rest))

def writes_none(ws: List<&2, Fg.FgWrite>, dry: Bool) -> {destroyed.read(Fg.said.writes(ws, Bool.pick(String, dry, "would write", "wrote")), Bool.pick(String, dry, "would destroy", "destroyed")) == Nil{} : List<&2, String>}:
  match ws:
    case Nil{}:
      {==}
    case Fg.Fg.Write{f, t, p} <> rest:
      match dry:
        case True{}:
          writes_none(rest, True{})
        case False{}:
          writes_none(rest, False{})

def destroys_read(ds: List<&2, String>, dry: Bool) -> {destroyed.read(Fg.said.destroys(ds, Bool.pick(String, dry, "would destroy", "destroyed")), Bool.pick(String, dry, "would destroy", "destroyed")) == ds : List<&2, String>}:
  match ds:
    case Nil{}:
      {==}
    case +d <> rest:
      match dry:
        case True{}:
          %Equal.sym(Bool, String.starts_with(d, SNil{}), True{}, sw_nil(d)) : {Bool.pick(List<&2, String>, _, String.drop(d, 0n) <> destroyed.read(Fg.said.destroys(rest, "would destroy"), "would destroy"), destroyed.read(Fg.said.destroys(rest, "would destroy"), "would destroy")) == d <> rest : List<&2, String>}
          %Equal.sym(String, String.drop(d, 0n), d, drop_zero(d)) : {_ <> destroyed.read(Fg.said.destroys(rest, "would destroy"), "would destroy") == d <> rest : List<&2, String>}
          Equal.cong(List<&2, String>, List<&2, String>, l => d <> l, destroyed.read(Fg.said.destroys(rest, "would destroy"), "would destroy"), rest, destroys_read(rest, True{}))
        case False{}:
          %Equal.sym(Bool, String.starts_with(d, SNil{}), True{}, sw_nil(d)) : {Bool.pick(List<&2, String>, _, String.drop(d, 0n) <> destroyed.read(Fg.said.destroys(rest, "destroyed"), "destroyed"), destroyed.read(Fg.said.destroys(rest, "destroyed"), "destroyed")) == d <> rest : List<&2, String>}
          %Equal.sym(String, String.drop(d, 0n), d, drop_zero(d)) : {_ <> destroyed.read(Fg.said.destroys(rest, "destroyed"), "destroyed") == d <> rest : List<&2, String>}
          Equal.cong(List<&2, String>, List<&2, String>, l => d <> l, destroyed.read(Fg.said.destroys(rest, "destroyed"), "destroyed"), rest, destroys_read(rest, False{}))

def elsewhere_none(n: Nat, dry: Bool) -> {destroyed.read(Fg.said.elsewhere(n), Bool.pick(String, dry, "would destroy", "destroyed")) == Nil{} : List<&2, String>}:
  match n dry:
    case 0n _:
      {==}
    case 1n+m True{}:
      {==}
    case 1n+m False{}:
      {==}

def cannot_none(lines: Bool, dry: Bool) -> {destroyed.read([Fg.said.cannot(lines)], Bool.pick(String, dry, "would destroy", "destroyed")) == Nil{} : List<&2, String>}:
  match lines dry:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def already_none(lines: Bool, dry: Bool) -> {destroyed.read([Bool.pick(String, lines, "those lines are already forgotten everywhere they are quoted", "those bytes are already forgotten")], Bool.pick(String, dry, "would destroy", "destroyed")) == Nil{} : List<&2, String>}:
  match lines dry:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def done_parts(+ws: List<&2, Fg.FgWrite>, +ds: List<&2, String>, +n: Nat, +lines: Bool, +dry: Bool) -> {destroyed.read(List.append(&2, String, Fg.said.writes(ws, Bool.pick(String, dry, "would write", "wrote")), List.append(&2, String, Fg.said.destroys(ds, Bool.pick(String, dry, "would destroy", "destroyed")), List.append(&2, String, Fg.said.elsewhere(n), [Fg.said.cannot(lines)]))), Bool.pick(String, dry, "would destroy", "destroyed")) == ds : List<&2, String>}:
  +v = Bool.pick(String, dry, "would destroy", "destroyed")
  +W = Fg.said.writes(ws, Bool.pick(String, dry, "would write", "wrote"))
  +D = Fg.said.destroys(ds, v)
  +E = Fg.said.elsewhere(n)
  +C = {[Fg.said.cannot(lines)] : List<&2, String>}
  %Equal.sym(List<&2, String>, destroyed.read(List.append(&2, String, W, List.append(&2, String, D, List.append(&2, String, E, C))), v), List.append(&2, String, destroyed.read(W, v), destroyed.read(List.append(&2, String, D, List.append(&2, String, E, C)), v)), read_app(W, List.append(&2, String, D, List.append(&2, String, E, C)), v)) : {_ == ds : List<&2, String>}
  %Equal.sym(List<&2, String>, destroyed.read(W, v), Nil{}, writes_none(ws, dry)) : {List.append(&2, String, _, destroyed.read(List.append(&2, String, D, List.append(&2, String, E, C)), v)) == ds : List<&2, String>}
  %Equal.sym(List<&2, String>, destroyed.read(List.append(&2, String, D, List.append(&2, String, E, C)), v), List.append(&2, String, destroyed.read(D, v), destroyed.read(List.append(&2, String, E, C), v)), read_app(D, List.append(&2, String, E, C), v)) : {_ == ds : List<&2, String>}
  %Equal.sym(List<&2, String>, destroyed.read(D, v), ds, destroys_read(ds, dry)) : {List.append(&2, String, _, destroyed.read(List.append(&2, String, E, C), v)) == ds : List<&2, String>}
  %Equal.sym(List<&2, String>, destroyed.read(List.append(&2, String, E, C), v), List.append(&2, String, destroyed.read(E, v), destroyed.read(C, v)), read_app(E, C, v)) : {List.append(&2, String, ds, _) == ds : List<&2, String>}
  %Equal.sym(List<&2, String>, destroyed.read(E, v), Nil{}, elsewhere_none(n, dry)) : {List.append(&2, String, ds, List.append(&2, String, _, destroyed.read(C, v))) == ds : List<&2, String>}
  %Equal.sym(List<&2, String>, destroyed.read(C, v), Nil{}, cannot_none(lines, dry)) : {List.append(&2, String, ds, List.append(&2, String, Nil{}, _)) == ds : List<&2, String>}
  lapp_nil(ds)

def done_read(ws: List<&2, Fg.FgWrite>, ds: List<&2, String>, +n: Nat, +lines: Bool, +dry: Bool) -> {destroyed.read(Fg.said.done(ws, ds, n, lines, dry), Bool.pick(String, dry, "would destroy", "destroyed")) == ds : List<&2, String>}:
  match ws:
    case Nil{}:
      match ds:
        case Nil{}:
          already_none(lines, dry)
        case +d <> +rest:
          done_parts(Nil{}, d <> rest, n, lines, dry)
    case +w <> +rest:
      done_parts(w <> rest, ds, n, lines, dry)

# What `forget` prints without `--fields` reads back, as its `destroyed`
# lines, as the files it destroys: each once, in the order it destroys
# them, `would destroy` under `--dry-run`, and no other line read as one.
def says_destroyed(p: Fg.FgPlan, +ds: List<&2, String>, +lines: Bool, +dry: Bool) -> {destroyed.read(Fg.said(p, False{}, ds, lines, dry), Bool.pick(String, dry, "would destroy", "destroyed")) == ds : List<&2, String>}:
  match p:
    case Fg.Fg.Plan{ts, ws, a, +n}:
      done_read(ws, ds, n, lines, dry)

# Where a document is filed
# -------------------------

# The name a document's own bytes give it under `operations/`.
def own(w: Fg.FgWrite) -> String:
  match w:
    case Fg.Fg.Write{f, +text, p}:
      "operations/" ++ Sha.digest(Utf8.encode(text)) ++ ".ops.txt"

def rev_go_app(a: String, -b: String, acc: String) -> {String.reverse.go(a ++ b, acc) == String.reverse.go(b, String.reverse.go(a, acc)) : String}:
  match a:
    case SNil{}:
      {==}
    case SCon{h, t}:
      rev_go_app(t, b, SCon{h, acc})

# A name ending `.ops.txt` reversed opens with it reversed.
def suffixed(+x: String, +acc: String) -> {String.starts_with(String.reverse.go(x ++ ".ops.txt", acc), "txt.spo.") == True{} : Bool}:
  %Equal.sym(String, String.reverse.go(x ++ ".ops.txt", acc), String.reverse.go(".ops.txt", String.reverse.go(x, acc)), rev_go_app(x, ".ops.txt", acc)) : {String.starts_with(_, "txt.spo.") == True{} : Bool}
  sw_nil(String.reverse.go(x, acc))

def own_ok(+fs: List<&2, Fg.FgFiled>, +text: String) -> {Bool.and(String.ends_with("operations/" ++ Sha.digest(Utf8.encode(text)) ++ ".ops.txt", ".ops.txt"), Bool.or(String.eq("operations/" ++ Sha.digest(Utf8.encode(text)) ++ ".ops.txt", "operations/" ++ Sha.digest(Utf8.encode(text)) ++ ".ops.txt"), Bool.not(Fg.filed.taken(fs, "operations/" ++ Sha.digest(Utf8.encode(text)) ++ ".ops.txt")))) == True{} : Bool}:
  +named = "operations/" ++ Sha.digest(Utf8.encode(text)) ++ ".ops.txt"
  %Equal.sym(Bool, String.eq(named, named), True{}, S.eq_refl(named)) : {Bool.and(String.ends_with(named, ".ops.txt"), Bool.or(_, Bool.not(Fg.filed.taken(fs, named)))) == True{} : Bool}
  %Equal.sym(Bool, String.ends_with(named, ".ops.txt"), True{}, suffixed(Sha.digest(Utf8.encode(text)), "/snoitarepo")) : {Bool.and(_, True{}) == True{} : Bool}
  {==}

def beside_ok(b: Bool, +fs: List<&2, Fg.FgFiled>, +d: String, +text: String, eb: {Fg.filed.taken(fs, d ++ ".ops.txt") == b : Bool}) -> {Bool.and(String.ends_with(Bool.pick(String, b, "operations/" ++ Sha.digest(Utf8.encode(text)) ++ ".ops.txt", d ++ ".ops.txt"), ".ops.txt"), Bool.or(String.eq(Bool.pick(String, b, "operations/" ++ Sha.digest(Utf8.encode(text)) ++ ".ops.txt", d ++ ".ops.txt"), "operations/" ++ Sha.digest(Utf8.encode(text)) ++ ".ops.txt"), Bool.not(Fg.filed.taken(fs, Bool.pick(String, b, "operations/" ++ Sha.digest(Utf8.encode(text)) ++ ".ops.txt", d ++ ".ops.txt"))))) == True{} : Bool}:
  match b:
    case True{}:
      own_ok(fs, text)
    case False{}:
      %Equal.sym(Bool, Fg.filed.taken(fs, d ++ ".ops.txt"), False{}, eb) : {Bool.and(String.ends_with(d ++ ".ops.txt", ".ops.txt"), Bool.or(String.eq(d ++ ".ops.txt", "operations/" ++ Sha.digest(Utf8.encode(text)) ++ ".ops.txt"), Bool.not(_))) == True{} : Bool}
      %Equal.sym(Bool, String.starts_with(String.reverse.go(d ++ ".ops.txt", SNil{}), "txt.spo."), True{}, suffixed(d, SNil{})) : {Bool.and(_, Bool.or(String.eq(d ++ ".ops.txt", "operations/" ++ Sha.digest(Utf8.encode(text)) ++ ".ops.txt"), True{})) == True{} : Bool}
      AL.or_right(String.eq(d ++ ".ops.txt", "operations/" ++ Sha.digest(Utf8.encode(text)) ++ ".ops.txt"), True{}, {==})

def payload_where(+fs: List<&2, Fg.FgFiled>, ds: List<&2, String>, +text: String) -> {Bool.and(String.ends_with(Fg.filed.beside(fs, ds, "operations/" ++ Sha.digest(Utf8.encode(text)) ++ ".ops.txt"), ".ops.txt"), Bool.or(String.eq(Fg.filed.beside(fs, ds, "operations/" ++ Sha.digest(Utf8.encode(text)) ++ ".ops.txt"), "operations/" ++ Sha.digest(Utf8.encode(text)) ++ ".ops.txt"), Bool.not(Fg.filed.taken(fs, Fg.filed.beside(fs, ds, "operations/" ++ Sha.digest(Utf8.encode(text)) ++ ".ops.txt"))))) == True{} : Bool}:
  match ds:
    case Nil{}:
      own_ok(fs, text)
    case +d <> rest:
      beside_ok(Fg.filed.taken(fs, d ++ ".ops.txt"), fs, d, text, {==})

def written_where(+fs: List<&2, Fg.FgFiled>, +ds: List<&2, String>, +text: String, payload: Bool) -> {Bool.and(String.ends_with(Bool.pick(String, payload, Fg.filed.beside(fs, ds, "operations/" ++ Sha.digest(Utf8.encode(text)) ++ ".ops.txt"), "operations/" ++ Sha.digest(Utf8.encode(text)) ++ ".ops.txt"), ".ops.txt"), Bool.or(String.eq(Bool.pick(String, payload, Fg.filed.beside(fs, ds, "operations/" ++ Sha.digest(Utf8.encode(text)) ++ ".ops.txt"), "operations/" ++ Sha.digest(Utf8.encode(text)) ++ ".ops.txt"), "operations/" ++ Sha.digest(Utf8.encode(text)) ++ ".ops.txt"), Bool.not(Fg.filed.taken(fs, Bool.pick(String, payload, Fg.filed.beside(fs, ds, "operations/" ++ Sha.digest(Utf8.encode(text)) ++ ".ops.txt"), "operations/" ++ Sha.digest(Utf8.encode(text)) ++ ".ops.txt"))))) == True{} : Bool}:
  match payload:
    case False{}:
      own_ok(fs, text)
    case True{}:
      payload_where(fs, ds, text)

# Every document `forget` writes is filed as one, and at the name its own
# bytes give it or at one nothing in `operations/` has.
def files_where(+fs: List<&2, Fg.FgFiled>, +ds: List<&2, String>, w: Fg.FgWrite) -> {Bool.and(String.ends_with(Fg.filed.as(fs, ds, w), ".ops.txt"), Bool.or(String.eq(Fg.filed.as(fs, ds, w), own(w)), Bool.not(Fg.filed.taken(fs, Fg.filed.as(fs, ds, w))))) == True{} : Bool}:
  match w:
    case Fg.Fg.Write{f, +text, payload}:
      written_where(fs, ds, text, payload)

# A file of lines is never forgotten whole
# ----------------------------------------

def whole_refused(+file: String, r: Result<&2, &2, String, List<&2, Ops.Item>>) -> {Result.is_done(&2, &2, Main.Refused, Fg.FgPlan, Fg.lines.whole.r(file, r)) == False{} : Bool}:
  match r:
    case Fail{e}:
      {==}
    case Done{items}:
      {==}

# Asked to forget a file of lines with no span, `forget` plans nothing,
# whatever the file holds.
def no_span(+fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +id: String, +file: String) -> {Result.is_done(&2, &2, Main.Refused, Fg.FgPlan, Fg.io.lines.plan.r(fs, ds, id, file, None{})) == False{} : Bool}:
  whole_refused(file, Main.content(fs, ds, id, file))

# What `operations/` loses empty
# ------------------------------

# Whether a directory listed, and listed nothing.
def listed.nothing(r: Result<&1, &1, U32 & String, String>) -> Bool:
  match r:
    case Done{+t}:
      String.is_empty(t)
    case Fail{e}:
      False{}

# A directory under `operations/` — not it, the path of no name — that
# listed nothing.
def emptied(+dir: String, r: Result<&1, &1, U32 & String, String>) -> Bool:
  Bool.and(Bool.not(String.is_empty(dir)), listed.nothing(r))

def kept_in(b: Bool, +x: String, +xs: List<&2, String>, +p: String, h: {Rev.member(Rev.keep(b, x, xs), p) == True{} : Bool}) -> {Bool.or(Rev.member(xs, p), Bool.and(String.eq(x, p), b)) == True{} : Bool}:
  match b:
    case False{}:
      AL.or_left(Rev.member(xs, p), Bool.and(String.eq(x, p), False{}), h)
    case True{}:
      AL.or_cases({Bool.or(Rev.member(xs, p), Bool.and(String.eq(x, p), True{})) == True{} : Bool}, String.eq(x, p), Rev.member(xs, p), h,
        hx => AL.or_right(Rev.member(xs, p), Bool.and(String.eq(x, p), True{}), AL.and_intro(String.eq(x, p), True{}, hx, {==})),
        hm => AL.or_left(Rev.member(xs, p), Bool.and(String.eq(x, p), True{}), hm))

# The sweep keeps a directory to remove only where it listed nothing, and
# never `operations/` itself.
def sweeps(+dir: String, r: Result<&1, &1, U32 & String, String>, +found: List<&2, String>, +p: String, h: {Rev.member(Fg.swept.empty(dir, Fg.io.listed(r), found), p) == True{} : Bool}) -> {Bool.or(Rev.member(found, p), Bool.and(String.eq(dir, p), emptied(dir, r))) == True{} : Bool}:
  match r:
    case Done{+t}:
      kept_in(Bool.and(Bool.not(String.is_empty(dir)), String.is_empty(t)), dir, found, p, h)
    case Fail{e}:
      kept_in(Bool.and(Bool.not(String.is_empty(dir)), String.is_empty("u")), dir, found, p, h)

# Every document quoting the span
# -------------------------------

# Whether a document found is `d`.
def found.is(m: Maybe<&2, String>, +d: String) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{x}:
      String.eq(x, d)

# Whether `d` is the document one of these deletes' revisions names for
# the file.
def deleted.in(dl: List<&2, Fg.FgQuote>, +ns: List<&2, Fg.FgNamed>, +d: String) -> Bool:
  match dl:
    case Nil{}:
      False{}
    case Fg.Fg.Quote{+by, op, item} <> rest:
      Bool.or(found.is(Fg.named.find(ns, by), d), deleted.in(rest, ns, d))

# Whether `d` quotes the element: the document the revision that wrote it
# names for the file, or one a revision whose delete quotes it names.
def quotes(q: Fg.FgQuoted, +ns: List<&2, Fg.FgNamed>, +d: String) -> Bool:
  match q:
    case Fg.Fg.Quoted{+by, op, item, t, dl, dr, f, v}:
      Bool.or(found.is(Fg.named.find(ns, by), d), deleted.in(dl, ns, d))

def mem_app_l(xs: List<&2, String>, +ys: List<&2, String>, +d: String, h: {Rev.member(xs, d) == True{} : Bool}) -> {Rev.member(List.append(&2, String, xs, ys), d) == True{} : Bool}:
  match xs:
    case Nil{}:
      Empty.absurd({Rev.member(ys, d) == True{} : Bool}, S.false_true(h))
    case +x <> +rest:
      GL.member_cons({Rev.member(x <> List.append(&2, String, rest, ys), d) == True{} : Bool}, x, rest, d, h,
        e => (%Equal.sym(String, x, d, e) : {Rev.member(_ <> List.append(&2, String, rest, ys), d) == True{} : Bool}; GL.member_head(d, List.append(&2, String, rest, ys))),
        t => GL.member_tail(x, List.append(&2, String, rest, ys), d, mem_app_l(rest, ys, d, t)))

def mem_app_r(xs: List<&2, String>, +ys: List<&2, String>, +d: String, h: {Rev.member(ys, d) == True{} : Bool}) -> {Rev.member(List.append(&2, String, xs, ys), d) == True{} : Bool}:
  match xs:
    case Nil{}:
      h
    case +x <> +rest:
      GL.member_tail(x, List.append(&2, String, rest, ys), d, mem_app_r(rest, ys, d, h))

def pick_found(m: Maybe<&2, String>, +op: Nat, +item: Nat, +rest: List<&2, Fg.FgPick>, +d: String, h: {found.is(m, d) == True{} : Bool}) -> {Rev.member(Fg.targets.of(Fg.pick.if(m, op, item, rest)), d) == True{} : Bool}:
  match m:
    case None{}:
      Empty.absurd({Rev.member(Fg.targets.of(rest), d) == True{} : Bool}, S.false_true(h))
    case Some{+x}:
      %Equal.sym(String, x, d, S.eq_true(x, d, h)) : {Rev.member(_ <> Fg.targets.of(rest), d) == True{} : Bool}
      GL.member_head(d, Fg.targets.of(rest))

def pick_rest(m: Maybe<&2, String>, +op: Nat, +item: Nat, +rest: List<&2, Fg.FgPick>, +d: String, h: {Rev.member(Fg.targets.of(rest), d) == True{} : Bool}) -> {Rev.member(Fg.targets.of(Fg.pick.if(m, op, item, rest)), d) == True{} : Bool}:
  match m:
    case None{}:
      h
    case Some{+x}:
      GL.member_tail(x, Fg.targets.of(rest), d, h)

# A delete quoting the element puts its document among the picks.
def deletes_picked(dl: List<&2, Fg.FgQuote>, +ns: List<&2, Fg.FgNamed>, +d: String, h: {deleted.in(dl, ns, d) == True{} : Bool}) -> {Rev.member(Fg.targets.of(Fg.picks.deletes(dl, ns)), d) == True{} : Bool}:
  match dl:
    case Nil{}:
      Empty.absurd({Rev.member(Nil{}, d) == True{} : Bool}, S.false_true(h))
    case Fg.Fg.Quote{+by, +op, +item} <> +rest:
      AL.or_cases({Rev.member(Fg.targets.of(Fg.pick.if(Fg.named.find(ns, by), op, item, Fg.picks.deletes(rest, ns))), d) == True{} : Bool}, found.is(Fg.named.find(ns, by), d), deleted.in(rest, ns, d), h,
        l => pick_found(Fg.named.find(ns, by), op, item, Fg.picks.deletes(rest, ns), d, l),
        r => pick_rest(Fg.named.find(ns, by), op, item, Fg.picks.deletes(rest, ns), d, deletes_picked(rest, ns, d, r)))

# An element taken puts every document quoting it among the picks.
def taken_picked(+ns: List<&2, Fg.FgNamed>, q: Fg.FgQuoted, +d: String, h: {quotes(q, ns, d) == True{} : Bool}) -> {Rev.member(Fg.targets.of(Fg.picks.of(ns, True{}, q)), d) == True{} : Bool}:
  match q:
    case Fg.Fg.Quoted{+by, +op, +item, t, +dl, dr, f, v}:
      AL.or_cases({Rev.member(Fg.targets.of(Fg.pick.if(Fg.named.find(ns, by), op, item, Fg.picks.deletes(dl, ns))), d) == True{} : Bool}, found.is(Fg.named.find(ns, by), d), deleted.in(dl, ns, d), h,
        l => pick_found(Fg.named.find(ns, by), op, item, Fg.picks.deletes(dl, ns), d, l),
        r => pick_rest(Fg.named.find(ns, by), op, item, Fg.picks.deletes(dl, ns), d, deletes_picked(dl, ns, d, r)))

def join_here(+taken: Bool, +forgot: Bool, +here: List<&2, Fg.FgPick>, r: Fg.FgPicked, +d: String, h: {Rev.member(Fg.targets.of(here), d) == True{} : Bool}) -> {Rev.member(Fg.targets.of(ForgetL.picks.of.picked(Fg.picked.join(taken, forgot, here, r))), d) == True{} : Bool}:
  match r:
    case Fg.Fg.Picked{+ps, n}:
      %Equal.sym(List<&2, String>, Fg.targets.of(List.append(&2, Fg.FgPick, here, ps)), List.append(&2, String, Fg.targets.of(here), Fg.targets.of(ps)), ForgetL.targets_app(here, ps)) : {Rev.member(_, d) == True{} : Bool}
      mem_app_l(Fg.targets.of(here), Fg.targets.of(ps), d, h)

def join_rest(+taken: Bool, +forgot: Bool, +here: List<&2, Fg.FgPick>, r: Fg.FgPicked, +d: String, h: {Rev.member(Fg.targets.of(ForgetL.picks.of.picked(r)), d) == True{} : Bool}) -> {Rev.member(Fg.targets.of(ForgetL.picks.of.picked(Fg.picked.join(taken, forgot, here, r))), d) == True{} : Bool}:
  match r:
    case Fg.Fg.Picked{+ps, n}:
      %Equal.sym(List<&2, String>, Fg.targets.of(List.append(&2, Fg.FgPick, here, ps)), List.append(&2, String, Fg.targets.of(here), Fg.targets.of(ps)), ForgetL.targets_app(here, ps)) : {Rev.member(_, d) == True{} : Bool}
      mem_app_r(Fg.targets.of(here), Fg.targets.of(ps), d, h)

# Every element of the walk whose key the span holds puts each document
# quoting it among the picks.
def picked_mem(qs: List<&2, Fg.FgQuoted>, +span: List<&2, String>, +ns: List<&2, Fg.FgNamed>, i: Nat, +q: Fg.FgQuoted, +d: String, hq: {List.get(&2, Fg.FgQuoted, qs, i) == Some{q} : Maybe<&2, Fg.FgQuoted>}, +hs: {Rev.member(span, Fg.quoted.key(q)) == True{} : Bool}, +hd: {quotes(q, ns, d) == True{} : Bool}) -> {Rev.member(Fg.targets.of(ForgetL.picks.of.picked(Fg.picked(qs, span, ns))), d) == True{} : Bool}:
  match qs i:
    case Nil{} _:
      Empty.absurd({Rev.member(Fg.targets.of(ForgetL.picks.of.picked(Fg.picked(Nil{}, span, ns))), d) == True{} : Bool}, Comp.false_true(Equal.cong(Maybe<&2, Fg.FgQuoted>, Bool, m => Maybe.is_some(&2, Fg.FgQuoted, m), None{}, Some{q}, hq)))
    case +q0 <> +rest 0n:
      +same = Equal.cong(Maybe<&2, Fg.FgQuoted>, Fg.FgQuoted, m => Maybe.default(&2, Fg.FgQuoted, m, q), Some{q0}, Some{q}, hq)
      %Equal.sym(Fg.FgQuoted, q0, q, same) : {Rev.member(Fg.targets.of(ForgetL.picks.of.picked(Fg.picked(_ <> rest, span, ns))), d) == True{} : Bool}
      %Equal.sym(Bool, Rev.member(span, Fg.quoted.key(q)), True{}, hs) : {Rev.member(Fg.targets.of(ForgetL.picks.of.picked(Fg.picked.join(_, Fg.quoted.forgot(q), Fg.picks.of(ns, _, q), Fg.picked(rest, span, ns)))), d) == True{} : Bool}
      join_here(True{}, Fg.quoted.forgot(q), Fg.picks.of(ns, True{}, q), Fg.picked(rest, span, ns), d, taken_picked(ns, q, d, hd))
    case +q0 <> +rest 1n+j:
      join_rest(Rev.member(span, Fg.quoted.key(q0)), Fg.quoted.forgot(q0), Fg.picks.of(ns, Rev.member(span, Fg.quoted.key(q0)), q0), Fg.picked(rest, span, ns), d, picked_mem(rest, span, ns, j, q, d, hq, hs, hd))

def keep_pick(b: Bool, +span: List<&2, String>, +m: String, +k: String, h: {Rev.member(span, k) == True{} : Bool}) -> {Rev.member(Bool.pick(List<&2, String>, b, span, List.append(&2, String, span, [m])), k) == True{} : Bool}:
  match b:
    case True{}:
      h
    case False{}:
      mem_app_l(span, [m], k, h)

def grown_keeps(more: List<&2, String>, +span: List<&2, String>, +k: String, h: {Rev.member(span, k) == True{} : Bool}) -> {Rev.member(Fg.copies.grown(more, span), k) == True{} : Bool}:
  match more:
    case Nil{}:
      h
    case +m <> rest:
      grown_keeps(rest, Bool.pick(List<&2, String>, Rev.member(span, m), span, List.append(&2, String, span, [m])), k, keep_pick(Rev.member(span, m), span, m, k, h))

def pick_keeps(b: Bool, -span: List<&2, String>, -x: List<&2, String>, -k: String, h: {Rev.member(span, k) == True{} : Bool}, hx: {Rev.member(x, k) == True{} : Bool}) -> {Rev.member(Bool.pick(List<&2, String>, b, span, x), k) == True{} : Bool}:
  match b:
    case True{}:
      h
    case False{}:
      hx

def go_grows(fuel: Nat, +every: List<&2, Fg.FgQuoted>, +span: List<&2, String>, +k: String, +h: {Rev.member(span, k) == True{} : Bool}) -> {Rev.member(Fg.copies.go(fuel, every, span), k) == True{} : Bool}:
  match fuel:
    case 0n:
      h
    case 1n+p:
      +next = Fg.copies.grown(Fg.copies.step(every, every, span), span)
      pick_keeps(Nat.is_eq(List.length(&2, String, next), List.length(&2, String, span)), span, Fg.copies.go(p, every, next), k, h, go_grows(p, every, next, k, grown_keeps(Fg.copies.step(every, every, span), span, k, h)))

# What a resolution copied only adds to the span: every element it named
# is still in it.
def copies_grows(+every: List<&2, Fg.FgQuoted>, +span: List<&2, String>, +k: String, +h: {Rev.member(span, k) == True{} : Bool}) -> {Rev.member(Fg.copies(every, span), k) == True{} : Bool}:
  go_grows(1n+List.length(&2, Fg.FgQuoted, every), every, span, k, h)

# Every document quoting an element of the span is among those the plan
# rewrites.
def rewrites_every(+fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +file: String, +span: List<&2, String>, +every: List<&2, Fg.FgQuoted>, +plan: Fg.FgPlan, +e: {Fg.lines.every(fs, ds, file, span, Done{every}) == Done{plan} : Result<&2, &2, Main.Refused, Fg.FgPlan>}, +i: Nat, +q: Fg.FgQuoted, +hq: {List.get(&2, Fg.FgQuoted, every, i) == Some{q} : Maybe<&2, Fg.FgQuoted>}, +hs: {Rev.member(span, Fg.quoted.key(q)) == True{} : Bool}, +d: String, +hd: {quotes(q, Fg.named(fs, file), d) == True{} : Bool}) -> {Rev.member(plan.targets(plan), d) == True{} : Bool}:
  +ns = Fg.named(fs, file)
  +pk = Fg.picked(every, Fg.copies(every, span), ns)
  +ps = ForgetL.picks.of.picked(pk)
  +m1 = picked_mem(every, Fg.copies(every, span), ns, i, q, d, hq, copies_grows(every, span, Fg.quoted.key(q), hs), hd)
  %ForgetL.lines_of(ds, pk, plan, e) : {Rev.member(_, d) == True{} : Bool}
  FetchL.distinct_mem(List.sort(~String, ~(a => b => String.is_le(a, b)), Fg.targets.of(ps)), d, FetchL.sort_mem(Fg.targets.of(ps), d, m1))

def fail_done(-x: Main.Refused, -plan: Fg.FgPlan, e: {Fail{x} == Done{plan} : Result<&2, &2, Main.Refused, Fg.FgPlan>}) -> Empty:
  Comp.false_true(Equal.cong(Result<&2, &2, Main.Refused, Fg.FgPlan>, Bool, r => Result.is_done(&2, &2, Main.Refused, Fg.FgPlan, r), Fail{x}, Done{plan}, e))

def within_every(+fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +id: String, +file: String, +first: String, +last: String, +visible: List<&2, Fg.FgQuoted>, ok: Result<&2, &2, Main.Refused, Unit>, +plan: Fg.FgPlan, e: {Fg.lines.within(fs, ds, id, file, first, last, visible, ok) == Done{plan} : Result<&2, &2, Main.Refused, Fg.FgPlan>}, +every: List<&2, Fg.FgQuoted>, +ev: {Fg.quotes(Fg.by_digest(fs), ds, id, file) == Done{every} : Result<&2, &2, String, List<&2, Fg.FgQuoted>>}) -> {Fg.lines.every(fs, ds, file, Fg.span.keys(visible, first, last), Done{every}) == Done{plan} : Result<&2, &2, Main.Refused, Fg.FgPlan>}:
  match ok:
    case Fail{x}:
      Empty.absurd({Fg.lines.every(fs, ds, file, Fg.span.keys(visible, first, last), Done{every}) == Done{plan} : Result<&2, &2, Main.Refused, Fg.FgPlan>}, fail_done(x, plan, e))
    case Done{u}:
      Equal.trans(Result<&2, &2, Main.Refused, Fg.FgPlan>, Fg.lines.every(fs, ds, file, Fg.span.keys(visible, first, last), Done{every}), Fg.lines.every(fs, ds, file, Fg.span.keys(visible, first, last), Fg.refused.of(List<&2, Fg.FgQuoted>, Fg.quotes(Fg.by_digest(fs), ds, id, file))), Done{plan},
        Equal.cong(Result<&2, &2, String, List<&2, Fg.FgQuoted>>, Result<&2, &2, Main.Refused, Fg.FgPlan>, r => Fg.lines.every(fs, ds, file, Fg.span.keys(visible, first, last), Fg.refused.of(List<&2, Fg.FgQuoted>, r)), Done{every}, Fg.quotes(Fg.by_digest(fs), ds, id, file), Equal.sym(Result<&2, &2, String, List<&2, Fg.FgQuoted>>, Fg.quotes(Fg.by_digest(fs), ds, id, file), Done{every}, ev)),
        e)

def checked_every(+fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +id: String, +file: String, +first: String, +last: String, ok: Result<&2, &2, Main.Refused, Unit>, +plan: Fg.FgPlan, e: {Fg.lines.checked(fs, ds, id, file, first, last, ok) == Done{plan} : Result<&2, &2, Main.Refused, Fg.FgPlan>}, +at: List<&2, Fg.FgQuoted>, +ea: {Fg.quotes(Main.walked.ancestry(fs, id), ds, id, file) == Done{at} : Result<&2, &2, String, List<&2, Fg.FgQuoted>>}, +every: List<&2, Fg.FgQuoted>, +ev: {Fg.quotes(Fg.by_digest(fs), ds, id, file) == Done{every} : Result<&2, &2, String, List<&2, Fg.FgQuoted>>}) -> {Fg.lines.every(fs, ds, file, Fg.span.keys(Fg.quoted.visible(at), first, last), Done{every}) == Done{plan} : Result<&2, &2, Main.Refused, Fg.FgPlan>}:
  match ok:
    case Fail{x}:
      Empty.absurd({Fg.lines.every(fs, ds, file, Fg.span.keys(Fg.quoted.visible(at), first, last), Done{every}) == Done{plan} : Result<&2, &2, Main.Refused, Fg.FgPlan>}, fail_done(x, plan, e))
    case Done{u}:
      +visible = Fg.quoted.visible(at)
      +e2 = Equal.trans(Result<&2, &2, Main.Refused, Fg.FgPlan>, Fg.lines.at(fs, ds, id, file, first, last, Done{at}), Fg.lines.at(fs, ds, id, file, first, last, Fg.refused.of(List<&2, Fg.FgQuoted>, Fg.quotes(Main.walked.ancestry(fs, id), ds, id, file))), Done{plan},
        Equal.cong(Result<&2, &2, String, List<&2, Fg.FgQuoted>>, Result<&2, &2, Main.Refused, Fg.FgPlan>, r => Fg.lines.at(fs, ds, id, file, first, last, Fg.refused.of(List<&2, Fg.FgQuoted>, r)), Done{at}, Fg.quotes(Main.walked.ancestry(fs, id), ds, id, file), Equal.sym(Result<&2, &2, String, List<&2, Fg.FgQuoted>>, Fg.quotes(Main.walked.ancestry(fs, id), ds, id, file), Done{at}, ea)),
        e)
      within_every(fs, ds, id, file, first, last, visible, Fg.span.within.r(last, List.length(&2, Fg.FgQuoted, visible)), plan, e2, every, ev)

# Forgetting lines `first..last` of a file rewrites every document that
# quotes them: for each element the history ever wrote to the file whose
# key is among the lines the span names at the revision, the document its
# author names for the file and each one whose delete quotes it.
def rewrites_quoting(+fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +id: String, +file: String, +first: String, +last: String, +plan: Fg.FgPlan, +e: {Fg.lines.plan.r(fs, ds, id, file, first, last) == Done{plan} : Result<&2, &2, Main.Refused, Fg.FgPlan>}, +at: List<&2, Fg.FgQuoted>, +ea: {Fg.quotes(Main.walked.ancestry(fs, id), ds, id, file) == Done{at} : Result<&2, &2, String, List<&2, Fg.FgQuoted>>}, +every: List<&2, Fg.FgQuoted>, +ev: {Fg.quotes(Fg.by_digest(fs), ds, id, file) == Done{every} : Result<&2, &2, String, List<&2, Fg.FgQuoted>>}, +i: Nat, +q: Fg.FgQuoted, +hq: {List.get(&2, Fg.FgQuoted, every, i) == Some{q} : Maybe<&2, Fg.FgQuoted>}, +hs: {Rev.member(Fg.span.keys(Fg.quoted.visible(at), first, last), Fg.quoted.key(q)) == True{} : Bool}, +d: String, +hd: {quotes(q, Fg.named(fs, file), d) == True{} : Bool}) -> {Rev.member(plan.targets(plan), d) == True{} : Bool}:
  rewrites_every(fs, ds, file, Fg.span.keys(Fg.quoted.visible(at), first, last), every, plan, checked_every(fs, ds, id, file, first, last, Fg.span.checked.r(first, last), plan, e, at, ea, every, ev), i, q, hq, hs, d, hd)
