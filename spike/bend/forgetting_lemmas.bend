# What `forget` says, where it files what it writes, and what it sweeps:
# the output read back as a person or a script would read it, the paths it
# writes to held apart from what the store already has, and the empty
# directories it removes.
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

# The paths of the files of `operations/` the host listed.
def paths(fs: List<&2, Fg.FgFiled>) -> List<&2, String>:
  match fs:
    case Nil{}:
      Nil{}
    case Fg.Fg.Filed{+q, d, n} <> rest:
      q <> paths(rest)

def taken_paths(fs: List<&2, Fg.FgFiled>, +p: String) -> {Fg.filed.taken(fs, p) == Rev.member(paths(fs), p) : Bool}:
  match fs:
    case Nil{}:
      {==}
    case Fg.Fg.Filed{+q, d, n} <> +rest:
      %Equal.sym(Bool, Fg.filed.taken(rest, p), Rev.member(paths(rest), p), taken_paths(rest, p)) : {Bool.or(String.eq(q, p), _) == Bool.or(String.eq(q, p), Rev.member(paths(rest), p)) : Bool}
      {==}

def beside_free(b: Bool, +fs: List<&2, Fg.FgFiled>, +d: String, +named: String, eb: {Fg.filed.taken(fs, d ++ ".ops.txt") == b : Bool}, hf: {Rev.member(paths(fs), d ++ ".ops.txt") == False{} : Bool}) -> {Bool.pick(String, b, named, d ++ ".ops.txt") == d ++ ".ops.txt" : String}:
  match b:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({named == d ++ ".ops.txt" : String}, S.false_true(Equal.trans(Bool, False{}, Rev.member(paths(fs), d ++ ".ops.txt"), True{}, Equal.sym(Bool, Rev.member(paths(fs), d ++ ".ops.txt"), False{}, hf), Equal.trans(Bool, Rev.member(paths(fs), d ++ ".ops.txt"), Fg.filed.taken(fs, d ++ ".ops.txt"), True{}, Equal.sym(Bool, Fg.filed.taken(fs, d ++ ".ops.txt"), Rev.member(paths(fs), d ++ ".ops.txt"), taken_paths(fs, d ++ ".ops.txt")), eb))))

# A payload's stand-in is filed where the payload was, at the first file
# it destroys with `.ops.txt` added, wherever no file has that name.
def payload_beside(+fs: List<&2, Fg.FgFiled>, +d: String, +rest: List<&2, String>, f: String, +text: String, hf: {Rev.member(paths(fs), d ++ ".ops.txt") == False{} : Bool}) -> {Fg.filed.as(fs, d <> rest, Fg.Fg.Write{f, text, True{}}) == d ++ ".ops.txt" : String}:
  beside_free(Fg.filed.taken(fs, d ++ ".ops.txt"), fs, d, "operations/" ++ Sha.digest(Utf8.encode(text)) ++ ".ops.txt", {==}, hf)

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

def bool_t(e: Bool, m: Bool) -> {Bool.or(e, m) == Bool.or(m, Bool.and(e, True{})) : Bool}:
  match e m:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def bool_f(e: Bool, m: Bool) -> {m == Bool.or(m, Bool.and(e, False{})) : Bool}:
  match e m:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def kept_iff(b: Bool, +x: String, +xs: List<&2, String>, +p: String) -> {Rev.member(Rev.keep(b, x, xs), p) == Bool.or(Rev.member(xs, p), Bool.and(String.eq(x, p), b)) : Bool}:
  match b:
    case True{}:
      bool_t(String.eq(x, p), Rev.member(xs, p))
    case False{}:
      bool_f(String.eq(x, p), Rev.member(xs, p))

# One step of the sweep adds to what it removes exactly the directory it
# listed, where that listing was read and said nothing, and never
# `operations/` itself.
def sweeps(+dir: String, r: Result<&1, &1, U32 & String, String>, +found: List<&2, String>, +p: String) -> {Rev.member(Fg.swept.empty(dir, Fg.io.listed(r), found), p) == Bool.or(Rev.member(found, p), Bool.and(String.eq(dir, p), emptied(dir, r))) : Bool}:
  match r:
    case Done{+t}:
      kept_iff(Bool.and(Bool.not(String.is_empty(dir)), String.is_empty(t)), dir, found, p)
    case Fail{e}:
      kept_iff(Bool.and(Bool.not(String.is_empty(dir)), String.is_empty("u")), dir, found, p)

# A link's line and the target line after it name no directory, whatever
# the target says.
def past_link(+dir: String, x: String, +t: String, +rest: List<&2, String>) -> {Fg.swept.dirs(dir, ("l " ++ x) <> t <> rest, False{}) == Fg.swept.dirs(dir, rest, False{}) : List<&2, String>}:
  %Equal.sym(Bool, String.starts_with(x, SNil{}), True{}, sw_nil(x)) : {Rev.keep(False{}, Fg.swept.join(dir, String.drop("l " ++ x, 2n)), Fg.swept.dirs(dir, t <> rest, _)) == Fg.swept.dirs(dir, rest, False{}) : List<&2, String>}
  {==}

# The directories a listing names on its `d ` lines, each under the
# directory listed, read with no regard to links.
def named_dirs(+dir: String, ls: List<&2, String>) -> List<&2, String>:
  match ls:
    case Nil{}:
      Nil{}
    case +l <> rest:
      Rev.keep(String.starts_with(l, "d "), Bool.pick(String, String.is_empty(dir), String.drop(l, 2n), dir ++ "/" ++ String.drop(l, 2n)), named_dirs(dir, rest))

def keep_sub(b: Bool, +y: String, +xs: List<&2, String>, +ys: List<&2, String>, +p: String, h: {Rev.member(Rev.keep(b, y, xs), p) == True{} : Bool}, sub: {Rev.member(xs, p) == True{} : Bool} -> {Rev.member(ys, p) == True{} : Bool}) -> {Rev.member(Rev.keep(b, y, ys), p) == True{} : Bool}:
  match b:
    case True{}:
      GL.member_cons({Rev.member(y <> ys, p) == True{} : Bool}, y, xs, p, h,
        e => (%Equal.sym(String, y, p, e) : {Rev.member(_ <> ys, p) == True{} : Bool}; GL.member_head(p, ys)),
        t => GL.member_tail(y, ys, p, sub(t)))
    case False{}:
      sub(h)

def keep_more(b: Bool, +y: String, +ys: List<&2, String>, +p: String, h: {Rev.member(ys, p) == True{} : Bool}) -> {Rev.member(Rev.keep(b, y, ys), p) == True{} : Bool}:
  match b:
    case True{}:
      GL.member_tail(y, ys, p, h)
    case False{}:
      h

# Every directory the sweep goes on to list is one its parent's listing
# names on a `d ` line.
def dirs_named(+dir: String, ls: List<&2, String>, skip: Bool, +p: String, h: {Rev.member(Fg.swept.dirs(dir, ls, skip), p) == True{} : Bool}) -> {Rev.member(named_dirs(dir, ls), p) == True{} : Bool}:
  match ls skip:
    case Nil{} s:
      Empty.absurd({Rev.member(Nil{}, p) == True{} : Bool}, S.false_true(h))
    case +l <> +rest True{}:
      keep_more(String.starts_with(l, "d "), Bool.pick(String, String.is_empty(dir), String.drop(l, 2n), dir ++ "/" ++ String.drop(l, 2n)), named_dirs(dir, rest), p, dirs_named(dir, rest, False{}, p, h))
    case +l <> +rest False{}:
      keep_sub(String.starts_with(l, "d "), Fg.swept.join(dir, String.drop(l, 2n)), Fg.swept.dirs(dir, rest, String.starts_with(l, "l ")), named_dirs(dir, rest), p, h,
        t => dirs_named(dir, rest, String.starts_with(l, "l "), p, t))
