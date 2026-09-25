# What `update` decides. It reads its words as they say; where it plans at
# all, every path the target's tree holds with one file lands in the folder
# as the target records it — a file of lines with its text, a file of bytes
# with its payload, each with its mode, and a link pointing where the tree
# says; and nothing it writes over or takes away holds bytes no revision
# records, which is decision 0030's rule.
import Base
import ./text.bend as T
import ./tree.bend as Tree
import ./revision.bend as Rev
import ./update.bend as U
import ./commands.bend as Main
import ./string_lemmas.bend as SL
import ./hunk_lemmas.bend as HL
import ./anchor_lemmas.bend as AL
import ./composition_lemmas.bend as Comp

# Results
# -------

def rdisc(-E: Data, -A: Data, r: Result<&2, &2, E, A>) -> Type:
  match r:
    case Done{x}:
      Empty
    case Fail{e}:
      Unit

def fail_done(-E: Data, -A: Data, -e: E, -x: A, h: {Fail{e} == Done{x} : Result<&2, &2, E, A>}) -> Empty:
  %h : {rdisc(E, A, _) : Type}
  Unit{}

def done_eq(-E: Data, -A: Data, -a: A, -b: A, h: {Done{a} == Done{b} : Result<&2, &2, E, A>}) -> {a == b : A}:
  Equal.cong(Result<&2, &2, E, A>, A, r => Result.default(&2, &2, E, A, r, a), Done{a}, Done{b}, h)

def ldisc(xs: List<&2, T.Split>) -> Type:
  match xs:
    case Nil{}:
      Empty
    case x <> rest:
      Unit

def cons_nil(-x: T.Split, -xs: List<&2, T.Split>, e: {x <> xs == Nil{} : List<&2, T.Split>}) -> Empty:
  %e : {ldisc(_) : Type}
  Unit{}

# Its words
# ---------

def none_or(t: Maybe<&2, String>) -> {t == Maybe.or(&2, String, t, None{}) : Maybe<&2, String>}:
  match t:
    case None{}:
      {==}
    case Some{x}:
      {==}

def false_or(d: Bool) -> {d == Bool.or(d, False{}) : Bool}:
  match d:
    case True{}:
      {==}
    case False{}:
      {==}

# The dry-run flag is a flag: a word that is `-n` or `--dry-run` begins
# with `-`, so it is never read as the target.
def dash.of(+w: String, x: Bool, hx: {String.eq(w, "-n") == x : Bool}, y: Bool, hy: {String.eq(w, "--dry-run") == y : Bool}) -> {Bool.and(Bool.or(x, y), Bool.not(String.starts_with(w, "-"))) == False{} : Bool}:
  match x:
    case True{}:
      %Equal.sym(String, w, "-n", SL.eq_true(w, "-n", hx)) : {Bool.not(String.starts_with(_, "-")) == False{} : Bool}
      {==}
    case False{}:
      match y:
        case True{}:
          %Equal.sym(String, w, "--dry-run", SL.eq_true(w, "--dry-run", hy)) : {Bool.not(String.starts_with(_, "-")) == False{} : Bool}
          {==}
        case False{}:
          {==}

def dash(+w: String) -> {Bool.and(Bool.or(String.eq(w, "-n"), String.eq(w, "--dry-run")), Bool.not(String.starts_with(w, "-"))) == False{} : Bool}:
  dash.of(w, String.eq(w, "-n"), {==}, String.eq(w, "--dry-run"), {==})

def args_word(+w: String, +rest: List<&2, String>, +d: Bool, +c: U.UpdateCmd, a: Bool, +b: Bool, +t: Maybe<&2, String>, imp: {Bool.and(a, Bool.not(b)) == False{} : Bool}, e: {U.args.go(w <> rest, t, d, U.uword.of(a, b)) == Done{c} : Result<&2, &2, Main.Refused, U.UpdateCmd>}, ih: @t2: Maybe<&2, String> -> @d2: Bool -> @c2: U.UpdateCmd -> {U.args.go(rest, t2, d2, U.uword(rest)) == Done{c2} : Result<&2, &2, Main.Refused, U.UpdateCmd>} -> {c2 == U.UpdateCmd{Maybe.or(&2, String, t2, U.uargs.target(rest)), Bool.or(d2, U.uargs.dry(rest))} : U.UpdateCmd}) -> {c == U.UpdateCmd{Maybe.or(&2, String, t, Bool.pick(Maybe<&2, String>, b, U.uargs.target(rest), Some{w})), Bool.or(d, Bool.or(a, U.uargs.dry(rest)))} : U.UpdateCmd}:
  match a:
    case True{}:
      match t:
        case None{}:
          %Equal.sym(Bool, b, True{}, HL.not_false(b, imp)) : {c == U.UpdateCmd{Bool.pick(Maybe<&2, String>, _, U.uargs.target(rest), Some{w}), Bool.or(d, True{})} : U.UpdateCmd}
          %Equal.sym(Bool, Bool.or(d, True{}), True{}, HL.or_true_r(d)) : {c == U.UpdateCmd{U.uargs.target(rest), _} : U.UpdateCmd}
          ih(None{}, True{}, c, e)
        case Some{x}:
          %Equal.sym(Bool, Bool.or(d, True{}), True{}, HL.or_true_r(d)) : {c == U.UpdateCmd{Some{x}, _} : U.UpdateCmd}
          ih(Some{x}, True{}, c, e)
    case False{}:
      match b:
        case True{}:
          match t:
            case None{}:
              Empty.absurd({c == U.UpdateCmd{U.uargs.target(rest), Bool.or(d, U.uargs.dry(rest))} : U.UpdateCmd}, fail_done(Main.Refused, U.UpdateCmd, Main.Refused{2, "`" ++ w ++ "` is not an `update` option"}, c, e))
            case Some{x}:
              Empty.absurd({c == U.UpdateCmd{Some{x}, Bool.or(d, U.uargs.dry(rest))} : U.UpdateCmd}, fail_done(Main.Refused, U.UpdateCmd, Main.Refused{2, "`" ++ w ++ "` is not an `update` option"}, c, e))
        case False{}:
          match t:
            case None{}:
              ih(Some{w}, d, c, e)
            case Some{x}:
              Empty.absurd({c == U.UpdateCmd{Some{x}, Bool.or(d, U.uargs.dry(rest))} : U.UpdateCmd}, fail_done(Main.Refused, U.UpdateCmd, Main.Refused{2, "`update` takes one target, and `" ++ w ++ "` is a second"}, c, e))

def args_go(ws: List<&2, String>, +t: Maybe<&2, String>, +d: Bool, +c: U.UpdateCmd, e: {U.args.go(ws, t, d, U.uword(ws)) == Done{c} : Result<&2, &2, Main.Refused, U.UpdateCmd>}) -> {c == U.UpdateCmd{Maybe.or(&2, String, t, U.uargs.target(ws)), Bool.or(d, U.uargs.dry(ws))} : U.UpdateCmd}:
  match ws:
    case Nil{}:
      %done_eq(Main.Refused, U.UpdateCmd, U.UpdateCmd{t, d}, c, e) : {_ == U.UpdateCmd{Maybe.or(&2, String, t, None{}), Bool.or(d, False{})} : U.UpdateCmd}
      %none_or(t) : {U.UpdateCmd{t, d} == U.UpdateCmd{_, Bool.or(d, False{})} : U.UpdateCmd}
      %false_or(d) : {U.UpdateCmd{t, d} == U.UpdateCmd{t, _} : U.UpdateCmd}
      {==}
    case +w <> +rest:
      args_word(w, rest, d, c, Bool.or(String.eq(w, "-n"), String.eq(w, "--dry-run")), String.starts_with(w, "-"), t, dash(w), e, t2 => d2 => c2 => h => args_go(rest, t2, d2, c2, h))

# `update` reads its words as they say.
def args_said(+ws: List<&2, String>, +c: U.UpdateCmd, e: {U.args.r(ws) == Done{c} : Result<&2, &2, Main.Refused, U.UpdateCmd>}) -> {c == U.UpdateCmd{U.uargs.target(ws), U.uargs.dry(ws)} : U.UpdateCmd}:
  args_go(ws, None{}, False{}, c, e)

# What lands
# ----------

# A step that is not a refusal leaves the path holding what the target
# records: stated for one path, as a Bool, so that a refusal counts too.
def refused(s: U.Step) -> Bool:
  match s:
    case U.Step.Refuse{b}:
      True{}
    case _:
      False{}

def sound(+w: U.Wants, +h: U.Held, +s: U.Step) -> Bool:
  Bool.or(refused(s), U.lands(w, U.after(w, h, s)))

def xor_self(x: Bool) -> {Bool.not(Bool.xor(x, x)) == True{} : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      {==}

# Bytes written are the bytes wanted, with the mode wanted.
def written(+dg: String, +r: Bool) -> {Bool.and(String.eq(dg, dg), Bool.not(Bool.xor(r, r))) == True{} : Bool}:
  AL.and_intro(String.eq(dg, dg), Bool.not(Bool.xor(r, r)), SL.eq_refl(dg), xor_self(r))

# A file of lines or of bytes, where the folder holds a file: the same
# bytes need at most the mode, and other bytes are written whole.
def file_on_file(+dg: String, +w: U.Wants, hd: {U.wants.digest(w) == dg : String}, +r: Bool, hr: {U.wants.runs(w) == r : Bool}, hl: @h2: U.Held -> {U.lands(w, h2) == U.lands.file(dg, r, h2) : Bool}, +d: String, +x: Bool, e1: Bool, h1: {String.eq(d, dg) == e1 : Bool}, e2: Bool, h2: {Bool.xor(x, r) == e2 : Bool}, e3: Bool) -> {sound(w, U.Held.File{d, x}, Bool.pick(U.Step, e1, Bool.pick(U.Step, e2, U.Step.Mode{}, U.Step.Keep{}), Bool.pick(U.Step, e3, U.Step.Write{}, U.Step.Refuse{U.UNRECORDED()}))) == True{} : Bool}:
  match e1:
    case True{}:
      match e2:
        case True{}:
          %Equal.sym(Bool, U.lands(w, U.Held.File{d, U.wants.runs(w)}), U.lands.file(dg, r, U.Held.File{d, U.wants.runs(w)}), hl(U.Held.File{d, U.wants.runs(w)})) : {_ == True{} : Bool}
          %Equal.sym(Bool, U.wants.runs(w), r, hr) : {Bool.and(String.eq(d, dg), Bool.not(Bool.xor(_, r))) == True{} : Bool}
          %Equal.sym(Bool, String.eq(d, dg), True{}, h1) : {Bool.and(_, Bool.not(Bool.xor(r, r))) == True{} : Bool}
          xor_self(r)
        case False{}:
          %Equal.sym(Bool, U.lands(w, U.Held.File{d, x}), U.lands.file(dg, r, U.Held.File{d, x}), hl(U.Held.File{d, x})) : {_ == True{} : Bool}
          %Equal.sym(Bool, String.eq(d, dg), True{}, h1) : {Bool.and(_, Bool.not(Bool.xor(x, r))) == True{} : Bool}
          %Equal.sym(Bool, Bool.xor(x, r), False{}, h2) : {Bool.not(_) == True{} : Bool}
          {==}
    case False{}:
      match e3:
        case True{}:
          %Equal.sym(Bool, U.lands(w, U.Held.File{U.wants.digest(w), U.wants.runs(w)}), U.lands.file(dg, r, U.Held.File{U.wants.digest(w), U.wants.runs(w)}), hl(U.Held.File{U.wants.digest(w), U.wants.runs(w)})) : {_ == True{} : Bool}
          %Equal.sym(String, U.wants.digest(w), dg, hd) : {U.lands.file(dg, r, U.Held.File{_, U.wants.runs(w)}) == True{} : Bool}
          %Equal.sym(Bool, U.wants.runs(w), r, hr) : {U.lands.file(dg, r, U.Held.File{dg, _}) == True{} : Bool}
          written(dg, r)
        case False{}:
          {==}

# A file wanted where the folder holds nothing is written; anything else
# the walk did not take refuses.
def file_sound(+dg: String, +w: U.Wants, hd: {U.wants.digest(w) == dg : String}, +r: Bool, hr: {U.wants.runs(w) == r : Bool}, hl: @h2: U.Held -> {U.lands(w, h2) == U.lands.file(dg, r, h2) : Bool}, +m: Tree.Mode, hm: {U.runs(m) == r : Bool}, h: U.Held, +rs: List<&2, String>) -> {sound(w, h, U.decide.file(dg, m, h, rs)) == True{} : Bool}:
  match h:
    case U.Held.File{+d, +x}:
      %Equal.sym(Bool, U.runs(m), r, hm) : {sound(w, U.Held.File{d, x}, Bool.pick(U.Step, String.eq(d, dg), Bool.pick(U.Step, Bool.xor(x, _), U.Step.Mode{}, U.Step.Keep{}), Bool.pick(U.Step, Rev.member(rs, d), U.Step.Write{}, U.Step.Refuse{U.UNRECORDED()}))) == True{} : Bool}
      file_on_file(dg, w, hd, r, hr, hl, d, x, String.eq(d, dg), {==}, Bool.xor(x, r), {==}, Rev.member(rs, d))
    case U.Held.Link{t}:
      {==}
    case U.Held.Unread{}:
      {==}
    case U.Held.Dir{}:
      {==}
    case U.Held.Other{}:
      {==}
    case U.Held.Nothing{}:
      %Equal.sym(Bool, U.lands(w, U.Held.File{U.wants.digest(w), U.wants.runs(w)}), U.lands.file(dg, r, U.Held.File{U.wants.digest(w), U.wants.runs(w)}), hl(U.Held.File{U.wants.digest(w), U.wants.runs(w)})) : {_ == True{} : Bool}
      %Equal.sym(String, U.wants.digest(w), dg, hd) : {U.lands.file(dg, r, U.Held.File{_, U.wants.runs(w)}) == True{} : Bool}
      %Equal.sym(Bool, U.wants.runs(w), r, hr) : {U.lands.file(dg, r, U.Held.File{dg, _}) == True{} : Bool}
      written(dg, r)

# A link wanted: kept where it already points there, and otherwise made to.
def link_kept(+t: String, +x: String, e: Bool, he: {String.eq(x, t) == e : Bool}) -> {sound(U.Wants.Link{t}, U.Held.Link{x}, Bool.pick(U.Step, e, U.Step.Keep{}, U.Step.Link{})) == True{} : Bool}:
  match e:
    case True{}:
      he
    case False{}:
      SL.eq_refl(t)

def link_filed(+t: String, +d: String, +x: Bool, e: Bool) -> {sound(U.Wants.Link{t}, U.Held.File{d, x}, Bool.pick(U.Step, e, U.Step.Link{}, U.Step.Refuse{U.UNRECORDED()})) == True{} : Bool}:
  match e:
    case True{}:
      SL.eq_refl(t)
    case False{}:
      {==}

def link_sound(+t: String, h: U.Held, +rs: List<&2, String>) -> {sound(U.Wants.Link{t}, h, U.decide.link(t, h, rs)) == True{} : Bool}:
  match h:
    case U.Held.Link{+x}:
      link_kept(t, x, String.eq(x, t), {==})
    case U.Held.File{+d, +x}:
      link_filed(t, d, x, Rev.member(rs, d))
    case U.Held.Nothing{}:
      SL.eq_refl(t)
    case U.Held.Dir{}:
      {==}
    case U.Held.Unread{}:
      {==}
    case U.Held.Other{}:
      {==}

# Every step `decide` takes lands the path, or refuses.
def decide_sound(w: U.Wants, +h: U.Held, +rs: List<&2, String>) -> {sound(w, h, U.decide(w, h, rs)) == True{} : Bool}:
  match w:
    case U.Wants.Lines{+text, +m}:
      file_sound(U.text_digest(text), U.Wants.Lines{text, m}, {==}, U.runs(m), {==}, h2 => {==}, m, {==}, h, rs)
    case U.Wants.Whole{+p, +at, +m}:
      file_sound(p, U.Wants.Whole{p, at, m}, {==}, U.runs(m), {==}, h2 => {==}, m, {==}, h, rs)
    case U.Wants.Link{+t}:
      link_sound(t, h, rs)
    case U.Wants.No{b}:
      {==}

def lands_one(+p: String, +w: U.Wants, +h: U.Held, +rs: List<&2, String>, s: U.Step, ok: {sound(w, h, s) == True{} : Bool}, +rest: List<&2, U.Decided>, e: {U.refusals(U.Decided{p, w, h, rs, s} <> rest) == Nil{} : List<&2, T.Split>}, ih: {U.refusals(rest) == Nil{} : List<&2, T.Split>} -> {U.lands_all(rest) == True{} : Bool}) -> {U.lands_all(U.Decided{p, w, h, rs, s} <> rest) == True{} : Bool}:
  match s:
    case U.Step.Refuse{b}:
      Empty.absurd({U.lands_all(U.Decided{p, w, h, rs, U.Step.Refuse{b}} <> rest) == True{} : Bool}, cons_nil(T.Split{p, b}, U.refusals(rest), e))
    case U.Step.Keep{}:
      AL.and_intro(U.lands(w, U.after(w, h, U.Step.Keep{})), U.lands_all(rest), ok, ih(e))
    case U.Step.Write{}:
      AL.and_intro(U.lands(w, U.after(w, h, U.Step.Write{})), U.lands_all(rest), ok, ih(e))
    case U.Step.Mode{}:
      AL.and_intro(U.lands(w, U.after(w, h, U.Step.Mode{})), U.lands_all(rest), ok, ih(e))
    case U.Step.Link{}:
      AL.and_intro(U.lands(w, U.after(w, h, U.Step.Link{})), U.lands_all(rest), ok, ih(e))

# Where no path of the target refuses, every one lands.
def lands_decided(ls: List<&2, U.Look>, e: {U.refusals(U.decided(ls)) == Nil{} : List<&2, T.Split>}) -> {U.lands_all(U.decided(ls)) == True{} : Bool}:
  match ls:
    case Nil{}:
      {==}
    case U.Look{+p, +w, +h, +rs} <> +rest:
      lands_one(p, w, h, rs, U.decide(w, h, rs), decide_sound(w, h, rs), U.decided(rest), e, hr => lands_decided(rest, hr))

def plan_of(+ls: List<&2, U.Look>, +ws: List<&2, U.Went>, r: List<&2, T.Split>, hr: {U.refusals(U.decided(ls)) == r : List<&2, T.Split>}, +p: U.Plan, e: {U.plan.of(U.decided(ls), ws, r) == Done{p} : Result<&2, &2, List<&2, T.Split>, U.Plan>}) -> {U.landed(p) == True{} : Bool}:
  match r:
    case Nil{}:
      %done_eq(List<&2, T.Split>, U.Plan, U.Plan{U.decided(ls), ws}, p, e) : {U.landed(_) == True{} : Bool}
      lands_decided(ls, hr)
    case +x <> +more:
      Empty.absurd({U.landed(p) == True{} : Bool}, fail_done(List<&2, T.Split>, U.Plan, U.sorted_refusals(x <> more), p, e))

# Where `update` plans at all, every path of the target's tree it steps
# through holds, once its step is done, what the target records there.
def plan_lands(tr: List<&2, T.Split>, +ls: List<&2, U.Look>, +gs: List<&2, U.Gone>, +p: U.Plan, e: {U.plan(tr, ls, gs) == Done{p} : Result<&2, &2, List<&2, T.Split>, U.Plan>}) -> {U.landed(p) == True{} : Bool}:
  match tr:
    case Nil{}:
      plan_of(ls, U.went(gs), U.refusals(U.decided(ls)), {==}, p, e)
    case +x <> +more:
      Empty.absurd({U.landed(p) == True{} : Bool}, fail_done(List<&2, T.Split>, U.Plan, U.sorted_refusals(x <> List.append(&2, T.Split, more, U.refusals(U.decided(ls)))), p, e))

# What is spared
# --------------

def spared_file(+d: String, +x: Bool, +rs: List<&2, String>, e1: Bool, e2: Bool, e3: Bool, h3: {Rev.member(rs, d) == e3 : Bool}) -> {U.spared.step(U.Held.File{d, x}, rs, U.replaces(Bool.pick(U.Step, e1, Bool.pick(U.Step, e2, U.Step.Mode{}, U.Step.Keep{}), Bool.pick(U.Step, e3, U.Step.Write{}, U.Step.Refuse{U.UNRECORDED()})))) == True{} : Bool}:
  match e1:
    case True{}:
      match e2:
        case True{}:
          {==}
        case False{}:
          {==}
    case False{}:
      match e3:
        case True{}:
          h3
        case False{}:
          {==}

def spared_decide.file(+dg: String, +m: Tree.Mode, h: U.Held, +rs: List<&2, String>) -> {U.spared.step(h, rs, U.replaces(U.decide.file(dg, m, h, rs))) == True{} : Bool}:
  match h:
    case U.Held.File{+d, +x}:
      spared_file(d, x, rs, String.eq(d, dg), Bool.xor(x, U.runs(m)), Rev.member(rs, d), {==})
    case U.Held.Link{t}:
      {==}
    case U.Held.Unread{}:
      {==}
    case U.Held.Dir{}:
      {==}
    case U.Held.Other{}:
      {==}
    case U.Held.Nothing{}:
      {==}

def spared_link(+d: String, +x: Bool, +rs: List<&2, String>, e: Bool, he: {Rev.member(rs, d) == e : Bool}) -> {U.spared.step(U.Held.File{d, x}, rs, U.replaces(Bool.pick(U.Step, e, U.Step.Link{}, U.Step.Refuse{U.UNRECORDED()}))) == True{} : Bool}:
  match e:
    case True{}:
      he
    case False{}:
      {==}

def spared_relink(+x: String, +rs: List<&2, String>, e: Bool) -> {U.spared.step(U.Held.Link{x}, rs, U.replaces(Bool.pick(U.Step, e, U.Step.Keep{}, U.Step.Link{}))) == True{} : Bool}:
  match e:
    case True{}:
      {==}
    case False{}:
      {==}

def spared_decide.link(+t: String, h: U.Held, +rs: List<&2, String>) -> {U.spared.step(h, rs, U.replaces(U.decide.link(t, h, rs))) == True{} : Bool}:
  match h:
    case U.Held.Link{+x}:
      spared_relink(x, rs, String.eq(x, t))
    case U.Held.File{+d, +x}:
      spared_link(d, x, rs, Rev.member(rs, d), {==})
    case U.Held.Nothing{}:
      {==}
    case U.Held.Dir{}:
      {==}
    case U.Held.Unread{}:
      {==}
    case U.Held.Other{}:
      {==}

# No step writes over a file whose bytes no revision records.
def spared_decide(w: U.Wants, +h: U.Held, +rs: List<&2, String>) -> {U.spared.step(h, rs, U.replaces(U.decide(w, h, rs))) == True{} : Bool}:
  match w:
    case U.Wants.Lines{+text, +m}:
      spared_decide.file(U.text_digest(text), m, h, rs)
    case U.Wants.Whole{+p, at, +m}:
      spared_decide.file(p, m, h, rs)
    case U.Wants.Link{+t}:
      spared_decide.link(t, h, rs)
    case U.Wants.No{b}:
      {==}

def spared_steps(ls: List<&2, U.Look>) -> {U.spared.steps(U.decided(ls)) == True{} : Bool}:
  match ls:
    case Nil{}:
      {==}
    case U.Look{+p, +w, +h, +rs} <> rest:
      AL.and_intro(U.spared.step(h, rs, U.replaces(U.decide(w, h, rs))), U.spared.steps(U.decided(rest)), spared_decide(w, h, rs), spared_steps(rest))

# A path the target does not hold is taken away only where some revision
# records what it holds: a file's bytes, or where a link points.
def went_of(+rs: List<&2, String>, -h: U.Held, e: Bool, he: {U.spared.gone(h, rs) == e : Bool}, t: Bool) -> {U.spared.went(h, rs, U.leaving.of(e, t)) == True{} : Bool}:
  match e:
    case True{}:
      he
    case False{}:
      match t:
        case True{}:
          {==}
        case False{}:
          {==}

def spared_went(h: U.Held, +rs: List<&2, String>, t: Bool) -> {U.spared.went(h, rs, U.leaving(h, rs, t)) == True{} : Bool}:
  match h:
    case U.Held.File{+d, +x}:
      went_of(rs, U.Held.File{d, x}, Rev.member(rs, d), {==}, t)
    case U.Held.Link{+x}:
      went_of(rs, U.Held.Link{x}, Rev.member(rs, x), {==}, t)
    case U.Held.Dir{}:
      {==}
    case U.Held.Unread{}:
      {==}
    case U.Held.Other{}:
      {==}
    case U.Held.Nothing{}:
      {==}

def spared_gones(gs: List<&2, U.Gone>) -> {U.spared.gones(U.went(gs)) == True{} : Bool}:
  match gs:
    case Nil{}:
      {==}
    case U.Gone{+p, +h, +rs, +t} <> rest:
      AL.and_intro(U.spared.went(h, rs, U.leaving(h, rs, t)), U.spared.gones(U.went(rest)), spared_went(h, rs, t), spared_gones(rest))

def spared_plan.of(+ls: List<&2, U.Look>, +gs: List<&2, U.Gone>, r: List<&2, T.Split>, +p: U.Plan, e: {U.plan.of(U.decided(ls), U.went(gs), r) == Done{p} : Result<&2, &2, List<&2, T.Split>, U.Plan>}) -> {U.spared(p) == True{} : Bool}:
  match r:
    case Nil{}:
      %done_eq(List<&2, T.Split>, U.Plan, U.Plan{U.decided(ls), U.went(gs)}, p, e) : {U.spared(_) == True{} : Bool}
      AL.and_intro(U.spared.steps(U.decided(ls)), U.spared.gones(U.went(gs)), spared_steps(ls), spared_gones(gs))
    case +x <> +more:
      Empty.absurd({U.spared(p) == True{} : Bool}, fail_done(List<&2, T.Split>, U.Plan, U.sorted_refusals(x <> more), p, e))

# Nothing a plan writes over or takes away holds bytes no revision records.
def plan_spares(tr: List<&2, T.Split>, +ls: List<&2, U.Look>, +gs: List<&2, U.Gone>, +p: U.Plan, e: {U.plan(tr, ls, gs) == Done{p} : Result<&2, &2, List<&2, T.Split>, U.Plan>}) -> {U.spared(p) == True{} : Bool}:
  spared_plan.of(ls, gs, List.append(&2, T.Split, tr, U.refusals(U.decided(ls))), p, e)
