# What `update` decides. It reads its words as they say; where it plans at
# all, every path the target's tree holds with one file holds, once the
# plan is carried out, what `cat` of the target reads there — the bytes of
# a file of lines, the payload of a file of bytes, each with its mode, and
# a link pointing where `cat` says; and every file it writes over or takes
# away holds bytes `cat` of some revision the store holds reads, which is
# decision 0030's rule.
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
import ./store.bend as Store
import ./ops.bend as Ops
import ./folder.bend as Folder
import ./graph_lemmas.bend as GL

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

# What `update` leaves is what `cat` reads
# ----------------------------------------

def bytes_held(+dg: String, m: Tree.Mode, x: U.Held, h: {U.lands.file(dg, U.runs(m), x) == True{} : Bool}) -> {U.holds.bytes(x, dg, U.executable(m)) == True{} : Bool}:
  match m x:
    case Tree.Executable{} U.Held.File{d, r}:
      h
    case Tree.Plain{} U.Held.File{d, r}:
      h
    case m2 U.Held.Link{s}:
      Empty.absurd({U.holds.bytes(U.Held.Link{s}, dg, U.executable(m2)) == True{} : Bool}, Comp.false_true(h))
    case m2 U.Held.Dir{}:
      Empty.absurd({U.holds.bytes(U.Held.Dir{}, dg, U.executable(m2)) == True{} : Bool}, Comp.false_true(h))
    case m2 U.Held.Unread{}:
      Empty.absurd({U.holds.bytes(U.Held.Unread{}, dg, U.executable(m2)) == True{} : Bool}, Comp.false_true(h))
    case m2 U.Held.Other{}:
      Empty.absurd({U.holds.bytes(U.Held.Other{}, dg, U.executable(m2)) == True{} : Bool}, Comp.false_true(h))
    case m2 U.Held.Nothing{}:
      Empty.absurd({U.holds.bytes(U.Held.Nothing{}, dg, U.executable(m2)) == True{} : Bool}, Comp.false_true(h))

# A file of lines holds the text `cat` reads.
def lines_reads(+m: Tree.Mode, +x: U.Held, r: Result<&2, &2, String, List<&2, Ops.Item>>, h: {U.lands(U.wants.lines(m, r), x) == True{} : Bool}) -> {U.holds.lines(x, U.executable(m), r) == True{} : Bool}:
  match r:
    case Done{+items}:
      bytes_held(U.text_digest(Ops.text(items)), m, x, h)
    case Fail{e}:
      Empty.absurd({U.holds.lines(x, U.executable(m), Fail{e}) == True{} : Bool}, Comp.false_true(h))

def held_pick(b: Bool, +d: String, +m: Tree.Mode, +at: String, +x: U.Held, h: {U.lands(Bool.pick(U.Wants, b, U.Wants.No{"this store does not hold the content " ++ d ++ "; receive the rest first"}, U.Wants.Whole{d, at, m}), x) == True{} : Bool}) -> {U.holds.bytes(x, d, U.executable(m)) == True{} : Bool}:
  match b:
    case True{}:
      Empty.absurd({U.holds.bytes(x, d, U.executable(m)) == True{} : Bool}, Comp.false_true(h))
    case False{}:
      bytes_held(d, m, x, h)

# A file of bytes holds the payload its tree names.
def whole_reads(+located: Map<&2, String>, +m: Tree.Mode, +x: U.Held, y: Maybe<&2, String>, h: {U.lands(U.wants.whole(located, m, y), x) == True{} : Bool}) -> {U.holds.payload(x, U.executable(m), y) == True{} : Bool}:
  match y:
    case None{}:
      Empty.absurd({U.holds.payload(x, U.executable(m), None{}) == True{} : Bool}, Comp.false_true(h))
    case Some{+d}:
      held_pick(String.is_empty(Main.stat_of(d, Map.get(String, SNil{}, located, d))), d, m, Main.stat_of(d, Map.get(String, SNil{}, located, d)), x, h)

def mdisc(m: Maybe<&2, String>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      Empty

def none_some(-s: String, e: {None{} == Some{s} : Maybe<&2, String>}) -> Empty:
  %e : {mdisc(_) : Type}
  Unit{}

def some_eq(-a: String, -b: String, e: {Some{a} == Some{b} : Maybe<&2, String>}) -> {a == b : String}:
  Equal.cong(Maybe<&2, String>, String, v => Maybe.default(&2, String, v, a), Some{a}, Some{b}, e)

def found_to(+at: String, +named: String, mp: Maybe<&2, String>, -s: String, e: {Maybe.map(&2, String, String, to => Main.relative_path(Main.directory_of(at), to), mp) == Some{s} : Maybe<&2, String>}) -> {Main.materialise.of(at, mp, "file:" ++ named) == s : String}:
  match mp:
    case None{}:
      Empty.absurd({Main.materialise.of(at, None{}, "file:" ++ named) == s : String}, none_some(s, e))
    case Some{+to}:
      some_eq(Main.relative_path(Main.directory_of(at), to), s, e)

# Where `update` spells a link, `cat` says it points the same way.
def spelled_same(+t: Tree.Tree(), +at: String, g: Tree.Target, -s: String, e: {U.materialise(t, at, g) == Some{s} : Maybe<&2, String>}) -> {Main.materialise(t, at, g) == s : String}:
  match g:
    case Tree.Verbatim{+v}:
      some_eq(v, s, e)
    case Tree.Reference{+named}:
      found_to(at, named, Tree.path(t, named), s, e)

def link_is(+s: String, x: U.Held, h: {U.lands.link(s, x) == True{} : Bool}) -> {U.holds.link(x, s) == True{} : Bool}:
  match x:
    case U.Held.Link{v}:
      h
    case U.Held.File{d, r}:
      Empty.absurd({U.holds.link(U.Held.File{d, r}, s) == True{} : Bool}, Comp.false_true(h))
    case U.Held.Dir{}:
      Empty.absurd({U.holds.link(U.Held.Dir{}, s) == True{} : Bool}, Comp.false_true(h))
    case U.Held.Unread{}:
      Empty.absurd({U.holds.link(U.Held.Unread{}, s) == True{} : Bool}, Comp.false_true(h))
    case U.Held.Other{}:
      Empty.absurd({U.holds.link(U.Held.Other{}, s) == True{} : Bool}, Comp.false_true(h))
    case U.Held.Nothing{}:
      Empty.absurd({U.holds.link(U.Held.Nothing{}, s) == True{} : Bool}, Comp.false_true(h))

def link_held(+t: Tree.Tree(), +at: String, +g: Tree.Target, mm: Maybe<&2, String>, +em: {U.materialise(t, at, g) == mm : Maybe<&2, String>}, +x: U.Held, h: {U.lands(U.wants.spelled(mm), x) == True{} : Bool}) -> {U.holds.link(x, Main.materialise(t, at, g)) == True{} : Bool}:
  match mm:
    case None{}:
      Empty.absurd({U.holds.link(x, Main.materialise(t, at, g)) == True{} : Bool}, Comp.false_true(h))
    case Some{+s}:
      %Equal.sym(String, Main.materialise(t, at, g), s, spelled_same(t, at, g, s, em)) : {U.holds.link(x, _) == True{} : Bool}
      link_is(s, x, h)

# A link points where `cat` says it points.
def link_reads(+t: Tree.Tree(), +at: String, +x: U.Held, g: Maybe<&2, Tree.Target>, h: {U.lands(U.wants.link(t, at, g), x) == True{} : Bool}) -> {U.holds.target(x, t, at, g) == True{} : Bool}:
  match g:
    case None{}:
      Empty.absurd({U.holds.target(x, t, at, None{}) == True{} : Bool}, Comp.false_true(h))
    case Some{+v}:
      link_held(t, at, v, U.materialise(t, at, v), {==}, x, h)

# Whatever a path lands as, it holds what `cat` of the target reads there.
def lands_reads(+fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +located: Map<&2, String>, +id: String, +t: Tree.Tree(), e: Tree.Entry, +x: U.Held, h: {U.lands(U.wants.of(fs, List.reverse(&2, Main.Full, Main.presentation(fs)), ds, located, id, t, e), x) == True{} : Bool}) -> {U.reads(fs, ds, id, t, e, x) == True{} : Bool}:
  match e:
    case Tree.Entry{+f, p, Tree.Lines{}, y, g, +m}:
      lines_reads(m, x, Main.content(fs, ds, id, f), h)
    case Tree.Entry{f, p, Tree.Whole{}, +y, g, +m}:
      whole_reads(located, m, x, y, h)
    case Tree.Entry{f, +p, Tree.Link{}, y, +g, m}:
      link_reads(t, p, x, g, h)

# Each path of the tree, stepped through in order, holds what `cat` reads.
def holds_go(+fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +located: Map<&2, String>, +id: String, +t: Tree.Tree(), +hm: Map<&2, Maybe<&2, U.Held>>, +ls: Map<&2, String>, es: List<&2, Tree.Entry>, +rec: List<&2, U.Rec>, +h: {U.lands_all(U.decided(U.looks(U.pres(fs, List.reverse(&2, Main.Full, Main.presentation(fs)), ds, located, id, t, hm, ls, es), rec))) == True{} : Bool}) -> {U.holds.go(fs, ds, id, t, es, U.decided(U.looks(U.pres(fs, List.reverse(&2, Main.Full, Main.presentation(fs)), ds, located, id, t, hm, ls, es), rec))) == True{} : Bool}:
  match es:
    case Nil{}:
      {==}
    case +e <> +rest:
      AL.and_intro(Bool.and(String.eq(Tree.entry_path(e), Tree.entry_path(e)), U.reads(fs, ds, id, t, e, U.after(U.wants.of(fs, List.reverse(&2, Main.Full, Main.presentation(fs)), ds, located, id, t, e), U.held.of(ls, Tree.entry_path(e), U.taken(hm, Tree.entry_path(e))), U.decide(U.wants.of(fs, List.reverse(&2, Main.Full, Main.presentation(fs)), ds, located, id, t, e), U.held.of(ls, Tree.entry_path(e), U.taken(hm, Tree.entry_path(e))), U.recorded.in(rec, Tree.entry_path(e)))))), U.holds.go(fs, ds, id, t, rest, U.decided(U.looks(U.pres(fs, List.reverse(&2, Main.Full, Main.presentation(fs)), ds, located, id, t, hm, ls, rest), rec))),
        AL.and_intro(String.eq(Tree.entry_path(e), Tree.entry_path(e)), U.reads(fs, ds, id, t, e, U.after(U.wants.of(fs, List.reverse(&2, Main.Full, Main.presentation(fs)), ds, located, id, t, e), U.held.of(ls, Tree.entry_path(e), U.taken(hm, Tree.entry_path(e))), U.decide(U.wants.of(fs, List.reverse(&2, Main.Full, Main.presentation(fs)), ds, located, id, t, e), U.held.of(ls, Tree.entry_path(e), U.taken(hm, Tree.entry_path(e))), U.recorded.in(rec, Tree.entry_path(e))))), SL.eq_refl(Tree.entry_path(e)),
          lands_reads(fs, ds, located, id, t, e, U.after(U.wants.of(fs, List.reverse(&2, Main.Full, Main.presentation(fs)), ds, located, id, t, e), U.held.of(ls, Tree.entry_path(e), U.taken(hm, Tree.entry_path(e))), U.decide(U.wants.of(fs, List.reverse(&2, Main.Full, Main.presentation(fs)), ds, located, id, t, e), U.held.of(ls, Tree.entry_path(e), U.taken(hm, Tree.entry_path(e))), U.recorded.in(rec, Tree.entry_path(e)))), Comp.and_left(U.lands(U.wants.of(fs, List.reverse(&2, Main.Full, Main.presentation(fs)), ds, located, id, t, e), U.after(U.wants.of(fs, List.reverse(&2, Main.Full, Main.presentation(fs)), ds, located, id, t, e), U.held.of(ls, Tree.entry_path(e), U.taken(hm, Tree.entry_path(e))), U.decide(U.wants.of(fs, List.reverse(&2, Main.Full, Main.presentation(fs)), ds, located, id, t, e), U.held.of(ls, Tree.entry_path(e), U.taken(hm, Tree.entry_path(e))), U.recorded.in(rec, Tree.entry_path(e))))), U.lands_all(U.decided(U.looks(U.pres(fs, List.reverse(&2, Main.Full, Main.presentation(fs)), ds, located, id, t, hm, ls, rest), rec))), h))),
        holds_go(fs, ds, located, id, t, hm, ls, rest, rec, Comp.and_right(U.lands(U.wants.of(fs, List.reverse(&2, Main.Full, Main.presentation(fs)), ds, located, id, t, e), U.after(U.wants.of(fs, List.reverse(&2, Main.Full, Main.presentation(fs)), ds, located, id, t, e), U.held.of(ls, Tree.entry_path(e), U.taken(hm, Tree.entry_path(e))), U.decide(U.wants.of(fs, List.reverse(&2, Main.Full, Main.presentation(fs)), ds, located, id, t, e), U.held.of(ls, Tree.entry_path(e), U.taken(hm, Tree.entry_path(e))), U.recorded.in(rec, Tree.entry_path(e))))), U.lands_all(U.decided(U.looks(U.pres(fs, List.reverse(&2, Main.Full, Main.presentation(fs)), ds, located, id, t, hm, ls, rest), rec))), h)))

# Where the plan goes on, it is the steps and the removals decided, and no
# step refuses.
def plan_done.of(+ls: List<&2, U.Look>, +gs: List<&2, U.Gone>, r: List<&2, T.Split>, -p: U.Plan, e: {U.plan.of(U.decided(ls), U.went(gs), r) == Done{p} : Result<&2, &2, List<&2, T.Split>, U.Plan>}) -> {U.Plan{U.decided(ls), U.went(gs)} == p : U.Plan}:
  match r:
    case Nil{}:
      done_eq(List<&2, T.Split>, U.Plan, U.Plan{U.decided(ls), U.went(gs)}, p, e)
    case +x <> +more:
      Empty.absurd({U.Plan{U.decided(ls), U.went(gs)} == p : U.Plan}, fail_done(List<&2, T.Split>, U.Plan, U.sorted_refusals(x <> more), p, e))

def plan_done(tr: List<&2, T.Split>, +ls: List<&2, U.Look>, +gs: List<&2, U.Gone>, -p: U.Plan, e: {U.plan(tr, ls, gs) == Done{p} : Result<&2, &2, List<&2, T.Split>, U.Plan>}) -> {U.Plan{U.decided(ls), U.went(gs)} == p : U.Plan}:
  match tr:
    case Nil{}:
      plan_done.of(ls, gs, U.refusals(U.decided(ls)), p, e)
    case +x <> +more:
      Empty.absurd({U.Plan{U.decided(ls), U.went(gs)} == p : U.Plan}, fail_done(List<&2, T.Split>, U.Plan, U.sorted_refusals(x <> List.append(&2, T.Split, more, U.refusals(U.decided(ls)))), p, e))

def plan_clear.of(+ls: List<&2, U.Look>, +gs: List<&2, U.Gone>, r: List<&2, T.Split>, +hr: {U.refusals(U.decided(ls)) == r : List<&2, T.Split>}, -p: U.Plan, e: {U.plan.of(U.decided(ls), U.went(gs), r) == Done{p} : Result<&2, &2, List<&2, T.Split>, U.Plan>}) -> {U.refusals(U.decided(ls)) == Nil{} : List<&2, T.Split>}:
  match r:
    case Nil{}:
      hr
    case +x <> +more:
      Empty.absurd({U.refusals(U.decided(ls)) == Nil{} : List<&2, T.Split>}, fail_done(List<&2, T.Split>, U.Plan, U.sorted_refusals(x <> more), p, e))

def plan_clear(tr: List<&2, T.Split>, +ls: List<&2, U.Look>, +gs: List<&2, U.Gone>, -p: U.Plan, e: {U.plan(tr, ls, gs) == Done{p} : Result<&2, &2, List<&2, T.Split>, U.Plan>}) -> {U.refusals(U.decided(ls)) == Nil{} : List<&2, T.Split>}:
  match tr:
    case Nil{}:
      plan_clear.of(ls, gs, U.refusals(U.decided(ls)), {==}, p, e)
    case +x <> +more:
      Empty.absurd({U.refusals(U.decided(ls)) == Nil{} : List<&2, T.Split>}, fail_done(List<&2, T.Split>, U.Plan, U.sorted_refusals(x <> List.append(&2, T.Split, more, U.refusals(U.decided(ls)))), p, e))

# Where `update` plans at all, every path the target's tree holds one file
# at holds, once the plan is carried out, what `cat` of the target reads
# there, with the tree's mode — or a link pointing where `cat` says it
# points.
def plan_holds(+fs: List<&2, Main.Full>, +id: String, +t: Tree.Tree(), +rs: List<&2, Folder.Scope>, +walked: List<&2, T.Split>, +found: List<&2, Folder.Found>, +dg: Map<&2, String>, +ls: Map<&2, String>, +located: Map<&2, String>, +ds: List<&2, Store.Doc>, +more: List<&2, Store.Doc>, -p: U.Plan, +e: {U.plan.from(fs, id, t, rs, walked, found, dg, ls, located, ds, more) == Done{p} : Result<&2, &2, List<&2, T.Split>, U.Plan>}) -> {U.holds(fs, ds, id, t, p) == True{} : Bool}:
  %plan_done(U.refuse.tree(Set.from_list(U.dirs(U.placings(t))), rs, walked, U.placings(t)), U.looks(U.pres(fs, List.reverse(&2, Main.Full, Main.presentation(fs)), ds, located, id, t, U.found.map(found, dg, Map.new(&2, Maybe<&2, U.Held>)), ls, U.single(U.placings(t))), U.recorded.list(List.append(&2, String, U.asks(U.pres(fs, List.reverse(&2, Main.Full, Main.presentation(fs)), ds, located, id, t, U.found.map(found, dg, Map.new(&2, Maybe<&2, U.Held>)), ls, U.single(U.placings(t)))), U.gone.paths(found, Set.from_list(T.map(~U.Placing, ~String, ~(q => U.placing.path(q)), U.placings(t))))), fs, List.reverse(&2, Main.Full, Main.presentation(fs)), List.append(&2, Store.Doc, ds, more))), U.gones(U.gone.paths(found, Set.from_list(T.map(~U.Placing, ~String, ~(q => U.placing.path(q)), U.placings(t)))), U.found.map(found, dg, Map.new(&2, Maybe<&2, U.Held>)), U.recorded.list(List.append(&2, String, U.asks(U.pres(fs, List.reverse(&2, Main.Full, Main.presentation(fs)), ds, located, id, t, U.found.map(found, dg, Map.new(&2, Maybe<&2, U.Held>)), ls, U.single(U.placings(t)))), U.gone.paths(found, Set.from_list(T.map(~U.Placing, ~String, ~(q => U.placing.path(q)), U.placings(t))))), fs, List.reverse(&2, Main.Full, Main.presentation(fs)), List.append(&2, Store.Doc, ds, more)), U.spelled.map(U.gone.links(U.gone.paths(found, Set.from_list(T.map(~U.Placing, ~String, ~(q => U.placing.path(q)), U.placings(t)))), U.found.map(found, dg, Map.new(&2, Maybe<&2, U.Held>))), fs, Map.new(&2, List<&2, String>)), Set.from_list(U.tracked(fs, U.heads.sorted(fs)))), p, e) : {U.holds(fs, ds, id, t, _) == True{} : Bool}
  holds_go(fs, ds, located, id, t, U.found.map(found, dg, Map.new(&2, Maybe<&2, U.Held>)), ls, U.single(U.placings(t)), U.recorded.list(List.append(&2, String, U.asks(U.pres(fs, List.reverse(&2, Main.Full, Main.presentation(fs)), ds, located, id, t, U.found.map(found, dg, Map.new(&2, Maybe<&2, U.Held>)), ls, U.single(U.placings(t)))), U.gone.paths(found, Set.from_list(T.map(~U.Placing, ~String, ~(q => U.placing.path(q)), U.placings(t))))), fs, List.reverse(&2, Main.Full, Main.presentation(fs)), List.append(&2, Store.Doc, ds, more)), lands_decided(U.looks(U.pres(fs, List.reverse(&2, Main.Full, Main.presentation(fs)), ds, located, id, t, U.found.map(found, dg, Map.new(&2, Maybe<&2, U.Held>)), ls, U.single(U.placings(t))), U.recorded.list(List.append(&2, String, U.asks(U.pres(fs, List.reverse(&2, Main.Full, Main.presentation(fs)), ds, located, id, t, U.found.map(found, dg, Map.new(&2, Maybe<&2, U.Held>)), ls, U.single(U.placings(t)))), U.gone.paths(found, Set.from_list(T.map(~U.Placing, ~String, ~(q => U.placing.path(q)), U.placings(t))))), fs, List.reverse(&2, Main.Full, Main.presentation(fs)), List.append(&2, Store.Doc, ds, more))), plan_clear(U.refuse.tree(Set.from_list(U.dirs(U.placings(t))), rs, walked, U.placings(t)), U.looks(U.pres(fs, List.reverse(&2, Main.Full, Main.presentation(fs)), ds, located, id, t, U.found.map(found, dg, Map.new(&2, Maybe<&2, U.Held>)), ls, U.single(U.placings(t))), U.recorded.list(List.append(&2, String, U.asks(U.pres(fs, List.reverse(&2, Main.Full, Main.presentation(fs)), ds, located, id, t, U.found.map(found, dg, Map.new(&2, Maybe<&2, U.Held>)), ls, U.single(U.placings(t)))), U.gone.paths(found, Set.from_list(T.map(~U.Placing, ~String, ~(q => U.placing.path(q)), U.placings(t))))), fs, List.reverse(&2, Main.Full, Main.presentation(fs)), List.append(&2, Store.Doc, ds, more))), U.gones(U.gone.paths(found, Set.from_list(T.map(~U.Placing, ~String, ~(q => U.placing.path(q)), U.placings(t)))), U.found.map(found, dg, Map.new(&2, Maybe<&2, U.Held>)), U.recorded.list(List.append(&2, String, U.asks(U.pres(fs, List.reverse(&2, Main.Full, Main.presentation(fs)), ds, located, id, t, U.found.map(found, dg, Map.new(&2, Maybe<&2, U.Held>)), ls, U.single(U.placings(t)))), U.gone.paths(found, Set.from_list(T.map(~U.Placing, ~String, ~(q => U.placing.path(q)), U.placings(t))))), fs, List.reverse(&2, Main.Full, Main.presentation(fs)), List.append(&2, Store.Doc, ds, more)), U.spelled.map(U.gone.links(U.gone.paths(found, Set.from_list(T.map(~U.Placing, ~String, ~(q => U.placing.path(q)), U.placings(t)))), U.found.map(found, dg, Map.new(&2, Maybe<&2, U.Held>))), fs, Map.new(&2, List<&2, String>)), Set.from_list(U.tracked(fs, U.heads.sorted(fs)))), p, e)))

# What `update` writes over or takes away can be had back
# -------------------------------------------------------

def lines_rec(+y: String, r: Result<&2, &2, String, List<&2, Ops.Item>>, h: {U.recorded.lines(r) == Some{y} : Maybe<&2, String>}) -> {U.records.lines(y, r) == True{} : Bool}:
  match r:
    case Done{+items}:
      %some_eq(Ops.state_digest(items), y, h) : {String.eq(Ops.state_digest(items), _) == True{} : Bool}
      SL.eq_refl(Ops.state_digest(items))
    case Fail{e}:
      Empty.absurd({U.records.lines(y, Fail{e}) == True{} : Bool}, none_some(y, h))

# A digest history records for a file of a revision's tree is what `cat`
# of that revision reads for it, or the payload its tree names.
def entry_rec(+fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +id: String, +x: String, +f: String, +p: String, k: Tree.FileKind, +yy: Maybe<&2, String>, +g: Maybe<&2, Tree.Target>, +m: Tree.Mode, +efx: {f == x : String}, +y: String, h: {U.recorded.entry(fs, ds, Main.contents.go(List.reverse(&2, Main.Full, Main.presentation(fs)), ds, x, Nil{}), id, x, Some{Tree.Entry{f, p, k, yy, g, m}}) == Some{y} : Maybe<&2, String>}) -> {U.entry.records(fs, ds, id, Tree.Entry{f, p, k, yy, g, m}, y) == True{} : Bool}:
  match k:
    case Tree.Lines{}:
      %Equal.sym(String, f, x, efx) : {U.records.lines(y, Main.content(fs, ds, id, _)) == True{} : Bool}
      lines_rec(y, Main.content(fs, ds, id, x), h)
    case Tree.Whole{}:
      %Equal.sym(Maybe<&2, String>, yy, Some{y}, h) : {U.records.payload(y, _) == True{} : Bool}
      SL.eq_refl(y)
    case Tree.Link{}:
      Empty.absurd({U.entry.records(fs, ds, id, Tree.Entry{f, p, Tree.Link{}, yy, g, m}, y) == True{} : Bool}, none_some(y, h))

def lookup_pick(b: Bool, +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +id: String, +x: String, +f: String, +p: String, +k: Tree.FileKind, +yy: Maybe<&2, String>, +g: Maybe<&2, Tree.Target>, +m: Tree.Mode, +rest: Tree.Tree(), +eb: {String.eq(f, x) == b : Bool}, +y: String, h: {U.recorded.entry(fs, ds, Main.contents.go(List.reverse(&2, Main.Full, Main.presentation(fs)), ds, x, Nil{}), id, x, Bool.pick(Maybe<&2, Tree.Entry>, b, Some{Tree.Entry{f, p, k, yy, g, m}}, Tree.lookup(rest, x))) == Some{y} : Maybe<&2, String>}, ih: {U.recorded.entry(fs, ds, Main.contents.go(List.reverse(&2, Main.Full, Main.presentation(fs)), ds, x, Nil{}), id, x, Tree.lookup(rest, x)) == Some{y} : Maybe<&2, String>} -> {U.tree.records(fs, ds, id, rest, y) == True{} : Bool}) -> {Bool.or(U.entry.records(fs, ds, id, Tree.Entry{f, p, k, yy, g, m}, y), U.tree.records(fs, ds, id, rest, y)) == True{} : Bool}:
  match b:
    case True{}:
      AL.or_left(U.entry.records(fs, ds, id, Tree.Entry{f, p, k, yy, g, m}, y), U.tree.records(fs, ds, id, rest, y), entry_rec(fs, ds, id, x, f, p, k, yy, g, m, SL.eq_true(f, x, eb), y, h))
    case False{}:
      AL.or_right(U.entry.records(fs, ds, id, Tree.Entry{f, p, k, yy, g, m}, y), U.tree.records(fs, ds, id, rest, y), ih(h))

def lookup_rec(t2: Tree.Tree(), +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +id: String, +x: String, +y: String, h: {U.recorded.entry(fs, ds, Main.contents.go(List.reverse(&2, Main.Full, Main.presentation(fs)), ds, x, Nil{}), id, x, Tree.lookup(t2, x)) == Some{y} : Maybe<&2, String>}) -> {U.tree.records(fs, ds, id, t2, y) == True{} : Bool}:
  match t2:
    case Nil{}:
      Empty.absurd({U.tree.records(fs, ds, id, Nil{}, y) == True{} : Bool}, none_some(y, h))
    case Tree.Entry{+f, +p, k, +yy, +g, +m} <> +rest:
      lookup_pick(String.eq(f, x), fs, ds, id, x, f, p, k, yy, g, m, rest, {==}, y, h, h2 => lookup_rec(rest, fs, ds, id, x, y, h2))

def tree_rec(+fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +id: String, +x: String, r: Result<&2, &2, Main.Refused, Tree.Tree()>, +y: String, h: {U.recorded.tree(fs, ds, Main.contents.go(List.reverse(&2, Main.Full, Main.presentation(fs)), ds, x, Nil{}), id, x, r) == Some{y} : Maybe<&2, String>}) -> {U.rev.records(fs, ds, id, r, y) == True{} : Bool}:
  match r:
    case Done{+t2}:
      lookup_rec(t2, fs, ds, id, x, y, h)
    case Fail{e}:
      Empty.absurd({U.rev.records(fs, ds, id, Fail{e}, y) == True{} : Bool}, none_some(y, h))

def push_pick(mm: Maybe<&2, String>, +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +x: String, +f: Main.Full, +rest: List<&2, Main.Full>, +later: List<&2, String>, +em: {U.recorded.tree(fs, ds, Main.contents.go(List.reverse(&2, Main.Full, Main.presentation(fs)), ds, x, Nil{}), Main.id_of(f), x, Main.tree.r(fs, Main.id_of(f))) == mm : Maybe<&2, String>}, +d: String, h: {Rev.member(U.push(mm, later), d) == True{} : Bool}, ih: {Rev.member(later, d) == True{} : Bool} -> {U.recoverable.go(rest, fs, ds, d) == True{} : Bool}) -> {U.recoverable.go(f <> rest, fs, ds, d) == True{} : Bool}:
  match mm:
    case None{}:
      AL.or_right(U.rev.records(fs, ds, Main.id_of(f), Main.tree.r(fs, Main.id_of(f)), d), U.recoverable.go(rest, fs, ds, d), ih(h))
    case Some{+v}:
      AL.or_cases({U.recoverable.go(f <> rest, fs, ds, d) == True{} : Bool}, String.eq(v, d), Rev.member(later, d), h,
        l => AL.or_left(U.rev.records(fs, ds, Main.id_of(f), Main.tree.r(fs, Main.id_of(f)), d), U.recoverable.go(rest, fs, ds, d),
          (%SL.eq_true(v, d, l) : {U.rev.records(fs, ds, Main.id_of(f), Main.tree.r(fs, Main.id_of(f)), _) == True{} : Bool}
            tree_rec(fs, ds, Main.id_of(f), x, Main.tree.r(fs, Main.id_of(f)), v, em))),
        r => AL.or_right(U.rev.records(fs, ds, Main.id_of(f), Main.tree.r(fs, Main.id_of(f)), d), U.recoverable.go(rest, fs, ds, d), ih(r)))

def revs_pick(b: Bool, +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +x: String, +f: Main.Full, +rest: List<&2, Main.Full>, +later: List<&2, String>, +d: String, h: {Rev.member(Bool.pick(List<&2, String>, b, U.push(U.recorded.tree(fs, ds, Main.contents.go(List.reverse(&2, Main.Full, Main.presentation(fs)), ds, x, Nil{}), Main.id_of(f), x, Main.tree.r(fs, Main.id_of(f))), later), later), d) == True{} : Bool}, ih: {Rev.member(later, d) == True{} : Bool} -> {U.recoverable.go(rest, fs, ds, d) == True{} : Bool}) -> {U.recoverable.go(f <> rest, fs, ds, d) == True{} : Bool}:
  match b:
    case True{}:
      push_pick(U.recorded.tree(fs, ds, Main.contents.go(List.reverse(&2, Main.Full, Main.presentation(fs)), ds, x, Nil{}), Main.id_of(f), x, Main.tree.r(fs, Main.id_of(f))), fs, ds, x, f, rest, later, {==}, d, h, ih)
    case False{}:
      AL.or_right(U.rev.records(fs, ds, Main.id_of(f), Main.tree.r(fs, Main.id_of(f)), d), U.recoverable.go(rest, fs, ds, d), ih(h))

def revs_rec(rs: List<&2, Main.Full>, +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +x: String, +d: String, h: {Rev.member(U.recorded.revs(rs, fs, ds, Main.contents.go(List.reverse(&2, Main.Full, Main.presentation(fs)), ds, x, Nil{}), x), d) == True{} : Bool}) -> {U.recoverable.go(rs, fs, ds, d) == True{} : Bool}:
  match rs:
    case Nil{}:
      Empty.absurd({U.recoverable.go(Nil{}, fs, ds, d) == True{} : Bool}, Comp.false_true(h))
    case +f <> +rest:
      revs_pick(U.touches(x, f), fs, ds, x, f, rest, U.recorded.revs(rest, fs, ds, Main.contents.go(List.reverse(&2, Main.Full, Main.presentation(fs)), ds, x, Nil{}), x), d, h, h2 => revs_rec(rest, fs, ds, x, d, h2))

def files_rec(xs: List<&2, String>, +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +d: String, h: {Rev.member(U.recorded.files(xs, fs, List.reverse(&2, Main.Full, Main.presentation(fs)), ds), d) == True{} : Bool}) -> {U.recoverable(fs, ds, d) == True{} : Bool}:
  match xs:
    case Nil{}:
      Empty.absurd({U.recoverable(fs, ds, d) == True{} : Bool}, Comp.false_true(h))
    case +x <> +rest:
      AL.or_cases({U.recoverable(fs, ds, d) == True{} : Bool}, Rev.member(U.recorded.revs(fs, fs, ds, Main.contents.go(List.reverse(&2, Main.Full, Main.presentation(fs)), ds, x, Nil{}), x), d), Rev.member(U.recorded.files(rest, fs, List.reverse(&2, Main.Full, Main.presentation(fs)), ds), d),
        GL.append_mem(U.recorded.revs(fs, fs, ds, Main.contents.go(List.reverse(&2, Main.Full, Main.presentation(fs)), ds, x, Nil{}), x), U.recorded.files(rest, fs, List.reverse(&2, Main.Full, Main.presentation(fs)), ds), d, h),
        l => revs_rec(fs, fs, ds, x, d, l),
        r => files_rec(rest, fs, ds, d, r))

# Every digest history is said to record at a path is one `cat` of some
# revision the store holds reads, or a payload its tree names.
def recorded_rec(+fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +path: String, +d: String, h: {Rev.member(U.recorded(fs, List.reverse(&2, Main.Full, Main.presentation(fs)), ds, path), d) == True{} : Bool}) -> {U.recoverable(fs, ds, d) == True{} : Bool}:
  files_rec(Main.sorted_distinct(U.files_at(fs, path)), fs, ds, d, h)

def in_pick(b: Bool, +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +q: String, +rest: List<&2, String>, +p: String, +d: String, h: {Rev.member(Bool.pick(List<&2, String>, b, U.recorded(fs, List.reverse(&2, Main.Full, Main.presentation(fs)), ds, q), U.recorded.in(U.recorded.list(rest, fs, List.reverse(&2, Main.Full, Main.presentation(fs)), ds), p)), d) == True{} : Bool}, ih: {Rev.member(U.recorded.in(U.recorded.list(rest, fs, List.reverse(&2, Main.Full, Main.presentation(fs)), ds), p), d) == True{} : Bool} -> {U.recoverable(fs, ds, d) == True{} : Bool}) -> {U.recoverable(fs, ds, d) == True{} : Bool}:
  match b:
    case True{}:
      recorded_rec(fs, ds, q, d, h)
    case False{}:
      ih(h)

def in_rec(qs: List<&2, String>, +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +p: String, +d: String, h: {Rev.member(U.recorded.in(U.recorded.list(qs, fs, List.reverse(&2, Main.Full, Main.presentation(fs)), ds), p), d) == True{} : Bool}) -> {U.recoverable(fs, ds, d) == True{} : Bool}:
  match qs:
    case Nil{}:
      Empty.absurd({U.recoverable(fs, ds, d) == True{} : Bool}, Comp.false_true(h))
    case +q <> +rest:
      in_pick(String.eq(q, p), fs, ds, q, rest, p, d, h, h2 => in_rec(rest, fs, ds, p, d, h2))

# A step that writes over a file is one decision 0030 allows, and so its
# bytes can be had back.
def step_pick(b: Bool, +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, h: U.Held, +rs: List<&2, String>, sp: {U.spared.step(h, rs, b) == True{} : Bool}, rok: @d: String -> {Rev.member(rs, d) == True{} : Bool} -> {U.recoverable(fs, ds, d) == True{} : Bool}) -> {Bool.or(Bool.not(b), U.held.recoverable(fs, ds, h)) == True{} : Bool}:
  match b h:
    case False{} _:
      {==}
    case True{} U.Held.File{+d, r}:
      rok(d, sp)
    case True{} U.Held.Link{t}:
      {==}
    case True{} U.Held.Dir{}:
      {==}
    case True{} U.Held.Unread{}:
      {==}
    case True{} U.Held.Other{}:
      {==}
    case True{} U.Held.Nothing{}:
      {==}

def touched_steps(ps: List<&2, U.Pre>, +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +qs: List<&2, String>) -> {U.touched.steps(fs, ds, U.decided(U.looks(ps, U.recorded.list(qs, fs, List.reverse(&2, Main.Full, Main.presentation(fs)), ds)))) == True{} : Bool}:
  match ps:
    case Nil{}:
      {==}
    case U.Pre{+p, +w, +h} <> +rest:
      AL.and_intro(Bool.or(Bool.not(U.replaces(U.decide(w, h, U.recorded.in(U.recorded.list(qs, fs, List.reverse(&2, Main.Full, Main.presentation(fs)), ds), p)))), U.held.recoverable(fs, ds, h)), U.touched.steps(fs, ds, U.decided(U.looks(rest, U.recorded.list(qs, fs, List.reverse(&2, Main.Full, Main.presentation(fs)), ds)))),
        step_pick(U.replaces(U.decide(w, h, U.recorded.in(U.recorded.list(qs, fs, List.reverse(&2, Main.Full, Main.presentation(fs)), ds), p))), fs, ds, h, U.recorded.in(U.recorded.list(qs, fs, List.reverse(&2, Main.Full, Main.presentation(fs)), ds), p), spared_decide(w, h, U.recorded.in(U.recorded.list(qs, fs, List.reverse(&2, Main.Full, Main.presentation(fs)), ds), p)), d => m => in_rec(qs, fs, ds, p, d, m)),
        touched_steps(rest, fs, ds, qs))

# A path the target does not hold is taken away only where it holds bytes
# that can be had back, or a link.
def leave_pick(b: Bool, t: Bool, +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +d: String, eb: {b == True{} : Bool} -> {U.recoverable(fs, ds, d) == True{} : Bool}) -> {Bool.or(Bool.not(U.leaving.remove(U.leaving.of(b, t))), U.recoverable(fs, ds, d)) == True{} : Bool}:
  match b t:
    case True{} _:
      eb({==})
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def went_ok(h: U.Held, +ds0: List<&2, String>, +sp: List<&2, String>, t: Bool, +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, rok: @d: String -> {Rev.member(ds0, d) == True{} : Bool} -> {U.recoverable(fs, ds, d) == True{} : Bool}) -> {Bool.or(Bool.not(U.leaving.remove(U.leaving(h, U.gone.recorded(h, ds0, sp), t))), U.held.recoverable(fs, ds, h)) == True{} : Bool}:
  match h:
    case U.Held.File{+d, r}:
      leave_pick(Rev.member(ds0, d), t, fs, ds, d, m => rok(d, m))
    case U.Held.Link{+s}:
      HL.or_true_r(Bool.not(U.leaving.remove(U.leaving(U.Held.Link{s}, sp, t))))
    case U.Held.Dir{}:
      {==}
    case U.Held.Unread{}:
      {==}
    case U.Held.Other{}:
      {==}
    case U.Held.Nothing{}:
      {==}

def touched_gone(gp: List<&2, String>, +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +hm: Map<&2, Maybe<&2, U.Held>>, +qs: List<&2, String>, +lk: Map<&2, List<&2, String>>, +tr: Set()) -> {U.touched.gone(fs, ds, U.went(U.gones(gp, hm, U.recorded.list(qs, fs, List.reverse(&2, Main.Full, Main.presentation(fs)), ds), lk, tr))) == True{} : Bool}:
  match gp:
    case Nil{}:
      {==}
    case +p <> +rest:
      AL.and_intro(Bool.or(Bool.not(U.leaving.remove(U.leaving(U.gone.held(U.taken(hm, p)), U.gone.recorded(U.gone.held(U.taken(hm, p)), U.recorded.in(U.recorded.list(qs, fs, List.reverse(&2, Main.Full, Main.presentation(fs)), ds), p), U.recorded.of(lk, p)), U.has(Set.has(tr, p))))), U.held.recoverable(fs, ds, U.gone.held(U.taken(hm, p)))), U.touched.gone(fs, ds, U.went(U.gones(rest, hm, U.recorded.list(qs, fs, List.reverse(&2, Main.Full, Main.presentation(fs)), ds), lk, tr))),
        went_ok(U.gone.held(U.taken(hm, p)), U.recorded.in(U.recorded.list(qs, fs, List.reverse(&2, Main.Full, Main.presentation(fs)), ds), p), U.recorded.of(lk, p), U.has(Set.has(tr, p)), fs, ds, d => m => in_rec(qs, fs, ds, p, d, m)),
        touched_gone(rest, fs, ds, hm, qs, lk, tr))

# Where `update` plans at all, every file it writes over or takes away
# holds bytes that `cat` of some revision the store holds reads for some
# file of it, or that its tree names as a file's payload: nothing it
# touches is lost to the store.
def plan_touches(+fs: List<&2, Main.Full>, +id: String, +t: Tree.Tree(), +rs: List<&2, Folder.Scope>, +walked: List<&2, T.Split>, +found: List<&2, Folder.Found>, +dg: Map<&2, String>, +ls: Map<&2, String>, +located: Map<&2, String>, +ds: List<&2, Store.Doc>, +more: List<&2, Store.Doc>, -p: U.Plan, +e: {U.plan.from(fs, id, t, rs, walked, found, dg, ls, located, ds, more) == Done{p} : Result<&2, &2, List<&2, T.Split>, U.Plan>}) -> {U.touches.recorded(fs, List.append(&2, Store.Doc, ds, more), p) == True{} : Bool}:
  %plan_done(U.refuse.tree(Set.from_list(U.dirs(U.placings(t))), rs, walked, U.placings(t)), U.looks(U.pres(fs, List.reverse(&2, Main.Full, Main.presentation(fs)), ds, located, id, t, U.found.map(found, dg, Map.new(&2, Maybe<&2, U.Held>)), ls, U.single(U.placings(t))), U.recorded.list(List.append(&2, String, U.asks(U.pres(fs, List.reverse(&2, Main.Full, Main.presentation(fs)), ds, located, id, t, U.found.map(found, dg, Map.new(&2, Maybe<&2, U.Held>)), ls, U.single(U.placings(t)))), U.gone.paths(found, Set.from_list(T.map(~U.Placing, ~String, ~(q => U.placing.path(q)), U.placings(t))))), fs, List.reverse(&2, Main.Full, Main.presentation(fs)), List.append(&2, Store.Doc, ds, more))), U.gones(U.gone.paths(found, Set.from_list(T.map(~U.Placing, ~String, ~(q => U.placing.path(q)), U.placings(t)))), U.found.map(found, dg, Map.new(&2, Maybe<&2, U.Held>)), U.recorded.list(List.append(&2, String, U.asks(U.pres(fs, List.reverse(&2, Main.Full, Main.presentation(fs)), ds, located, id, t, U.found.map(found, dg, Map.new(&2, Maybe<&2, U.Held>)), ls, U.single(U.placings(t)))), U.gone.paths(found, Set.from_list(T.map(~U.Placing, ~String, ~(q => U.placing.path(q)), U.placings(t))))), fs, List.reverse(&2, Main.Full, Main.presentation(fs)), List.append(&2, Store.Doc, ds, more)), U.spelled.map(U.gone.links(U.gone.paths(found, Set.from_list(T.map(~U.Placing, ~String, ~(q => U.placing.path(q)), U.placings(t)))), U.found.map(found, dg, Map.new(&2, Maybe<&2, U.Held>))), fs, Map.new(&2, List<&2, String>)), Set.from_list(U.tracked(fs, U.heads.sorted(fs)))), p, e) : {U.touches.recorded(fs, List.append(&2, Store.Doc, ds, more), _) == True{} : Bool}
  AL.and_intro(U.touched.steps(fs, List.append(&2, Store.Doc, ds, more), U.decided(U.looks(U.pres(fs, List.reverse(&2, Main.Full, Main.presentation(fs)), ds, located, id, t, U.found.map(found, dg, Map.new(&2, Maybe<&2, U.Held>)), ls, U.single(U.placings(t))), U.recorded.list(List.append(&2, String, U.asks(U.pres(fs, List.reverse(&2, Main.Full, Main.presentation(fs)), ds, located, id, t, U.found.map(found, dg, Map.new(&2, Maybe<&2, U.Held>)), ls, U.single(U.placings(t)))), U.gone.paths(found, Set.from_list(T.map(~U.Placing, ~String, ~(q => U.placing.path(q)), U.placings(t))))), fs, List.reverse(&2, Main.Full, Main.presentation(fs)), List.append(&2, Store.Doc, ds, more))))), U.touched.gone(fs, List.append(&2, Store.Doc, ds, more), U.went(U.gones(U.gone.paths(found, Set.from_list(T.map(~U.Placing, ~String, ~(q => U.placing.path(q)), U.placings(t)))), U.found.map(found, dg, Map.new(&2, Maybe<&2, U.Held>)), U.recorded.list(List.append(&2, String, U.asks(U.pres(fs, List.reverse(&2, Main.Full, Main.presentation(fs)), ds, located, id, t, U.found.map(found, dg, Map.new(&2, Maybe<&2, U.Held>)), ls, U.single(U.placings(t)))), U.gone.paths(found, Set.from_list(T.map(~U.Placing, ~String, ~(q => U.placing.path(q)), U.placings(t))))), fs, List.reverse(&2, Main.Full, Main.presentation(fs)), List.append(&2, Store.Doc, ds, more)), U.spelled.map(U.gone.links(U.gone.paths(found, Set.from_list(T.map(~U.Placing, ~String, ~(q => U.placing.path(q)), U.placings(t)))), U.found.map(found, dg, Map.new(&2, Maybe<&2, U.Held>))), fs, Map.new(&2, List<&2, String>)), Set.from_list(U.tracked(fs, U.heads.sorted(fs)))))), touched_steps(U.pres(fs, List.reverse(&2, Main.Full, Main.presentation(fs)), ds, located, id, t, U.found.map(found, dg, Map.new(&2, Maybe<&2, U.Held>)), ls, U.single(U.placings(t))), fs, List.append(&2, Store.Doc, ds, more), List.append(&2, String, U.asks(U.pres(fs, List.reverse(&2, Main.Full, Main.presentation(fs)), ds, located, id, t, U.found.map(found, dg, Map.new(&2, Maybe<&2, U.Held>)), ls, U.single(U.placings(t)))), U.gone.paths(found, Set.from_list(T.map(~U.Placing, ~String, ~(q => U.placing.path(q)), U.placings(t)))))), touched_gone(U.gone.paths(found, Set.from_list(T.map(~U.Placing, ~String, ~(q => U.placing.path(q)), U.placings(t)))), fs, List.append(&2, Store.Doc, ds, more), U.found.map(found, dg, Map.new(&2, Maybe<&2, U.Held>)), List.append(&2, String, U.asks(U.pres(fs, List.reverse(&2, Main.Full, Main.presentation(fs)), ds, located, id, t, U.found.map(found, dg, Map.new(&2, Maybe<&2, U.Held>)), ls, U.single(U.placings(t)))), U.gone.paths(found, Set.from_list(T.map(~U.Placing, ~String, ~(q => U.placing.path(q)), U.placings(t))))), U.spelled.map(U.gone.links(U.gone.paths(found, Set.from_list(T.map(~U.Placing, ~String, ~(q => U.placing.path(q)), U.placings(t)))), U.found.map(found, dg, Map.new(&2, Maybe<&2, U.Held>))), fs, Map.new(&2, List<&2, String>)), Set.from_list(U.tracked(fs, U.heads.sorted(fs)))))
