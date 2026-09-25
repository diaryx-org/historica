# What `update` decides. It reads its words as they say, and lays out only
# a current head. Where it plans at all, every path the target's tree holds
# with one file holds, once the plan is carried out, what `cat` of the
# target reads there — the bytes of a file of lines, the payload of a file
# of bytes, each with its mode, and a link pointing where `cat` says; every
# file it writes over or takes away holds bytes `cat` of some revision the
# store holds reads, which is decision 0030's rule; and everything it does
# is at a path the target holds, save removals, each where history records
# the bytes the walk found. It says the folder holds the target exactly
# where carrying the plan out would change nothing, and its dry run names
# exactly the effects it performs. What a path holds after a step is
# `after`'s model of the host's writes.
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
import ./map_lemmas.bend as ML
import ./sort_lemmas.bend as SortL
import ./rewrite_lemmas.bend as RewriteL
import ./fetch_lemmas.bend as FetchL
import ./bookmark.bend as Bm

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
def sound(+w: U.Wants, +h: U.Held, +s: U.Step) -> Bool:
  Bool.or(U.refuses(s), U.lands(w, U.after(w, h, s)))

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

# Run again, it keeps what it left
# --------------------------------

def not_true(b: Bool, h: {Bool.not(b) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, Comp.false_true(h))

def or_false(a: Bool, -b: Bool, ea: {a == False{} : Bool}, h: {Bool.or(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case False{}:
      h
    case True{}:
      Empty.absurd({b == True{} : Bool}, Comp.false_true(Equal.sym(Bool, True{}, False{}, ea)))

# A path holding the bytes and the bit wanted is kept.
def kept_file(+dg: String, +m: Tree.Mode, h: U.Held, +rs: List<&2, String>, +hl: {U.lands.file(dg, U.runs(m), h) == True{} : Bool}) -> {U.decide.file(dg, m, h, rs) == U.Step.Keep{} : U.Step}:
  match h:
    case U.Held.File{+d, +x}:
      %Equal.sym(Bool, String.eq(d, dg), True{}, Comp.and_left(String.eq(d, dg), Bool.not(Bool.xor(x, U.runs(m))), hl)) : {Bool.pick(U.Step, _, Bool.pick(U.Step, Bool.xor(x, U.runs(m)), U.Step.Mode{}, U.Step.Keep{}), Bool.pick(U.Step, Rev.member(rs, d), U.Step.Write{}, U.Step.Refuse{U.UNRECORDED()})) == U.Step.Keep{} : U.Step}
      %Equal.sym(Bool, Bool.xor(x, U.runs(m)), False{}, not_true(Bool.xor(x, U.runs(m)), Comp.and_right(String.eq(d, dg), Bool.not(Bool.xor(x, U.runs(m))), hl))) : {Bool.pick(U.Step, _, U.Step.Mode{}, U.Step.Keep{}) == U.Step.Keep{} : U.Step}
      {==}
    case U.Held.Link{t}:
      Empty.absurd({U.decide.file(dg, m, U.Held.Link{t}, rs) == U.Step.Keep{} : U.Step}, Comp.false_true(hl))
    case U.Held.Unread{}:
      Empty.absurd({U.decide.file(dg, m, U.Held.Unread{}, rs) == U.Step.Keep{} : U.Step}, Comp.false_true(hl))
    case U.Held.Dir{}:
      Empty.absurd({U.decide.file(dg, m, U.Held.Dir{}, rs) == U.Step.Keep{} : U.Step}, Comp.false_true(hl))
    case U.Held.Other{}:
      Empty.absurd({U.decide.file(dg, m, U.Held.Other{}, rs) == U.Step.Keep{} : U.Step}, Comp.false_true(hl))
    case U.Held.Nothing{}:
      Empty.absurd({U.decide.file(dg, m, U.Held.Nothing{}, rs) == U.Step.Keep{} : U.Step}, Comp.false_true(hl))

# A link pointing where it is wanted is kept.
def kept_link(+t: String, h: U.Held, +rs: List<&2, String>, hl: {U.lands.link(t, h) == True{} : Bool}) -> {U.decide.link(t, h, rs) == U.Step.Keep{} : U.Step}:
  match h:
    case U.Held.Link{+x}:
      %Equal.sym(Bool, String.eq(x, t), True{}, hl) : {Bool.pick(U.Step, _, U.Step.Keep{}, U.Step.Link{}) == U.Step.Keep{} : U.Step}
      {==}
    case U.Held.File{d, x}:
      Empty.absurd({U.decide.link(t, U.Held.File{d, x}, rs) == U.Step.Keep{} : U.Step}, Comp.false_true(hl))
    case U.Held.Unread{}:
      Empty.absurd({U.decide.link(t, U.Held.Unread{}, rs) == U.Step.Keep{} : U.Step}, Comp.false_true(hl))
    case U.Held.Dir{}:
      Empty.absurd({U.decide.link(t, U.Held.Dir{}, rs) == U.Step.Keep{} : U.Step}, Comp.false_true(hl))
    case U.Held.Other{}:
      Empty.absurd({U.decide.link(t, U.Held.Other{}, rs) == U.Step.Keep{} : U.Step}, Comp.false_true(hl))
    case U.Held.Nothing{}:
      Empty.absurd({U.decide.link(t, U.Held.Nothing{}, rs) == U.Step.Keep{} : U.Step}, Comp.false_true(hl))

def kept(w: U.Wants, h: U.Held, +rs: List<&2, String>, hl: {U.lands(w, h) == True{} : Bool}) -> {U.decide(w, h, rs) == U.Step.Keep{} : U.Step}:
  match w:
    case U.Wants.Lines{+text, +m}:
      kept_file(U.text_digest(text), m, h, rs, hl)
    case U.Wants.Whole{+p, at, +m}:
      kept_file(p, m, h, rs, hl)
    case U.Wants.Link{+t}:
      kept_link(t, h, rs, hl)
    case U.Wants.No{b}:
      Empty.absurd({U.decide(U.Wants.No{b}, h, rs) == U.Step.Keep{} : U.Step}, Comp.false_true(hl))

# `update` run again from what it left keeps every path it stepped through.
def again_keeps(+w: U.Wants, +h: U.Held, +rs: List<&2, String>, +rs2: List<&2, String>, e: {U.refuses(U.decide(w, h, rs)) == False{} : Bool}) -> {U.decide(w, U.after(w, h, U.decide(w, h, rs)), rs2) == U.Step.Keep{} : U.Step}:
  kept(w, U.after(w, h, U.decide(w, h, rs)), rs2, or_false(U.refuses(U.decide(w, h, rs)), U.lands(w, U.after(w, h, U.decide(w, h, rs))), e, decide_sound(w, h, rs)))

# What it says is settled
# -----------------------
#
# It says the folder already holds the target exactly where carrying the
# plan out would change nothing: each step `decide` takes leaves its path
# as it was exactly where it neither writes, sets a mode nor points a link,
# and nothing is taken away exactly where nothing is removed.

def same_held(h: U.Held) -> {U.held.same(h, h) == True{} : Bool}:
  match h:
    case U.Held.File{+d, +x}:
      written(d, x)
    case U.Held.Link{+t}:
      SL.eq_refl(t)
    case U.Held.Dir{}:
      {==}
    case U.Held.Unread{}:
      {==}
    case U.Held.Other{}:
      {==}
    case U.Held.Nothing{}:
      {==}

# Whether a step does anything to the folder: writes, sets a mode, or
# points a link.
def changes(+s: U.Step) -> Bool:
  Bool.or(U.step.write(s), Bool.or(U.step.mode(s), U.step.link(s)))

def and_false(x: Bool) -> {Bool.and(x, False{}) == False{} : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      {==}

def xor_flip(a: Bool, b: Bool) -> {Bool.xor(a, b) == Bool.xor(b, a) : Bool}:
  match a b:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

# A file whose bytes are right keeps them; one set to another mode holds
# another mode; one written over held other bytes.
def still_file.on(+dg: String, +w: U.Wants, hd: {U.wants.digest(w) == dg : String}, +r: Bool, hr: {U.wants.runs(w) == r : Bool}, +d: String, +x: Bool, e1: Bool, h1: {String.eq(d, dg) == e1 : Bool}, e2: Bool, h2: {Bool.xor(x, r) == e2 : Bool}, e3: Bool) -> {U.held.same(U.after(w, U.Held.File{d, x}, Bool.pick(U.Step, e1, Bool.pick(U.Step, e2, U.Step.Mode{}, U.Step.Keep{}), Bool.pick(U.Step, e3, U.Step.Write{}, U.Step.Refuse{U.UNRECORDED()}))), U.Held.File{d, x}) == Bool.not(changes(Bool.pick(U.Step, e1, Bool.pick(U.Step, e2, U.Step.Mode{}, U.Step.Keep{}), Bool.pick(U.Step, e3, U.Step.Write{}, U.Step.Refuse{U.UNRECORDED()})))) : Bool}:
  match e1:
    case True{}:
      match e2:
        case True{}:
          %Equal.sym(Bool, U.wants.runs(w), r, hr) : {Bool.and(String.eq(d, d), Bool.not(Bool.xor(_, x))) == False{} : Bool}
          %Equal.sym(Bool, String.eq(d, d), True{}, SL.eq_refl(d)) : {Bool.and(_, Bool.not(Bool.xor(r, x))) == False{} : Bool}
          %xor_flip(x, r) : {Bool.not(_) == False{} : Bool}
          %Equal.sym(Bool, Bool.xor(x, r), True{}, h2) : {Bool.not(_) == False{} : Bool}
          {==}
        case False{}:
          same_held(U.Held.File{d, x})
    case False{}:
      match e3:
        case True{}:
          %Equal.sym(String, U.wants.digest(w), dg, hd) : {Bool.and(String.eq(_, d), Bool.not(Bool.xor(U.wants.runs(w), x))) == False{} : Bool}
          %ML.eq_sym(d, dg) : {Bool.and(_, Bool.not(Bool.xor(U.wants.runs(w), x))) == False{} : Bool}
          %Equal.sym(Bool, String.eq(d, dg), False{}, h1) : {Bool.and(_, Bool.not(Bool.xor(U.wants.runs(w), x))) == False{} : Bool}
          {==}
        case False{}:
          same_held(U.Held.File{d, x})

def still_file(+dg: String, +w: U.Wants, hd: {U.wants.digest(w) == dg : String}, +m: Tree.Mode, hr: {U.wants.runs(w) == U.runs(m) : Bool}, h: U.Held, +rs: List<&2, String>) -> {U.held.same(U.after(w, h, U.decide.file(dg, m, h, rs)), h) == Bool.not(changes(U.decide.file(dg, m, h, rs))) : Bool}:
  match h:
    case U.Held.File{+d, +x}:
      still_file.on(dg, w, hd, U.runs(m), hr, d, x, String.eq(d, dg), {==}, Bool.xor(x, U.runs(m)), {==}, Rev.member(rs, d))
    case U.Held.Link{t}:
      SL.eq_refl(t)
    case U.Held.Unread{}:
      {==}
    case U.Held.Dir{}:
      {==}
    case U.Held.Other{}:
      {==}
    case U.Held.Nothing{}:
      {==}

def still_link.kept(+t: String, +x: String, e: Bool, he: {String.eq(x, t) == e : Bool}) -> {U.held.same(U.after(U.Wants.Link{t}, U.Held.Link{x}, Bool.pick(U.Step, e, U.Step.Keep{}, U.Step.Link{})), U.Held.Link{x}) == Bool.not(changes(Bool.pick(U.Step, e, U.Step.Keep{}, U.Step.Link{}))) : Bool}:
  match e:
    case True{}:
      SL.eq_refl(x)
    case False{}:
      %ML.eq_sym(x, t) : {_ == False{} : Bool}
      he

def still_link.filed(+t: String, +d: String, +x: Bool, e: Bool) -> {U.held.same(U.after(U.Wants.Link{t}, U.Held.File{d, x}, Bool.pick(U.Step, e, U.Step.Link{}, U.Step.Refuse{U.UNRECORDED()})), U.Held.File{d, x}) == Bool.not(changes(Bool.pick(U.Step, e, U.Step.Link{}, U.Step.Refuse{U.UNRECORDED()}))) : Bool}:
  match e:
    case True{}:
      {==}
    case False{}:
      written(d, x)

def still_link(+t: String, h: U.Held, +rs: List<&2, String>) -> {U.held.same(U.after(U.Wants.Link{t}, h, U.decide.link(t, h, rs)), h) == Bool.not(changes(U.decide.link(t, h, rs))) : Bool}:
  match h:
    case U.Held.Link{+x}:
      still_link.kept(t, x, String.eq(x, t), {==})
    case U.Held.File{+d, +x}:
      still_link.filed(t, d, x, Rev.member(rs, d))
    case U.Held.Nothing{}:
      {==}
    case U.Held.Dir{}:
      {==}
    case U.Held.Unread{}:
      {==}
    case U.Held.Other{}:
      {==}

# A step `decide` takes leaves the path as it was exactly where it neither
# writes, sets a mode nor points a link.
def still(w: U.Wants, +h: U.Held, +rs: List<&2, String>) -> {U.held.same(U.after(w, h, U.decide(w, h, rs)), h) == Bool.not(changes(U.decide(w, h, rs))) : Bool}:
  match w:
    case U.Wants.Lines{+text, +m}:
      still_file(U.text_digest(text), U.Wants.Lines{text, m}, {==}, m, {==}, h, rs)
    case U.Wants.Whole{+p, +at, +m}:
      still_file(p, U.Wants.Whole{p, at, m}, {==}, m, {==}, h, rs)
    case U.Wants.Link{+t}:
      still_link(t, h, rs)
    case U.Wants.No{b}:
      same_held(h)

# One step more: the plan changes nothing at this path and after it exactly
# where it writes nothing, sets no mode and points no link here or after.
def still_one(s: U.Step, +w: U.Wants, +h: U.Held, +p: String, +rs: List<&2, String>, +rest: List<&2, U.Decided>, hs: {U.held.same(U.after(w, h, s), h) == Bool.not(changes(s)) : Bool}, ih: {Bool.and(List.is_empty(&2, U.Decided, U.writes(rest)), Bool.and(List.is_empty(&2, U.Decided, U.modes(rest)), List.is_empty(&2, U.Decided, U.links(rest)))) == U.unchanged.steps(rest) : Bool}) -> {Bool.and(List.is_empty(&2, U.Decided, Tree.keep(~U.Decided, U.step.write(s), U.Decided{p, w, h, rs, s}, U.writes(rest))), Bool.and(List.is_empty(&2, U.Decided, Tree.keep(~U.Decided, U.step.mode(s), U.Decided{p, w, h, rs, s}, U.modes(rest))), List.is_empty(&2, U.Decided, Tree.keep(~U.Decided, U.step.link(s), U.Decided{p, w, h, rs, s}, U.links(rest))))) == Bool.and(U.held.same(U.after(w, h, s), h), U.unchanged.steps(rest)) : Bool}:
  match s:
    case U.Step.Refuse{b}:
      %Equal.sym(Bool, U.held.same(U.after(w, h, U.Step.Refuse{b}), h), True{}, hs) : {Bool.and(List.is_empty(&2, U.Decided, U.writes(rest)), Bool.and(List.is_empty(&2, U.Decided, U.modes(rest)), List.is_empty(&2, U.Decided, U.links(rest)))) == Bool.and(_, U.unchanged.steps(rest)) : Bool}
      ih
    case U.Step.Keep{}:
      %Equal.sym(Bool, U.held.same(U.after(w, h, U.Step.Keep{}), h), True{}, hs) : {Bool.and(List.is_empty(&2, U.Decided, U.writes(rest)), Bool.and(List.is_empty(&2, U.Decided, U.modes(rest)), List.is_empty(&2, U.Decided, U.links(rest)))) == Bool.and(_, U.unchanged.steps(rest)) : Bool}
      ih
    case U.Step.Write{}:
      %Equal.sym(Bool, U.held.same(U.after(w, h, U.Step.Write{}), h), False{}, hs) : {False{} == Bool.and(_, U.unchanged.steps(rest)) : Bool}
      {==}
    case U.Step.Mode{}:
      %Equal.sym(Bool, U.held.same(U.after(w, h, U.Step.Mode{}), h), False{}, hs) : {Bool.and(List.is_empty(&2, U.Decided, U.writes(rest)), False{}) == Bool.and(_, U.unchanged.steps(rest)) : Bool}
      and_false(List.is_empty(&2, U.Decided, U.writes(rest)))
    case U.Step.Link{}:
      %Equal.sym(Bool, U.held.same(U.after(w, h, U.Step.Link{}), h), False{}, hs) : {Bool.and(List.is_empty(&2, U.Decided, U.writes(rest)), Bool.and(List.is_empty(&2, U.Decided, U.modes(rest)), False{})) == Bool.and(_, U.unchanged.steps(rest)) : Bool}
      %Equal.sym(Bool, Bool.and(List.is_empty(&2, U.Decided, U.modes(rest)), False{}), False{}, and_false(List.is_empty(&2, U.Decided, U.modes(rest)))) : {Bool.and(List.is_empty(&2, U.Decided, U.writes(rest)), _) == False{} : Bool}
      and_false(List.is_empty(&2, U.Decided, U.writes(rest)))

def still_steps(ls: List<&2, U.Look>) -> {Bool.and(List.is_empty(&2, U.Decided, U.writes(U.decided(ls))), Bool.and(List.is_empty(&2, U.Decided, U.modes(U.decided(ls))), List.is_empty(&2, U.Decided, U.links(U.decided(ls))))) == U.unchanged.steps(U.decided(ls)) : Bool}:
  match ls:
    case Nil{}:
      {==}
    case U.Look{+p, +w, +h, +rs} <> +rest:
      still_one(U.decide(w, h, rs), w, h, p, rs, U.decided(rest), still(w, h, rs), still_steps(rest))

def still_gone.pick(b: Bool, +p: String, +rest: List<&2, U.Went>, ih: {List.is_empty(&2, String, U.removes(rest)) == U.unchanged.gone(rest) : Bool}) -> {List.is_empty(&2, String, Rev.keep(b, p, U.removes(rest))) == Bool.and(Bool.not(b), U.unchanged.gone(rest)) : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      ih

# Nothing is removed exactly where nothing is taken away.
def still_gone(ws: List<&2, U.Went>) -> {List.is_empty(&2, String, U.removes(ws)) == U.unchanged.gone(ws) : Bool}:
  match ws:
    case Nil{}:
      {==}
    case U.Went{+p, h, rs, +l} <> +rest:
      still_gone.pick(U.leaving.remove(l), p, rest, still_gone(rest))

def and4(a: Bool, b: Bool, c: Bool, d: Bool) -> {Bool.and(Bool.and(a, b), Bool.and(c, d)) == Bool.and(Bool.and(a, Bool.and(c, d)), b) : Bool}:
  match a b c d:
    case True{} True{} True{} True{}:
      {==}
    case True{} True{} True{} False{}:
      {==}
    case True{} True{} False{} True{}:
      {==}
    case True{} True{} False{} False{}:
      {==}
    case True{} False{} True{} True{}:
      {==}
    case True{} False{} True{} False{}:
      {==}
    case True{} False{} False{} True{}:
      {==}
    case True{} False{} False{} False{}:
      {==}
    case False{} b2 c2 d2:
      {==}

# For any plan `update` decides, it says the folder already holds the
# target exactly where carrying the plan out would change nothing.
def settled_iff(+ls: List<&2, U.Look>, +ws: List<&2, U.Went>) -> {U.settled(U.Plan{U.decided(ls), ws}) == U.unchanged(U.Plan{U.decided(ls), ws}) : Bool}:
  %still_steps(ls) : {U.settled(U.Plan{U.decided(ls), ws}) == Bool.and(_, U.unchanged.gone(ws)) : Bool}
  %still_gone(ws) : {U.settled(U.Plan{U.decided(ls), ws}) == Bool.and(Bool.and(List.is_empty(&2, U.Decided, U.writes(U.decided(ls))), Bool.and(List.is_empty(&2, U.Decided, U.modes(U.decided(ls))), List.is_empty(&2, U.Decided, U.links(U.decided(ls))))), _) : Bool}
  and4(List.is_empty(&2, U.Decided, U.writes(U.decided(ls))), List.is_empty(&2, String, U.removes(ws)), List.is_empty(&2, U.Decided, U.modes(U.decided(ls))), List.is_empty(&2, U.Decided, U.links(U.decided(ls))))

# The plan `update` decides
# -------------------------

# The paths the target's tree holds one file at, what the plan decides each
# from, and the paths the walk took that the tree does not hold — as
# `plan.from` builds them.
def plan.looks(+fs: List<&2, Main.Full>, +id: String, +t: Tree.Tree(), +found: List<&2, Folder.Found>, +dg: Map<&2, String>, +ls: Map<&2, String>, +located: Map<&2, String>, +ds: List<&2, Store.Doc>, +more: List<&2, Store.Doc>) -> List<&2, U.Look>:
  U.looks(U.pres(fs, List.reverse(&2, Main.Full, Main.presentation(fs)), ds, located, id, t, U.found.map(found, dg, Map.new(&2, Maybe<&2, U.Held>)), ls, U.single(U.placings(t))), U.recorded.list(List.append(&2, String, U.asks(U.pres(fs, List.reverse(&2, Main.Full, Main.presentation(fs)), ds, located, id, t, U.found.map(found, dg, Map.new(&2, Maybe<&2, U.Held>)), ls, U.single(U.placings(t)))), U.gone.paths(found, Set.from_list(T.map(~U.Placing, ~String, ~(q => U.placing.path(q)), U.placings(t))))), fs, List.reverse(&2, Main.Full, Main.presentation(fs)), List.append(&2, Store.Doc, ds, more)))

def plan.gones(+fs: List<&2, Main.Full>, +id: String, +t: Tree.Tree(), +found: List<&2, Folder.Found>, +dg: Map<&2, String>, +ls: Map<&2, String>, +located: Map<&2, String>, +ds: List<&2, Store.Doc>, +more: List<&2, Store.Doc>) -> List<&2, U.Gone>:
  U.gones(U.gone.paths(found, Set.from_list(T.map(~U.Placing, ~String, ~(q => U.placing.path(q)), U.placings(t)))), U.found.map(found, dg, Map.new(&2, Maybe<&2, U.Held>)), U.recorded.list(List.append(&2, String, U.asks(U.pres(fs, List.reverse(&2, Main.Full, Main.presentation(fs)), ds, located, id, t, U.found.map(found, dg, Map.new(&2, Maybe<&2, U.Held>)), ls, U.single(U.placings(t)))), U.gone.paths(found, Set.from_list(T.map(~U.Placing, ~String, ~(q => U.placing.path(q)), U.placings(t))))), fs, List.reverse(&2, Main.Full, Main.presentation(fs)), List.append(&2, Store.Doc, ds, more)), U.spelled.map(U.gone.links(U.gone.paths(found, Set.from_list(T.map(~U.Placing, ~String, ~(q => U.placing.path(q)), U.placings(t)))), U.found.map(found, dg, Map.new(&2, Maybe<&2, U.Held>))), fs, Map.new(&2, List<&2, String>)), Set.from_list(U.tracked(fs, U.heads.sorted(fs))))

# Where `update` plans at all, its plan is those steps and those leavings.
def plan_from(+fs: List<&2, Main.Full>, +id: String, +t: Tree.Tree(), +rs: List<&2, Folder.Scope>, +walked: List<&2, T.Split>, +found: List<&2, Folder.Found>, +dg: Map<&2, String>, +ls: Map<&2, String>, +located: Map<&2, String>, +ds: List<&2, Store.Doc>, +more: List<&2, Store.Doc>, -p: U.Plan, +e: {U.plan.from(fs, id, t, rs, walked, found, dg, ls, located, ds, more) == Done{p} : Result<&2, &2, List<&2, T.Split>, U.Plan>}) -> {U.Plan{U.decided(plan.looks(fs, id, t, found, dg, ls, located, ds, more)), U.went(plan.gones(fs, id, t, found, dg, ls, located, ds, more))} == p : U.Plan}:
  plan_done(U.refuse.tree(Set.from_list(U.dirs(U.placings(t))), rs, walked, U.placings(t)), plan.looks(fs, id, t, found, dg, ls, located, ds, more), plan.gones(fs, id, t, found, dg, ls, located, ds, more), p, e)

# Where `update` plans at all, it says the folder already holds the target
# exactly where carrying the plan out would change nothing.
def plan_settled(+fs: List<&2, Main.Full>, +id: String, +t: Tree.Tree(), +rs: List<&2, Folder.Scope>, +walked: List<&2, T.Split>, +found: List<&2, Folder.Found>, +dg: Map<&2, String>, +ls: Map<&2, String>, +located: Map<&2, String>, +ds: List<&2, Store.Doc>, +more: List<&2, Store.Doc>, -p: U.Plan, +e: {U.plan.from(fs, id, t, rs, walked, found, dg, ls, located, ds, more) == Done{p} : Result<&2, &2, List<&2, T.Split>, U.Plan>}) -> {U.settled(p) == U.unchanged(p) : Bool}:
  %plan_from(fs, id, t, rs, walked, found, dg, ls, located, ds, more, p, e) : {U.settled(_) == U.unchanged(_) : Bool}
  settled_iff(plan.looks(fs, id, t, found, dg, ls, located, ds, more), U.went(plan.gones(fs, id, t, found, dg, ls, located, ds, more)))

# What the dry run says, read back
# --------------------------------
#
# Each piece of the dry run, read by its verbs: a line of one verb is read
# only as that verb, since no verb the dry run prints begins another.

def starts_nil(s: String) -> {String.starts_with(s, SNil{}) == True{} : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{h, t}:
      {==}

# A line that begins with the verb read, read as what follows it.
def as_hit(s: String, -rest: List<&2, String>) -> {Rev.keep(String.starts_with(s, SNil{}), String.drop(s, 0n), rest) == s <> rest : List<&2, String>}:
  match s:
    case SNil{}:
      {==}
    case SCon{h, t}:
      {==}

def pre.w(xs: List<&2, String>, r: U.Named) -> U.Named:
  match r:
    case U.Named{a, b, c, d, x}:
      U.Named{List.append(&2, String, xs, a), b, c, d, x}

def pre.r(xs: List<&2, String>, r: U.Named) -> U.Named:
  match r:
    case U.Named{a, b, c, d, x}:
      U.Named{a, List.append(&2, String, xs, b), c, d, x}

def pre.m(xs: List<&2, String>, r: U.Named) -> U.Named:
  match r:
    case U.Named{a, b, c, d, x}:
      U.Named{a, b, List.append(&2, String, xs, c), d, x}

def pre.l(xs: List<&2, String>, r: U.Named) -> U.Named:
  match r:
    case U.Named{a, b, c, d, x}:
      U.Named{a, b, c, List.append(&2, String, xs, d), x}

def pre_w_nil(r: U.Named) -> {r == pre.w(Nil{}, r) : U.Named}:
  match r:
    case U.Named{a, b, c, d, x}:
      {==}

def pre_r_nil(r: U.Named) -> {r == pre.r(Nil{}, r) : U.Named}:
  match r:
    case U.Named{a, b, c, d, x}:
      {==}

def pre_m_nil(r: U.Named) -> {r == pre.m(Nil{}, r) : U.Named}:
  match r:
    case U.Named{a, b, c, d, x}:
      {==}

def pre_l_nil(r: U.Named) -> {r == pre.l(Nil{}, r) : U.Named}:
  match r:
    case U.Named{a, b, c, d, x}:
      {==}

# The lines naming a mode set, and a link made, as `effect.named` names
# them.
def moded.lines(ds: List<&2, U.Decided>) -> List<&2, String>:
  match ds:
    case Nil{}:
      Nil{}
    case U.Decided{p, +w, h, rs, s} <> rest:
      (p ++ "  (" ++ Bool.pick(String, U.wants.runs(w), "executable", "plain") ++ ")") <> moded.lines(rest)

def linked.lines(ds: List<&2, U.Decided>) -> List<&2, String>:
  match ds:
    case Nil{}:
      Nil{}
    case U.Decided{p, +w, h, rs, s} <> rest:
      (p ++ "  (" ++ U.wants.target(w) ++ ")") <> linked.lines(rest)

# The mode a dry run shows is the bit the effect sets.
def mode_shown(w: U.Wants) -> {U.wants.mode(w) == Bool.pick(String, U.wants.runs(w), "executable", "plain") : String}:
  match w:
    case U.Wants.Lines{t, m}:
      match m:
        case Tree.Executable{}:
          {==}
        case Tree.Plain{}:
          {==}
    case U.Wants.Whole{p, at, m}:
      match m:
        case Tree.Executable{}:
          {==}
        case Tree.Plain{}:
          {==}
    case U.Wants.Link{t}:
      {==}
    case U.Wants.No{b}:
      {==}

def dry_w.line(+p: String, +more: List<&2, String>, r: U.Named) -> {U.dry.line(Main.pad("write", 7n) ++ " " ++ p, pre.w(more, r)) == pre.w(p <> more, r) : U.Named}:
  match r:
    case U.Named{a, b, c, d, x}:
      %Equal.sym(List<&2, String>, Rev.keep(String.starts_with(p, SNil{}), String.drop(p, 0n), List.append(&2, String, more, a)), p <> List.append(&2, String, more, a), as_hit(p, List.append(&2, String, more, a))) : {U.Named{_, b, c, d, x} == U.Named{p <> List.append(&2, String, more, a), b, c, d, x} : U.Named}
      {==}

# The paths the dry run says it writes read back as themselves.
def dry_writes(ps: List<&2, String>, +rest: List<&2, String>) -> {U.dry.read(List.append(&2, String, U.said.paths("write", ps), rest)) == pre.w(ps, U.dry.read(rest)) : U.Named}:
  match ps:
    case Nil{}:
      pre_w_nil(U.dry.read(rest))
    case +p <> +more:
      %Equal.sym(U.Named, U.dry.read(List.append(&2, String, U.said.paths("write", more), rest)), pre.w(more, U.dry.read(rest)), dry_writes(more, rest)) : {U.dry.line(Main.pad("write", 7n) ++ " " ++ p, _) == pre.w(p <> more, U.dry.read(rest)) : U.Named}
      dry_w.line(p, more, U.dry.read(rest))

def dry_r.line(+p: String, +more: List<&2, String>, r: U.Named) -> {U.dry.line(Main.pad("remove", 7n) ++ " " ++ p, pre.r(more, r)) == pre.r(p <> more, r) : U.Named}:
  match r:
    case U.Named{a, b, c, d, x}:
      %Equal.sym(List<&2, String>, Rev.keep(String.starts_with(p, SNil{}), String.drop(p, 0n), List.append(&2, String, more, b)), p <> List.append(&2, String, more, b), as_hit(p, List.append(&2, String, more, b))) : {U.Named{a, _, c, d, x} == U.Named{a, p <> List.append(&2, String, more, b), c, d, x} : U.Named}
      {==}

# The paths the dry run says it removes read back as themselves.
def dry_removes(ps: List<&2, String>, +rest: List<&2, String>) -> {U.dry.read(List.append(&2, String, U.said.paths("remove", ps), rest)) == pre.r(ps, U.dry.read(rest)) : U.Named}:
  match ps:
    case Nil{}:
      pre_r_nil(U.dry.read(rest))
    case +p <> +more:
      %Equal.sym(U.Named, U.dry.read(List.append(&2, String, U.said.paths("remove", more), rest)), pre.r(more, U.dry.read(rest)), dry_removes(more, rest)) : {U.dry.line(Main.pad("remove", 7n) ++ " " ++ p, _) == pre.r(p <> more, U.dry.read(rest)) : U.Named}
      dry_r.line(p, more, U.dry.read(rest))

def dry_m.line(+p: String, +w: U.Wants, +more: List<&2, String>, r: U.Named) -> {U.dry.line(Main.pad("mode", 7n) ++ " " ++ p ++ "  (" ++ U.wants.mode(w) ++ ")", pre.m(more, r)) == pre.m((p ++ "  (" ++ Bool.pick(String, U.wants.runs(w), "executable", "plain") ++ ")") <> more, r) : U.Named}:
  match r:
    case U.Named{a, b, c, d, x}:
      %Equal.sym(List<&2, String>, Rev.keep(String.starts_with(p ++ "  (" ++ U.wants.mode(w) ++ ")", SNil{}), String.drop(p ++ "  (" ++ U.wants.mode(w) ++ ")", 0n), List.append(&2, String, more, c)), (p ++ "  (" ++ U.wants.mode(w) ++ ")") <> List.append(&2, String, more, c), as_hit(p ++ "  (" ++ U.wants.mode(w) ++ ")", List.append(&2, String, more, c))) : {U.Named{a, b, _, d, x} == U.Named{a, b, (p ++ "  (" ++ Bool.pick(String, U.wants.runs(w), "executable", "plain") ++ ")") <> List.append(&2, String, more, c), d, x} : U.Named}
      %mode_shown(w) : {U.Named{a, b, (p ++ "  (" ++ U.wants.mode(w) ++ ")") <> List.append(&2, String, more, c), d, x} == U.Named{a, b, (p ++ "  (" ++ _ ++ ")") <> List.append(&2, String, more, c), d, x} : U.Named}
      {==}

# The modes the dry run says it sets read back as each path and the bit.
def dry_modes(ds: List<&2, U.Decided>, +rest: List<&2, String>) -> {U.dry.read(List.append(&2, String, U.said.modes("mode", ds), rest)) == pre.m(moded.lines(ds), U.dry.read(rest)) : U.Named}:
  match ds:
    case Nil{}:
      pre_m_nil(U.dry.read(rest))
    case U.Decided{+p, +w, h, rs, s} <> +more:
      %Equal.sym(U.Named, U.dry.read(List.append(&2, String, U.said.modes("mode", more), rest)), pre.m(moded.lines(more), U.dry.read(rest)), dry_modes(more, rest)) : {U.dry.line(Main.pad("mode", 7n) ++ " " ++ p ++ "  (" ++ U.wants.mode(w) ++ ")", _) == pre.m(moded.lines(U.Decided{p, w, h, rs, s} <> more), U.dry.read(rest)) : U.Named}
      dry_m.line(p, w, moded.lines(more), U.dry.read(rest))

def dry_l.line(+p: String, +w: U.Wants, +more: List<&2, String>, r: U.Named) -> {U.dry.line(Main.pad("link", 7n) ++ " " ++ p ++ "  (" ++ U.wants.target(w) ++ ")", pre.l(more, r)) == pre.l((p ++ "  (" ++ U.wants.target(w) ++ ")") <> more, r) : U.Named}:
  match r:
    case U.Named{a, b, c, d, x}:
      %Equal.sym(List<&2, String>, Rev.keep(String.starts_with(p ++ "  (" ++ U.wants.target(w) ++ ")", SNil{}), String.drop(p ++ "  (" ++ U.wants.target(w) ++ ")", 0n), List.append(&2, String, more, d)), (p ++ "  (" ++ U.wants.target(w) ++ ")") <> List.append(&2, String, more, d), as_hit(p ++ "  (" ++ U.wants.target(w) ++ ")", List.append(&2, String, more, d))) : {U.Named{a, b, c, _, x} == U.Named{a, b, c, (p ++ "  (" ++ U.wants.target(w) ++ ")") <> List.append(&2, String, more, d), x} : U.Named}
      {==}

# The links the dry run says it makes read back as each path and where it
# points.
def dry_links(ds: List<&2, U.Decided>, +rest: List<&2, String>) -> {U.dry.read(List.append(&2, String, U.said.links("link", ds), rest)) == pre.l(linked.lines(ds), U.dry.read(rest)) : U.Named}:
  match ds:
    case Nil{}:
      pre_l_nil(U.dry.read(rest))
    case U.Decided{+p, +w, h, rs, s} <> +more:
      %Equal.sym(U.Named, U.dry.read(List.append(&2, String, U.said.links("link", more), rest)), pre.l(linked.lines(more), U.dry.read(rest)), dry_links(more, rest)) : {U.dry.line(Main.pad("link", 7n) ++ " " ++ p ++ "  (" ++ U.wants.target(w) ++ ")", _) == pre.l(linked.lines(U.Decided{p, w, h, rs, s} <> more), U.dry.read(rest)) : U.Named}
      dry_l.line(p, w, linked.lines(more), U.dry.read(rest))

def dry_left.line(+p: String, r: U.Named) -> {U.dry.line("left " ++ p ++ " alone: " ++ U.UNRECORDED(), r) == r : U.Named}:
  match r:
    case U.Named{a, b, c, d, x}:
      {==}

# What the dry run says it leaves alone is read as none of the effects.
def dry_leaves(ps: List<&2, String>, +rest: List<&2, String>) -> {U.dry.read(List.append(&2, String, U.said.leaves(ps), rest)) == U.dry.read(rest) : U.Named}:
  match ps:
    case Nil{}:
      {==}
    case +p <> +more:
      %Equal.sym(U.Named, U.dry.read(List.append(&2, String, U.said.leaves(more), rest)), U.dry.read(rest), dry_leaves(more, rest)) : {U.dry.line("left " ++ p ++ " alone: " ++ U.UNRECORDED(), _) == U.dry.read(rest) : U.Named}
      dry_left.line(p, U.dry.read(rest))

# And the folder is said to hold the target already where it is settled.
def dry_holds(b: Bool, +s: String) -> {U.dry.read(List.append(&2, String, Bool.pick(List<&2, String>, b, ["the folder already holds " ++ s], Nil{}), Nil{})) == U.Named{Nil{}, Nil{}, Nil{}, Nil{}, Bool.pick(List<&2, String>, b, [s], Nil{})} : U.Named}:
  match b:
    case True{}:
      %Equal.sym(List<&2, String>, Rev.keep(String.starts_with(s, SNil{}), String.drop(s, 0n), Nil{}), [s], as_hit(s, Nil{})) : {U.Named{Nil{}, Nil{}, Nil{}, Nil{}, _} == U.Named{Nil{}, Nil{}, Nil{}, Nil{}, [s]} : U.Named}
      {==}
    case False{}:
      {==}

# The whole dry run, read back: each kind of effect it names, in turn, and
# whether it says the folder holds the target already.
def dry_side(+s: String, +ds: List<&2, U.Decided>, +ws: List<&2, U.Went>) -> {U.dry.read(U.said.dry(s, U.Plan{ds, ws})) == pre.w(T.map(~U.Decided, ~String, ~(d => U.decided.path(d)), U.writes(ds)), pre.r(U.removes(ws), pre.m(moded.lines(U.modes(ds)), pre.l(linked.lines(U.links(ds)), U.Named{Nil{}, Nil{}, Nil{}, Nil{}, Bool.pick(List<&2, String>, U.settled(U.Plan{ds, ws}), [s], Nil{})})))) : U.Named}:
  %Equal.sym(U.Named, U.dry.read(List.append(&2, String, U.said.paths("write", T.map(~U.Decided, ~String, ~(d => U.decided.path(d)), U.writes(ds))), List.append(&2, String, U.said.paths("remove", U.removes(ws)), List.append(&2, String, U.said.modes("mode", U.modes(ds)), List.append(&2, String, U.said.links("link", U.links(ds)), List.append(&2, String, U.said.leaves(U.leaves(ws)), List.append(&2, String, Bool.pick(List<&2, String>, U.settled(U.Plan{ds, ws}), ["the folder already holds " ++ s], Nil{}), Nil{}))))))), pre.w(T.map(~U.Decided, ~String, ~(d => U.decided.path(d)), U.writes(ds)), U.dry.read(List.append(&2, String, U.said.paths("remove", U.removes(ws)), List.append(&2, String, U.said.modes("mode", U.modes(ds)), List.append(&2, String, U.said.links("link", U.links(ds)), List.append(&2, String, U.said.leaves(U.leaves(ws)), List.append(&2, String, Bool.pick(List<&2, String>, U.settled(U.Plan{ds, ws}), ["the folder already holds " ++ s], Nil{}), Nil{}))))))), dry_writes(T.map(~U.Decided, ~String, ~(d => U.decided.path(d)), U.writes(ds)), List.append(&2, String, U.said.paths("remove", U.removes(ws)), List.append(&2, String, U.said.modes("mode", U.modes(ds)), List.append(&2, String, U.said.links("link", U.links(ds)), List.append(&2, String, U.said.leaves(U.leaves(ws)), List.append(&2, String, Bool.pick(List<&2, String>, U.settled(U.Plan{ds, ws}), ["the folder already holds " ++ s], Nil{}), Nil{}))))))) : {_ == pre.w(T.map(~U.Decided, ~String, ~(d => U.decided.path(d)), U.writes(ds)), pre.r(U.removes(ws), pre.m(moded.lines(U.modes(ds)), pre.l(linked.lines(U.links(ds)), U.Named{Nil{}, Nil{}, Nil{}, Nil{}, Bool.pick(List<&2, String>, U.settled(U.Plan{ds, ws}), [s], Nil{})})))) : U.Named}
  %Equal.sym(U.Named, U.dry.read(List.append(&2, String, U.said.paths("remove", U.removes(ws)), List.append(&2, String, U.said.modes("mode", U.modes(ds)), List.append(&2, String, U.said.links("link", U.links(ds)), List.append(&2, String, U.said.leaves(U.leaves(ws)), List.append(&2, String, Bool.pick(List<&2, String>, U.settled(U.Plan{ds, ws}), ["the folder already holds " ++ s], Nil{}), Nil{})))))), pre.r(U.removes(ws), U.dry.read(List.append(&2, String, U.said.modes("mode", U.modes(ds)), List.append(&2, String, U.said.links("link", U.links(ds)), List.append(&2, String, U.said.leaves(U.leaves(ws)), List.append(&2, String, Bool.pick(List<&2, String>, U.settled(U.Plan{ds, ws}), ["the folder already holds " ++ s], Nil{}), Nil{})))))), dry_removes(U.removes(ws), List.append(&2, String, U.said.modes("mode", U.modes(ds)), List.append(&2, String, U.said.links("link", U.links(ds)), List.append(&2, String, U.said.leaves(U.leaves(ws)), List.append(&2, String, Bool.pick(List<&2, String>, U.settled(U.Plan{ds, ws}), ["the folder already holds " ++ s], Nil{}), Nil{})))))) : {pre.w(T.map(~U.Decided, ~String, ~(d => U.decided.path(d)), U.writes(ds)), _) == pre.w(T.map(~U.Decided, ~String, ~(d => U.decided.path(d)), U.writes(ds)), pre.r(U.removes(ws), pre.m(moded.lines(U.modes(ds)), pre.l(linked.lines(U.links(ds)), U.Named{Nil{}, Nil{}, Nil{}, Nil{}, Bool.pick(List<&2, String>, U.settled(U.Plan{ds, ws}), [s], Nil{})})))) : U.Named}
  %Equal.sym(U.Named, U.dry.read(List.append(&2, String, U.said.modes("mode", U.modes(ds)), List.append(&2, String, U.said.links("link", U.links(ds)), List.append(&2, String, U.said.leaves(U.leaves(ws)), List.append(&2, String, Bool.pick(List<&2, String>, U.settled(U.Plan{ds, ws}), ["the folder already holds " ++ s], Nil{}), Nil{}))))), pre.m(moded.lines(U.modes(ds)), U.dry.read(List.append(&2, String, U.said.links("link", U.links(ds)), List.append(&2, String, U.said.leaves(U.leaves(ws)), List.append(&2, String, Bool.pick(List<&2, String>, U.settled(U.Plan{ds, ws}), ["the folder already holds " ++ s], Nil{}), Nil{}))))), dry_modes(U.modes(ds), List.append(&2, String, U.said.links("link", U.links(ds)), List.append(&2, String, U.said.leaves(U.leaves(ws)), List.append(&2, String, Bool.pick(List<&2, String>, U.settled(U.Plan{ds, ws}), ["the folder already holds " ++ s], Nil{}), Nil{}))))) : {pre.w(T.map(~U.Decided, ~String, ~(d => U.decided.path(d)), U.writes(ds)), pre.r(U.removes(ws), _)) == pre.w(T.map(~U.Decided, ~String, ~(d => U.decided.path(d)), U.writes(ds)), pre.r(U.removes(ws), pre.m(moded.lines(U.modes(ds)), pre.l(linked.lines(U.links(ds)), U.Named{Nil{}, Nil{}, Nil{}, Nil{}, Bool.pick(List<&2, String>, U.settled(U.Plan{ds, ws}), [s], Nil{})})))) : U.Named}
  %Equal.sym(U.Named, U.dry.read(List.append(&2, String, U.said.links("link", U.links(ds)), List.append(&2, String, U.said.leaves(U.leaves(ws)), List.append(&2, String, Bool.pick(List<&2, String>, U.settled(U.Plan{ds, ws}), ["the folder already holds " ++ s], Nil{}), Nil{})))), pre.l(linked.lines(U.links(ds)), U.dry.read(List.append(&2, String, U.said.leaves(U.leaves(ws)), List.append(&2, String, Bool.pick(List<&2, String>, U.settled(U.Plan{ds, ws}), ["the folder already holds " ++ s], Nil{}), Nil{})))), dry_links(U.links(ds), List.append(&2, String, U.said.leaves(U.leaves(ws)), List.append(&2, String, Bool.pick(List<&2, String>, U.settled(U.Plan{ds, ws}), ["the folder already holds " ++ s], Nil{}), Nil{})))) : {pre.w(T.map(~U.Decided, ~String, ~(d => U.decided.path(d)), U.writes(ds)), pre.r(U.removes(ws), pre.m(moded.lines(U.modes(ds)), _))) == pre.w(T.map(~U.Decided, ~String, ~(d => U.decided.path(d)), U.writes(ds)), pre.r(U.removes(ws), pre.m(moded.lines(U.modes(ds)), pre.l(linked.lines(U.links(ds)), U.Named{Nil{}, Nil{}, Nil{}, Nil{}, Bool.pick(List<&2, String>, U.settled(U.Plan{ds, ws}), [s], Nil{})})))) : U.Named}
  %Equal.sym(U.Named, U.dry.read(List.append(&2, String, U.said.leaves(U.leaves(ws)), List.append(&2, String, Bool.pick(List<&2, String>, U.settled(U.Plan{ds, ws}), ["the folder already holds " ++ s], Nil{}), Nil{}))), U.dry.read(List.append(&2, String, Bool.pick(List<&2, String>, U.settled(U.Plan{ds, ws}), ["the folder already holds " ++ s], Nil{}), Nil{})), dry_leaves(U.leaves(ws), List.append(&2, String, Bool.pick(List<&2, String>, U.settled(U.Plan{ds, ws}), ["the folder already holds " ++ s], Nil{}), Nil{}))) : {pre.w(T.map(~U.Decided, ~String, ~(d => U.decided.path(d)), U.writes(ds)), pre.r(U.removes(ws), pre.m(moded.lines(U.modes(ds)), pre.l(linked.lines(U.links(ds)), _)))) == pre.w(T.map(~U.Decided, ~String, ~(d => U.decided.path(d)), U.writes(ds)), pre.r(U.removes(ws), pre.m(moded.lines(U.modes(ds)), pre.l(linked.lines(U.links(ds)), U.Named{Nil{}, Nil{}, Nil{}, Nil{}, Bool.pick(List<&2, String>, U.settled(U.Plan{ds, ws}), [s], Nil{})})))) : U.Named}
  %Equal.sym(U.Named, U.dry.read(List.append(&2, String, Bool.pick(List<&2, String>, U.settled(U.Plan{ds, ws}), ["the folder already holds " ++ s], Nil{}), Nil{})), U.Named{Nil{}, Nil{}, Nil{}, Nil{}, Bool.pick(List<&2, String>, U.settled(U.Plan{ds, ws}), [s], Nil{})}, dry_holds(U.settled(U.Plan{ds, ws}), s)) : {pre.w(T.map(~U.Decided, ~String, ~(d => U.decided.path(d)), U.writes(ds)), pre.r(U.removes(ws), pre.m(moded.lines(U.modes(ds)), pre.l(linked.lines(U.links(ds)), _)))) == pre.w(T.map(~U.Decided, ~String, ~(d => U.decided.path(d)), U.writes(ds)), pre.r(U.removes(ws), pre.m(moded.lines(U.modes(ds)), pre.l(linked.lines(U.links(ds)), U.Named{Nil{}, Nil{}, Nil{}, Nil{}, Bool.pick(List<&2, String>, U.settled(U.Plan{ds, ws}), [s], Nil{})})))) : U.Named}
  {==}

def eff_r.one(+p: String, +more: List<&2, String>, r: U.Named) -> {U.effect.named(U.Effect.Remove{p}, pre.r(more, r)) == pre.r(p <> more, r) : U.Named}:
  match r:
    case U.Named{a, b, c, d, x}:
      {==}

def eff_w.one(+p: String, +w: U.Wants, +more: List<&2, String>, r: U.Named) -> {U.effect.named(U.Effect.Write{p, w}, pre.w(more, r)) == pre.w(p <> more, r) : U.Named}:
  match r:
    case U.Named{a, b, c, d, x}:
      {==}

def eff_l.one(+p: String, +t: String, +more: List<&2, String>, r: U.Named) -> {U.effect.named(U.Effect.Link{p, t}, pre.l(more, r)) == pre.l((p ++ "  (" ++ t ++ ")") <> more, r) : U.Named}:
  match r:
    case U.Named{a, b, c, d, x}:
      {==}

def eff_m.one(+p: String, +w: U.Wants, +more: List<&2, String>, r: U.Named) -> {U.effect.named(U.Effect.Mode{p, w}, pre.m(more, r)) == pre.m((p ++ "  (" ++ Bool.pick(String, U.wants.runs(w), "executable", "plain") ++ ")") <> more, r) : U.Named}:
  match r:
    case U.Named{a, b, c, d, x}:
      {==}

# Each kind of effect, named, is what the dry run names for it.
def eff_removes(xs: List<&2, String>, +rest: List<&2, U.Effect>) -> {U.effects.named(List.append(&2, U.Effect, U.effects.removes(xs), rest)) == pre.r(xs, U.effects.named(rest)) : U.Named}:
  match xs:
    case Nil{}:
      pre_r_nil(U.effects.named(rest))
    case +p <> +more:
      %Equal.sym(U.Named, U.effects.named(List.append(&2, U.Effect, U.effects.removes(more), rest)), pre.r(more, U.effects.named(rest)), eff_removes(more, rest)) : {U.effect.named(U.Effect.Remove{p}, _) == pre.r(p <> more, U.effects.named(rest)) : U.Named}
      eff_r.one(p, more, U.effects.named(rest))

def eff_writes(ds: List<&2, U.Decided>, +rest: List<&2, U.Effect>) -> {U.effects.named(List.append(&2, U.Effect, U.effects.writes(ds), rest)) == pre.w(T.map(~U.Decided, ~String, ~(d => U.decided.path(d)), ds), U.effects.named(rest)) : U.Named}:
  match ds:
    case Nil{}:
      pre_w_nil(U.effects.named(rest))
    case U.Decided{+p, +w, h, rs, s} <> +more:
      %Equal.sym(U.Named, U.effects.named(List.append(&2, U.Effect, U.effects.writes(more), rest)), pre.w(T.map(~U.Decided, ~String, ~(d => U.decided.path(d)), more), U.effects.named(rest)), eff_writes(more, rest)) : {U.effect.named(U.Effect.Write{p, w}, _) == pre.w(p <> T.map(~U.Decided, ~String, ~(d => U.decided.path(d)), more), U.effects.named(rest)) : U.Named}
      eff_w.one(p, w, T.map(~U.Decided, ~String, ~(d => U.decided.path(d)), more), U.effects.named(rest))

def eff_links(ds: List<&2, U.Decided>, +rest: List<&2, U.Effect>) -> {U.effects.named(List.append(&2, U.Effect, U.effects.links(ds), rest)) == pre.l(linked.lines(ds), U.effects.named(rest)) : U.Named}:
  match ds:
    case Nil{}:
      pre_l_nil(U.effects.named(rest))
    case U.Decided{+p, +w, h, rs, s} <> +more:
      %Equal.sym(U.Named, U.effects.named(List.append(&2, U.Effect, U.effects.links(more), rest)), pre.l(linked.lines(more), U.effects.named(rest)), eff_links(more, rest)) : {U.effect.named(U.Effect.Link{p, U.wants.target(w)}, _) == pre.l(linked.lines(U.Decided{p, w, h, rs, s} <> more), U.effects.named(rest)) : U.Named}
      eff_l.one(p, U.wants.target(w), linked.lines(more), U.effects.named(rest))

def eff_modes(ds: List<&2, U.Decided>, +rest: List<&2, U.Effect>) -> {U.effects.named(List.append(&2, U.Effect, U.effects.modes(ds), rest)) == pre.m(moded.lines(ds), U.effects.named(rest)) : U.Named}:
  match ds:
    case Nil{}:
      pre_m_nil(U.effects.named(rest))
    case U.Decided{+p, +w, h, rs, s} <> +more:
      %Equal.sym(U.Named, U.effects.named(List.append(&2, U.Effect, U.effects.modes(more), rest)), pre.m(moded.lines(more), U.effects.named(rest)), eff_modes(more, rest)) : {U.effect.named(U.Effect.Mode{p, w}, _) == pre.m(moded.lines(U.Decided{p, w, h, rs, s} <> more), U.effects.named(rest)) : U.Named}
      eff_m.one(p, w, moded.lines(more), U.effects.named(rest))

# Every effect `apply` performs, named, in turn.
def eff_side(+ds: List<&2, U.Decided>, +ws: List<&2, U.Went>) -> {U.effects.named(U.effects(U.Plan{ds, ws})) == pre.r(U.removes(ws), pre.w(T.map(~U.Decided, ~String, ~(d => U.decided.path(d)), U.writes(ds)), pre.l(linked.lines(U.links(ds)), pre.m(moded.lines(U.modes(ds)), U.Named{Nil{}, Nil{}, Nil{}, Nil{}, Nil{}})))) : U.Named}:
  %Equal.sym(U.Named, U.effects.named(List.append(&2, U.Effect, U.effects.removes(U.removes(ws)), List.append(&2, U.Effect, U.effects.writes(U.writes(ds)), List.append(&2, U.Effect, U.effects.links(U.links(ds)), List.append(&2, U.Effect, U.effects.modes(U.modes(ds)), Nil{}))))), pre.r(U.removes(ws), U.effects.named(List.append(&2, U.Effect, U.effects.writes(U.writes(ds)), List.append(&2, U.Effect, U.effects.links(U.links(ds)), List.append(&2, U.Effect, U.effects.modes(U.modes(ds)), Nil{}))))), eff_removes(U.removes(ws), List.append(&2, U.Effect, U.effects.writes(U.writes(ds)), List.append(&2, U.Effect, U.effects.links(U.links(ds)), List.append(&2, U.Effect, U.effects.modes(U.modes(ds)), Nil{}))))) : {_ == pre.r(U.removes(ws), pre.w(T.map(~U.Decided, ~String, ~(d => U.decided.path(d)), U.writes(ds)), pre.l(linked.lines(U.links(ds)), pre.m(moded.lines(U.modes(ds)), U.Named{Nil{}, Nil{}, Nil{}, Nil{}, Nil{}})))) : U.Named}
  %Equal.sym(U.Named, U.effects.named(List.append(&2, U.Effect, U.effects.writes(U.writes(ds)), List.append(&2, U.Effect, U.effects.links(U.links(ds)), List.append(&2, U.Effect, U.effects.modes(U.modes(ds)), Nil{})))), pre.w(T.map(~U.Decided, ~String, ~(d => U.decided.path(d)), U.writes(ds)), U.effects.named(List.append(&2, U.Effect, U.effects.links(U.links(ds)), List.append(&2, U.Effect, U.effects.modes(U.modes(ds)), Nil{})))), eff_writes(U.writes(ds), List.append(&2, U.Effect, U.effects.links(U.links(ds)), List.append(&2, U.Effect, U.effects.modes(U.modes(ds)), Nil{})))) : {pre.r(U.removes(ws), _) == pre.r(U.removes(ws), pre.w(T.map(~U.Decided, ~String, ~(d => U.decided.path(d)), U.writes(ds)), pre.l(linked.lines(U.links(ds)), pre.m(moded.lines(U.modes(ds)), U.Named{Nil{}, Nil{}, Nil{}, Nil{}, Nil{}})))) : U.Named}
  %Equal.sym(U.Named, U.effects.named(List.append(&2, U.Effect, U.effects.links(U.links(ds)), List.append(&2, U.Effect, U.effects.modes(U.modes(ds)), Nil{}))), pre.l(linked.lines(U.links(ds)), U.effects.named(List.append(&2, U.Effect, U.effects.modes(U.modes(ds)), Nil{}))), eff_links(U.links(ds), List.append(&2, U.Effect, U.effects.modes(U.modes(ds)), Nil{}))) : {pre.r(U.removes(ws), pre.w(T.map(~U.Decided, ~String, ~(d => U.decided.path(d)), U.writes(ds)), _)) == pre.r(U.removes(ws), pre.w(T.map(~U.Decided, ~String, ~(d => U.decided.path(d)), U.writes(ds)), pre.l(linked.lines(U.links(ds)), pre.m(moded.lines(U.modes(ds)), U.Named{Nil{}, Nil{}, Nil{}, Nil{}, Nil{}})))) : U.Named}
  %Equal.sym(U.Named, U.effects.named(List.append(&2, U.Effect, U.effects.modes(U.modes(ds)), Nil{})), pre.m(moded.lines(U.modes(ds)), U.effects.named(Nil{})), eff_modes(U.modes(ds), Nil{})) : {pre.r(U.removes(ws), pre.w(T.map(~U.Decided, ~String, ~(d => U.decided.path(d)), U.writes(ds)), pre.l(linked.lines(U.links(ds)), _))) == pre.r(U.removes(ws), pre.w(T.map(~U.Decided, ~String, ~(d => U.decided.path(d)), U.writes(ds)), pre.l(linked.lines(U.links(ds)), pre.m(moded.lines(U.modes(ds)), U.Named{Nil{}, Nil{}, Nil{}, Nil{}, Nil{}})))) : U.Named}
  {==}

def empty_app(xs: List<&2, U.Effect>, -ys: List<&2, U.Effect>) -> {List.is_empty(&2, U.Effect, List.append(&2, U.Effect, xs, ys)) == Bool.and(List.is_empty(&2, U.Effect, xs), List.is_empty(&2, U.Effect, ys)) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case x <> rest:
      {==}

def empty_removes(xs: List<&2, String>) -> {List.is_empty(&2, U.Effect, U.effects.removes(xs)) == List.is_empty(&2, String, xs) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case x <> rest:
      {==}

def empty_writes(ds: List<&2, U.Decided>) -> {List.is_empty(&2, U.Effect, U.effects.writes(ds)) == List.is_empty(&2, U.Decided, ds) : Bool}:
  match ds:
    case Nil{}:
      {==}
    case U.Decided{p, w, h, rs, s} <> rest:
      {==}

def empty_links(ds: List<&2, U.Decided>) -> {List.is_empty(&2, U.Effect, U.effects.links(ds)) == List.is_empty(&2, U.Decided, ds) : Bool}:
  match ds:
    case Nil{}:
      {==}
    case U.Decided{p, w, h, rs, s} <> rest:
      {==}

def empty_modes(ds: List<&2, U.Decided>) -> {List.is_empty(&2, U.Effect, U.effects.modes(ds)) == List.is_empty(&2, U.Decided, ds) : Bool}:
  match ds:
    case Nil{}:
      {==}
    case U.Decided{p, w, h, rs, s} <> rest:
      {==}

def and4.eff(a: Bool, b: Bool, c: Bool, d: Bool) -> {Bool.and(Bool.and(a, b), Bool.and(c, d)) == Bool.and(b, Bool.and(a, Bool.and(d, Bool.and(c, True{})))) : Bool}:
  match a b c d:
    case True{} True{} True{} True{}:
      {==}
    case True{} True{} True{} False{}:
      {==}
    case True{} True{} False{} True{}:
      {==}
    case True{} True{} False{} False{}:
      {==}
    case True{} False{} c2 d2:
      {==}
    case False{} True{} c2 d2:
      {==}
    case False{} False{} c2 d2:
      {==}

# It says the folder holds the target already exactly where it would
# perform nothing.
def settled_empty(+ds: List<&2, U.Decided>, +ws: List<&2, U.Went>) -> {U.settled(U.Plan{ds, ws}) == List.is_empty(&2, U.Effect, U.effects(U.Plan{ds, ws})) : Bool}:
  %Equal.sym(Bool, List.is_empty(&2, U.Effect, List.append(&2, U.Effect, U.effects.removes(U.removes(ws)), List.append(&2, U.Effect, U.effects.writes(U.writes(ds)), List.append(&2, U.Effect, U.effects.links(U.links(ds)), List.append(&2, U.Effect, U.effects.modes(U.modes(ds)), Nil{}))))), Bool.and(List.is_empty(&2, U.Effect, U.effects.removes(U.removes(ws))), List.is_empty(&2, U.Effect, List.append(&2, U.Effect, U.effects.writes(U.writes(ds)), List.append(&2, U.Effect, U.effects.links(U.links(ds)), List.append(&2, U.Effect, U.effects.modes(U.modes(ds)), Nil{}))))), empty_app(U.effects.removes(U.removes(ws)), List.append(&2, U.Effect, U.effects.writes(U.writes(ds)), List.append(&2, U.Effect, U.effects.links(U.links(ds)), List.append(&2, U.Effect, U.effects.modes(U.modes(ds)), Nil{}))))) : {U.settled(U.Plan{ds, ws}) == _ : Bool}
  %Equal.sym(Bool, List.is_empty(&2, U.Effect, List.append(&2, U.Effect, U.effects.writes(U.writes(ds)), List.append(&2, U.Effect, U.effects.links(U.links(ds)), List.append(&2, U.Effect, U.effects.modes(U.modes(ds)), Nil{})))), Bool.and(List.is_empty(&2, U.Effect, U.effects.writes(U.writes(ds))), List.is_empty(&2, U.Effect, List.append(&2, U.Effect, U.effects.links(U.links(ds)), List.append(&2, U.Effect, U.effects.modes(U.modes(ds)), Nil{})))), empty_app(U.effects.writes(U.writes(ds)), List.append(&2, U.Effect, U.effects.links(U.links(ds)), List.append(&2, U.Effect, U.effects.modes(U.modes(ds)), Nil{})))) : {U.settled(U.Plan{ds, ws}) == Bool.and(List.is_empty(&2, U.Effect, U.effects.removes(U.removes(ws))), _) : Bool}
  %Equal.sym(Bool, List.is_empty(&2, U.Effect, List.append(&2, U.Effect, U.effects.links(U.links(ds)), List.append(&2, U.Effect, U.effects.modes(U.modes(ds)), Nil{}))), Bool.and(List.is_empty(&2, U.Effect, U.effects.links(U.links(ds))), List.is_empty(&2, U.Effect, List.append(&2, U.Effect, U.effects.modes(U.modes(ds)), Nil{}))), empty_app(U.effects.links(U.links(ds)), List.append(&2, U.Effect, U.effects.modes(U.modes(ds)), Nil{}))) : {U.settled(U.Plan{ds, ws}) == Bool.and(List.is_empty(&2, U.Effect, U.effects.removes(U.removes(ws))), Bool.and(List.is_empty(&2, U.Effect, U.effects.writes(U.writes(ds))), _)) : Bool}
  %Equal.sym(Bool, List.is_empty(&2, U.Effect, List.append(&2, U.Effect, U.effects.modes(U.modes(ds)), Nil{})), Bool.and(List.is_empty(&2, U.Effect, U.effects.modes(U.modes(ds))), True{}), empty_app(U.effects.modes(U.modes(ds)), Nil{})) : {U.settled(U.Plan{ds, ws}) == Bool.and(List.is_empty(&2, U.Effect, U.effects.removes(U.removes(ws))), Bool.and(List.is_empty(&2, U.Effect, U.effects.writes(U.writes(ds))), Bool.and(List.is_empty(&2, U.Effect, U.effects.links(U.links(ds))), _))) : Bool}
  %Equal.sym(Bool, List.is_empty(&2, U.Effect, U.effects.removes(U.removes(ws))), List.is_empty(&2, String, U.removes(ws)), empty_removes(U.removes(ws))) : {U.settled(U.Plan{ds, ws}) == Bool.and(_, Bool.and(List.is_empty(&2, U.Effect, U.effects.writes(U.writes(ds))), Bool.and(List.is_empty(&2, U.Effect, U.effects.links(U.links(ds))), Bool.and(List.is_empty(&2, U.Effect, U.effects.modes(U.modes(ds))), True{})))) : Bool}
  %Equal.sym(Bool, List.is_empty(&2, U.Effect, U.effects.writes(U.writes(ds))), List.is_empty(&2, U.Decided, U.writes(ds)), empty_writes(U.writes(ds))) : {U.settled(U.Plan{ds, ws}) == Bool.and(List.is_empty(&2, String, U.removes(ws)), Bool.and(_, Bool.and(List.is_empty(&2, U.Effect, U.effects.links(U.links(ds))), Bool.and(List.is_empty(&2, U.Effect, U.effects.modes(U.modes(ds))), True{})))) : Bool}
  %Equal.sym(Bool, List.is_empty(&2, U.Effect, U.effects.links(U.links(ds))), List.is_empty(&2, U.Decided, U.links(ds)), empty_links(U.links(ds))) : {U.settled(U.Plan{ds, ws}) == Bool.and(List.is_empty(&2, String, U.removes(ws)), Bool.and(List.is_empty(&2, U.Decided, U.writes(ds)), Bool.and(_, Bool.and(List.is_empty(&2, U.Effect, U.effects.modes(U.modes(ds))), True{})))) : Bool}
  %Equal.sym(Bool, List.is_empty(&2, U.Effect, U.effects.modes(U.modes(ds))), List.is_empty(&2, U.Decided, U.modes(ds)), empty_modes(U.modes(ds))) : {U.settled(U.Plan{ds, ws}) == Bool.and(List.is_empty(&2, String, U.removes(ws)), Bool.and(List.is_empty(&2, U.Decided, U.writes(ds)), Bool.and(List.is_empty(&2, U.Decided, U.links(ds)), Bool.and(_, True{})))) : Bool}
  and4.eff(List.is_empty(&2, U.Decided, U.writes(ds)), List.is_empty(&2, String, U.removes(ws)), List.is_empty(&2, U.Decided, U.modes(ds)), List.is_empty(&2, U.Decided, U.links(ds)))

# `update --dry-run` names, kind by kind and in order, exactly the effects
# `update` performs, and says the folder holds the target already exactly
# where it performs none.
def dry_names(p: U.Plan, +s: String) -> {U.dry.read(U.said.dry(s, p)) == U.effects.read(s, U.effects(p)) : U.Named}:
  match p:
    case U.Plan{+ds, +ws}:
      %Equal.sym(U.Named, U.dry.read(U.said.dry(s, U.Plan{ds, ws})), pre.w(T.map(~U.Decided, ~String, ~(d => U.decided.path(d)), U.writes(ds)), pre.r(U.removes(ws), pre.m(moded.lines(U.modes(ds)), pre.l(linked.lines(U.links(ds)), U.Named{Nil{}, Nil{}, Nil{}, Nil{}, Bool.pick(List<&2, String>, U.settled(U.Plan{ds, ws}), [s], Nil{})})))), dry_side(s, ds, ws)) : {_ == U.effects.read(s, U.effects(U.Plan{ds, ws})) : U.Named}
      %Equal.sym(U.Named, U.effects.named(U.effects(U.Plan{ds, ws})), pre.r(U.removes(ws), pre.w(T.map(~U.Decided, ~String, ~(d => U.decided.path(d)), U.writes(ds)), pre.l(linked.lines(U.links(ds)), pre.m(moded.lines(U.modes(ds)), U.Named{Nil{}, Nil{}, Nil{}, Nil{}, Nil{}})))), eff_side(ds, ws)) : {pre.w(T.map(~U.Decided, ~String, ~(d => U.decided.path(d)), U.writes(ds)), pre.r(U.removes(ws), pre.m(moded.lines(U.modes(ds)), pre.l(linked.lines(U.links(ds)), U.Named{Nil{}, Nil{}, Nil{}, Nil{}, Bool.pick(List<&2, String>, U.settled(U.Plan{ds, ws}), [s], Nil{})})))) == U.named.settled(_, Bool.pick(List<&2, String>, List.is_empty(&2, U.Effect, U.effects(U.Plan{ds, ws})), [s], Nil{})) : U.Named}
      %settled_empty(ds, ws) : {pre.w(T.map(~U.Decided, ~String, ~(d => U.decided.path(d)), U.writes(ds)), pre.r(U.removes(ws), pre.m(moded.lines(U.modes(ds)), pre.l(linked.lines(U.links(ds)), U.Named{Nil{}, Nil{}, Nil{}, Nil{}, Bool.pick(List<&2, String>, U.settled(U.Plan{ds, ws}), [s], Nil{})})))) == U.named.settled(pre.r(U.removes(ws), pre.w(T.map(~U.Decided, ~String, ~(d => U.decided.path(d)), U.writes(ds)), pre.l(linked.lines(U.links(ds)), pre.m(moded.lines(U.modes(ds)), U.Named{Nil{}, Nil{}, Nil{}, Nil{}, Nil{}})))), Bool.pick(List<&2, String>, _, [s], Nil{})) : U.Named}
      {==}

# Where it reaches
# ----------------
#
# Every file `update` writes, every mode it sets and every link it makes is
# at a path the target's tree holds, and every path it removes anything at
# is one the tree does not hold, where the walk found a file whose bytes
# some revision records for a file history put at that path, or a link.

# The paths `update` places are the tree's own: sorting by path keeps every
# path, and gathering the files under each keeps every path once.
def tree_keyed.pick(b: Bool, +x: Tree.Entry, +rest: List<&2, Tree.Entry>, +p: String, ih: {U.tree.has(rest, p) == Bool.not(List.is_empty(&2, Tree.Entry, SortL.keyed(~Tree.Entry, ~(e => Tree.entry_path(e)), p, rest))) : Bool}) -> {Bool.or(b, U.tree.has(rest, p)) == Bool.not(List.is_empty(&2, Tree.Entry, Bool.pick(List<&2, Tree.Entry>, b, x <> SortL.keyed(~Tree.Entry, ~(e => Tree.entry_path(e)), p, rest), SortL.keyed(~Tree.Entry, ~(e => Tree.entry_path(e)), p, rest)))) : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      ih

def tree_keyed(xs: List<&2, Tree.Entry>, +p: String) -> {U.tree.has(xs, p) == Bool.not(List.is_empty(&2, Tree.Entry, SortL.keyed(~Tree.Entry, ~(e => Tree.entry_path(e)), p, xs))) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      tree_keyed.pick(String.eq(Tree.entry_path(x), p), x, rest, p, tree_keyed(rest, p))


def tree_sort(+t: Tree.Tree(), +p: String) -> {U.tree.has(List.sort(~Tree.Entry, ~(a => b => String.is_le(Tree.entry_path(a), Tree.entry_path(b))), t), p) == U.tree.has(t, p) : Bool}:
  Equal.trans(Bool, U.tree.has(List.sort(~Tree.Entry, ~(a => b => String.is_le(Tree.entry_path(a), Tree.entry_path(b))), t), p), Bool.not(List.is_empty(&2, Tree.Entry, SortL.keyed(~Tree.Entry, ~(e => Tree.entry_path(e)), p, List.sort(~Tree.Entry, ~(a => b => String.is_le(Tree.entry_path(a), Tree.entry_path(b))), t)))), U.tree.has(t, p),
    tree_keyed(List.sort(~Tree.Entry, ~(a => b => String.is_le(Tree.entry_path(a), Tree.entry_path(b))), t), p),
    Equal.trans(Bool, Bool.not(List.is_empty(&2, Tree.Entry, SortL.keyed(~Tree.Entry, ~(e => Tree.entry_path(e)), p, List.sort(~Tree.Entry, ~(a => b => String.is_le(Tree.entry_path(a), Tree.entry_path(b))), t)))), Bool.not(List.is_empty(&2, Tree.Entry, SortL.keyed(~Tree.Entry, ~(e => Tree.entry_path(e)), p, t))), U.tree.has(t, p),
      Equal.cong(List<&2, Tree.Entry>, Bool, xs => Bool.not(List.is_empty(&2, Tree.Entry, xs)), SortL.keyed(~Tree.Entry, ~(e => Tree.entry_path(e)), p, List.sort(~Tree.Entry, ~(a => b => String.is_le(Tree.entry_path(a), Tree.entry_path(b))), t)), SortL.keyed(~Tree.Entry, ~(e => Tree.entry_path(e)), p, t), SortL.sort_keyed(~Tree.Entry, ~(e => Tree.entry_path(e)), t, p)),
      Equal.sym(Bool, U.tree.has(t, p), Bool.not(List.is_empty(&2, Tree.Entry, SortL.keyed(~Tree.Entry, ~(e => Tree.entry_path(e)), p, t))), tree_keyed(t, p))))

def or_idem(a: Bool, -m: Bool) -> {Bool.or(a, m) == Bool.or(a, Bool.or(a, m)) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def put_paths.pick(b: Bool, +e: Tree.Entry, +p: String, +fs: List<&2, Tree.Entry>, +rest: List<&2, U.Placing>, +q: String, +eb: {String.eq(p, Tree.entry_path(e)) == b : Bool}) -> {Rev.member(T.map(~U.Placing, ~String, ~(x => U.placing.path(x)), Bool.pick(List<&2, U.Placing>, b, U.Placing{p, e <> fs} <> rest, U.Placing{Tree.entry_path(e), [e]} <> U.Placing{p, fs} <> rest)), q) == Bool.or(String.eq(Tree.entry_path(e), q), Bool.or(String.eq(p, q), Rev.member(T.map(~U.Placing, ~String, ~(x => U.placing.path(x)), rest), q))) : Bool}:
  match b:
    case True{}:
      %SL.eq_true(p, Tree.entry_path(e), eb) : {Bool.or(String.eq(p, q), Rev.member(T.map(~U.Placing, ~String, ~(x => U.placing.path(x)), rest), q)) == Bool.or(String.eq(_, q), Bool.or(String.eq(p, q), Rev.member(T.map(~U.Placing, ~String, ~(x => U.placing.path(x)), rest), q))) : Bool}
      or_idem(String.eq(p, q), Rev.member(T.map(~U.Placing, ~String, ~(x => U.placing.path(x)), rest), q))
    case False{}:
      {==}

# A file placed adds its path, once, to the paths already placed.
def put_paths(+e: Tree.Entry, ps: List<&2, U.Placing>, +q: String) -> {Rev.member(T.map(~U.Placing, ~String, ~(x => U.placing.path(x)), U.placings.put(e, ps)), q) == Bool.or(String.eq(Tree.entry_path(e), q), Rev.member(T.map(~U.Placing, ~String, ~(x => U.placing.path(x)), ps), q)) : Bool}:
  match ps:
    case Nil{}:
      {==}
    case U.Placing{+p, +fs} <> +rest:
      put_paths.pick(String.eq(p, Tree.entry_path(e)), e, p, fs, rest, q, {==})

def placed_paths(ys: List<&2, Tree.Entry>, +q: String) -> {Rev.member(T.map(~U.Placing, ~String, ~(x => U.placing.path(x)), U.placings.go(ys)), q) == U.tree.has(ys, q) : Bool}:
  match ys:
    case Nil{}:
      {==}
    case +y <> +rest:
      %Equal.sym(Bool, Rev.member(T.map(~U.Placing, ~String, ~(x => U.placing.path(x)), U.placings.put(y, U.placings.go(rest))), q), Bool.or(String.eq(Tree.entry_path(y), q), Rev.member(T.map(~U.Placing, ~String, ~(x => U.placing.path(x)), U.placings.go(rest)), q)), put_paths(y, U.placings.go(rest), q)) : {_ == U.tree.has(y <> rest, q) : Bool}
      %placed_paths(rest, q) : {Bool.or(String.eq(Tree.entry_path(y), q), Rev.member(T.map(~U.Placing, ~String, ~(x => U.placing.path(x)), U.placings.go(rest)), q)) == Bool.or(String.eq(Tree.entry_path(y), q), _) : Bool}
      {==}

# The paths `update` places a tree's files at are exactly the tree's paths.
def placings_paths(+t: Tree.Tree(), +q: String) -> {Rev.member(T.map(~U.Placing, ~String, ~(x => U.placing.path(x)), U.placings(t)), q) == U.tree.has(t, q) : Bool}:
  Equal.trans(Bool, Rev.member(T.map(~U.Placing, ~String, ~(x => U.placing.path(x)), U.placings(t)), q), U.tree.has(List.sort(~Tree.Entry, ~(a => b => String.is_le(Tree.entry_path(a), Tree.entry_path(b))), t), q), U.tree.has(t, q),
    placed_paths(List.sort(~Tree.Entry, ~(a => b => String.is_le(Tree.entry_path(a), Tree.entry_path(b))), t), q),
    tree_sort(t, q))

# Every file of a tree `update` steps through is at one of the tree's
# paths.
def ents.at(+c: Tree.Tree(), es: List<&2, Tree.Entry>) -> Bool:
  match es:
    case Nil{}:
      True{}
    case e <> rest:
      Bool.and(U.tree.has(c, Tree.entry_path(e)), ents.at(c, rest))

def placed.at(+c: Tree.Tree(), ps: List<&2, U.Placing>) -> Bool:
  match ps:
    case Nil{}:
      True{}
    case U.Placing{p, fs} <> rest:
      Bool.and(ents.at(c, fs), placed.at(c, rest))

def ents_weaken(+y: Tree.Entry, +c: Tree.Tree(), es: List<&2, Tree.Entry>, +h: {ents.at(c, es) == True{} : Bool}) -> {ents.at(y <> c, es) == True{} : Bool}:
  match es:
    case Nil{}:
      {==}
    case +e <> +rest:
      AL.and_intro(Bool.or(String.eq(Tree.entry_path(y), Tree.entry_path(e)), U.tree.has(c, Tree.entry_path(e))), ents.at(y <> c, rest),
        AL.or_right(String.eq(Tree.entry_path(y), Tree.entry_path(e)), U.tree.has(c, Tree.entry_path(e)), Comp.and_left(U.tree.has(c, Tree.entry_path(e)), ents.at(c, rest), h)),
        ents_weaken(y, c, rest, Comp.and_right(U.tree.has(c, Tree.entry_path(e)), ents.at(c, rest), h)))

def placed_weaken(+y: Tree.Entry, +c: Tree.Tree(), ps: List<&2, U.Placing>, +h: {placed.at(c, ps) == True{} : Bool}) -> {placed.at(y <> c, ps) == True{} : Bool}:
  match ps:
    case Nil{}:
      {==}
    case U.Placing{p, +fs} <> +rest:
      AL.and_intro(ents.at(y <> c, fs), placed.at(y <> c, rest),
        ents_weaken(y, c, fs, Comp.and_left(ents.at(c, fs), placed.at(c, rest), h)),
        placed_weaken(y, c, rest, Comp.and_right(ents.at(c, fs), placed.at(c, rest), h)))

def put_at.pick(b: Bool, +c: Tree.Tree(), +e: Tree.Entry, +p: String, +fs: List<&2, Tree.Entry>, +rest: List<&2, U.Placing>, +he: {U.tree.has(c, Tree.entry_path(e)) == True{} : Bool}, +h: {placed.at(c, U.Placing{p, fs} <> rest) == True{} : Bool}) -> {placed.at(c, Bool.pick(List<&2, U.Placing>, b, U.Placing{p, e <> fs} <> rest, U.Placing{Tree.entry_path(e), [e]} <> U.Placing{p, fs} <> rest)) == True{} : Bool}:
  match b:
    case True{}:
      AL.and_intro(Bool.and(U.tree.has(c, Tree.entry_path(e)), ents.at(c, fs)), placed.at(c, rest),
        AL.and_intro(U.tree.has(c, Tree.entry_path(e)), ents.at(c, fs), he, Comp.and_left(ents.at(c, fs), placed.at(c, rest), h)),
        Comp.and_right(ents.at(c, fs), placed.at(c, rest), h))
    case False{}:
      AL.and_intro(Bool.and(U.tree.has(c, Tree.entry_path(e)), True{}), Bool.and(ents.at(c, fs), placed.at(c, rest)),
        AL.and_intro(U.tree.has(c, Tree.entry_path(e)), True{}, he, {==}),
        h)

def put_at(+c: Tree.Tree(), +e: Tree.Entry, ps: List<&2, U.Placing>, +he: {U.tree.has(c, Tree.entry_path(e)) == True{} : Bool}, +h: {placed.at(c, ps) == True{} : Bool}) -> {placed.at(c, U.placings.put(e, ps)) == True{} : Bool}:
  match ps:
    case Nil{}:
      AL.and_intro(Bool.and(U.tree.has(c, Tree.entry_path(e)), True{}), True{}, AL.and_intro(U.tree.has(c, Tree.entry_path(e)), True{}, he, {==}), {==})
    case U.Placing{+p, +fs} <> +rest:
      put_at.pick(String.eq(p, Tree.entry_path(e)), c, e, p, fs, rest, he, h)

def go_at(ys: List<&2, Tree.Entry>) -> {placed.at(ys, U.placings.go(ys)) == True{} : Bool}:
  match ys:
    case Nil{}:
      {==}
    case +y <> +rest:
      put_at(y <> rest, y, U.placings.go(rest), AL.or_left(String.eq(Tree.entry_path(y), Tree.entry_path(y)), U.tree.has(rest, Tree.entry_path(y)), SL.eq_refl(Tree.entry_path(y))), placed_weaken(y, rest, U.placings.go(rest), go_at(rest)))

def single_at(+c: Tree.Tree(), ps: List<&2, U.Placing>, +h: {placed.at(c, ps) == True{} : Bool}) -> {ents.at(c, U.single(ps)) == True{} : Bool}:
  match ps:
    case Nil{}:
      {==}
    case U.Placing{p, fs} <> +rest:
      match fs:
        case Nil{}:
          single_at(c, rest, Comp.and_right(True{}, placed.at(c, rest), h))
        case +e <> more:
          match more:
            case Nil{}:
              AL.and_intro(U.tree.has(c, Tree.entry_path(e)), ents.at(c, U.single(rest)),
                Comp.and_left(U.tree.has(c, Tree.entry_path(e)), True{}, Comp.and_left(Bool.and(U.tree.has(c, Tree.entry_path(e)), True{}), placed.at(c, rest), h)),
                single_at(c, rest, Comp.and_right(Bool.and(U.tree.has(c, Tree.entry_path(e)), True{}), placed.at(c, rest), h)))
            case +e2 <> +m2:
              single_at(c, rest, Comp.and_right(Bool.and(U.tree.has(c, Tree.entry_path(e)), Bool.and(U.tree.has(c, Tree.entry_path(e2)), ents.at(c, m2))), placed.at(c, rest), h))

def ents_sort(+t: Tree.Tree(), es: List<&2, Tree.Entry>, +h: {ents.at(List.sort(~Tree.Entry, ~(a => b => String.is_le(Tree.entry_path(a), Tree.entry_path(b))), t), es) == True{} : Bool}) -> {ents.at(t, es) == True{} : Bool}:
  match es:
    case Nil{}:
      {==}
    case +e <> +rest:
      AL.and_intro(U.tree.has(t, Tree.entry_path(e)), ents.at(t, rest),
        (%tree_sort(t, Tree.entry_path(e)) : {_ == True{} : Bool}
          Comp.and_left(U.tree.has(List.sort(~Tree.Entry, ~(a => b => String.is_le(Tree.entry_path(a), Tree.entry_path(b))), t), Tree.entry_path(e)), ents.at(List.sort(~Tree.Entry, ~(a => b => String.is_le(Tree.entry_path(a), Tree.entry_path(b))), t), rest), h)),
        ents_sort(t, rest, Comp.and_right(U.tree.has(List.sort(~Tree.Entry, ~(a => b => String.is_le(Tree.entry_path(a), Tree.entry_path(b))), t), Tree.entry_path(e)), ents.at(List.sort(~Tree.Entry, ~(a => b => String.is_le(Tree.entry_path(a), Tree.entry_path(b))), t), rest), h)))

# Each path the tree holds one file at is one of its paths.
def single_all(+t: Tree.Tree()) -> {ents.at(t, U.single(U.placings(t))) == True{} : Bool}:
  ents_sort(t, U.single(U.placings(t)), single_at(List.sort(~Tree.Entry, ~(a => b => String.is_le(Tree.entry_path(a), Tree.entry_path(b))), t), U.placings(t), go_at(List.sort(~Tree.Entry, ~(a => b => String.is_le(Tree.entry_path(a), Tree.entry_path(b))), t))))

# The steps are at the tree's paths, and so is every write, mode and link.
def decided.at(+c: Tree.Tree(), ds: List<&2, U.Decided>) -> Bool:
  match ds:
    case Nil{}:
      True{}
    case U.Decided{p, w, h, rs, s} <> rest:
      Bool.and(U.tree.has(c, p), decided.at(c, rest))

def pres_at(+c: Tree.Tree(), +fs: List<&2, Main.Full>, +oldest: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +located: Map<&2, String>, +id: String, +t: Tree.Tree(), +hm: Map<&2, Maybe<&2, U.Held>>, +ls: Map<&2, String>, es: List<&2, Tree.Entry>, +rec: List<&2, U.Rec>, +h: {ents.at(c, es) == True{} : Bool}) -> {decided.at(c, U.decided(U.looks(U.pres(fs, oldest, ds, located, id, t, hm, ls, es), rec))) == True{} : Bool}:
  match es:
    case Nil{}:
      {==}
    case +e <> +rest:
      AL.and_intro(U.tree.has(c, Tree.entry_path(e)), decided.at(c, U.decided(U.looks(U.pres(fs, oldest, ds, located, id, t, hm, ls, rest), rec))),
        Comp.and_left(U.tree.has(c, Tree.entry_path(e)), ents.at(c, rest), h),
        pres_at(c, fs, oldest, ds, located, id, t, hm, ls, rest, rec, Comp.and_right(U.tree.has(c, Tree.entry_path(e)), ents.at(c, rest), h)))

def keep_at(b: Bool, +c: Tree.Tree(), +p: String, +w: U.Wants, +hh: U.Held, +rs: List<&2, String>, +s: U.Step, +rest: List<&2, U.Decided>, +hp: {U.tree.has(c, p) == True{} : Bool}, +ih: {decided.at(c, rest) == True{} : Bool}) -> {decided.at(c, Tree.keep(~U.Decided, b, U.Decided{p, w, hh, rs, s}, rest)) == True{} : Bool}:
  match b:
    case True{}:
      AL.and_intro(U.tree.has(c, p), decided.at(c, rest), hp, ih)
    case False{}:
      ih

def stepping_at(~pick: U.Step -> Bool, +c: Tree.Tree(), ds: List<&2, U.Decided>, +h: {decided.at(c, ds) == True{} : Bool}) -> {decided.at(c, U.stepping(~pick, ds)) == True{} : Bool}:
  match ds:
    case Nil{}:
      {==}
    case U.Decided{+p, +w, +hh, +rs, +s} <> +rest:
      keep_at(pick(s), c, p, w, hh, rs, s, U.stepping(~pick, rest), Comp.and_left(U.tree.has(c, p), decided.at(c, rest), h), stepping_at(~pick, c, rest, Comp.and_right(U.tree.has(c, p), decided.at(c, rest), h)))

def writes_conf(+fs: List<&2, Main.Full>, +dss: List<&2, Store.Doc>, +t: Tree.Tree(), +found: List<&2, Folder.Found>, +dg: Map<&2, String>, ds: List<&2, U.Decided>, +h: {decided.at(t, ds) == True{} : Bool}) -> {U.confined(fs, dss, t, found, dg, U.effects.writes(ds)) == True{} : Bool}:
  match ds:
    case Nil{}:
      {==}
    case U.Decided{+p, w, hh, rs, s} <> +rest:
      AL.and_intro(U.tree.has(t, p), U.confined(fs, dss, t, found, dg, U.effects.writes(rest)), Comp.and_left(U.tree.has(t, p), decided.at(t, rest), h), writes_conf(fs, dss, t, found, dg, rest, Comp.and_right(U.tree.has(t, p), decided.at(t, rest), h)))

def links_conf(+fs: List<&2, Main.Full>, +dss: List<&2, Store.Doc>, +t: Tree.Tree(), +found: List<&2, Folder.Found>, +dg: Map<&2, String>, ds: List<&2, U.Decided>, +h: {decided.at(t, ds) == True{} : Bool}) -> {U.confined(fs, dss, t, found, dg, U.effects.links(ds)) == True{} : Bool}:
  match ds:
    case Nil{}:
      {==}
    case U.Decided{+p, w, hh, rs, s} <> +rest:
      AL.and_intro(U.tree.has(t, p), U.confined(fs, dss, t, found, dg, U.effects.links(rest)), Comp.and_left(U.tree.has(t, p), decided.at(t, rest), h), links_conf(fs, dss, t, found, dg, rest, Comp.and_right(U.tree.has(t, p), decided.at(t, rest), h)))

def modes_conf(+fs: List<&2, Main.Full>, +dss: List<&2, Store.Doc>, +t: Tree.Tree(), +found: List<&2, Folder.Found>, +dg: Map<&2, String>, ds: List<&2, U.Decided>, +h: {decided.at(t, ds) == True{} : Bool}) -> {U.confined(fs, dss, t, found, dg, U.effects.modes(ds)) == True{} : Bool}:
  match ds:
    case Nil{}:
      {==}
    case U.Decided{+p, w, hh, rs, s} <> +rest:
      AL.and_intro(U.tree.has(t, p), U.confined(fs, dss, t, found, dg, U.effects.modes(rest)), Comp.and_left(U.tree.has(t, p), decided.at(t, rest), h), modes_conf(fs, dss, t, found, dg, rest, Comp.and_right(U.tree.has(t, p), decided.at(t, rest), h)))

def confined_app(+fs: List<&2, Main.Full>, +dss: List<&2, Store.Doc>, +t: Tree.Tree(), +found: List<&2, Folder.Found>, +dg: Map<&2, String>, xs: List<&2, U.Effect>, +ys: List<&2, U.Effect>, +hx: {U.confined(fs, dss, t, found, dg, xs) == True{} : Bool}, +hy: {U.confined(fs, dss, t, found, dg, ys) == True{} : Bool}) -> {U.confined(fs, dss, t, found, dg, List.append(&2, U.Effect, xs, ys)) == True{} : Bool}:
  match xs:
    case Nil{}:
      hy
    case +x <> +rest:
      AL.and_intro(U.reaches(fs, dss, t, found, dg, x), U.confined(fs, dss, t, found, dg, List.append(&2, U.Effect, rest, ys)),
        Comp.and_left(U.reaches(fs, dss, t, found, dg, x), U.confined(fs, dss, t, found, dg, rest), hx),
        confined_app(fs, dss, t, found, dg, rest, ys, Comp.and_right(U.reaches(fs, dss, t, found, dg, x), U.confined(fs, dss, t, found, dg, rest), hx), hy))

# What `update` removes is at a path the tree does not hold
# ---------------------------------------------------------

def gone.out(+t: Tree.Tree(), ps: List<&2, String>) -> Bool:
  match ps:
    case Nil{}:
      True{}
    case +p <> rest:
      Bool.and(Bool.not(U.tree.has(t, p)), gone.out(t, rest))

def has_hv(r: Set() & Bool) -> {U.has(r) == ML.hv(Unit, r) : Bool}:
  match r:
    case (s, b):
      {==}

def out_pick(b: Bool, +t: Tree.Tree(), +x: String, +rest: List<&2, String>, +eb: {Bool.not(U.has(Set.has(Set.from_list(T.map(~U.Placing, ~String, ~(q => U.placing.path(q)), U.placings(t))), x))) == b : Bool}, +ih: {gone.out(t, rest) == True{} : Bool}) -> {gone.out(t, Rev.keep(b, x, rest)) == True{} : Bool}:
  match b:
    case True{}:
      AL.and_intro(Bool.not(U.tree.has(t, x)), gone.out(t, rest),
        (%placings_paths(t, x) : {Bool.not(_) == True{} : Bool}
          %ML.set_from_list(T.map(~U.Placing, ~String, ~(q => U.placing.path(q)), U.placings(t)), x) : {Bool.not(_) == True{} : Bool}
          %has_hv(Set.has(Set.from_list(T.map(~U.Placing, ~String, ~(q => U.placing.path(q)), U.placings(t))), x)) : {Bool.not(_) == True{} : Bool}
          eb),
        ih)
    case False{}:
      ih

# The paths the walk took that the tree does not place are paths the tree
# does not hold.
def gone_out(fnd: List<&2, Folder.Found>, +t: Tree.Tree()) -> {gone.out(t, U.gone.paths(fnd, Set.from_list(T.map(~U.Placing, ~String, ~(q => U.placing.path(q)), U.placings(t))))) == True{} : Bool}:
  match fnd:
    case Nil{}:
      {==}
    case +f <> +rest:
      out_pick(Bool.not(U.has(Set.has(Set.from_list(T.map(~U.Placing, ~String, ~(q => U.placing.path(q)), U.placings(t))), Folder.found.path(f)))), t, Folder.found.path(f), U.gone.paths(rest, Set.from_list(T.map(~U.Placing, ~String, ~(q => U.placing.path(q)), U.placings(t)))), {==}, gone_out(rest, t))

# What the walk found at a path, read through the map `update` builds: the
# last thing the walk took there, or what the map held before.
def found.last(fnd: List<&2, Folder.Found>, +dg: Map<&2, String>, +p: String, acc: Maybe<&2, U.Held>) -> Maybe<&2, U.Held>:
  match fnd:
    case Nil{}:
      acc
    case Folder.Found.File{+q, r, n} <> rest:
      found.last(rest, dg, p, Bool.pick(Maybe<&2, U.Held>, String.eq(q, p), Some{U.Held.File{Main.status.folder_digest(dg, q), r}}, acc))
    case Folder.Found.Link{+q, t} <> rest:
      found.last(rest, dg, p, Bool.pick(Maybe<&2, U.Held>, String.eq(q, p), Some{U.Held.Link{t}}, acc))

def took_gv(r: Map<&2, Maybe<&2, U.Held>> & Maybe<&2, U.Held>) -> {U.took(r) == ML.gv(Maybe<&2, U.Held>, r) : Maybe<&2, U.Held>}:
  match r:
    case (m, h):
      {==}

def taken_new(+p: String) -> {U.taken(Map.new(&2, Maybe<&2, U.Held>), p) == None{} : Maybe<&2, U.Held>}:
  Equal.trans(Maybe<&2, U.Held>, U.taken(Map.new(&2, Maybe<&2, U.Held>), p), ML.gv(Maybe<&2, U.Held>, Map.get(Maybe<&2, U.Held>, None{}, Map.new(&2, Maybe<&2, U.Held>), p)), None{}, took_gv(Map.get(Maybe<&2, U.Held>, None{}, Map.new(&2, Maybe<&2, U.Held>), p)), ML.get_new(Maybe<&2, U.Held>, None{}, p))

def taken_set.pick(b: Bool, +m: Map<&2, Maybe<&2, U.Held>>, +w: ML.Wf.top(Maybe<&2, U.Held>, m), +q: String, +v: Maybe<&2, U.Held>, +p: String, +eb: {String.eq(q, p) == b : Bool}) -> {U.taken(Map.set(&2, Maybe<&2, U.Held>, m, q, v), p) == Bool.pick(Maybe<&2, U.Held>, b, v, U.taken(m, p)) : Maybe<&2, U.Held>}:
  match b:
    case True{}:
      %Equal.sym(String, q, p, SL.eq_true(q, p, eb)) : {U.taken(Map.set(&2, Maybe<&2, U.Held>, m, _, v), p) == v : Maybe<&2, U.Held>}
      Equal.trans(Maybe<&2, U.Held>, U.taken(Map.set(&2, Maybe<&2, U.Held>, m, p, v), p), ML.gv(Maybe<&2, U.Held>, Map.get(Maybe<&2, U.Held>, None{}, Map.set(&2, Maybe<&2, U.Held>, m, p, v), p)), v, took_gv(Map.get(Maybe<&2, U.Held>, None{}, Map.set(&2, Maybe<&2, U.Held>, m, p, v), p)), ML.get_set_same(Maybe<&2, U.Held>, None{}, m, p, v))
    case False{}:
      Equal.trans(Maybe<&2, U.Held>, U.taken(Map.set(&2, Maybe<&2, U.Held>, m, q, v), p), ML.gv(Maybe<&2, U.Held>, Map.get(Maybe<&2, U.Held>, None{}, Map.set(&2, Maybe<&2, U.Held>, m, q, v), p)), U.taken(m, p), took_gv(Map.get(Maybe<&2, U.Held>, None{}, Map.set(&2, Maybe<&2, U.Held>, m, q, v), p)),
        Equal.trans(Maybe<&2, U.Held>, ML.gv(Maybe<&2, U.Held>, Map.get(Maybe<&2, U.Held>, None{}, Map.set(&2, Maybe<&2, U.Held>, m, q, v), p)), ML.gv(Maybe<&2, U.Held>, Map.get(Maybe<&2, U.Held>, None{}, m, p)), U.taken(m, p),
          ML.get_set_other(Maybe<&2, U.Held>, None{}, m, w, q, v, p, (%ML.eq_sym(q, p) : {_ == False{} : Bool} eb)),
          Equal.sym(Maybe<&2, U.Held>, U.taken(m, p), ML.gv(Maybe<&2, U.Held>, Map.get(Maybe<&2, U.Held>, None{}, m, p)), took_gv(Map.get(Maybe<&2, U.Held>, None{}, m, p)))))

def taken_set(+m: Map<&2, Maybe<&2, U.Held>>, +w: ML.Wf.top(Maybe<&2, U.Held>, m), +q: String, +v: Maybe<&2, U.Held>, +p: String) -> {U.taken(Map.set(&2, Maybe<&2, U.Held>, m, q, v), p) == Bool.pick(Maybe<&2, U.Held>, String.eq(q, p), v, U.taken(m, p)) : Maybe<&2, U.Held>}:
  taken_set.pick(String.eq(q, p), m, w, q, v, p, {==})

def found_last(fnd: List<&2, Folder.Found>, +dg: Map<&2, String>, +m: Map<&2, Maybe<&2, U.Held>>, +w: ML.Wf.top(Maybe<&2, U.Held>, m), +p: String) -> {U.taken(U.found.map(fnd, dg, m), p) == found.last(fnd, dg, p, U.taken(m, p)) : Maybe<&2, U.Held>}:
  match fnd:
    case Nil{}:
      {==}
    case Folder.Found.File{+q, +r, n} <> +rest:
      %taken_set(m, w, q, Some{U.Held.File{Main.status.folder_digest(dg, q), r}}, p) : {U.taken(U.found.map(rest, dg, Map.set(&2, Maybe<&2, U.Held>, m, q, Some{U.Held.File{Main.status.folder_digest(dg, q), r}})), p) == found.last(rest, dg, p, _) : Maybe<&2, U.Held>}
      found_last(rest, dg, Map.set(&2, Maybe<&2, U.Held>, m, q, Some{U.Held.File{Main.status.folder_digest(dg, q), r}}), ML.wf_set_map(Maybe<&2, U.Held>, m, w, q, Some{U.Held.File{Main.status.folder_digest(dg, q), r}}), p)
    case Folder.Found.Link{+q, +t} <> +rest:
      %taken_set(m, w, q, Some{U.Held.Link{t}}, p) : {U.taken(U.found.map(rest, dg, Map.set(&2, Maybe<&2, U.Held>, m, q, Some{U.Held.Link{t}})), p) == found.last(rest, dg, p, _) : Maybe<&2, U.Held>}
      found_last(rest, dg, Map.set(&2, Maybe<&2, U.Held>, m, q, Some{U.Held.Link{t}}), ML.wf_set_map(Maybe<&2, U.Held>, m, w, q, Some{U.Held.Link{t}}), p)

# What the walk took at a path, by what it holds there.
def held.from(fnd: List<&2, Folder.Found>, +dg: Map<&2, String>, +p: String, +h: U.Held) -> Bool:
  match fnd:
    case Nil{}:
      False{}
    case Folder.Found.File{+q, r, n} <> rest:
      Bool.or(Bool.and(String.eq(q, p), U.held.same(U.Held.File{Main.status.folder_digest(dg, q), r}, h)), held.from(rest, dg, p, h))
    case Folder.Found.Link{+q, t} <> rest:
      Bool.or(Bool.and(String.eq(q, p), U.held.same(U.Held.Link{t}, h)), held.from(rest, dg, p, h))

def maybe.is(m: Maybe<&2, U.Held>, +h: U.Held) -> Bool:
  match m:
    case Some{x}:
      U.held.same(x, h)
    case None{}:
      False{}

def last_pick(b: Bool, +vx: U.Held, +acc: Maybe<&2, U.Held>, +h: U.Held, +hf: Bool, ih: {Bool.or(hf, maybe.is(Bool.pick(Maybe<&2, U.Held>, b, Some{vx}, acc), h)) == True{} : Bool}) -> {Bool.or(Bool.or(Bool.and(b, U.held.same(vx, h)), hf), maybe.is(acc, h)) == True{} : Bool}:
  match b:
    case True{}:
      AL.or_cases({Bool.or(Bool.or(U.held.same(vx, h), hf), maybe.is(acc, h)) == True{} : Bool}, hf, U.held.same(vx, h), ih,
        l => AL.or_left(Bool.or(U.held.same(vx, h), hf), maybe.is(acc, h), AL.or_right(U.held.same(vx, h), hf, l)),
        r => AL.or_left(Bool.or(U.held.same(vx, h), hf), maybe.is(acc, h), AL.or_left(U.held.same(vx, h), hf, r)))
    case False{}:
      ih

# Whatever the map holds at a path came from something the walk took
# there, or was there before.
def last_from(fnd: List<&2, Folder.Found>, +dg: Map<&2, String>, +p: String, +acc: Maybe<&2, U.Held>, +h: U.Held, e: {maybe.is(found.last(fnd, dg, p, acc), h) == True{} : Bool}) -> {Bool.or(held.from(fnd, dg, p, h), maybe.is(acc, h)) == True{} : Bool}:
  match fnd:
    case Nil{}:
      e
    case Folder.Found.File{+q, +r, n} <> +rest:
      last_pick(String.eq(q, p), U.Held.File{Main.status.folder_digest(dg, q), r}, acc, h, held.from(rest, dg, p, h), last_from(rest, dg, p, Bool.pick(Maybe<&2, U.Held>, String.eq(q, p), Some{U.Held.File{Main.status.folder_digest(dg, q), r}}, acc), h, e))
    case Folder.Found.Link{+q, +t} <> +rest:
      last_pick(String.eq(q, p), U.Held.Link{t}, acc, h, held.from(rest, dg, p, h), last_from(rest, dg, p, Bool.pick(Maybe<&2, U.Held>, String.eq(q, p), Some{U.Held.Link{t}}, acc), h, e))

def or_nil(a: Bool, e: {Bool.or(a, False{}) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      e

# What the map `update` builds holds at a path is something the walk took
# there.
def taken_from(+fnd: List<&2, Folder.Found>, +dg: Map<&2, String>, +p: String, +h: U.Held, e: {U.taken(U.found.map(fnd, dg, Map.new(&2, Maybe<&2, U.Held>)), p) == Some{h} : Maybe<&2, U.Held>}) -> {held.from(fnd, dg, p, h) == True{} : Bool}:
  or_nil(held.from(fnd, dg, p, h),
    (%taken_new(p) : {Bool.or(held.from(fnd, dg, p, h), maybe.is(_, h)) == True{} : Bool}
      last_from(fnd, dg, p, U.taken(Map.new(&2, Maybe<&2, U.Held>), p), h,
        (%found_last(fnd, dg, Map.new(&2, Maybe<&2, U.Held>), ML.wf_new(Maybe<&2, U.Held>), p) : {maybe.is(_, h) == True{} : Bool}
          %Equal.sym(Maybe<&2, U.Held>, U.taken(U.found.map(fnd, dg, Map.new(&2, Maybe<&2, U.Held>)), p), Some{h}, e) : {maybe.is(_, h) == True{} : Bool}
          same_held(h)))))

# What some revision records at a path
# ------------------------------------

# A digest history is said to record at a path is one `cat` of some
# revision reads for a file some revision put there, or its tree names as
# that file's payload.
def entry_there(+fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +id: String, +x: String, m: Maybe<&2, Tree.Entry>, +y: String, h: {U.recorded.entry(fs, ds, Main.contents.go(List.reverse(&2, Main.Full, Main.presentation(fs)), ds, x, Nil{}), id, x, m) == Some{y} : Maybe<&2, String>}) -> {U.reads.as(fs, ds, id, x, m, y) == True{} : Bool}:
  match m:
    case None{}:
      Empty.absurd({U.reads.as(fs, ds, id, x, None{}, y) == True{} : Bool}, none_some(y, h))
    case Some{Tree.Entry{f, p, k, yy, g, mo}}:
      match k:
        case Tree.Lines{}:
          lines_rec(y, Main.content(fs, ds, id, x), h)
        case Tree.Whole{}:
          %Equal.sym(Maybe<&2, String>, yy, Some{y}, h) : {U.records.payload(y, _) == True{} : Bool}
          SL.eq_refl(y)
        case Tree.Link{}:
          Empty.absurd({U.reads.as(fs, ds, id, x, Some{Tree.Entry{f, p, Tree.Link{}, yy, g, mo}}, y) == True{} : Bool}, none_some(y, h))

def tree_there(+fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +id: String, +x: String, r: Result<&2, &2, Main.Refused, Tree.Tree()>, +y: String, h: {U.recorded.tree(fs, ds, Main.contents.go(List.reverse(&2, Main.Full, Main.presentation(fs)), ds, x, Nil{}), id, x, r) == Some{y} : Maybe<&2, String>}) -> {U.rev.reads.as(fs, ds, id, x, r, y) == True{} : Bool}:
  match r:
    case Done{+t2}:
      entry_there(fs, ds, id, x, Tree.lookup(t2, x), y, h)
    case Fail{e}:
      Empty.absurd({U.rev.reads.as(fs, ds, id, x, Fail{e}, y) == True{} : Bool}, none_some(y, h))

def push_there(mm: Maybe<&2, String>, +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +x: String, +f: Main.Full, +rest: List<&2, Main.Full>, +later: List<&2, String>, +em: {U.recorded.tree(fs, ds, Main.contents.go(List.reverse(&2, Main.Full, Main.presentation(fs)), ds, x, Nil{}), Main.id_of(f), x, Main.tree.r(fs, Main.id_of(f))) == mm : Maybe<&2, String>}, +d: String, h: {Rev.member(U.push(mm, later), d) == True{} : Bool}, ih: {Rev.member(later, d) == True{} : Bool} -> {U.revs.read.as(rest, fs, ds, x, d) == True{} : Bool}) -> {U.revs.read.as(f <> rest, fs, ds, x, d) == True{} : Bool}:
  match mm:
    case None{}:
      AL.or_right(U.rev.reads.as(fs, ds, Main.id_of(f), x, Main.tree.r(fs, Main.id_of(f)), d), U.revs.read.as(rest, fs, ds, x, d), ih(h))
    case Some{+v}:
      AL.or_cases({U.revs.read.as(f <> rest, fs, ds, x, d) == True{} : Bool}, String.eq(v, d), Rev.member(later, d), h,
        l => AL.or_left(U.rev.reads.as(fs, ds, Main.id_of(f), x, Main.tree.r(fs, Main.id_of(f)), d), U.revs.read.as(rest, fs, ds, x, d),
          (%SL.eq_true(v, d, l) : {U.rev.reads.as(fs, ds, Main.id_of(f), x, Main.tree.r(fs, Main.id_of(f)), _) == True{} : Bool}
            tree_there(fs, ds, Main.id_of(f), x, Main.tree.r(fs, Main.id_of(f)), v, em))),
        r => AL.or_right(U.rev.reads.as(fs, ds, Main.id_of(f), x, Main.tree.r(fs, Main.id_of(f)), d), U.revs.read.as(rest, fs, ds, x, d), ih(r)))

def revs_there.pick(b: Bool, +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +x: String, +f: Main.Full, +rest: List<&2, Main.Full>, +later: List<&2, String>, +d: String, h: {Rev.member(Bool.pick(List<&2, String>, b, U.push(U.recorded.tree(fs, ds, Main.contents.go(List.reverse(&2, Main.Full, Main.presentation(fs)), ds, x, Nil{}), Main.id_of(f), x, Main.tree.r(fs, Main.id_of(f))), later), later), d) == True{} : Bool}, ih: {Rev.member(later, d) == True{} : Bool} -> {U.revs.read.as(rest, fs, ds, x, d) == True{} : Bool}) -> {U.revs.read.as(f <> rest, fs, ds, x, d) == True{} : Bool}:
  match b:
    case True{}:
      push_there(U.recorded.tree(fs, ds, Main.contents.go(List.reverse(&2, Main.Full, Main.presentation(fs)), ds, x, Nil{}), Main.id_of(f), x, Main.tree.r(fs, Main.id_of(f))), fs, ds, x, f, rest, later, {==}, d, h, ih)
    case False{}:
      AL.or_right(U.rev.reads.as(fs, ds, Main.id_of(f), x, Main.tree.r(fs, Main.id_of(f)), d), U.revs.read.as(rest, fs, ds, x, d), ih(h))

def revs_there(rs: List<&2, Main.Full>, +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +x: String, +d: String, h: {Rev.member(U.recorded.revs(rs, fs, ds, Main.contents.go(List.reverse(&2, Main.Full, Main.presentation(fs)), ds, x, Nil{}), x), d) == True{} : Bool}) -> {U.revs.read.as(rs, fs, ds, x, d) == True{} : Bool}:
  match rs:
    case Nil{}:
      Empty.absurd({U.revs.read.as(Nil{}, fs, ds, x, d) == True{} : Bool}, Comp.false_true(h))
    case +f <> +rest:
      revs_there.pick(U.touches(x, f), fs, ds, x, f, rest, U.recorded.revs(rest, fs, ds, Main.contents.go(List.reverse(&2, Main.Full, Main.presentation(fs)), ds, x, Nil{}), x), d, h, h2 => revs_there(rest, fs, ds, x, d, h2))

def files_there(xs: List<&2, String>, +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +d: String, h: {Rev.member(U.recorded.files(xs, fs, List.reverse(&2, Main.Full, Main.presentation(fs)), ds), d) == True{} : Bool}) -> {U.files.read.as(xs, fs, ds, d) == True{} : Bool}:
  match xs:
    case Nil{}:
      Empty.absurd({U.files.read.as(Nil{}, fs, ds, d) == True{} : Bool}, Comp.false_true(h))
    case +x <> +rest:
      AL.or_cases({U.files.read.as(x <> rest, fs, ds, d) == True{} : Bool}, Rev.member(U.recorded.revs(fs, fs, ds, Main.contents.go(List.reverse(&2, Main.Full, Main.presentation(fs)), ds, x, Nil{}), x), d), Rev.member(U.recorded.files(rest, fs, List.reverse(&2, Main.Full, Main.presentation(fs)), ds), d),
        GL.append_mem(U.recorded.revs(fs, fs, ds, Main.contents.go(List.reverse(&2, Main.Full, Main.presentation(fs)), ds, x, Nil{}), x), U.recorded.files(rest, fs, List.reverse(&2, Main.Full, Main.presentation(fs)), ds), d, h),
        l => AL.or_left(U.revs.read.as(fs, fs, ds, x, d), U.files.read.as(rest, fs, ds, d), revs_there(fs, fs, ds, x, d, l)),
        r => AL.or_right(U.revs.read.as(fs, fs, ds, x, d), U.files.read.as(rest, fs, ds, d), files_there(rest, fs, ds, d, r)))

# A file named among others is one of them.
def read_mem(ys: List<&2, String>, +x: String, +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +d: String, hm: {Rev.member(ys, x) == True{} : Bool}, +hr: {U.revs.read.as(fs, fs, ds, x, d) == True{} : Bool}) -> {U.files.read.as(ys, fs, ds, d) == True{} : Bool}:
  match ys:
    case Nil{}:
      Empty.absurd({U.files.read.as(Nil{}, fs, ds, d) == True{} : Bool}, Comp.false_true(hm))
    case +y <> +rest:
      AL.or_cases({U.files.read.as(y <> rest, fs, ds, d) == True{} : Bool}, String.eq(y, x), Rev.member(rest, x), hm,
        l => AL.or_left(U.revs.read.as(fs, fs, ds, y, d), U.files.read.as(rest, fs, ds, d),
          (%Equal.sym(String, y, x, SL.eq_true(y, x, l)) : {U.revs.read.as(fs, fs, ds, _, d) == True{} : Bool}
            hr)),
        r => AL.or_right(U.revs.read.as(fs, fs, ds, y, d), U.files.read.as(rest, fs, ds, d), read_mem(rest, x, fs, ds, d, r, hr)))

def read_sub(zs: List<&2, String>, +ys: List<&2, String>, +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +d: String, +hall: {Main.all_held(ys, zs) == True{} : Bool}, h: {U.files.read.as(zs, fs, ds, d) == True{} : Bool}) -> {U.files.read.as(ys, fs, ds, d) == True{} : Bool}:
  match zs:
    case Nil{}:
      Empty.absurd({U.files.read.as(ys, fs, ds, d) == True{} : Bool}, Comp.false_true(h))
    case +z <> +rest:
      AL.or_cases({U.files.read.as(ys, fs, ds, d) == True{} : Bool}, U.revs.read.as(fs, fs, ds, z, d), U.files.read.as(rest, fs, ds, d), h,
        l => read_mem(ys, z, fs, ds, d, Comp.and_left(Rev.member(ys, z), Main.all_held(ys, rest), hall), l),
        r => read_sub(rest, ys, fs, ds, d, Comp.and_right(Rev.member(ys, z), Main.all_held(ys, rest), hall), r))

def there_rec(+fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +p: String, +d: String, h: {Rev.member(U.recorded(fs, List.reverse(&2, Main.Full, Main.presentation(fs)), ds, p), d) == True{} : Bool}) -> {U.recorded.there(fs, ds, p, d) == True{} : Bool}:
  read_sub(Main.sorted_distinct(U.files_at(fs, p)), U.files_at(fs, p), fs, ds, d, RewriteL.dist_held(U.files_at(fs, p)), files_there(Main.sorted_distinct(U.files_at(fs, p)), fs, ds, d, h))

def in_there.pick(b: Bool, +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +q: String, +rest: List<&2, String>, +p: String, +d: String, +eb: {String.eq(q, p) == b : Bool}, h: {Rev.member(Bool.pick(List<&2, String>, b, U.recorded(fs, List.reverse(&2, Main.Full, Main.presentation(fs)), ds, q), U.recorded.in(U.recorded.list(rest, fs, List.reverse(&2, Main.Full, Main.presentation(fs)), ds), p)), d) == True{} : Bool}, ih: {Rev.member(U.recorded.in(U.recorded.list(rest, fs, List.reverse(&2, Main.Full, Main.presentation(fs)), ds), p), d) == True{} : Bool} -> {U.recorded.there(fs, ds, p, d) == True{} : Bool}) -> {U.recorded.there(fs, ds, p, d) == True{} : Bool}:
  match b:
    case True{}:
      %SL.eq_true(q, p, eb) : {U.recorded.there(fs, ds, _, d) == True{} : Bool}
      there_rec(fs, ds, q, d, h)
    case False{}:
      ih(h)

# Every digest the plan is told history records at a path, some revision
# records for a file history put there.
def in_there(qs: List<&2, String>, +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +p: String, +d: String, h: {Rev.member(U.recorded.in(U.recorded.list(qs, fs, List.reverse(&2, Main.Full, Main.presentation(fs)), ds), p), d) == True{} : Bool}) -> {U.recorded.there(fs, ds, p, d) == True{} : Bool}:
  match qs:
    case Nil{}:
      Empty.absurd({U.recorded.there(fs, ds, p, d) == True{} : Bool}, Comp.false_true(h))
    case +q <> +rest:
      in_there.pick(String.eq(q, p), fs, ds, q, rest, p, d, {==}, h, h2 => in_there(rest, fs, ds, p, d, h2))


# What `update` removes, the walk found, and history records there
# ----------------------------------------------------------------

def and_nil(a: Bool, e: {Bool.and(a, False{}) == True{} : Bool}) -> Empty:
  match a:
    case True{}:
      Comp.false_true(e)
    case False{}:
      Comp.false_true(e)

# A file the walk took at the path, with bytes history records there.
def from_file.hit(+fs: List<&2, Main.Full>, +dss: List<&2, Store.Doc>, +dg: Map<&2, String>, +p: String, +q: String, +r: Bool, +d: String, +r0: Bool, +l: {Bool.and(String.eq(q, p), Bool.and(String.eq(Main.status.folder_digest(dg, q), d), Bool.not(Bool.xor(r, r0)))) == True{} : Bool}, +hr: {U.recorded.there(fs, dss, p, d) == True{} : Bool}) -> {Bool.and(String.eq(q, p), U.recorded.there(fs, dss, p, Main.status.folder_digest(dg, p))) == True{} : Bool}:
  AL.and_intro(String.eq(q, p), U.recorded.there(fs, dss, p, Main.status.folder_digest(dg, p)),
    Comp.and_left(String.eq(q, p), Bool.and(String.eq(Main.status.folder_digest(dg, q), d), Bool.not(Bool.xor(r, r0))), l),
    (%SL.eq_true(q, p, Comp.and_left(String.eq(q, p), Bool.and(String.eq(Main.status.folder_digest(dg, q), d), Bool.not(Bool.xor(r, r0))), l)) : {U.recorded.there(fs, dss, p, Main.status.folder_digest(dg, _)) == True{} : Bool}
      %Equal.sym(String, Main.status.folder_digest(dg, q), d, SL.eq_true(Main.status.folder_digest(dg, q), d, Comp.and_left(String.eq(Main.status.folder_digest(dg, q), d), Bool.not(Bool.xor(r, r0)), Comp.and_right(String.eq(q, p), Bool.and(String.eq(Main.status.folder_digest(dg, q), d), Bool.not(Bool.xor(r, r0))), l)))) : {U.recorded.there(fs, dss, p, _) == True{} : Bool}
      hr))

def from_file(fnd: List<&2, Folder.Found>, +fs: List<&2, Main.Full>, +dss: List<&2, Store.Doc>, +dg: Map<&2, String>, +p: String, +d: String, +r0: Bool, hf: {held.from(fnd, dg, p, U.Held.File{d, r0}) == True{} : Bool}, +hr: {U.recorded.there(fs, dss, p, d) == True{} : Bool}) -> {U.found.recorded(fnd, fs, dss, dg, p) == True{} : Bool}:
  match fnd:
    case Nil{}:
      Empty.absurd({U.found.recorded(Nil{}, fs, dss, dg, p) == True{} : Bool}, Comp.false_true(hf))
    case Folder.Found.File{+q, +r, n} <> +rest:
      AL.or_cases({Bool.or(Bool.and(String.eq(q, p), U.recorded.there(fs, dss, p, Main.status.folder_digest(dg, p))), U.found.recorded(rest, fs, dss, dg, p)) == True{} : Bool}, Bool.and(String.eq(q, p), Bool.and(String.eq(Main.status.folder_digest(dg, q), d), Bool.not(Bool.xor(r, r0)))), held.from(rest, dg, p, U.Held.File{d, r0}), hf,
        l => AL.or_left(Bool.and(String.eq(q, p), U.recorded.there(fs, dss, p, Main.status.folder_digest(dg, p))), U.found.recorded(rest, fs, dss, dg, p), from_file.hit(fs, dss, dg, p, q, r, d, r0, l, hr)),
        rr => AL.or_right(Bool.and(String.eq(q, p), U.recorded.there(fs, dss, p, Main.status.folder_digest(dg, p))), U.found.recorded(rest, fs, dss, dg, p), from_file(rest, fs, dss, dg, p, d, r0, rr, hr)))
    case Folder.Found.Link{+q, t} <> +rest:
      AL.or_cases({Bool.or(String.eq(q, p), U.found.recorded(rest, fs, dss, dg, p)) == True{} : Bool}, Bool.and(String.eq(q, p), False{}), held.from(rest, dg, p, U.Held.File{d, r0}), hf,
        l => Empty.absurd({Bool.or(String.eq(q, p), U.found.recorded(rest, fs, dss, dg, p)) == True{} : Bool}, and_nil(String.eq(q, p), l)),
        rr => AL.or_right(String.eq(q, p), U.found.recorded(rest, fs, dss, dg, p), from_file(rest, fs, dss, dg, p, d, r0, rr, hr)))

# A link the walk took at the path.
def from_link(fnd: List<&2, Folder.Found>, +fs: List<&2, Main.Full>, +dss: List<&2, Store.Doc>, +dg: Map<&2, String>, +p: String, +s: String, hf: {held.from(fnd, dg, p, U.Held.Link{s}) == True{} : Bool}) -> {U.found.recorded(fnd, fs, dss, dg, p) == True{} : Bool}:
  match fnd:
    case Nil{}:
      Empty.absurd({U.found.recorded(Nil{}, fs, dss, dg, p) == True{} : Bool}, Comp.false_true(hf))
    case Folder.Found.File{+q, r, n} <> +rest:
      AL.or_cases({Bool.or(Bool.and(String.eq(q, p), U.recorded.there(fs, dss, p, Main.status.folder_digest(dg, p))), U.found.recorded(rest, fs, dss, dg, p)) == True{} : Bool}, Bool.and(String.eq(q, p), False{}), held.from(rest, dg, p, U.Held.Link{s}), hf,
        l => Empty.absurd({Bool.or(Bool.and(String.eq(q, p), U.recorded.there(fs, dss, p, Main.status.folder_digest(dg, p))), U.found.recorded(rest, fs, dss, dg, p)) == True{} : Bool}, and_nil(String.eq(q, p), l)),
        rr => AL.or_right(Bool.and(String.eq(q, p), U.recorded.there(fs, dss, p, Main.status.folder_digest(dg, p))), U.found.recorded(rest, fs, dss, dg, p), from_link(rest, fs, dss, dg, p, s, rr)))
    case Folder.Found.Link{+q, +t} <> +rest:
      AL.or_cases({Bool.or(String.eq(q, p), U.found.recorded(rest, fs, dss, dg, p)) == True{} : Bool}, Bool.and(String.eq(q, p), String.eq(t, s)), held.from(rest, dg, p, U.Held.Link{s}), hf,
        l => AL.or_left(String.eq(q, p), U.found.recorded(rest, fs, dss, dg, p), Comp.and_left(String.eq(q, p), String.eq(t, s), l)),
        rr => AL.or_right(String.eq(q, p), U.found.recorded(rest, fs, dss, dg, p), from_link(rest, fs, dss, dg, p, s, rr)))

def rm_of(b: Bool, tr: Bool, hr: {U.leaving.remove(U.leaving.of(b, tr)) == True{} : Bool}) -> {b == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      match tr:
        case True{}:
          Empty.absurd({False{} == True{} : Bool}, Comp.false_true(hr))
        case False{}:
          Empty.absurd({False{} == True{} : Bool}, Comp.false_true(hr))

# A path `update` removes something from is one the tree does not hold,
# where the walk found a file history records there, or a link.
def removed_ok(mh: Maybe<&2, U.Held>, +p: String, +fs: List<&2, Main.Full>, +dss: List<&2, Store.Doc>, +t: Tree.Tree(), +fnd: List<&2, Folder.Found>, +dg: Map<&2, String>, +hm: Map<&2, Maybe<&2, U.Held>>, +recs: List<&2, String>, +sp: List<&2, String>, tr: Bool, +em: {U.taken(hm, p) == mh : Maybe<&2, U.Held>}, +hout: {Bool.not(U.tree.has(t, p)) == True{} : Bool}, hfrom: @h: U.Held -> {U.taken(hm, p) == Some{h} : Maybe<&2, U.Held>} -> {held.from(fnd, dg, p, h) == True{} : Bool}, hrec: @d: String -> {Rev.member(recs, d) == True{} : Bool} -> {U.recorded.there(fs, dss, p, d) == True{} : Bool}, hr: {U.leaving.remove(U.leaving(U.gone.held(mh), U.gone.recorded(U.gone.held(mh), recs, sp), tr)) == True{} : Bool}) -> {U.reaches(fs, dss, t, fnd, dg, U.Effect.Remove{p}) == True{} : Bool}:
  match mh:
    case None{}:
      Empty.absurd({U.reaches(fs, dss, t, fnd, dg, U.Effect.Remove{p}) == True{} : Bool}, Comp.false_true(hr))
    case Some{x}:
      match x:
        case U.Held.File{+d, +r}:
          AL.and_intro(Bool.not(U.tree.has(t, p)), U.found.recorded(fnd, fs, dss, dg, p), hout,
            from_file(fnd, fs, dss, dg, p, d, r, hfrom(U.Held.File{d, r}, em), hrec(d, rm_of(Rev.member(recs, d), tr, hr))))
        case U.Held.Link{+s}:
          AL.and_intro(Bool.not(U.tree.has(t, p)), U.found.recorded(fnd, fs, dss, dg, p), hout,
            from_link(fnd, fs, dss, dg, p, s, hfrom(U.Held.Link{s}, em)))
        case U.Held.Dir{}:
          Empty.absurd({U.reaches(fs, dss, t, fnd, dg, U.Effect.Remove{p}) == True{} : Bool}, Comp.false_true(hr))
        case U.Held.Unread{}:
          Empty.absurd({U.reaches(fs, dss, t, fnd, dg, U.Effect.Remove{p}) == True{} : Bool}, Comp.false_true(hr))
        case U.Held.Other{}:
          Empty.absurd({U.reaches(fs, dss, t, fnd, dg, U.Effect.Remove{p}) == True{} : Bool}, Comp.false_true(hr))
        case U.Held.Nothing{}:
          Empty.absurd({U.reaches(fs, dss, t, fnd, dg, U.Effect.Remove{p}) == True{} : Bool}, Comp.false_true(hr))

def keep_rm(b: Bool, +p: String, +rest: List<&2, String>, +fs: List<&2, Main.Full>, +dss: List<&2, Store.Doc>, +t: Tree.Tree(), +fnd: List<&2, Folder.Found>, +dg: Map<&2, String>, hr: {b == True{} : Bool} -> {U.reaches(fs, dss, t, fnd, dg, U.Effect.Remove{p}) == True{} : Bool}, +ih: {U.confined(fs, dss, t, fnd, dg, U.effects.removes(rest)) == True{} : Bool}) -> {U.confined(fs, dss, t, fnd, dg, U.effects.removes(Rev.keep(b, p, rest))) == True{} : Bool}:
  match b:
    case True{}:
      AL.and_intro(U.reaches(fs, dss, t, fnd, dg, U.Effect.Remove{p}), U.confined(fs, dss, t, fnd, dg, U.effects.removes(rest)), hr({==}), ih)
    case False{}:
      ih

def removes_ok(gp: List<&2, String>, +fs: List<&2, Main.Full>, +dss: List<&2, Store.Doc>, +t: Tree.Tree(), +fnd: List<&2, Folder.Found>, +dg: Map<&2, String>, +qs: List<&2, String>, +lk: Map<&2, List<&2, String>>, +tr: Set(), +hout: {gone.out(t, gp) == True{} : Bool}) -> {U.confined(fs, dss, t, fnd, dg, U.effects.removes(U.removes(U.went(U.gones(gp, U.found.map(fnd, dg, Map.new(&2, Maybe<&2, U.Held>)), U.recorded.list(qs, fs, List.reverse(&2, Main.Full, Main.presentation(fs)), dss), lk, tr))))) == True{} : Bool}:
  match gp:
    case Nil{}:
      {==}
    case +p <> +rest:
      keep_rm(U.leaving.remove(U.leaving(U.gone.held(U.taken(U.found.map(fnd, dg, Map.new(&2, Maybe<&2, U.Held>)), p)), U.gone.recorded(U.gone.held(U.taken(U.found.map(fnd, dg, Map.new(&2, Maybe<&2, U.Held>)), p)), U.recorded.in(U.recorded.list(qs, fs, List.reverse(&2, Main.Full, Main.presentation(fs)), dss), p), U.recorded.of(lk, p)), U.has(Set.has(tr, p)))), p, U.removes(U.went(U.gones(rest, U.found.map(fnd, dg, Map.new(&2, Maybe<&2, U.Held>)), U.recorded.list(qs, fs, List.reverse(&2, Main.Full, Main.presentation(fs)), dss), lk, tr))), fs, dss, t, fnd, dg,
        hb => removed_ok(U.taken(U.found.map(fnd, dg, Map.new(&2, Maybe<&2, U.Held>)), p), p, fs, dss, t, fnd, dg, U.found.map(fnd, dg, Map.new(&2, Maybe<&2, U.Held>)), U.recorded.in(U.recorded.list(qs, fs, List.reverse(&2, Main.Full, Main.presentation(fs)), dss), p), U.recorded.of(lk, p), U.has(Set.has(tr, p)), {==}, Comp.and_left(Bool.not(U.tree.has(t, p)), gone.out(t, rest), hout), h => e => taken_from(fnd, dg, p, h, e), d => m => in_there(qs, fs, dss, p, d, m), hb),
        removes_ok(rest, fs, dss, t, fnd, dg, qs, lk, tr, Comp.and_right(Bool.not(U.tree.has(t, p)), gone.out(t, rest), hout)))

# Where `update` plans at all, everything it does to the folder is at a
# path the target's tree holds, save removals, each at a path the tree
# does not hold where the walk found a file history records there, or a
# link.
def plan_confined(+fs: List<&2, Main.Full>, +id: String, +t: Tree.Tree(), +rs: List<&2, Folder.Scope>, +walked: List<&2, T.Split>, +found: List<&2, Folder.Found>, +dg: Map<&2, String>, +ls: Map<&2, String>, +located: Map<&2, String>, +ds: List<&2, Store.Doc>, +more: List<&2, Store.Doc>, -p: U.Plan, +e: {U.plan.from(fs, id, t, rs, walked, found, dg, ls, located, ds, more) == Done{p} : Result<&2, &2, List<&2, T.Split>, U.Plan>}) -> {U.confined(fs, List.append(&2, Store.Doc, ds, more), t, found, dg, U.effects(p)) == True{} : Bool}:
  %plan_from(fs, id, t, rs, walked, found, dg, ls, located, ds, more, p, e) : {U.confined(fs, List.append(&2, Store.Doc, ds, more), t, found, dg, U.effects(_)) == True{} : Bool}
  confined_app(fs, List.append(&2, Store.Doc, ds, more), t, found, dg, U.effects.removes(U.removes(U.went(plan.gones(fs, id, t, found, dg, ls, located, ds, more)))), List.append(&2, U.Effect, U.effects.writes(U.writes(U.decided(plan.looks(fs, id, t, found, dg, ls, located, ds, more)))), List.append(&2, U.Effect, U.effects.links(U.links(U.decided(plan.looks(fs, id, t, found, dg, ls, located, ds, more)))), List.append(&2, U.Effect, U.effects.modes(U.modes(U.decided(plan.looks(fs, id, t, found, dg, ls, located, ds, more)))), Nil{}))),
    removes_ok(U.gone.paths(found, Set.from_list(T.map(~U.Placing, ~String, ~(q => U.placing.path(q)), U.placings(t)))), fs, List.append(&2, Store.Doc, ds, more), t, found, dg, List.append(&2, String, U.asks(U.pres(fs, List.reverse(&2, Main.Full, Main.presentation(fs)), ds, located, id, t, U.found.map(found, dg, Map.new(&2, Maybe<&2, U.Held>)), ls, U.single(U.placings(t)))), U.gone.paths(found, Set.from_list(T.map(~U.Placing, ~String, ~(q => U.placing.path(q)), U.placings(t))))), U.spelled.map(U.gone.links(U.gone.paths(found, Set.from_list(T.map(~U.Placing, ~String, ~(q => U.placing.path(q)), U.placings(t)))), U.found.map(found, dg, Map.new(&2, Maybe<&2, U.Held>))), fs, Map.new(&2, List<&2, String>)), Set.from_list(U.tracked(fs, U.heads.sorted(fs))), gone_out(found, t)),
    confined_app(fs, List.append(&2, Store.Doc, ds, more), t, found, dg, U.effects.writes(U.writes(U.decided(plan.looks(fs, id, t, found, dg, ls, located, ds, more)))), List.append(&2, U.Effect, U.effects.links(U.links(U.decided(plan.looks(fs, id, t, found, dg, ls, located, ds, more)))), List.append(&2, U.Effect, U.effects.modes(U.modes(U.decided(plan.looks(fs, id, t, found, dg, ls, located, ds, more)))), Nil{})),
      writes_conf(fs, List.append(&2, Store.Doc, ds, more), t, found, dg, U.writes(U.decided(plan.looks(fs, id, t, found, dg, ls, located, ds, more))), stepping_at(~(s => U.step.write(s)), t, U.decided(plan.looks(fs, id, t, found, dg, ls, located, ds, more)), pres_at(t, fs, List.reverse(&2, Main.Full, Main.presentation(fs)), ds, located, id, t, U.found.map(found, dg, Map.new(&2, Maybe<&2, U.Held>)), ls, U.single(U.placings(t)), U.recorded.list(List.append(&2, String, U.asks(U.pres(fs, List.reverse(&2, Main.Full, Main.presentation(fs)), ds, located, id, t, U.found.map(found, dg, Map.new(&2, Maybe<&2, U.Held>)), ls, U.single(U.placings(t)))), U.gone.paths(found, Set.from_list(T.map(~U.Placing, ~String, ~(q => U.placing.path(q)), U.placings(t))))), fs, List.reverse(&2, Main.Full, Main.presentation(fs)), List.append(&2, Store.Doc, ds, more)), single_all(t)))),
      confined_app(fs, List.append(&2, Store.Doc, ds, more), t, found, dg, U.effects.links(U.links(U.decided(plan.looks(fs, id, t, found, dg, ls, located, ds, more)))), List.append(&2, U.Effect, U.effects.modes(U.modes(U.decided(plan.looks(fs, id, t, found, dg, ls, located, ds, more)))), Nil{}),
        links_conf(fs, List.append(&2, Store.Doc, ds, more), t, found, dg, U.links(U.decided(plan.looks(fs, id, t, found, dg, ls, located, ds, more))), stepping_at(~(s => U.step.link(s)), t, U.decided(plan.looks(fs, id, t, found, dg, ls, located, ds, more)), pres_at(t, fs, List.reverse(&2, Main.Full, Main.presentation(fs)), ds, located, id, t, U.found.map(found, dg, Map.new(&2, Maybe<&2, U.Held>)), ls, U.single(U.placings(t)), U.recorded.list(List.append(&2, String, U.asks(U.pres(fs, List.reverse(&2, Main.Full, Main.presentation(fs)), ds, located, id, t, U.found.map(found, dg, Map.new(&2, Maybe<&2, U.Held>)), ls, U.single(U.placings(t)))), U.gone.paths(found, Set.from_list(T.map(~U.Placing, ~String, ~(q => U.placing.path(q)), U.placings(t))))), fs, List.reverse(&2, Main.Full, Main.presentation(fs)), List.append(&2, Store.Doc, ds, more)), single_all(t)))),
        confined_app(fs, List.append(&2, Store.Doc, ds, more), t, found, dg, U.effects.modes(U.modes(U.decided(plan.looks(fs, id, t, found, dg, ls, located, ds, more)))), Nil{},
          modes_conf(fs, List.append(&2, Store.Doc, ds, more), t, found, dg, U.modes(U.decided(plan.looks(fs, id, t, found, dg, ls, located, ds, more))), stepping_at(~(s => U.step.mode(s)), t, U.decided(plan.looks(fs, id, t, found, dg, ls, located, ds, more)), pres_at(t, fs, List.reverse(&2, Main.Full, Main.presentation(fs)), ds, located, id, t, U.found.map(found, dg, Map.new(&2, Maybe<&2, U.Held>)), ls, U.single(U.placings(t)), U.recorded.list(List.append(&2, String, U.asks(U.pres(fs, List.reverse(&2, Main.Full, Main.presentation(fs)), ds, located, id, t, U.found.map(found, dg, Map.new(&2, Maybe<&2, U.Held>)), ls, U.single(U.placings(t)))), U.gone.paths(found, Set.from_list(T.map(~U.Placing, ~String, ~(q => U.placing.path(q)), U.placings(t))))), fs, List.reverse(&2, Main.Full, Main.presentation(fs)), List.append(&2, Store.Doc, ds, more)), single_all(t)))),
          {==}))))

# Settled, it says what its dry run says
# --------------------------------------

def empty_nil(-A: Data, xs: List<&2, A>, e: {List.is_empty(&2, A, xs) == True{} : Bool}) -> {xs == Nil{} : List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case x <> rest:
      Empty.absurd({x <> rest == Nil{} : List<&2, A>}, Comp.false_true(e))

# Where there is nothing to do, `update` says what `update --dry-run` says.
def settled_says(p: U.Plan, +s: String, +e: {U.settled(p) == True{} : Bool}) -> {U.said.settled(s, p) == U.said.dry(s, p) : List<&2, String>}:
  match p:
    case U.Plan{+ds, +ws}:
      %Equal.sym(Bool, U.settled(U.Plan{ds, ws}), True{}, e) : {U.said.settled(s, U.Plan{ds, ws}) == List.concat(&2, String, [U.said.paths("write", T.map(~U.Decided, ~String, ~(d => U.decided.path(d)), U.writes(ds))), U.said.paths("remove", U.removes(ws)), U.said.modes("mode", U.modes(ds)), U.said.links("link", U.links(ds)), U.said.leaves(U.leaves(ws)), Bool.pick(List<&2, String>, _, ["the folder already holds " ++ s], Nil{})]) : List<&2, String>}
      %Equal.sym(List<&2, U.Decided>, U.writes(ds), Nil{}, empty_nil(U.Decided, U.writes(ds), Comp.and_left(List.is_empty(&2, U.Decided, U.writes(ds)), List.is_empty(&2, String, U.removes(ws)), Comp.and_left(Bool.and(List.is_empty(&2, U.Decided, U.writes(ds)), List.is_empty(&2, String, U.removes(ws))), Bool.and(List.is_empty(&2, U.Decided, U.modes(ds)), List.is_empty(&2, U.Decided, U.links(ds))), e)))) : {U.said.settled(s, U.Plan{ds, ws}) == List.concat(&2, String, [U.said.paths("write", T.map(~U.Decided, ~String, ~(d => U.decided.path(d)), _)), U.said.paths("remove", U.removes(ws)), U.said.modes("mode", U.modes(ds)), U.said.links("link", U.links(ds)), U.said.leaves(U.leaves(ws)), ["the folder already holds " ++ s]]) : List<&2, String>}
      %Equal.sym(List<&2, String>, U.removes(ws), Nil{}, empty_nil(String, U.removes(ws), Comp.and_right(List.is_empty(&2, U.Decided, U.writes(ds)), List.is_empty(&2, String, U.removes(ws)), Comp.and_left(Bool.and(List.is_empty(&2, U.Decided, U.writes(ds)), List.is_empty(&2, String, U.removes(ws))), Bool.and(List.is_empty(&2, U.Decided, U.modes(ds)), List.is_empty(&2, U.Decided, U.links(ds))), e)))) : {U.said.settled(s, U.Plan{ds, ws}) == List.concat(&2, String, [Nil{}, U.said.paths("remove", _), U.said.modes("mode", U.modes(ds)), U.said.links("link", U.links(ds)), U.said.leaves(U.leaves(ws)), ["the folder already holds " ++ s]]) : List<&2, String>}
      %Equal.sym(List<&2, U.Decided>, U.modes(ds), Nil{}, empty_nil(U.Decided, U.modes(ds), Comp.and_left(List.is_empty(&2, U.Decided, U.modes(ds)), List.is_empty(&2, U.Decided, U.links(ds)), Comp.and_right(Bool.and(List.is_empty(&2, U.Decided, U.writes(ds)), List.is_empty(&2, String, U.removes(ws))), Bool.and(List.is_empty(&2, U.Decided, U.modes(ds)), List.is_empty(&2, U.Decided, U.links(ds))), e)))) : {U.said.settled(s, U.Plan{ds, ws}) == List.concat(&2, String, [Nil{}, Nil{}, U.said.modes("mode", _), U.said.links("link", U.links(ds)), U.said.leaves(U.leaves(ws)), ["the folder already holds " ++ s]]) : List<&2, String>}
      %Equal.sym(List<&2, U.Decided>, U.links(ds), Nil{}, empty_nil(U.Decided, U.links(ds), Comp.and_right(List.is_empty(&2, U.Decided, U.modes(ds)), List.is_empty(&2, U.Decided, U.links(ds)), Comp.and_right(Bool.and(List.is_empty(&2, U.Decided, U.writes(ds)), List.is_empty(&2, String, U.removes(ws))), Bool.and(List.is_empty(&2, U.Decided, U.modes(ds)), List.is_empty(&2, U.Decided, U.links(ds))), e)))) : {U.said.settled(s, U.Plan{ds, ws}) == List.concat(&2, String, [Nil{}, Nil{}, Nil{}, U.said.links("link", _), U.said.leaves(U.leaves(ws)), ["the folder already holds " ++ s]]) : List<&2, String>}
      {==}

# The folder is only ever given a head
# ------------------------------------

def mem_keyed.pick(b: Bool, +x: String, +rest: List<&2, String>, +d: String, h: {Bool.or(b, Rev.member(rest, d)) == True{} : Bool}, ih: {Rev.member(rest, d) == True{} : Bool} -> {List.is_empty(&2, String, SortL.keyed(~String, ~(s => s), d, rest)) == False{} : Bool}) -> {List.is_empty(&2, String, Bool.pick(List<&2, String>, b, x <> SortL.keyed(~String, ~(s => s), d, rest), SortL.keyed(~String, ~(s => s), d, rest))) == False{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      ih(h)

# A string a list holds is one its items under that string hold.
def mem_keyed(ys: List<&2, String>, +d: String, h: {Rev.member(ys, d) == True{} : Bool}) -> {List.is_empty(&2, String, SortL.keyed(~String, ~(s => s), d, ys)) == False{} : Bool}:
  match ys:
    case Nil{}:
      Empty.absurd({List.is_empty(&2, String, Nil{}) == False{} : Bool}, Comp.false_true(h))
    case +y <> +rest:
      mem_keyed.pick(String.eq(y, d), y, rest, d, h, t => mem_keyed(rest, d, t))

# What a sorted list holds, the list held.
def sort_back(+xs: List<&2, String>, +d: String, m: {Rev.member(List.sort(~String, ~(a => b => String.is_le(a, b)), xs), d) == True{} : Bool}) -> {Rev.member(xs, d) == True{} : Bool}:
  FetchL.keyed_mem(xs, d,
    (%SortL.sort_keyed(~String, ~(s => s), xs, d) : {List.is_empty(&2, String, _) == False{} : Bool}
      mem_keyed(List.sort(~String, ~(a => b => String.is_le(a, b)), xs), d, m)))

def sorted_all(ys: List<&2, String>, +xs: List<&2, String>, +h: {Main.all_held(xs, ys) == True{} : Bool}) -> {Main.all_held(List.sort(~String, ~(a => b => String.is_le(a, b)), xs), ys) == True{} : Bool}:
  match ys:
    case Nil{}:
      {==}
    case +y <> +rest:
      AL.and_intro(Rev.member(List.sort(~String, ~(a => b => String.is_le(a, b)), xs), y), Main.all_held(List.sort(~String, ~(a => b => String.is_le(a, b)), xs), rest),
        FetchL.sort_mem(xs, y, Comp.and_left(Rev.member(xs, y), Main.all_held(xs, rest), h)),
        sorted_all(rest, xs, Comp.and_right(Rev.member(xs, y), Main.all_held(xs, rest), h)))

def head_of.pick(b: Bool, +fs: List<&2, Main.Full>, +bs: List<&2, Bm.Bookmark>, +id: String, -u: Unit, e: {Bool.pick(Result<&2, &2, Main.Refused, Unit>, b, Done{Unit{}}, Fail{Main.Refused{1, U.spelled.id(fs, bs, id) ++ " is not a head, and the folder only ever holds one; reading the past is `show` and `cat`, and going back is `abandon`. the heads:" ++ Main.described(fs, bs, U.heads.sorted(fs))}}) == Done{u} : Result<&2, &2, Main.Refused, Unit>}) -> {b == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, fail_done(Main.Refused, Unit, Main.Refused{1, U.spelled.id(fs, bs, id) ++ " is not a head, and the folder only ever holds one; reading the past is `show` and `cat`, and going back is `abandon`. the heads:" ++ Main.described(fs, bs, U.heads.sorted(fs))}, u, e))

# Told nothing, `update` takes the store's one head, and there is no other.
def none_only(hs: List<&2, String>, +fs: List<&2, Main.Full>, +bs: List<&2, Bm.Bookmark>, -id: String, +ehs: {U.heads.sorted(fs) == hs : List<&2, String>}, e: {U.target.none(fs, bs, hs) == Done{id} : Result<&2, &2, Main.Refused, String>}) -> {Main.all_held([id], Main.current_heads(Main.history(fs))) == True{} : Bool}:
  match hs:
    case Nil{}:
      Empty.absurd({Main.all_held([id], Main.current_heads(Main.history(fs))) == True{} : Bool}, fail_done(Main.Refused, String, Main.Refused{1, "nothing is recorded here yet"}, id, e))
    case +only <> more:
      match more:
        case Nil{}:
          %done_eq(Main.Refused, String, only, id, e) : {Main.all_held([_], Main.current_heads(Main.history(fs))) == True{} : Bool}
          %ehs : {Main.all_held(_, Main.current_heads(Main.history(fs))) == True{} : Bool}
          sorted_all(Main.current_heads(Main.history(fs)), Main.current_heads(Main.history(fs)), RewriteL.held_refl(Main.current_heads(Main.history(fs))))
        case +x <> +rest:
          Empty.absurd({Main.all_held([id], Main.current_heads(Main.history(fs))) == True{} : Bool}, fail_done(Main.Refused, String, Main.Refused{1, "this store has " ++ Nat.show(List.length(&2, String, only <> x <> rest)) ++ " heads, so nothing here is `the` latest; name the one the folder should hold:" ++ Main.described(fs, bs, only <> x <> rest)}, id, e))

def only_when(t: Maybe<&2, String>, +fs: List<&2, Main.Full>, +bs: List<&2, Bm.Bookmark>, -id: String, e: {U.target.r(fs, bs, t) == Done{id} : Result<&2, &2, Main.Refused, String>}) -> {Bool.or(Maybe.is_some(&2, String, t), Main.all_held([id], Main.current_heads(Main.history(fs)))) == True{} : Bool}:
  match t:
    case None{}:
      none_only(U.heads.sorted(fs), fs, bs, id, {==}, e)
    case Some{s}:
      {==}

# Whatever `update` is told, the revision it lays out is a current head of
# the store; told nothing, it is the store's only head.
def only_heads(+fs: List<&2, Main.Full>, +bs: List<&2, Bm.Bookmark>, +t: Maybe<&2, String>, +id: String, -u: Unit, e1: {U.target.r(fs, bs, t) == Done{id} : Result<&2, &2, Main.Refused, String>}, e2: {U.head.r(fs, bs, id) == Done{u} : Result<&2, &2, Main.Refused, Unit>}) -> {Bool.and(Rev.member(Main.current_heads(Main.history(fs)), id), Bool.or(Maybe.is_some(&2, String, t), Main.all_held([id], Main.current_heads(Main.history(fs))))) == True{} : Bool}:
  AL.and_intro(Rev.member(Main.current_heads(Main.history(fs)), id), Bool.or(Maybe.is_some(&2, String, t), Main.all_held([id], Main.current_heads(Main.history(fs)))),
    sort_back(Main.current_heads(Main.history(fs)), id, head_of.pick(Rev.member(U.heads.sorted(fs), id), fs, bs, id, u, e2)),
    only_when(t, fs, bs, id, e1))
