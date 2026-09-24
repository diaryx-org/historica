# A bookmark file reads back as the bookmark it was written for. The Rust
# tool writes the target line — `change`, `revision` or `file` and the
# identifier — and `private` below it where the name stays out of an export;
# `Bm.parse` reads exactly that bookmark back from those bytes, wherever the
# identifier is spelled as its kind is.
import Base
import ./bookmark.bend as Bm
import ./text.bend as T
import ./ident.bend as Id
import ./string_lemmas.bend as S
import ./composition_lemmas.bend as Comp
import ./anchor_lemmas.bend as AL

# Characters
# ----------

def chr_eq(c: Char, d: Char, e: {Char.is_eq(c, d) == True{} : Bool}) -> {c == d : Char}:
  match c d:
    case Chr{U32{+a}} Chr{U32{+b}}:
      Equal.cong(Word(32n), Char, w => Chr{U32{w}}, a, b, S.word_eq(32n, a, b, S.is_eq_true(Word.cmp(32n, a, b), e)))

# A string with no newline in it.
def nonl(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{c, t}:
      Bool.and(Bool.not(Char.is_eq(c, '\n')), nonl(t))

def letter_nl.at(+c: Char, b: Bool, eb: {Char.is_eq(c, '\n') == b : Bool}, h: {Id.is_letter(c) == True{} : Bool}) -> {Bool.not(b) == True{} : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({Bool.not(True{}) == True{} : Bool}, S.false_true(Equal.trans(Bool, False{}, Id.is_letter(c), True{}, (%Equal.sym(Char, c, '\n', chr_eq(c, '\n', eb)) : {False{} == Id.is_letter(_) : Bool}
        {==}), h)))

def hex_nl.at(+c: Char, b: Bool, eb: {Char.is_eq(c, '\n') == b : Bool}, h: {T.is_hex(c) == True{} : Bool}) -> {Bool.not(b) == True{} : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({Bool.not(True{}) == True{} : Bool}, S.false_true(Equal.trans(Bool, False{}, T.is_hex(c), True{}, (%Equal.sym(Char, c, '\n', chr_eq(c, '\n', eb)) : {False{} == T.is_hex(_) : Bool}
        {==}), h)))

def nonl_letters(s: String, +h: {T.all_chars(~Id.is_letter, s) == True{} : Bool}) -> {nonl(s) == True{} : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      AL.and_intro(Bool.not(Char.is_eq(c, '\n')), nonl(t),
        letter_nl.at(c, Char.is_eq(c, '\n'), {==}, Comp.and_left(Id.is_letter(c), T.all_chars(~Id.is_letter, t), h)),
        nonl_letters(t, Comp.and_right(Id.is_letter(c), T.all_chars(~Id.is_letter, t), h)))

def nonl_hex(s: String, +h: {T.all_chars(~T.is_hex, s) == True{} : Bool}) -> {nonl(s) == True{} : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      AL.and_intro(Bool.not(Char.is_eq(c, '\n')), nonl(t),
        hex_nl.at(c, Char.is_eq(c, '\n'), {==}, Comp.and_left(T.is_hex(c), T.all_chars(~T.is_hex, t), h)),
        nonl_hex(t, Comp.and_right(T.is_hex(c), T.all_chars(~T.is_hex, t), h)))

def nonl_app(a: String, -b: String, +ha: {nonl(a) == True{} : Bool}, hb: {nonl(b) == True{} : Bool}) -> {nonl(a ++ b) == True{} : Bool}:
  match a:
    case SNil{}:
      hb
    case SCon{+c, +t}:
      AL.and_intro(Bool.not(Char.is_eq(c, '\n')), nonl(t ++ b), Comp.and_left(Bool.not(Char.is_eq(c, '\n')), nonl(t), ha), nonl_app(t, b, Comp.and_right(Bool.not(Char.is_eq(c, '\n')), nonl(t), ha), hb))

# A line with no newline in it, and a newline: the line, then the rest.
def split_nl(s: String, -r: String, +h: {nonl(s) == True{} : Bool}) -> {String.split(s ++ SCon{'\n', r}, '\n') == s <> String.split(r, '\n') : List<&2, String>}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      Equal.trans(List<&2, String>, String.split.fin(c, String.split(t ++ SCon{'\n', r}, '\n'), Char.is_eq(c, '\n')), String.split.fin(c, String.split(t ++ SCon{'\n', r}, '\n'), False{}), SCon{c, t} <> String.split(r, '\n'),
        Equal.cong(Bool, List<&2, String>, b => String.split.fin(c, String.split(t ++ SCon{'\n', r}, '\n'), b), Char.is_eq(c, '\n'), False{}, AL.not_of_true(Char.is_eq(c, '\n'), Comp.and_left(Bool.not(Char.is_eq(c, '\n')), nonl(t), h))),
        Equal.cong(List<&2, String>, List<&2, String>, l => String.split.push(c, l), String.split(t ++ SCon{'\n', r}, '\n'), t <> String.split(r, '\n'), split_nl(t, r, Comp.and_right(Bool.not(Char.is_eq(c, '\n')), nonl(t), h))))

# The target line
# ---------------

def target_nl(t: Bm.Target, h: {Bm.target_ok(t) == True{} : Bool}) -> {nonl(Bm.show_target(t)) == True{} : Bool}:
  match t:
    case Bm.Target.Change{+id}:
      nonl_app("change ", id, {==}, nonl_letters(id, Comp.and_right(Nat.is_eq(String.length(id), 24n), T.all_chars(~Id.is_letter, id), h)))
    case Bm.Target.Revision{+id}:
      nonl_app("revision ", id, {==}, nonl_hex(id, Comp.and_right(Nat.is_eq(String.length(id), 64n), T.all_chars(~T.is_hex, id), h)))
    case Bm.Target.File{+id}:
      nonl_app("file ", id, {==}, nonl_letters(id, Comp.and_right(Nat.is_eq(String.length(id), 24n), T.all_chars(~Id.is_letter, id), h)))

def target_back(t: Bm.Target, h: {Bm.target_ok(t) == True{} : Bool}) -> {Bm.target(T.split_once(Bm.show_target(t))) == Done{t} : Result<&2, &2, String, Bm.Target>}:
  match t:
    case Bm.Target.Change{+id}:
      (%Equal.sym(Bool, Id.is_assigned(id), True{}, h) : {Bool.pick(Result<&2, &2, String, Bm.Target>, _, Done{Bm.Target.Change{id}}, Fail{Bm.target_error()}) == Done{Bm.Target.Change{id}} : Result<&2, &2, String, Bm.Target>}
        {==})
    case Bm.Target.Revision{+id}:
      (%Equal.sym(Bool, Id.is_digest(id), True{}, h) : {Bool.pick(Result<&2, &2, String, Bm.Target>, _, Done{Bm.Target.Revision{id}}, Fail{Bm.target_error()}) == Done{Bm.Target.Revision{id}} : Result<&2, &2, String, Bm.Target>}
        {==})
    case Bm.Target.File{+id}:
      (%Equal.sym(Bool, Id.is_assigned(id), True{}, h) : {Bool.pick(Result<&2, &2, String, Bm.Target>, _, Done{Bm.Target.File{id}}, Fail{Bm.target_error()}) == Done{Bm.Target.File{id}} : Result<&2, &2, String, Bm.Target>}
        {==})

# The file
# --------

def lines_back(+first: String, +t: Bm.Target, p: Bool, ht: {Bm.target(T.split_once(first)) == Done{t} : Result<&2, &2, String, Bm.Target>}) -> {Bm.parse.lines(Bm.lines.trim(first <> String.split(Bm.private_line(p), '\n'), Bm.last_empty(first <> String.split(Bm.private_line(p), '\n')))) == Done{Bm.Stated{t, p}} : Result<&2, &2, String, Bm.Stated>}:
  match p:
    case False{}:
      Equal.cong(Result<&2, &2, String, Bm.Target>, Result<&2, &2, String, Bm.Stated>, r => Bm.parse.target(r, Nil{}), Bm.target(T.split_once(first)), Done{t}, ht)
    case True{}:
      Equal.cong(Result<&2, &2, String, Bm.Target>, Result<&2, &2, String, Bm.Stated>, r => Bm.parse.target(r, ["private"]), Bm.target(T.split_once(first)), Done{t}, ht)

# What the Rust tool writes for a bookmark reads back as that bookmark.
def reads_back(+t: Bm.Target, p: Bool, +h: {Bm.target_ok(t) == True{} : Bool}) -> {Bm.parse(Bm.write(Bm.Stated{t, p})) == Done{Bm.Stated{t, p}} : Result<&2, &2, String, Bm.Stated>}:
  Equal.trans(Result<&2, &2, String, Bm.Stated>, Bm.parse(Bm.write(Bm.Stated{t, p})), Bm.parse.lines(Bm.lines.trim(Bm.show_target(t) <> String.split(Bm.private_line(p), '\n'), Bm.last_empty(Bm.show_target(t) <> String.split(Bm.private_line(p), '\n')))), Done{Bm.Stated{t, p}},
    Equal.cong(List<&2, String>, Result<&2, &2, String, Bm.Stated>, +ls => Bm.parse.lines(Bm.lines.trim(ls, Bm.last_empty(ls))), String.split(Bm.show_target(t) ++ SCon{'\n', Bm.private_line(p)}, '\n'), Bm.show_target(t) <> String.split(Bm.private_line(p), '\n'), split_nl(Bm.show_target(t), Bm.private_line(p), target_nl(t, h))),
    lines_back(Bm.show_target(t), t, p, target_back(t, h)))
