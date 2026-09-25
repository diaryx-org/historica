# `identity` writes one line, `author` and the name, and the file reads back
# as that author for work in any directory: the default block, which every
# `under` block defers to — wherever the name is one a revision can hold.
import Base
import ./identity.bend as Identity
import ./folder.bend as Folder
import ./text.bend as T
import ./bookmark_lemmas.bend as BmL
import ./anchor_lemmas.bend as AL
import ./composition_lemmas.bend as Comp

# Characters
# ----------

# A character that is not a control character is not one that is.
def ctl.at(+c: Char, +d: Char, b: Bool, eb: {Char.is_eq(c, d) == b : Bool}, hd: {Folder.is_control(d) == True{} : Bool}, hc: {Folder.is_control(c) == False{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, Comp.false_true(Equal.trans(Bool, False{}, Folder.is_control(c), True{},
        Equal.sym(Bool, Folder.is_control(c), False{}, hc),
        Equal.trans(Bool, Folder.is_control(c), Folder.is_control(d), True{}, Equal.cong(Char, Bool, x => Folder.is_control(x), c, d, BmL.chr_eq(c, d, eb)), hd))))

def quiet(s: String) -> Bool:
  List.any(~&2, ~Char, ~Folder.is_control, String.to_list(s))

# A value with no control character in it has no newline in it.
def nonl(s: String, +h: {quiet(s) == False{} : Bool}) -> {BmL.nonl(s) == True{} : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %Equal.sym(Bool, Char.is_eq(c, '\n'), False{}, ctl.at(c, '\n', Char.is_eq(c, '\n'), {==}, {==}, AL.or_false_l(Folder.is_control(c), quiet(t), h))) : {Bool.and(Bool.not(_), BmL.nonl(t)) == True{} : Bool}
      nonl(t, AL.or_false_r(Folder.is_control(c), quiet(t), h))

# Whether a string opens with a carriage return.
def cr_first(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{c, t}:
      Char.is_eq(c, '\r')

def cr_start(acc: String, h: {cr_first(acc) == False{} : Bool}) -> {String.starts_with(acc, "\r") == False{} : Bool}:
  match acc:
    case SNil{}:
      {==}
    case SCon{+c, t}:
      %Equal.sym(Bool, Char.is_eq(c, '\r'), False{}, h) : {String.starts_with.if(t, SNil{}, _) == False{} : Bool}
      {==}

# Reversed onto something that does not open with a carriage return, a
# value with no control character in it does not either.
def cr_rev(s: String, +acc: String, +hs: {quiet(s) == False{} : Bool}, ha: {cr_first(acc) == False{} : Bool}) -> {String.starts_with(String.reverse.go(s, acc), "\r") == False{} : Bool}:
  match s:
    case SNil{}:
      cr_start(acc, ha)
    case SCon{+c, +t}:
      cr_rev(t, SCon{c, acc}, AL.or_false_r(Folder.is_control(c), quiet(t), hs), ctl.at(c, '\r', Char.is_eq(c, '\r'), {==}, {==}, AL.or_false_l(Folder.is_control(c), quiet(t), hs)))

# The line `identity` writes
# --------------------------

def reads_back(+file: String, +a: String, +directory: String, +home: Maybe<&2, String>, +h: {Identity.unusable(a) == False{} : Bool}) -> {Identity.from_text(file, Identity.wanted(a), directory, home) == Done{a} : Result<&2, &2, String, String>}:
  +q = AL.or_false_r(Folder.untrimmed(a), quiet(a), h)
  %Equal.sym(List<&2, String>, String.split(("author " ++ a) ++ SCon{'\n', SNil{}}, '\n'), ("author " ++ a) <> String.split(SNil{}, '\n'), BmL.split_nl("author " ++ a, SNil{}, nonl(a, q))) : {Identity.from_ids(file, Identity.parse.go(Folder.lines.trimmed(_), 1n, Done{Identity.Reading{Identity.Ids{None{}, Nil{}}, None{}, None{}, 0n}}), directory, home) == Done{a} : Result<&2, &2, String, String>}
  %Equal.sym(Bool, String.ends_with("author " ++ a, "\r"), False{}, cr_rev(a, " rohtua", q, {==})) : {Identity.from_ids(file, Identity.parse.go([Bool.pick(String, _, String.take("author " ++ a, Nat.sub(String.length("author " ++ a), 1n)), "author " ++ a)], 1n, Done{Identity.Reading{Identity.Ids{None{}, Nil{}}, None{}, None{}, 0n}}), directory, home) == Done{a} : Result<&2, &2, String, String>}
  %Equal.sym(Bool, Identity.unusable(a), False{}, h) : {Identity.from_ids(file, Identity.parse.go(Nil{}, 2n, Identity.line(Identity.Reading{Identity.Ids{None{}, Nil{}}, None{}, None{}, 0n}, 1n, Bool.pick(Identity.Said, _, Identity.Said.Unusable{}, Bool.pick(Identity.Said, String.eq("author", "under"), Identity.Said.Under{Identity.unslashed(a)}, Bool.pick(Identity.Said, String.eq("author", "author"), Identity.Said.Author{a}, Identity.Said.Other{}))))), directory, home) == Done{a} : Result<&2, &2, String, String>}
  %Equal.sym(Bool, Identity.unusable(a), False{}, h) : {Bool.pick(Result<&2, &2, String, String>, _, Fail{Identity.checked.said(a, Some{file})}, Done{a}) == Done{a} : Result<&2, &2, String, String>}
  {==}
