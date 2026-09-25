# `diff` over the folder compares like with like: for each path, what it
# replays at the position and what it reads from the folder are decided by
# what each side holds there, and a file of lines against a regular file is
# replayed exactly where the folder's is read. And it believes the digest a
# statement gives: where a file's nearest statement is `text` and a digest,
# it is replayed and read exactly where the first word the host answers for
# its path is another.
import Base
import ./text.bend as T
import ./tree.bend as Tree
import ./folder.bend as Folder
import ./store.bend as Store
import ./revision.bend as Rev
import ./commands.bend as Main
import ./composition_lemmas.bend as Comp
import ./anchor_lemmas.bend as AL
import ./decimal_lemmas.bend as Dec

def keep2(-b1: Bool, -b2: Bool, -x: String, -l1: List<&2, String>, -l2: List<&2, String>, eb: {b1 == b2 : Bool}, el: {l1 == l2 : List<&2, String>}) -> {Rev.keep(b1, x, l1) == Rev.keep(b2, x, l2) : List<&2, String>}:
  %eb : {Rev.keep(b1, x, l1) == Rev.keep(_, x, l2) : List<&2, String>}
  %el : {Rev.keep(b1, x, l1) == Rev.keep(b1, x, _) : List<&2, String>}
  {==}

# Like with like
# --------------

def same_not_xor(b: Bool) -> {Bool.not(Bool.xor(b, b)) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# One path, by what the position and the folder hold there.
def like_one(+dg: Map<&2, String>, +os: Map<&2, T.Split>, +eds: List<&2, Store.Doc>, h: Main.Here) -> {Main.planned.like(Main.plan(dg, os, eds, h)) == True{} : Bool}:
  match h:
    case Main.Here{p, None{}, None{}}:
      {==}
    case Main.Here{p, None{}, Some{Folder.Found.File{r, x, n}}}:
      {==}
    case Main.Here{p, None{}, Some{Folder.Found.Link{r, x}}}:
      {==}
    case Main.Here{+p, Some{Tree.Entry{+f, +q, Tree.Lines{}, +y, +g, +m}}, Some{Folder.Found.File{+r, +x, +n}}}:
      same_not_xor(Bool.not(Main.here.same(eds, os, Main.Here{p, Some{Tree.Entry{f, q, Tree.Lines{}, y, g, m}}, Some{Folder.Found.File{r, x, n}}}, Main.here.digest(dg, Main.Here{p, Some{Tree.Entry{f, q, Tree.Lines{}, y, g, m}}, Some{Folder.Found.File{r, x, n}}}))))
    case Main.Here{p, Some{Tree.Entry{f, q, Tree.Lines{}, y, g, m}}, None{}}:
      {==}
    case Main.Here{p, Some{Tree.Entry{f, q, Tree.Lines{}, y, g, m}}, Some{Folder.Found.Link{r, x}}}:
      {==}
    case Main.Here{p, Some{Tree.Entry{f, q, Tree.Whole{}, y, g, m}}, None{}}:
      {==}
    case Main.Here{p, Some{Tree.Entry{f, q, Tree.Whole{}, y, g, m}}, Some{Folder.Found.File{r, x, n}}}:
      {==}
    case Main.Here{p, Some{Tree.Entry{f, q, Tree.Whole{}, y, g, m}}, Some{Folder.Found.Link{r, x}}}:
      {==}
    case Main.Here{p, Some{Tree.Entry{f, q, Tree.Link{}, y, g, m}}, None{}}:
      {==}
    case Main.Here{p, Some{Tree.Entry{f, q, Tree.Link{}, y, g, m}}, Some{Folder.Found.File{r, x, n}}}:
      {==}
    case Main.Here{p, Some{Tree.Entry{f, q, Tree.Link{}, y, g, m}}, Some{Folder.Found.Link{r, x}}}:
      {==}

def plans_like(+dg: Map<&2, String>, +os: Map<&2, T.Split>, +eds: List<&2, Store.Doc>, hs: List<&2, Main.Here>) -> {Main.plans.like(Main.plans(dg, os, eds, hs)) == True{} : Bool}:
  match hs:
    case Nil{}:
      {==}
    case +h <> +rest:
      AL.and_intro(Main.planned.like(Main.plan(dg, os, eds, h)), Main.plans.like(Main.plans(dg, os, eds, rest)), like_one(dg, os, eds, h), plans_like(dg, os, eds, rest))

# The digest a statement gives
# ----------------------------

def not_true_false(b: Bool, e: {Bool.not(b) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      Equal.sym(Bool, False{}, True{}, e)
    case False{}:
      {==}

# A word with no space in it, a space and more: the split falls after the
# word, whatever came before it.
def fast_word(w: String, +acc: String, +more: String, +hw: {T.all_chars(~(c => Bool.not(Char.is_eq(c, ' '))), w) == True{} : Bool}) -> {T.split_once.fast(w ++ (" " ++ more), acc, T.space_first(w ++ (" " ++ more))) == Some{T.Split{String.reverse(String.reverse.go(w, acc)), more}} : Maybe<&2, T.Split>}:
  match w:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %Equal.sym(Bool, Char.is_eq(c, ' '), False{}, not_true_false(Char.is_eq(c, ' '), Comp.and_left(Bool.not(Char.is_eq(c, ' ')), T.all_chars(~(c => Bool.not(Char.is_eq(c, ' '))), t), hw))) : {T.split_once.fast(SCon{c, t ++ (" " ++ more)}, acc, _) == Some{T.Split{String.reverse(String.reverse.go(t, SCon{c, acc})), more}} : Maybe<&2, T.Split>}
      fast_word(t, SCon{c, acc}, more, Comp.and_right(Bool.not(Char.is_eq(c, ' ')), T.all_chars(~(c => Bool.not(Char.is_eq(c, ' '))), t), hw))

# So its first word is the word.
def word_first(+w: String, +more: String, hw: {T.all_chars(~(c => Bool.not(Char.is_eq(c, ' '))), w) == True{} : Bool}) -> {T.word(w ++ (" " ++ more)) == w : String}:
  %Equal.sym(Maybe<&2, T.Split>, T.split_once.fast(w ++ (" " ++ more), SNil{}, T.space_first(w ++ (" " ++ more))), Some{T.Split{String.reverse(String.reverse.go(w, SNil{})), more}}, fast_word(w, SNil{}, more, hw)) : {T.word.of(w ++ (" " ++ more), _) == w : String}
  Dec.rev_rev(w)

# A file of lines whose nearest statement is `text` and a digest, against
# a regular file the host answered a word for: replayed and read exactly
# where the word is another.
def believed(+dg: Map<&2, String>, +os: Map<&2, T.Split>, +eds: List<&2, Store.Doc>, +path: String, +file: String, +at: String, +y: Maybe<&2, String>, +g: Maybe<&2, Tree.Target>, +m: Tree.Mode, +fp: String, +runs: Bool, +size: Nat, +d: String, +os2: Map<&2, T.Split>, ho: {Map.get(T.Split, T.Split{SNil{}, SNil{}}, os, file) == (os2, T.Split{"text", d}) : Map<&2, T.Split> & T.Split}, +w: String, hw: {T.all_chars(~(c => Bool.not(Char.is_eq(c, ' '))), w) == True{} : Bool}, +more: String, +dg2: Map<&2, String>, hd: {Map.get(String, SNil{}, dg, path) == (dg2, w ++ (" " ++ more)) : Map<&2, String> & String}) -> {Main.plan(dg, os, eds, Main.Here{path, Some{Tree.Entry{file, at, Tree.Lines{}, y, g, m}}, Some{Folder.Found.File{fp, runs, size}}}) == Main.Planned{Main.Here{path, Some{Tree.Entry{file, at, Tree.Lines{}, y, g, m}}, Some{Folder.Found.File{fp, runs, size}}}, w, Bool.not(String.eq(d, w)), Bool.not(String.eq(d, w))} : Main.Planned}:
  %Equal.sym(Map<&2, String> & String, Map.get(String, SNil{}, dg, path), (dg2, w ++ (" " ++ more)), hd) : {Main.plan.of(Main.Here{path, Some{Tree.Entry{file, at, Tree.Lines{}, y, g, m}}, Some{Folder.Found.File{fp, runs, size}}}, T.word(Main.stat_of(path, _)), True{}, True{}, Main.maybe_eq(Main.stated_digest(eds, Main.origin(os, file)), Some{T.word(Main.stat_of(path, _))})) == Main.Planned{Main.Here{path, Some{Tree.Entry{file, at, Tree.Lines{}, y, g, m}}, Some{Folder.Found.File{fp, runs, size}}}, w, Bool.not(String.eq(d, w)), Bool.not(String.eq(d, w))} : Main.Planned}
  %Equal.sym(String, T.word(w ++ (" " ++ more)), w, word_first(w, more, hw)) : {Main.plan.of(Main.Here{path, Some{Tree.Entry{file, at, Tree.Lines{}, y, g, m}}, Some{Folder.Found.File{fp, runs, size}}}, _, True{}, True{}, Main.maybe_eq(Main.stated_digest(eds, Main.origin(os, file)), Some{_})) == Main.Planned{Main.Here{path, Some{Tree.Entry{file, at, Tree.Lines{}, y, g, m}}, Some{Folder.Found.File{fp, runs, size}}}, w, Bool.not(String.eq(d, w)), Bool.not(String.eq(d, w))} : Main.Planned}
  %Equal.sym(Map<&2, T.Split> & T.Split, Map.get(T.Split, T.Split{SNil{}, SNil{}}, os, file), (os2, T.Split{"text", d}), ho) : {Main.plan.of(Main.Here{path, Some{Tree.Entry{file, at, Tree.Lines{}, y, g, m}}, Some{Folder.Found.File{fp, runs, size}}}, w, True{}, True{}, Main.maybe_eq(Main.stated_digest(eds, Main.origin.of(file, _)), Some{w})) == Main.Planned{Main.Here{path, Some{Tree.Entry{file, at, Tree.Lines{}, y, g, m}}, Some{Folder.Found.File{fp, runs, size}}}, w, Bool.not(String.eq(d, w)), Bool.not(String.eq(d, w))} : Main.Planned}
  {==}

# What the fetch law names
# -------------------------

# The files `diff` over the folder replays are the files of lines no
# statement settles, which is how `LAWS.diff_folder_fetches_what_it_replays`
# names them.
def replay_flag(+dg: Map<&2, String>, +os: Map<&2, T.Split>, +eds: List<&2, Store.Doc>, h: Main.Here) -> {Bool.and(Main.here.lines(h), Bool.not(Bool.and(Main.here.regular(h), Main.here.same(eds, os, h, Main.here.digest(dg, h))))) == Bool.and(Main.here.lines(h), Bool.not(Main.here.settled(dg, os, eds, h))) : Bool}:
  match h:
    case Main.Here{p, None{}, found}:
      {==}
    case Main.Here{p, Some{Tree.Entry{f, q, Tree.Lines{}, y, g, m}}, None{}}:
      {==}
    case Main.Here{p, Some{Tree.Entry{f, q, Tree.Lines{}, y, g, m}}, Some{Folder.Found.File{r, x, n}}}:
      {==}
    case Main.Here{p, Some{Tree.Entry{f, q, Tree.Lines{}, y, g, m}}, Some{Folder.Found.Link{r, x}}}:
      {==}
    case Main.Here{p, Some{Tree.Entry{f, q, Tree.Whole{}, y, g, m}}, found}:
      {==}
    case Main.Here{p, Some{Tree.Entry{f, q, Tree.Link{}, y, g, m}}, found}:
      {==}

def replayed_unsettled(+dg: Map<&2, String>, +os: Map<&2, T.Split>, +eds: List<&2, Store.Doc>, hs: List<&2, Main.Here>) -> {Main.planned.replayed(Main.plans(dg, os, eds, hs)) == Main.unsettled.files(dg, os, eds, hs) : List<&2, String>}:
  match hs:
    case Nil{}:
      {==}
    case +h <> +rest:
      keep2(Bool.and(Main.here.lines(h), Bool.not(Bool.and(Main.here.regular(h), Main.here.same(eds, os, h, Main.here.digest(dg, h))))), Bool.and(Main.here.lines(h), Bool.not(Main.here.settled(dg, os, eds, h))), Main.here.file(h),
        Main.planned.replayed(Main.plans(dg, os, eds, rest)), Main.unsettled.files(dg, os, eds, rest),
        replay_flag(dg, os, eds, h), replayed_unsettled(dg, os, eds, rest))
