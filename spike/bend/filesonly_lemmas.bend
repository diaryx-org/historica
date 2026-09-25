# What `export --files-only` reads of the directory it lays a folder out
# into: the host's listing, read back, names exactly the entries the
# directory holds, in order, so it goes on exactly where there are none.
import Base
import ./export.bend as Export
import ./text.bend as T
import ./commands.bend as Main
import ./export_lemmas.bend as ExportL
import ./spelling_lemmas.bend as SpL
import ./bookmark_lemmas.bend as BmL
import ./anchor_lemmas.bend as AL
import ./composition_lemmas.bend as Comp
import ./string_lemmas.bend as SL
import ./equality_lemmas.bend as Eq
import ./dryrun_lemmas.bend as DryL

# Splitting at newlines
# ---------------------

def pre_head(+s: String, l: List<&2, String>) -> List<&2, String>:
  match l:
    case Nil{}:
      [s]
    case h <> t:
      (s ++ h) <> t

def pre_push(+c: Char, +t: String, l: List<&2, String>) -> {String.split.push(c, pre_head(t, l)) == pre_head(SCon{c, t}, l) : List<&2, String>}:
  match l:
    case Nil{}:
      {==}
    case h <> r:
      {==}

def pre_nil(l: List<&2, String>, ne: {SpL.nonempty(String, l) == True{} : Bool}) -> {pre_head(SNil{}, l) == l : List<&2, String>}:
  match l:
    case Nil{}:
      Empty.absurd({[SNil{}] == Nil{} : List<&2, String>}, Comp.false_true(ne))
    case h <> r:
      {==}

def nl_false(+c: Char, h: {Export.line.char(c) == True{} : Bool}) -> {Char.is_eq(c, '\n') == False{} : Bool}:
  AL.not_of_true(Char.is_eq(c, '\n'), h)

# A string with no newline, then anything: its lines are the rest's, the
# first led by the string.
def split_app(s: String, +b: String, +h: {T.all_chars(~(c => Export.line.char(c)), s) == True{} : Bool}) -> {String.split(s ++ b, '\n') == pre_head(s, String.split(b, '\n')) : List<&2, String>}:
  match s:
    case SNil{}:
      Equal.sym(List<&2, String>, pre_head(SNil{}, String.split(b, '\n')), String.split(b, '\n'), pre_nil(String.split(b, '\n'), SpL.split_nonempty(b, '\n')))
    case SCon{+c, +t}:
      %Equal.sym(Bool, Char.is_eq(c, '\n'), False{}, nl_false(c, Comp.and_left(Export.line.char(c), T.all_chars(~(c => Export.line.char(c)), t), h))) : {String.split.fin(c, String.split(t ++ b, '\n'), _) == pre_head(SCon{c, t}, String.split(b, '\n')) : List<&2, String>}
      %Equal.sym(List<&2, String>, String.split(t ++ b, '\n'), pre_head(t, String.split(b, '\n')), split_app(t, b, Comp.and_right(Export.line.char(c), T.all_chars(~(c => Export.line.char(c)), t), h))) : {String.split.push(c, _) == pre_head(SCon{c, t}, String.split(b, '\n')) : List<&2, String>}
      pre_push(c, t, String.split(b, '\n'))

def split_end(+s: String, +h: {T.all_chars(~(c => Export.line.char(c)), s) == True{} : Bool}) -> {String.split(s ++ SNil{}, '\n') == [s] : List<&2, String>}:
  %Equal.sym(List<&2, String>, String.split(s ++ SNil{}, '\n'), pre_head(s, String.split(SNil{}, '\n')), split_app(s, SNil{}, h)) : {_ == [s] : List<&2, String>}
  %Equal.sym(String, s ++ SNil{}, s, Eq.app_nil(s)) : {[_] == [s] : List<&2, String>}
  {==}

# What the lines after the first are.
def after(es: List<&2, Export.Listed>) -> List<&2, String>:
  match es:
    case Nil{}:
      Nil{}
    case e <> rest:
      String.split(Export.listed.then(e, Export.listed.more(rest)), '\n')

# A line, then the rest of the listing: that line, then the rest's lines.
def split_line(+s: String, es: List<&2, Export.Listed>, +h: {T.all_chars(~(c => Export.line.char(c)), s) == True{} : Bool}) -> {String.split(s ++ Export.listed.more(es), '\n') == s <> after(es) : List<&2, String>}:
  match es:
    case Nil{}:
      split_end(s, h)
    case e <> rest:
      %Equal.sym(List<&2, String>, String.split(s ++ SCon{'\n', Export.listed.then(e, Export.listed.more(rest))}, '\n'), pre_head(s, String.split(SCon{'\n', Export.listed.then(e, Export.listed.more(rest))}, '\n')), split_app(s, SCon{'\n', Export.listed.then(e, Export.listed.more(rest))}, h)) : {_ == s <> String.split(Export.listed.then(e, Export.listed.more(rest)), '\n') : List<&2, String>}
      %Equal.sym(String, s ++ SNil{}, s, Eq.app_nil(s)) : {_ <> String.split(Export.listed.then(e, Export.listed.more(rest)), '\n') == s <> String.split(Export.listed.then(e, Export.listed.more(rest)), '\n') : List<&2, String>}
      {==}

# Cutting at spaces
# -----------------

def space_false(+c: Char, h: {Export.size.char(c) == True{} : Bool}) -> {Char.is_eq(c, ' ') == False{} : Bool}:
  AL.or_false_l(Char.is_eq(c, ' '), Char.is_eq(c, '\n'), AL.not_of_true(Bool.or(Char.is_eq(c, ' '), Char.is_eq(c, '\n')), h))

def fast_go(s: String, +acc: String, +r: String, +h: {T.all_chars(~(c => Export.size.char(c)), s) == True{} : Bool}) -> {Export.entry.file_name(T.split_once.fast(s ++ SCon{' ', r}, acc, T.space_first(s ++ SCon{' ', r}))) == Some{r} : Maybe<&2, String>}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %Equal.sym(Bool, Char.is_eq(c, ' '), False{}, space_false(c, Comp.and_left(Export.size.char(c), T.all_chars(~(c => Export.size.char(c)), t), h))) : {Export.entry.file_name(T.split_once.fast(SCon{c, t ++ SCon{' ', r}}, acc, _)) == Some{r} : Maybe<&2, String>}
      fast_go(t, SCon{c, acc}, r, Comp.and_right(Export.size.char(c), T.all_chars(~(c => Export.size.char(c)), t), h))

# A size with no space in it, a space, and a name: the name.
def file_rest(+size: String, +name: String, +h: {T.all_chars(~(c => Export.size.char(c)), size) == True{} : Bool}) -> {Export.entry.file_name(T.split_once(size ++ SCon{' ', name})) == Some{name} : Maybe<&2, String>}:
  fast_go(size, SNil{}, name, h)

def size_line(s: String, +h: {T.all_chars(~(c => Export.size.char(c)), s) == True{} : Bool}) -> {T.all_chars(~(c => Export.line.char(c)), s) == True{} : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      ExportL.and_tt(Export.line.char(c), T.all_chars(~(c => Export.line.char(c)), t),
        DryL.not_false(Char.is_eq(c, '\n'), AL.or_false_r(Char.is_eq(c, ' '), Char.is_eq(c, '\n'), AL.not_of_true(Bool.or(Char.is_eq(c, ' '), Char.is_eq(c, '\n')), Comp.and_left(Export.size.char(c), T.all_chars(~(c => Export.size.char(c)), t), h)))),
        size_line(t, Comp.and_right(Export.size.char(c), T.all_chars(~(c => Export.size.char(c)), t), h)))

# Reading the listing back
# ------------------------

def dir_names(+name: String, +rest: List<&2, Export.Listed>, +hn: {T.all_chars(~(c => Export.line.char(c)), name) == True{} : Bool}, ih: {Export.entry.names(after(rest), False{}) == Export.listed.names(rest) : List<&2, String>}) -> {Export.entry.names(String.split(Export.listed.then(Export.Listed.Dir{name}, Export.listed.more(rest)), '\n'), False{}) == name <> Export.listed.names(rest) : List<&2, String>}:
  %Equal.sym(List<&2, String>, String.split(name ++ Export.listed.more(rest), '\n'), name <> after(rest), split_line(name, rest, hn)) : {Export.entry.names(String.split.push('d', String.split.push(' ', _)), False{}) == name <> Export.listed.names(rest) : List<&2, String>}
  %Equal.sym(List<&2, String>, Export.entry.names(after(rest), False{}), Export.listed.names(rest), ih) : {name <> _ == name <> Export.listed.names(rest) : List<&2, String>}
  {==}

def other_names(+name: String, +rest: List<&2, Export.Listed>, +hn: {T.all_chars(~(c => Export.line.char(c)), name) == True{} : Bool}, ih: {Export.entry.names(after(rest), False{}) == Export.listed.names(rest) : List<&2, String>}) -> {Export.entry.names(String.split(Export.listed.then(Export.Listed.Other{name}, Export.listed.more(rest)), '\n'), False{}) == name <> Export.listed.names(rest) : List<&2, String>}:
  %Equal.sym(List<&2, String>, String.split(name ++ Export.listed.more(rest), '\n'), name <> after(rest), split_line(name, rest, hn)) : {Export.entry.names(String.split.push('o', String.split.push(' ', _)), False{}) == name <> Export.listed.names(rest) : List<&2, String>}
  %Equal.sym(List<&2, String>, Export.entry.names(after(rest), False{}), Export.listed.names(rest), ih) : {name <> _ == name <> Export.listed.names(rest) : List<&2, String>}
  {==}

# A link's line names it, and the line after it, where it points, is no
# entry of its own.
def link_names(+name: String, +target: String, +rest: List<&2, Export.Listed>, +hn: {T.all_chars(~(c => Export.line.char(c)), name) == True{} : Bool}, +ht: {T.all_chars(~(c => Export.line.char(c)), target) == True{} : Bool}, ih: {Export.entry.names(after(rest), False{}) == Export.listed.names(rest) : List<&2, String>}) -> {Export.entry.names(String.split(Export.listed.then(Export.Listed.Link{name, target}, Export.listed.more(rest)), '\n'), False{}) == name <> Export.listed.names(rest) : List<&2, String>}:
  %Equal.sym(List<&2, String>, String.split(name ++ SCon{'\n', target ++ Export.listed.more(rest)}, '\n'), pre_head(name, String.split(SCon{'\n', target ++ Export.listed.more(rest)}, '\n')), split_app(name, SCon{'\n', target ++ Export.listed.more(rest)}, hn)) : {Export.entry.names(String.split.push('l', String.split.push(' ', _)), False{}) == name <> Export.listed.names(rest) : List<&2, String>}
  %Equal.sym(String, name ++ SNil{}, name, Eq.app_nil(name)) : {Export.entry.names(String.split.push('l', String.split.push(' ', _ <> String.split(target ++ Export.listed.more(rest), '\n'))), False{}) == name <> Export.listed.names(rest) : List<&2, String>}
  %Equal.sym(List<&2, String>, String.split(target ++ Export.listed.more(rest), '\n'), target <> after(rest), split_line(target, rest, ht)) : {Export.entry.names(String.split.push('l', String.split.push(' ', name <> _)), False{}) == name <> Export.listed.names(rest) : List<&2, String>}
  %Equal.sym(Bool, String.starts_with(name, ""), True{}, DryL.sw_nil(name)) : {name <> Export.entry.names(target <> after(rest), _) == name <> Export.listed.names(rest) : List<&2, String>}
  %Equal.sym(List<&2, String>, Export.entry.names(after(rest), False{}), Export.listed.names(rest), ih) : {name <> _ == name <> Export.listed.names(rest) : List<&2, String>}
  {==}

# A file's line names it, whatever its mode and size.
def file_names(runs: Bool, +size: String, +name: String, +rest: List<&2, Export.Listed>, +hs: {T.all_chars(~(c => Export.size.char(c)), size) == True{} : Bool}, +hn: {T.all_chars(~(c => Export.line.char(c)), name) == True{} : Bool}, ih: {Export.entry.names(after(rest), False{}) == Export.listed.names(rest) : List<&2, String>}) -> {Export.entry.names(String.split(Export.listed.then(Export.Listed.File{runs, size, name}, Export.listed.more(rest)), '\n'), False{}) == name <> Export.listed.names(rest) : List<&2, String>}:
  match runs:
    case True{}:
      %Equal.sym(List<&2, String>, String.split(size ++ (" " ++ (name ++ Export.listed.more(rest))), '\n'), pre_head(size, String.split(" " ++ (name ++ Export.listed.more(rest)), '\n')), split_app(size, " " ++ (name ++ Export.listed.more(rest)), size_line(size, hs))) : {Export.entry.names(String.split.push('f', String.split.push(' ', String.split.push('1', String.split.push(' ', _)))), False{}) == name <> Export.listed.names(rest) : List<&2, String>}
      %Equal.sym(List<&2, String>, String.split(name ++ Export.listed.more(rest), '\n'), name <> after(rest), split_line(name, rest, hn)) : {Export.entry.names(String.split.push('f', String.split.push(' ', String.split.push('1', String.split.push(' ', pre_head(size, String.split.push(' ', _)))))), False{}) == name <> Export.listed.names(rest) : List<&2, String>}
      %Equal.sym(Maybe<&2, String>, Export.entry.file_name(T.split_once(size ++ SCon{' ', name})), Some{name}, file_rest(size, name, hs)) : {Export.name.push(_, Export.entry.names(after(rest), False{})) == name <> Export.listed.names(rest) : List<&2, String>}
      %Equal.sym(List<&2, String>, Export.entry.names(after(rest), False{}), Export.listed.names(rest), ih) : {name <> _ == name <> Export.listed.names(rest) : List<&2, String>}
      {==}
    case False{}:
      %Equal.sym(List<&2, String>, String.split(size ++ (" " ++ (name ++ Export.listed.more(rest))), '\n'), pre_head(size, String.split(" " ++ (name ++ Export.listed.more(rest)), '\n')), split_app(size, " " ++ (name ++ Export.listed.more(rest)), size_line(size, hs))) : {Export.entry.names(String.split.push('f', String.split.push(' ', String.split.push('0', String.split.push(' ', _)))), False{}) == name <> Export.listed.names(rest) : List<&2, String>}
      %Equal.sym(List<&2, String>, String.split(name ++ Export.listed.more(rest), '\n'), name <> after(rest), split_line(name, rest, hn)) : {Export.entry.names(String.split.push('f', String.split.push(' ', String.split.push('0', String.split.push(' ', pre_head(size, String.split.push(' ', _)))))), False{}) == name <> Export.listed.names(rest) : List<&2, String>}
      %Equal.sym(Maybe<&2, String>, Export.entry.file_name(T.split_once(size ++ SCon{' ', name})), Some{name}, file_rest(size, name, hs)) : {Export.name.push(_, Export.entry.names(after(rest), False{})) == name <> Export.listed.names(rest) : List<&2, String>}
      %Equal.sym(List<&2, String>, Export.entry.names(after(rest), False{}), Export.listed.names(rest), ih) : {name <> _ == name <> Export.listed.names(rest) : List<&2, String>}
      {==}

# Read back, the listing names every entry, in order.
def names_after(es: List<&2, Export.Listed>, +h: {Export.listed.ok(es) == True{} : Bool}) -> {Export.entry.names(after(es), False{}) == Export.listed.names(es) : List<&2, String>}:
  match es:
    case Nil{}:
      {==}
    case e <> +rest:
      match e:
        case Export.Listed.Dir{+name}:
          dir_names(name, rest, Comp.and_left(T.all_chars(~(c => Export.line.char(c)), name), Export.listed.ok(rest), h), names_after(rest, Comp.and_right(T.all_chars(~(c => Export.line.char(c)), name), Export.listed.ok(rest), h)))
        case Export.Listed.File{runs, +size, +name}:
          +h2 = Comp.and_right(T.all_chars(~(c => Export.size.char(c)), size), Bool.and(T.all_chars(~(c => Export.line.char(c)), name), Export.listed.ok(rest)), h)
          file_names(runs, size, name, rest, Comp.and_left(T.all_chars(~(c => Export.size.char(c)), size), Bool.and(T.all_chars(~(c => Export.line.char(c)), name), Export.listed.ok(rest)), h), Comp.and_left(T.all_chars(~(c => Export.line.char(c)), name), Export.listed.ok(rest), h2), names_after(rest, Comp.and_right(T.all_chars(~(c => Export.line.char(c)), name), Export.listed.ok(rest), h2)))
        case Export.Listed.Link{+name, +target}:
          +h2 = Comp.and_right(T.all_chars(~(c => Export.line.char(c)), name), Bool.and(T.all_chars(~(c => Export.line.char(c)), target), Export.listed.ok(rest)), h)
          link_names(name, target, rest, Comp.and_left(T.all_chars(~(c => Export.line.char(c)), name), Bool.and(T.all_chars(~(c => Export.line.char(c)), target), Export.listed.ok(rest)), h), Comp.and_left(T.all_chars(~(c => Export.line.char(c)), target), Export.listed.ok(rest), h2), names_after(rest, Comp.and_right(T.all_chars(~(c => Export.line.char(c)), target), Export.listed.ok(rest), h2)))
        case Export.Listed.Other{+name}:
          other_names(name, rest, Comp.and_left(T.all_chars(~(c => Export.line.char(c)), name), Export.listed.ok(rest), h), names_after(rest, Comp.and_right(T.all_chars(~(c => Export.line.char(c)), name), Export.listed.ok(rest), h)))

# What the host says a directory holds, read back, is the entries' names,
# in order.
def names_back(es: List<&2, Export.Listed>, +h: {Export.listed.ok(es) == True{} : Bool}) -> {Export.dir.names(Export.listing(es)) == Export.listed.names(es) : List<&2, String>}:
  match es:
    case Nil{}:
      {==}
    case e <> +rest:
      match e:
        case Export.Listed.Dir{+name}:
          names_after(Export.Listed.Dir{name} <> rest, h)
        case Export.Listed.File{+runs, +size, +name}:
          names_after(Export.Listed.File{runs, size, name} <> rest, h)
        case Export.Listed.Link{+name, +target}:
          names_after(Export.Listed.Link{name, target} <> rest, h)
        case Export.Listed.Other{+name}:
          names_after(Export.Listed.Other{name} <> rest, h)

def is_done_fail(-e: Main.Refused) -> {Result.is_done(&2, &2, Main.Refused, Unit, Fail{e}) == False{} : Bool}:
  {==}

# Where a directory holds anything, neither a folder alone nor a fresh copy
# is laid out there.
def held_not(+into: String, +name: String, +rest: List<&2, String>, header: Result<&1, &1, U32 & String, String>, +text: String, et: {String.is_empty(text) == False{} : Bool}) -> {Bool.and(Export.bool.same(Result.is_done(&2, &2, Main.Refused, Unit, Export.holding.r(into, name <> rest)), False{}), Export.bool.same(Export.dest.fresh(Export.dest.r(into, Done{text}, header)), False{})) == True{} : Bool}:
  match header:
    case Fail{x}:
      %Equal.sym(Bool, String.is_empty(text), False{}, et) : {Bool.and(True{}, Export.bool.same(Export.dest.fresh(Export.dest.held(into, _, False{})), False{})) == True{} : Bool}
      {==}
    case Done{x}:
      %Equal.sym(Bool, String.is_empty(text), False{}, et) : {Bool.and(True{}, Export.bool.same(Export.dest.fresh(Export.dest.held(into, _, True{})), False{})) == True{} : Bool}
      {==}

def nothing_cases(+into: String, es: List<&2, Export.Listed>, header: Result<&1, &1, U32 & String, String>) -> {Bool.and(Export.bool.same(Result.is_done(&2, &2, Main.Refused, Unit, Export.holding.r(into, Export.listed.names(es))), List.is_empty(&2, Export.Listed, es)), Export.bool.same(Export.dest.fresh(Export.dest.r(into, Done{Export.listing(es)}, header)), List.is_empty(&2, Export.Listed, es))) == True{} : Bool}:
  match es:
    case Nil{}:
      {==}
    case e <> +rest:
      match e:
        case Export.Listed.Dir{+name}:
          held_not(into, name, Export.listed.names(rest), header, Export.listing(Export.Listed.Dir{name} <> rest), {==})
        case Export.Listed.File{+runs, +size, +name}:
          held_not(into, name, Export.listed.names(rest), header, Export.listing(Export.Listed.File{runs, size, name} <> rest), {==})
        case Export.Listed.Link{+name, +target}:
          held_not(into, name, Export.listed.names(rest), header, Export.listing(Export.Listed.Link{name, target} <> rest), {==})
        case Export.Listed.Other{+name}:
          held_not(into, name, Export.listed.names(rest), header, Export.listing(Export.Listed.Other{name} <> rest), {==})

# An export writes only into a directory holding nothing, reading the
# host's listing of it.
def into_nothing(+into: String, +es: List<&2, Export.Listed>, header: Result<&1, &1, U32 & String, String>, +h: {Export.listed.ok(es) == True{} : Bool}) -> {Bool.and(Export.bool.same(Result.is_done(&2, &2, Main.Refused, Unit, Export.empty.r(into, Done{Export.listing(es)})), List.is_empty(&2, Export.Listed, es)), Export.bool.same(Export.dest.fresh(Export.dest.r(into, Done{Export.listing(es)}, header)), List.is_empty(&2, Export.Listed, es))) == True{} : Bool}:
  %Equal.sym(List<&2, String>, Export.dir.names(Export.listing(es)), Export.listed.names(es), names_back(es, h)) : {Bool.and(Export.bool.same(Result.is_done(&2, &2, Main.Refused, Unit, Export.holding.r(into, _)), List.is_empty(&2, Export.Listed, es)), Export.bool.same(Export.dest.fresh(Export.dest.r(into, Done{Export.listing(es)}, header)), List.is_empty(&2, Export.Listed, es))) == True{} : Bool}
  nothing_cases(into, es, header)
