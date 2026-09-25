# What `prune` clears from `cache/`. The host's listing of the directory,
# read as `prune` reads it, gives exactly the directory's files named by a
# digest, in the order listed: no directory, no link and no link's target,
# nothing of any other kind, and no file under any other name.
import Base
import ./prune.bend as Prune
import ./export.bend as Export
import ./revision.bend as Rev
import ./text.bend as T
import ./composition_lemmas.bend as Comp
import ./equality_lemmas.bend as Eq
import ./dryrun_lemmas.bend as DryL
import ./filesonly_lemmas.bend as FL

# The names of the files among these entries that are digests, in order.
def digest_files(es: List<&2, Export.Listed>) -> List<&2, String>:
  match es:
    case Nil{}:
      Nil{}
    case Export.Listed.Dir{name} <> rest:
      digest_files(rest)
    case Export.Listed.File{r, z, +name} <> rest:
      Rev.keep(T.is_digest(name), name, digest_files(rest))
    case Export.Listed.Link{name, t} <> rest:
      digest_files(rest)
    case Export.Listed.Other{name} <> rest:
      digest_files(rest)

def named_is(cut: Maybe<&2, T.Split>) -> {Prune.file.named(cut) == Export.entry.file_name(cut) : Maybe<&2, String>}:
  match cut:
    case None{}:
      {==}
    case Some{s}:
      match s:
        case T.Split{a, b}:
          {==}

# A size with no space in it, a space, and a name: the name.
def named_rest(+size: String, +name: String, +h: {T.all_chars(~(c => Export.size.char(c)), size) == True{} : Bool}) -> {Prune.file.named(T.split_once(size ++ SCon{' ', name})) == Some{name} : Maybe<&2, String>}:
  Equal.trans(Maybe<&2, String>, Prune.file.named(T.split_once(size ++ SCon{' ', name})), Export.entry.file_name(T.split_once(size ++ SCon{' ', name})), Some{name}, named_is(T.split_once(size ++ SCon{' ', name})), FL.file_rest(size, name, h))

# A directory's line gives no file.
def dir_cleared(+name: String, +rest: List<&2, Export.Listed>, +hn: {T.all_chars(~(c => Export.line.char(c)), name) == True{} : Bool}, ih: {Prune.cached(FL.after(rest), False{}) == digest_files(rest) : List<&2, String>}) -> {Prune.cached(String.split(Export.listed.then(Export.Listed.Dir{name}, Export.listed.more(rest)), '\n'), False{}) == digest_files(rest) : List<&2, String>}:
  %Equal.sym(List<&2, String>, String.split(name ++ Export.listed.more(rest), '\n'), name <> FL.after(rest), FL.split_line(name, rest, hn)) : {Prune.cached(String.split.push('d', String.split.push(' ', _)), False{}) == digest_files(rest) : List<&2, String>}
  ih

# Nor does the line of anything else.
def other_cleared(+name: String, +rest: List<&2, Export.Listed>, +hn: {T.all_chars(~(c => Export.line.char(c)), name) == True{} : Bool}, ih: {Prune.cached(FL.after(rest), False{}) == digest_files(rest) : List<&2, String>}) -> {Prune.cached(String.split(Export.listed.then(Export.Listed.Other{name}, Export.listed.more(rest)), '\n'), False{}) == digest_files(rest) : List<&2, String>}:
  %Equal.sym(List<&2, String>, String.split(name ++ Export.listed.more(rest), '\n'), name <> FL.after(rest), FL.split_line(name, rest, hn)) : {Prune.cached(String.split.push('o', String.split.push(' ', _)), False{}) == digest_files(rest) : List<&2, String>}
  ih

# A link's line gives no file, and the line after it, where it points, is
# read as no entry at all, whatever it says.
def link_cleared(+name: String, +target: String, +rest: List<&2, Export.Listed>, +hn: {T.all_chars(~(c => Export.line.char(c)), name) == True{} : Bool}, +ht: {T.all_chars(~(c => Export.line.char(c)), target) == True{} : Bool}, ih: {Prune.cached(FL.after(rest), False{}) == digest_files(rest) : List<&2, String>}) -> {Prune.cached(String.split(Export.listed.then(Export.Listed.Link{name, target}, Export.listed.more(rest)), '\n'), False{}) == digest_files(rest) : List<&2, String>}:
  %Equal.sym(List<&2, String>, String.split(name ++ SCon{'\n', target ++ Export.listed.more(rest)}, '\n'), FL.pre_head(name, String.split(SCon{'\n', target ++ Export.listed.more(rest)}, '\n')), FL.split_app(name, SCon{'\n', target ++ Export.listed.more(rest)}, hn)) : {Prune.cached(String.split.push('l', String.split.push(' ', _)), False{}) == digest_files(rest) : List<&2, String>}
  %Equal.sym(String, name ++ SNil{}, name, Eq.app_nil(name)) : {Prune.cached(String.split.push('l', String.split.push(' ', _ <> String.split(target ++ Export.listed.more(rest), '\n'))), False{}) == digest_files(rest) : List<&2, String>}
  %Equal.sym(List<&2, String>, String.split(target ++ Export.listed.more(rest), '\n'), target <> FL.after(rest), FL.split_line(target, rest, ht)) : {Prune.cached(String.split.push('l', String.split.push(' ', name <> _)), False{}) == digest_files(rest) : List<&2, String>}
  %Equal.sym(Bool, String.starts_with(name, ""), True{}, DryL.sw_nil(name)) : {Prune.cached(target <> FL.after(rest), _) == digest_files(rest) : List<&2, String>}
  ih

# A file's line gives its name, whatever its mode and size, and it is
# cleared exactly where that name is a digest.
def file_cleared(runs: Bool, +size: String, +name: String, +rest: List<&2, Export.Listed>, +hs: {T.all_chars(~(c => Export.size.char(c)), size) == True{} : Bool}, +hn: {T.all_chars(~(c => Export.line.char(c)), name) == True{} : Bool}, ih: {Prune.cached(FL.after(rest), False{}) == digest_files(rest) : List<&2, String>}) -> {Prune.cached(String.split(Export.listed.then(Export.Listed.File{runs, size, name}, Export.listed.more(rest)), '\n'), False{}) == Rev.keep(T.is_digest(name), name, digest_files(rest)) : List<&2, String>}:
  match runs:
    case True{}:
      %Equal.sym(List<&2, String>, String.split(size ++ (" " ++ (name ++ Export.listed.more(rest))), '\n'), FL.pre_head(size, String.split(" " ++ (name ++ Export.listed.more(rest)), '\n')), FL.split_app(size, " " ++ (name ++ Export.listed.more(rest)), FL.size_line(size, hs))) : {Prune.cached(String.split.push('f', String.split.push(' ', String.split.push('1', String.split.push(' ', _)))), False{}) == Rev.keep(T.is_digest(name), name, digest_files(rest)) : List<&2, String>}
      %Equal.sym(List<&2, String>, String.split(name ++ Export.listed.more(rest), '\n'), name <> FL.after(rest), FL.split_line(name, rest, hn)) : {Prune.cached(String.split.push('f', String.split.push(' ', String.split.push('1', String.split.push(' ', FL.pre_head(size, String.split.push(' ', _)))))), False{}) == Rev.keep(T.is_digest(name), name, digest_files(rest)) : List<&2, String>}
      %Equal.sym(Maybe<&2, String>, Prune.file.named(T.split_once(size ++ SCon{' ', name})), Some{name}, named_rest(size, name, hs)) : {Prune.digest.push(_, Prune.cached(FL.after(rest), False{})) == Rev.keep(T.is_digest(name), name, digest_files(rest)) : List<&2, String>}
      %Equal.sym(List<&2, String>, Prune.cached(FL.after(rest), False{}), digest_files(rest), ih) : {Rev.keep(T.is_digest(name), name, _) == Rev.keep(T.is_digest(name), name, digest_files(rest)) : List<&2, String>}
      {==}
    case False{}:
      %Equal.sym(List<&2, String>, String.split(size ++ (" " ++ (name ++ Export.listed.more(rest))), '\n'), FL.pre_head(size, String.split(" " ++ (name ++ Export.listed.more(rest)), '\n')), FL.split_app(size, " " ++ (name ++ Export.listed.more(rest)), FL.size_line(size, hs))) : {Prune.cached(String.split.push('f', String.split.push(' ', String.split.push('0', String.split.push(' ', _)))), False{}) == Rev.keep(T.is_digest(name), name, digest_files(rest)) : List<&2, String>}
      %Equal.sym(List<&2, String>, String.split(name ++ Export.listed.more(rest), '\n'), name <> FL.after(rest), FL.split_line(name, rest, hn)) : {Prune.cached(String.split.push('f', String.split.push(' ', String.split.push('0', String.split.push(' ', FL.pre_head(size, String.split.push(' ', _)))))), False{}) == Rev.keep(T.is_digest(name), name, digest_files(rest)) : List<&2, String>}
      %Equal.sym(Maybe<&2, String>, Prune.file.named(T.split_once(size ++ SCon{' ', name})), Some{name}, named_rest(size, name, hs)) : {Prune.digest.push(_, Prune.cached(FL.after(rest), False{})) == Rev.keep(T.is_digest(name), name, digest_files(rest)) : List<&2, String>}
      %Equal.sym(List<&2, String>, Prune.cached(FL.after(rest), False{}), digest_files(rest), ih) : {Rev.keep(T.is_digest(name), name, _) == Rev.keep(T.is_digest(name), name, digest_files(rest)) : List<&2, String>}
      {==}

# Read as `prune` reads it, the listing gives each file named by a digest,
# in order, and nothing else.
def cleared_after(es: List<&2, Export.Listed>, +h: {Export.listed.ok(es) == True{} : Bool}) -> {Prune.cached(FL.after(es), False{}) == digest_files(es) : List<&2, String>}:
  match es:
    case Nil{}:
      {==}
    case e <> +rest:
      match e:
        case Export.Listed.Dir{+name}:
          dir_cleared(name, rest, Comp.and_left(T.all_chars(~(c => Export.line.char(c)), name), Export.listed.ok(rest), h), cleared_after(rest, Comp.and_right(T.all_chars(~(c => Export.line.char(c)), name), Export.listed.ok(rest), h)))
        case Export.Listed.File{runs, +size, +name}:
          +h2 = Comp.and_right(T.all_chars(~(c => Export.size.char(c)), size), Bool.and(T.all_chars(~(c => Export.line.char(c)), name), Export.listed.ok(rest)), h)
          file_cleared(runs, size, name, rest, Comp.and_left(T.all_chars(~(c => Export.size.char(c)), size), Bool.and(T.all_chars(~(c => Export.line.char(c)), name), Export.listed.ok(rest)), h), Comp.and_left(T.all_chars(~(c => Export.line.char(c)), name), Export.listed.ok(rest), h2), cleared_after(rest, Comp.and_right(T.all_chars(~(c => Export.line.char(c)), name), Export.listed.ok(rest), h2)))
        case Export.Listed.Link{+name, +target}:
          +h2 = Comp.and_right(T.all_chars(~(c => Export.line.char(c)), name), Bool.and(T.all_chars(~(c => Export.line.char(c)), target), Export.listed.ok(rest)), h)
          link_cleared(name, target, rest, Comp.and_left(T.all_chars(~(c => Export.line.char(c)), name), Bool.and(T.all_chars(~(c => Export.line.char(c)), target), Export.listed.ok(rest)), h), Comp.and_left(T.all_chars(~(c => Export.line.char(c)), target), Export.listed.ok(rest), h2), cleared_after(rest, Comp.and_right(T.all_chars(~(c => Export.line.char(c)), target), Export.listed.ok(rest), h2)))
        case Export.Listed.Other{+name}:
          other_cleared(name, rest, Comp.and_left(T.all_chars(~(c => Export.line.char(c)), name), Export.listed.ok(rest), h), cleared_after(rest, Comp.and_right(T.all_chars(~(c => Export.line.char(c)), name), Export.listed.ok(rest), h)))

# What `prune` clears from `cache/`, given the host's listing of it, is
# `cache/` and each file of it named by a digest, in order.
def cleared(es: List<&2, Export.Listed>, +h: {Export.listed.ok(es) == True{} : Bool}) -> {Prune.cleared.paths(Export.listing(es)) == T.map(~String, ~String, ~(n => "cache/" ++ n), digest_files(es)) : List<&2, String>}:
  match es:
    case Nil{}:
      {==}
    case +e <> +rest:
      Equal.cong(List<&2, String>, List<&2, String>, l => T.map(~String, ~String, ~(n => "cache/" ++ n), l), Prune.cached(FL.after(e <> rest), False{}), digest_files(e <> rest), cleared_after(e <> rest, h))
