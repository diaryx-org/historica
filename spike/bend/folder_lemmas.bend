# The folder's walk takes nothing a rule skips. The host lists a directory
# a line an entry; reading that listing adds a file, or a link, only where
# no rule skips its path, and a directory to walk next only where no rule
# skips it whole. `walk` reads each directory's listing onto what the last
# left, starting from nothing, so no file it returns is one a rule skips.
import Base
import ./folder.bend as F
import ./text.bend as T
import ./bookmark.bend as Bm
import ./composition_lemmas.bend as Comp
import ./merge_lemmas.bend as ML
import ./anchor_lemmas.bend as AL
import ./target_lemmas.bend as TG

def ok3(a: Bool, b: Bool, -c: Bool, ea: {a == True{} : Bool}, eb: {b == True{} : Bool}, ec: {c == True{} : Bool}) -> {Bool.and(a, Bool.and(b, c)) == True{} : Bool}:
  AL.and_intro(a, Bool.and(b, c), ea, AL.and_intro(b, c, eb, ec))

def linked_ok(+rules: List<&2, F.Scope>, +dirs: List<&2, String>, +found: List<&2, F.Found>, +p: String, +line: String, empty: Bool, ee: {String.is_empty(p) == empty : Bool}, hd: {F.dirs_kept(rules, dirs) == True{} : Bool}, hf: {F.none_skipped(rules, found) == True{} : Bool}, hl: {Bool.or(String.is_empty(p), Bool.not(F.skips(rules, p))) == True{} : Bool}) -> {F.listing.ok(rules, F.listing.linked(dirs, found, p, line, empty)) == True{} : Bool}:
  match empty:
    case True{}:
      ok3(F.dirs_kept(rules, dirs), F.none_skipped(rules, found), True{}, hd, hf, {==})
    case False{}:
      ok3(F.dirs_kept(rules, dirs), F.none_skipped(rules, F.Found.Link{p, line} <> found), True{}, hd,
        AL.and_intro(Bool.not(F.skips(rules, p)), F.none_skipped(rules, found), ML.or_left_false(String.is_empty(p), Bool.not(F.skips(rules, p)), hl, ee), hf),
        {==})

def dir_ok(+rules: List<&2, F.Scope>, +dirs: List<&2, String>, +found: List<&2, F.Found>, +prefix: String, +name: String, skip: Bool, es: {Bool.or(F.is_store(prefix, name), F.skips_directory(rules, F.joined(prefix, name))) == skip : Bool}, hd: {F.dirs_kept(rules, dirs) == True{} : Bool}, hf: {F.none_skipped(rules, found) == True{} : Bool}) -> {F.listing.ok(rules, F.listing.dir(dirs, found, prefix, rules, name, skip)) == True{} : Bool}:
  match skip:
    case True{}:
      ok3(F.dirs_kept(rules, dirs), F.none_skipped(rules, found), True{}, hd, hf, {==})
    case False{}:
      ok3(F.dirs_kept(rules, F.joined(prefix, name) <> dirs), F.none_skipped(rules, found), True{},
        AL.and_intro(Bool.not(F.skips_directory(rules, F.joined(prefix, name))), F.dirs_kept(rules, dirs), AL.not_true(F.skips_directory(rules, F.joined(prefix, name)), AL.or_false_r(F.is_store(prefix, name), F.skips_directory(rules, F.joined(prefix, name)), es)), hd),
        hf, {==})

# A file is taken only where `tracked` says so, which asks the rules first.
def took_ok(+rules: List<&2, F.Scope>, +dirs: List<&2, String>, +found: List<&2, F.Found>, +prefix: String, +runs: Bool, +size: String, +name: String, take: Bool, et: {F.tracked(prefix, name, rules) == take : Bool}, hd: {F.dirs_kept(rules, dirs) == True{} : Bool}, hf: {F.none_skipped(rules, found) == True{} : Bool}) -> {F.listing.ok(rules, F.listing.took(dirs, found, prefix, runs, size, name, take)) == True{} : Bool}:
  match take:
    case True{}:
      ok3(F.dirs_kept(rules, dirs), F.none_skipped(rules, F.Found.File{F.joined(prefix, name), runs, Maybe.default(&2, Nat, Nat.read(size), 0n)} <> found), True{}, hd,
        AL.and_intro(Bool.not(F.skips(rules, F.joined(prefix, name))), F.none_skipped(rules, found),
          Comp.and_left(Bool.not(F.skips(rules, F.joined(prefix, name))), Bm.name_ok(F.joined(prefix, name)), Comp.and_right(Bool.not(F.is_store(prefix, name)), Bool.and(Bool.not(F.skips(rules, F.joined(prefix, name))), Bm.name_ok(F.joined(prefix, name))), et)),
          hf),
        {==})
    case False{}:
      ok3(F.dirs_kept(rules, dirs), F.none_skipped(rules, found), True{}, hd, hf, {==})

def file_ok(+rules: List<&2, F.Scope>, +dirs: List<&2, String>, +found: List<&2, F.Found>, +prefix: String, +runs: Bool, cut: Maybe<&2, T.Split>, hd: {F.dirs_kept(rules, dirs) == True{} : Bool}, hf: {F.none_skipped(rules, found) == True{} : Bool}) -> {F.listing.ok(rules, F.listing.file(dirs, found, prefix, rules, runs, cut)) == True{} : Bool}:
  match cut:
    case None{}:
      ok3(F.dirs_kept(rules, dirs), F.none_skipped(rules, found), True{}, hd, hf, {==})
    case Some{T.Split{+size, +name}}:
      took_ok(rules, dirs, found, prefix, runs, size, name, F.tracked(prefix, name, rules), {==}, hd, hf)

def link_ok(+rules: List<&2, F.Scope>, +dirs: List<&2, String>, +found: List<&2, F.Found>, +prefix: String, +name: String, take: Bool, et: {F.tracked(prefix, name, rules) == take : Bool}, hd: {F.dirs_kept(rules, dirs) == True{} : Bool}, hf: {F.none_skipped(rules, found) == True{} : Bool}) -> {F.listing.ok(rules, F.listing.link(dirs, found, prefix, name, take)) == True{} : Bool}:
  match take:
    case True{}:
      ok3(F.dirs_kept(rules, dirs), F.none_skipped(rules, found), Bool.or(String.is_empty(F.joined(prefix, name)), Bool.not(F.skips(rules, F.joined(prefix, name)))), hd, hf,
        AL.or_right(String.is_empty(F.joined(prefix, name)), Bool.not(F.skips(rules, F.joined(prefix, name))),
          Comp.and_left(Bool.not(F.skips(rules, F.joined(prefix, name))), Bm.name_ok(F.joined(prefix, name)), Comp.and_right(Bool.not(F.is_store(prefix, name)), Bool.and(Bool.not(F.skips(rules, F.joined(prefix, name))), Bm.name_ok(F.joined(prefix, name))), et))))
    case False{}:
      ok3(F.dirs_kept(rules, dirs), F.none_skipped(rules, found), True{}, hd, hf, {==})

def kind_ok(+rules: List<&2, F.Scope>, +dirs: List<&2, String>, +found: List<&2, F.Found>, +prefix: String, +name: String, d: Bool, f: Bool, l: Bool, hd: {F.dirs_kept(rules, dirs) == True{} : Bool}, hf: {F.none_skipped(rules, found) == True{} : Bool}) -> {F.listing.ok(rules, F.listing.kind(dirs, found, prefix, rules, name, d, f, l)) == True{} : Bool}:
  match d:
    case True{}:
      dir_ok(rules, dirs, found, prefix, name, Bool.or(F.is_store(prefix, name), F.skips_directory(rules, F.joined(prefix, name))), {==}, hd, hf)
    case False{}:
      match f:
        case True{}:
          file_ok(rules, dirs, found, prefix, String.starts_with(name, "1"), T.split_once(String.drop(name, 2n)), hd, hf)
        case False{}:
          match l:
            case True{}:
              link_ok(rules, dirs, found, prefix, name, F.tracked(prefix, name, rules), {==}, hd, hf)
            case False{}:
              ok3(F.dirs_kept(rules, dirs), F.none_skipped(rules, found), True{}, hd, hf, {==})

def line_ok(l: F.Listing, +prefix: String, +rules: List<&2, F.Scope>, +line: String, +h: {F.listing.ok(rules, l) == True{} : Bool}) -> {F.listing.ok(rules, F.listing.line(l, prefix, rules, line)) == True{} : Bool}:
  match l:
    case F.Listing{+dirs, +found, Some{+p}}:
      linked_ok(rules, dirs, found, p, line, String.is_empty(p), {==},
        Comp.and_left(F.dirs_kept(rules, dirs), Bool.and(F.none_skipped(rules, found), F.link_kept(rules, Some{p})), h),
        Comp.and_left(F.none_skipped(rules, found), F.link_kept(rules, Some{p}), Comp.and_right(F.dirs_kept(rules, dirs), Bool.and(F.none_skipped(rules, found), F.link_kept(rules, Some{p})), h)),
        Comp.and_right(F.none_skipped(rules, found), F.link_kept(rules, Some{p}), Comp.and_right(F.dirs_kept(rules, dirs), Bool.and(F.none_skipped(rules, found), F.link_kept(rules, Some{p})), h)))
    case F.Listing{+dirs, +found, None{}}:
      kind_ok(rules, dirs, found, prefix, String.drop(line, 2n), String.eq(String.take(line, 1n), "d"), String.eq(String.take(line, 1n), "f"), String.eq(String.take(line, 1n), "l"),
        Comp.and_left(F.dirs_kept(rules, dirs), Bool.and(F.none_skipped(rules, found), True{}), h),
        Comp.and_left(F.none_skipped(rules, found), True{}, Comp.and_right(F.dirs_kept(rules, dirs), Bool.and(F.none_skipped(rules, found), True{}), h)))

def listing_ok(ls: List<&2, String>, +prefix: String, +rules: List<&2, F.Scope>, +l: F.Listing, h: {F.listing.ok(rules, l) == True{} : Bool}) -> {F.listing.ok(rules, F.listing.go(ls, prefix, rules, l)) == True{} : Bool}:
  match ls:
    case Nil{}:
      h
    case +line <> rest:
      listing_ok(rest, prefix, rules, F.listing.line(l, prefix, rules, line), line_ok(l, prefix, rules, line, h))

# The rules a file states
# -----------------------

def sdisc(r: Result<&2, &2, String, F.Scope>) -> Type:
  match r:
    case Done{x}:
      Empty
    case Fail{e}:
      Unit

def sfail(-e: String, -x: F.Scope, h: {Fail{e} == Done{x} : Result<&2, &2, String, F.Scope>}) -> Empty:
  %h : {sdisc(_) : Type}
  Unit{}

def sdone(-a: F.Scope, -b: F.Scope, h: {Done{a} == Done{b} : Result<&2, &2, String, F.Scope>}) -> {a == b : F.Scope}:
  Equal.cong(Result<&2, &2, String, F.Scope>, F.Scope, r => Result.default(&2, &2, String, F.Scope, r, a), Done{a}, Done{b}, h)

def pat_ok(+v: String, a: Bool, ea: {String.is_empty(v) == a : Bool}, b: Bool, eb: {F.has_slash(v) == b : Bool}, c: Bool, ec: {F.all_stars(v) == c : Bool}, +p: String, e: {Bool.pick(Result<&2, &2, String, String>, a, Fail{"a pattern is not empty"}, Bool.pick(Result<&2, &2, String, String>, b, Fail{"a pattern is one path component and holds no `/`: a path is spelled with `skip`"}, Bool.pick(Result<&2, &2, String, String>, c, Fail{"a pattern of nothing but `*` is the whole folder, which rules exist to name the exceptions to"}, Done{v}))) == Done{p} : Result<&2, &2, String, String>}) -> {Bool.and(Bool.not(String.is_empty(p)), Bool.and(Bool.not(F.has_slash(p)), Bool.not(F.all_stars(p)))) == True{} : Bool}:
  match a:
    case True{}:
      Empty.absurd({Bool.and(Bool.not(String.is_empty(p)), Bool.and(Bool.not(F.has_slash(p)), Bool.not(F.all_stars(p)))) == True{} : Bool}, TG.fail_done("a pattern is not empty", p, e))
    case False{}:
      match b:
        case True{}:
          Empty.absurd({Bool.and(Bool.not(String.is_empty(p)), Bool.and(Bool.not(F.has_slash(p)), Bool.not(F.all_stars(p)))) == True{} : Bool}, TG.fail_done("a pattern is one path component and holds no `/`: a path is spelled with `skip`", p, e))
        case False{}:
          match c:
            case True{}:
              Empty.absurd({Bool.and(Bool.not(String.is_empty(p)), Bool.and(Bool.not(F.has_slash(p)), Bool.not(F.all_stars(p)))) == True{} : Bool}, TG.fail_done("a pattern of nothing but `*` is the whole folder, which rules exist to name the exceptions to", p, e))
            case False{}:
              (%TG.done_eq(v, p, e) : {Bool.and(Bool.not(String.is_empty(_)), Bool.and(Bool.not(F.has_slash(_)), Bool.not(F.all_stars(_)))) == True{} : Bool}
                (%Equal.sym(Bool, String.is_empty(v), False{}, ea) : {Bool.and(Bool.not(_), Bool.and(Bool.not(F.has_slash(v)), Bool.not(F.all_stars(v)))) == True{} : Bool}
                  (%Equal.sym(Bool, F.has_slash(v), False{}, eb) : {Bool.and(True{}, Bool.and(Bool.not(_), Bool.not(F.all_stars(v)))) == True{} : Bool}
                    (%Equal.sym(Bool, F.all_stars(v), False{}, ec) : {Bool.and(True{}, Bool.and(True{}, Bool.not(_))) == True{} : Bool}
                      {==}))))

def pattern_ok(+v: String, +p: String, e: {F.pattern(v) == Done{p} : Result<&2, &2, String, String>}) -> {Bool.and(Bool.not(String.is_empty(p)), Bool.and(Bool.not(F.has_slash(p)), Bool.not(F.all_stars(p)))) == True{} : Bool}:
  pat_ok(v, String.is_empty(v), {==}, F.has_slash(v), {==}, F.all_stars(v), {==}, p, e)

def named_under(r: Result<&2, &2, String, String>, +v: String, er: {F.pattern(v) == r : Result<&2, &2, String, String>}, -sc: F.Scope, e: {Result.map(&2, &2, String, String, F.Scope, p => F.Scope.NameUnder{p}, r) == Done{sc} : Result<&2, &2, String, F.Scope>}) -> {F.scope.ok(sc) == True{} : Bool}:
  match r:
    case Fail{m}:
      Empty.absurd({F.scope.ok(sc) == True{} : Bool}, sfail(m, sc, e))
    case Done{+p}:
      (%sdone(F.Scope.NameUnder{p}, sc, e) : {F.scope.ok(_) == True{} : Bool}
        pattern_ok(v, p, er))

def named_plain(r: Result<&2, &2, String, String>, +v: String, er: {F.pattern(v) == r : Result<&2, &2, String, String>}, -sc: F.Scope, e: {Result.map(&2, &2, String, String, F.Scope, p => F.Scope.Name{p}, r) == Done{sc} : Result<&2, &2, String, F.Scope>}) -> {F.scope.ok(sc) == True{} : Bool}:
  match r:
    case Fail{m}:
      Empty.absurd({F.scope.ok(sc) == True{} : Bool}, sfail(m, sc, e))
    case Done{+p}:
      (%sdone(F.Scope.Name{p}, sc, e) : {F.scope.ok(_) == True{} : Bool}
        pattern_ok(v, p, er))

def of_ok(+bare: String, name: Bool, u: Bool, +en: {String.is_empty(bare) == False{} : Bool}, -sc: F.Scope, e: {F.scope.of(bare, name, u) == Done{sc} : Result<&2, &2, String, F.Scope>}) -> {F.scope.ok(sc) == True{} : Bool}:
  match name:
    case False{}:
      match u:
        case True{}:
          (%sdone(F.Scope.Under{bare}, sc, e) : {F.scope.ok(_) == True{} : Bool}
            (%Equal.sym(Bool, String.is_empty(bare), False{}, en) : {Bool.not(_) == True{} : Bool}
              {==}))
        case False{}:
          (%sdone(F.Scope.Path{bare}, sc, e) : {F.scope.ok(_) == True{} : Bool}
            (%Equal.sym(Bool, String.is_empty(bare), False{}, en) : {Bool.not(_) == True{} : Bool}
              {==}))
    case True{}:
      match u:
        case True{}:
          named_under(F.pattern(bare), bare, {==}, sc, e)
        case False{}:
          named_plain(F.pattern(bare), bare, {==}, sc, e)

def val_at(+bare: String, b: Bool, eb: {String.is_empty(bare) == b : Bool}, name: Bool, u: Bool, -sc: F.Scope, e: {Bool.pick(Result<&2, &2, String, F.Scope>, b, Fail{F.value_error()}, F.scope.of(bare, name, u)) == Done{sc} : Result<&2, &2, String, F.Scope>}) -> {F.scope.ok(sc) == True{} : Bool}:
  match b:
    case True{}:
      Empty.absurd({F.scope.ok(sc) == True{} : Bool}, sfail(F.value_error(), sc, e))
    case False{}:
      of_ok(bare, name, u, eb, sc, e)

def value_ok(+v: String, name: Bool, -sc: F.Scope, e: {F.scope.value(v, name) == Done{sc} : Result<&2, &2, String, F.Scope>}) -> {F.scope.ok(sc) == True{} : Bool}:
  val_at(F.trim_slashes(String.reverse(v)), String.is_empty(F.trim_slashes(String.reverse(v))), {==}, name, String.ends_with(v, "/"), sc, e)

def keyed_ok(+v: String, path: Bool, name: Bool, retired: Bool, -sc: F.Scope, e: {F.scope.keyed(v, path, name, retired) == Done{sc} : Result<&2, &2, String, F.Scope>}) -> {F.scope.ok(sc) == True{} : Bool}:
  match path:
    case True{}:
      value_ok(v, False{}, sc, e)
    case False{}:
      match name:
        case True{}:
          value_ok(v, True{}, sc, e)
        case False{}:
          match retired:
            case True{}:
              Empty.absurd({F.scope.ok(sc) == True{} : Bool}, sfail("`skip-suffix` is retired: an ending is now `skip-name *` and the ending, matched against a file's own name", sc, e))
            case False{}:
              Empty.absurd({F.scope.ok(sc) == True{} : Bool}, sfail("the keys are `skip`, `skip-name`, `private` and `private-name`", sc, e))

def trimmed_ok(+k: String, +v: String, t: Bool, -sc: F.Scope, e: {Bool.pick(Result<&2, &2, String, F.Scope>, t, Fail{F.value_error()}, F.scope.key(k, v)) == Done{sc} : Result<&2, &2, String, F.Scope>}) -> {F.scope.ok(sc) == True{} : Bool}:
  match t:
    case True{}:
      Empty.absurd({F.scope.ok(sc) == True{} : Bool}, sfail(F.value_error(), sc, e))
    case False{}:
      keyed_ok(v, Bool.or(String.eq(k, "skip"), String.eq(k, "private")), Bool.or(String.eq(k, "skip-name"), String.eq(k, "private-name")), String.eq(k, "skip-suffix"), sc, e)

def cut_ok(cut: Maybe<&2, T.Split>, -sc: F.Scope, e: {F.scope.cut(cut) == Done{sc} : Result<&2, &2, String, F.Scope>}) -> {F.scope.ok(sc) == True{} : Bool}:
  match cut:
    case None{}:
      Empty.absurd({F.scope.ok(sc) == True{} : Bool}, sfail(F.line_error(), sc, e))
    case Some{T.Split{+k, +v}}:
      trimmed_ok(k, v, F.untrimmed(v), sc, e)

def said_ok_of(sd: F.Said) -> Bool:
  match sd:
    case F.Said.Rule{sc}:
      F.scope.ok(sc)
    case F.Said.Nothing{}:
      True{}
    case F.Said.Wrong{e}:
      True{}

def said_of(r: Result<&2, &2, String, F.Scope>, +line: String, er: {F.scope(line) == r : Result<&2, &2, String, F.Scope>}) -> {said_ok_of(F.said.of(r)) == True{} : Bool}:
  match r:
    case Fail{e}:
      {==}
    case Done{sc}:
      cut_ok(T.split_once(line), sc, er)

def said_at(+line: String, b: Bool) -> {said_ok_of(Bool.pick(F.Said, b, F.Said.Nothing{}, F.said.of(F.scope(line)))) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      said_of(F.scope(line), line, {==})

def said_ok(+line: String) -> {said_ok_of(F.said(line)) == True{} : Bool}:
  said_at(line, Bool.or(String.is_empty(line), String.starts_with(line, "#")))

def stated_line_ok(st: F.Stated, +at: Nat, sd: F.Said, hs: {F.stated.ok(st) == True{} : Bool}, hd: {said_ok_of(sd) == True{} : Bool}) -> {F.stated.ok(F.stated.line(st, at, sd)) == True{} : Bool}:
  match st sd:
    case F.Stated.Wrong{e} F.Said.Nothing{}:
      {==}
    case F.Stated.Wrong{e} F.Said.Rule{sc}:
      {==}
    case F.Stated.Wrong{e} F.Said.Wrong{e2}:
      {==}
    case F.Stated.None{} F.Said.Nothing{}:
      {==}
    case F.Stated.None{} F.Said.Rule{sc}:
      hd
    case F.Stated.None{} F.Said.Wrong{e2}:
      {==}
    case F.Stated.One{sc} F.Said.Nothing{}:
      hs
    case F.Stated.One{sc} F.Said.Rule{sc2}:
      {==}
    case F.Stated.One{sc} F.Said.Wrong{e2}:
      {==}

def stated_go_ok(ls: List<&2, String>, +at: Nat, +st: F.Stated, h: {F.stated.ok(st) == True{} : Bool}) -> {F.stated.ok(F.stated.go(ls, at, st)) == True{} : Bool}:
  match ls:
    case Nil{}:
      h
    case +l <> rest:
      stated_go_ok(rest, 1n+at, F.stated.line(st, at, F.said(l)), stated_line_ok(st, at, F.said(l), h, said_ok(l)))

# Every rule a file states is well formed.
def rules_ok(+text: String) -> {F.stated.ok(F.rule_in(text)) == True{} : Bool}:
  stated_go_ok(F.lines.trimmed(String.split(text, '\n')), 1n, F.Stated.None{}, {==})
