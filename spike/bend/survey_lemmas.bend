# What `status` says. A rule in `skipped/` silences a path, so the walk
# refuses none a rule skips: each listing line is refused only after the
# rules are asked, and a refusal names the path that was asked about. And a
# file arriving carries its content, mode and target in with it, so the
# only lines that name it are `added` and, where a file of another kind
# stood there, `dropped`: every other line is filtered by the arrivals.
import Base
import ./folder.bend as F
import ./survey.bend as Sv
import ./text.bend as T
import ./tree.bend as Tree
import ./revision.bend as Rev
import ./commands.bend as Main
import ./blamed_lemmas.bend as Blamed
import ./anchor_lemmas.bend as AL
import ./string_lemmas.bend as S
import ./composition_lemmas.bend as Comp
import ./sort_lemmas.bend as SortL
import ./pair_lemmas.bend as PairL
import ./naming_lemmas.bend as NamingL
import ./naming.bend as Naming
import ./name_lemmas.bend as NameL
import ./map_lemmas.bend as ML

# The walk's refusals
# -------------------

def spelled_ok(+rules: List<&2, F.Scope>, +path: String, fault: Maybe<&2, String>, unreadable: Bool, e: {F.skips(rules, path) == False{} : Bool}) -> {F.refusal_ok(rules, F.refusal.spelled(path, fault, unreadable)) == True{} : Bool}:
  match fault:
    case Some{because}:
      AL.not_true(F.skips(rules, path), e)
    case None{}:
      match unreadable:
        case True{}:
          AL.not_true(F.skips(rules, path), e)
        case False{}:
          {==}

def kind_ok(+rules: List<&2, F.Scope>, +path: String, other: Bool, unreadable: Bool, e: {F.skips(rules, path) == False{} : Bool}) -> {F.refusal_ok(rules, F.refusal.kind(path, other, unreadable)) == True{} : Bool}:
  match other:
    case True{}:
      AL.not_true(F.skips(rules, path), e)
    case False{}:
      spelled_ok(rules, path, F.path_fault(path), unreadable, e)

# Asked of the rules first: a path one skips is never refused.
def of_pick(+rules: List<&2, F.Scope>, +prefix: String, +name: String, other: Bool, unreadable: Bool, c: Bool, ec: {Bool.or(F.is_store(prefix, name), F.skips(rules, F.joined(prefix, name))) == c : Bool}) -> {F.refusal_ok(rules, Bool.pick(Maybe<&2, T.Split>, c, None{}, F.refusal.kind(F.joined(prefix, name), other, unreadable))) == True{} : Bool}:
  match c:
    case True{}:
      {==}
    case False{}:
      kind_ok(rules, F.joined(prefix, name), other, unreadable, AL.or_false_r(F.is_store(prefix, name), F.skips(rules, F.joined(prefix, name)), ec))

def of_ok(+rules: List<&2, F.Scope>, +prefix: String, +name: String, other: Bool, unreadable: Bool) -> {F.refusal_ok(rules, F.refusal.of(prefix, rules, name, other, unreadable)) == True{} : Bool}:
  of_pick(rules, prefix, name, other, unreadable, Bool.or(F.is_store(prefix, name), F.skips(rules, F.joined(prefix, name))), {==})

def file_ok(+rules: List<&2, F.Scope>, +prefix: String, cut: Maybe<&2, T.Split>) -> {F.refusal_ok(rules, F.refusal.file(prefix, rules, cut)) == True{} : Bool}:
  match cut:
    case None{}:
      {==}
    case Some{T.Split{size, +name}}:
      of_ok(rules, prefix, name, False{}, False{})

def line_pick(+rules: List<&2, F.Scope>, a: Bool, b: Bool, c: Bool, -x: Maybe<&2, T.Split>, -y: Maybe<&2, T.Split>, -z: Maybe<&2, T.Split>, hx: {F.refusal_ok(rules, x) == True{} : Bool}, hy: {F.refusal_ok(rules, y) == True{} : Bool}, hz: {F.refusal_ok(rules, z) == True{} : Bool}) -> {F.refusal_ok(rules, Bool.pick(Maybe<&2, T.Split>, a, x, Bool.pick(Maybe<&2, T.Split>, b, y, Bool.pick(Maybe<&2, T.Split>, c, z, None{})))) == True{} : Bool}:
  match a:
    case True{}:
      hx
    case False{}:
      match b:
        case True{}:
          hy
        case False{}:
          match c:
            case True{}:
              hz
            case False{}:
              {==}

def line_ok(+rules: List<&2, F.Scope>, +prefix: String, +line: String) -> {F.refusal_ok(rules, F.refusal.line(prefix, rules, line)) == True{} : Bool}:
  line_pick(rules, String.eq(String.take(line, 1n), "f"), Bool.or(String.eq(String.take(line, 1n), "l"), String.eq(String.take(line, 1n), "L")), String.eq(String.take(line, 1n), "o"),
    F.refusal.file(prefix, rules, T.split_once(String.drop(String.drop(line, 2n), 2n))),
    F.refusal.of(prefix, rules, String.drop(line, 2n), False{}, String.eq(String.take(line, 1n), "L")),
    F.refusal.of(prefix, rules, String.drop(line, 2n), True{}, False{}),
    file_ok(rules, prefix, T.split_once(String.drop(String.drop(line, 2n), 2n))),
    of_ok(rules, prefix, String.drop(line, 2n), False{}, String.eq(String.take(line, 1n), "L")),
    of_ok(rules, prefix, String.drop(line, 2n), True{}, False{}))

def push_ok(+rules: List<&2, F.Scope>, r: Maybe<&2, T.Split>, +rest: List<&2, T.Split>, hr: {F.refusal_ok(rules, r) == True{} : Bool}, hrest: {F.refused_kept(rules, rest) == True{} : Bool}) -> {F.refused_kept(rules, F.refusal.push(r, rest)) == True{} : Bool}:
  match r:
    case None{}:
      hrest
    case Some{T.Split{+p, b}}:
      AL.and_intro(Bool.not(F.skips(rules, p)), F.refused_kept(rules, rest), hr, hrest)

def refusals_ok(ls: List<&2, String>, +prefix: String, +rules: List<&2, F.Scope>, after: Bool, +acc: List<&2, T.Split>, h: {F.refused_kept(rules, acc) == True{} : Bool}) -> {F.refused_kept(rules, F.refusals.go(ls, prefix, rules, after, acc)) == True{} : Bool}:
  match ls after:
    case Nil{} _:
      h
    case line <> rest True{}:
      refusals_ok(rest, prefix, rules, False{}, acc, h)
    case +line <> rest False{}:
      refusals_ok(rest, prefix, rules, String.eq(String.take(line, 1n), "l"), F.refusal.push(F.refusal.line(prefix, rules, line), acc),
        push_ok(rules, F.refusal.line(prefix, rules, line), acc, line_ok(rules, prefix, line), h))

# One line an arrival
# -------------------

def app_ok(+s: Set(), xs: List<&2, T.Split>, +ys: List<&2, T.Split>, +hx: {Sv.arrives_once(s, xs) == True{} : Bool}, hy: {Sv.arrives_once(s, ys) == True{} : Bool}) -> {Sv.arrives_once(s, List.append(&2, T.Split, xs, ys)) == True{} : Bool}:
  match xs:
    case Nil{}:
      hy
    case T.Split{+k, +p} <> rest:
      AL.and_intro(Bool.or(String.eq(k, "added"), Bool.or(String.eq(k, "dropped"), Bool.not(Sv.has(s, p)))), Sv.arrives_once(s, List.append(&2, T.Split, rest, ys)),
        Comp.and_left(Bool.or(String.eq(k, "added"), Bool.or(String.eq(k, "dropped"), Bool.not(Sv.has(s, p)))), Sv.arrives_once(s, rest), hx),
        app_ok(s, rest, ys, Comp.and_right(Bool.or(String.eq(k, "added"), Bool.or(String.eq(k, "dropped"), Bool.not(Sv.has(s, p)))), Sv.arrives_once(s, rest), hx), hy))

# An `added` line and a `dropped` line are what they say.
def added_ok(+s: Set(), ps: List<&2, String>) -> {Sv.arrives_once(s, Sv.fact("added", ps)) == True{} : Bool}:
  match ps:
    case Nil{}:
      {==}
    case p <> rest:
      added_ok(s, rest)

def dropped_ok(+s: Set(), ps: List<&2, String>) -> {Sv.arrives_once(s, Sv.fact("dropped", ps)) == True{} : Bool}:
  match ps:
    case Nil{}:
      {==}
    case p <> rest:
      dropped_ok(s, rest)

# Every other line was filtered by the arrivals.
def or2(+a: Bool, +b: Bool, +c: Bool, e: {c == True{} : Bool}) -> {Bool.or(a, Bool.or(b, c)) == True{} : Bool}:
  AL.or_right(a, Bool.or(b, c), AL.or_right(b, c, e))

def pick_ok(+s: Set(), +k: String, c: Bool, +x: String, +later: List<&2, String>, ec: {Sv.has(s, x) == c : Bool}, h: {Sv.arrives_once(s, Sv.fact(k, later)) == True{} : Bool}) -> {Sv.arrives_once(s, Sv.fact(k, Sv.without.pick(c, x, later))) == True{} : Bool}:
  match c:
    case True{}:
      h
    case False{}:
      AL.and_intro(Bool.or(String.eq(k, "added"), Bool.or(String.eq(k, "dropped"), Bool.not(Sv.has(s, x)))), Sv.arrives_once(s, Sv.fact(k, later)),
        or2(String.eq(k, "added"), String.eq(k, "dropped"), Bool.not(Sv.has(s, x)), AL.not_true(Sv.has(s, x), ec)), h)

def without_ok(+s: Set(), +k: String, +xs: List<&2, String>) -> {Sv.arrives_once(s, Sv.fact(k, Sv.without(xs, s))) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      pick_ok(s, k, Sv.has(s, x), x, Sv.without(rest, s), {==}, without_ok(s, k, rest))

def facts_ok(+s: Set(), +os: List<&2, Sv.Obs>, +links: List<&2, String>) -> {Sv.arrives_once(s, Sv.facts.with(s, os, links)) == True{} : Bool}:
  app_ok(s, Sv.fact("added", Sv.sorted(Sv.added(os))), List.append(&2, T.Split, Sv.fact("dropped", Sv.sorted(Sv.dropped_paths(os))), List.append(&2, T.Split, Sv.fact("edited", Sv.without(Sv.sorted(Sv.edited(os)), s)), List.append(&2, T.Split, Sv.fact("mode", Sv.without(Sv.sorted(Sv.modes(os)), s)), Sv.fact("link", Sv.without(Sv.sorted(links), s))))),
    added_ok(s, Sv.sorted(Sv.added(os))),
    app_ok(s, Sv.fact("dropped", Sv.sorted(Sv.dropped_paths(os))), List.append(&2, T.Split, Sv.fact("edited", Sv.without(Sv.sorted(Sv.edited(os)), s)), List.append(&2, T.Split, Sv.fact("mode", Sv.without(Sv.sorted(Sv.modes(os)), s)), Sv.fact("link", Sv.without(Sv.sorted(links), s)))),
      dropped_ok(s, Sv.sorted(Sv.dropped_paths(os))),
      app_ok(s, Sv.fact("edited", Sv.without(Sv.sorted(Sv.edited(os)), s)), List.append(&2, T.Split, Sv.fact("mode", Sv.without(Sv.sorted(Sv.modes(os)), s)), Sv.fact("link", Sv.without(Sv.sorted(links), s))),
        without_ok(s, "edited", Sv.sorted(Sv.edited(os))),
        app_ok(s, Sv.fact("mode", Sv.without(Sv.sorted(Sv.modes(os)), s)), Sv.fact("link", Sv.without(Sv.sorted(links), s)),
          without_ok(s, "mode", Sv.sorted(Sv.modes(os))),
          without_ok(s, "link", Sv.sorted(links))))))

# A link left dangling
# --------------------

# Where the link names a file going, `record` refuses; where it names
# anything else, it goes on to the next.
def gone_pick(h: Bool, -msg: String, -later: Maybe<&2, String>, -rest: Bool, ih: {Maybe.is_none(&2, String, later) == rest : Bool}) -> {Maybe.is_none(&2, String, Bool.pick(Maybe<&2, String>, h, Some{msg}, later)) == Bool.and(Bool.not(h), rest) : Bool}:
  match h:
    case True{}:
      {==}
    case False{}:
      ih

def target_ok(+link: String, g: Maybe<&2, Tree.Target>, +gone: Set(), +os: List<&2, Sv.Obs>, -later: Maybe<&2, String>, -rest: Bool, ih: {Maybe.is_none(&2, String, later) == rest : Bool}) -> {Maybe.is_none(&2, String, Sv.dangle.target(link, g, gone, os, later)) == Bool.and(Bool.not(Sv.names_gone(g, gone)), rest) : Bool}:
  match g:
    case None{}:
      ih
    case Some{Tree.Reference{+named}}:
      gone_pick(Sv.has(gone, named), "`" ++ Sv.dropped_at(os, named) ++ "` is going, and `" ++ link ++ "` is a link to it that this record is not looking at; name `" ++ link ++ "` too, so its target can be written down as the string it will be", later, rest, ih)
    case Some{Tree.Verbatim{s}}:
      ih

def dangle_pick(c: Bool, +link: String, g: Maybe<&2, Tree.Target>, +gone: Set(), +os: List<&2, Sv.Obs>, -later: Maybe<&2, String>, -rest: Bool, ih: {Maybe.is_none(&2, String, later) == rest : Bool}) -> {Maybe.is_none(&2, String, Bool.pick(Maybe<&2, String>, c, later, Sv.dangle.target(link, g, gone, os, later))) == Bool.and(Bool.or(c, Bool.not(Sv.names_gone(g, gone))), rest) : Bool}:
  match c:
    case True{}:
      ih
    case False{}:
      target_ok(link, g, gone, os, later, rest, ih)

def dangle_ok(t: Tree.Tree(), +gone: Set(), +pointing: Set(), +os: List<&2, Sv.Obs>) -> {Maybe.is_none(&2, String, Sv.dangle(t, gone, pointing, os)) == Sv.anchored(t, gone, pointing) : Bool}:
  match t:
    case Nil{}:
      {==}
    case Tree.Entry{+f, +p, k, y, g, m} <> rest:
      dangle_pick(Bool.or(Sv.has(gone, f), Sv.has(pointing, p)), p, g, gone, os, Sv.dangle(rest, gone, pointing, os), Sv.anchored(rest, gone, pointing), dangle_ok(rest, gone, pointing, os))

# What `status` refuses
# ---------------------

def refusals_app(xs: List<&2, Sv.Obs>, +ys: List<&2, Sv.Obs>) -> {Sv.refusals(List.append(&2, Sv.Obs, xs, ys)) == List.append(&2, T.Split, Sv.refusals(xs), Sv.refusals(ys)) : List<&2, T.Split>}:
  match xs:
    case Nil{}:
      {==}
    case Sv.Obs.Refused{+p, +why} <> rest:
      %refusals_app(rest, ys) : {T.Split{p, why} <> Sv.refusals(List.append(&2, Sv.Obs, rest, ys)) == T.Split{p, why} <> _ : List<&2, T.Split>}
      {==}
    case Sv.Obs.Added{p} <> rest:
      refusals_app(rest, ys)
    case Sv.Obs.Dropped{f, p, c} <> rest:
      refusals_app(rest, ys)
    case Sv.Obs.Edited{p} <> rest:
      refusals_app(rest, ys)
    case Sv.Obs.Mode{p} <> rest:
      refusals_app(rest, ys)
    case Sv.Obs.Accept{p} <> rest:
      refusals_app(rest, ys)
    case Sv.Obs.Points{p, g, h, s} <> rest:
      refusals_app(rest, ys)
    case Sv.Obs.Arrived{p, d} <> rest:
      refusals_app(rest, ys)
    case Sv.Obs.Emptied{p} <> rest:
      refusals_app(rest, ys)
    case Sv.Obs.Marked{p, n} <> rest:
      refusals_app(rest, ys)

# Every refusal names a path some surveyed path found in the folder.
def found_all(+ss: List<&2, Sv.Seen>, rs: List<&2, T.Split>) -> Bool:
  match rs:
    case Nil{}:
      True{}
    case T.Split{+p, b} <> rest:
      Bool.and(Sv.found_at(ss, p), found_all(ss, rest))

def found_app(+ss: List<&2, Sv.Seen>, xs: List<&2, T.Split>, +ys: List<&2, T.Split>, +hx: {found_all(ss, xs) == True{} : Bool}, hy: {found_all(ss, ys) == True{} : Bool}) -> {found_all(ss, List.append(&2, T.Split, xs, ys)) == True{} : Bool}:
  match xs:
    case Nil{}:
      hy
    case T.Split{+p, b} <> rest:
      AL.and_intro(Sv.found_at(ss, p), found_all(ss, List.append(&2, T.Split, rest, ys)),
        Comp.and_left(Sv.found_at(ss, p), found_all(ss, rest), hx),
        found_app(ss, rest, ys, Comp.and_right(Sv.found_at(ss, p), found_all(ss, rest), hx), hy))

def found_weaken(rs: List<&2, T.Split>, +s: Sv.Seen, +rest: List<&2, Sv.Seen>, +h: {found_all(rest, rs) == True{} : Bool}) -> {found_all(s <> rest, rs) == True{} : Bool}:
  match rs:
    case Nil{}:
      {==}
    case T.Split{+p, b} <> more:
      match s:
        case Sv.Seen{+path, +e, +found, +d, +before, +x, +sh, +pr, +mk}:
          AL.and_intro(Sv.found_at(Sv.Seen{path, e, found, d, before, x, sh, pr, mk} <> rest, p), found_all(Sv.Seen{path, e, found, d, before, x, sh, pr, mk} <> rest, more),
            AL.or_right(Bool.and(String.eq(path, p), Maybe.is_some(&2, F.Found, found)), Sv.found_at(rest, p), Comp.and_left(Sv.found_at(rest, p), found_all(rest, more), h)),
            found_weaken(more, Sv.Seen{path, e, found, d, before, x, sh, pr, mk}, rest, Comp.and_right(Sv.found_at(rest, p), found_all(rest, more), h)))

# A surveyed path the folder found something at is one a refusal of it may
# name.
def here(+path: String, -e: Maybe<&2, Tree.Entry>, -f: F.Found, -d: String, -b: Maybe<&2, String>, -x: Bool, -sh: Maybe<&2, String>, -pr: Bool, -mk: Nat, -rest: List<&2, Sv.Seen>) -> {Sv.found_at(Sv.Seen{path, e, Some{f}, d, b, x, sh, pr, mk} <> rest, path) == True{} : Bool}:
  %Equal.sym(Bool, String.eq(path, path), True{}, S.eq_refl(path)) : {Bool.or(Bool.and(_, True{}), Sv.found_at(rest, path)) == True{} : Bool}
  {==}

def found_refused(+ss: List<&2, Sv.Seen>, +path: String, -why: String, +hp: {Sv.found_at(ss, path) == True{} : Bool}) -> {found_all(ss, [T.Split{path, why}]) == True{} : Bool}:
  AL.and_intro(Sv.found_at(ss, path), True{}, hp, {==})

def found_dropped(+ss: List<&2, Sv.Seen>, +path: String, e: Tree.Entry, +before: Maybe<&2, String>, -xs: List<&2, Sv.Obs>, h: {found_all(ss, Sv.refusals(xs)) == True{} : Bool}) -> {found_all(ss, Sv.refusals(Sv.dropped(path, e, before) <> xs)) == True{} : Bool}:
  match e:
    case Tree.Entry{f, p, Tree.Link{}, y, g, m}:
      h
    case Tree.Entry{f, p, Tree.Whole{}, y, g, m}:
      h
    case Tree.Entry{f, p, Tree.Lines{}, y, g, m}:
      h

def found_link(+ss: List<&2, Sv.Seen>, +path: String, +target: String, held: Maybe<&2, Tree.Entry>, shown: Maybe<&2, String>, fault: Maybe<&2, String>, fresh: Bool, +hp: {Sv.found_at(ss, path) == True{} : Bool}) -> {found_all(ss, Sv.refusals(Sv.link.checked(path, target, held, shown, fresh, fault))) == True{} : Bool}:
  match fault:
    case Some{because}:
      found_refused(ss, path, "it points at a target this format cannot hold: " ++ because, hp)
    case None{}:
      match fresh:
        case True{}:
          {==}
        case False{}:
          {==}

def found_mode(+ss: List<&2, Sv.Seen>, +path: String, c: Bool, -xs: List<&2, Sv.Obs>, h: {found_all(ss, Sv.refusals(xs)) == True{} : Bool}) -> {found_all(ss, Sv.refusals(List.append(&2, Sv.Obs, Bool.pick(List<&2, Sv.Obs>, c, Nil{}, [Sv.Obs.Mode{path}]), xs))) == True{} : Bool}:
  match c:
    case True{}:
      h
    case False{}:
      h

def found_mode1(+ss: List<&2, Sv.Seen>, +path: String, c: Bool) -> {found_all(ss, Sv.refusals(Bool.pick(List<&2, Sv.Obs>, c, Nil{}, [Sv.Obs.Mode{path}]))) == True{} : Bool}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

def found_edited(+ss: List<&2, Sv.Seen>, +path: String, c: Bool) -> {found_all(ss, Sv.refusals(Bool.pick(List<&2, Sv.Obs>, c, Nil{}, [Sv.Obs.Edited{path}]))) == True{} : Bool}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

def found_whole(+ss: List<&2, Sv.Seen>, +path: String, +e: Tree.Entry, +digest: String, +runs: Bool, payload: Maybe<&2, String>) -> {found_all(ss, Sv.refusals(Sv.whole(path, e, digest, runs, payload))) == True{} : Bool}:
  match payload:
    case None{}:
      found_mode(ss, path, Tree.mode_eq(Tree.entry_mode(e), Bool.pick(Tree.Mode, runs, Tree.Executable{}, Tree.Plain{})), [Sv.Obs.Accept{path}, Sv.Obs.Edited{path}], {==})
    case Some{+p}:
      found_mode(ss, path, Tree.mode_eq(Tree.entry_mode(e), Bool.pick(Tree.Mode, runs, Tree.Executable{}, Tree.Plain{})), Bool.pick(List<&2, Sv.Obs>, String.eq(p, digest), Nil{}, [Sv.Obs.Edited{path}]), found_edited(ss, path, String.eq(p, digest)))

def found_changed(+ss: List<&2, Sv.Seen>, +path: String, +e: Tree.Entry, +runs: Bool, text: Bool, +hp: {Sv.found_at(ss, path) == True{} : Bool}) -> {found_all(ss, Sv.refusals(Sv.lines.changed(path, e, runs, text))) == True{} : Bool}:
  match text:
    case True{}:
      found_mode(ss, path, Tree.mode_eq(Tree.entry_mode(e), Bool.pick(Tree.Mode, runs, Tree.Executable{}, Tree.Plain{})), [Sv.Obs.Edited{path}], {==})
    case False{}:
      found_refused(ss, path, "recorded as lines and no longer UTF-8 text; drop it and add it again", hp)

def found_agreed(+ss: List<&2, Sv.Seen>, +path: String, +e: Tree.Entry, +runs: Bool, +text: Bool, c: Bool, +hp: {Sv.found_at(ss, path) == True{} : Bool}) -> {found_all(ss, Sv.refusals(Bool.pick(List<&2, Sv.Obs>, c, Sv.mode(path, e, runs), Sv.lines.changed(path, e, runs, text)))) == True{} : Bool}:
  match c:
    case True{}:
      found_mode1(ss, path, Tree.mode_eq(Tree.entry_mode(e), Bool.pick(Tree.Mode, runs, Tree.Executable{}, Tree.Plain{})))
    case False{}:
      found_changed(ss, path, e, runs, text, hp)

def found_emptied(+ss: List<&2, Sv.Seen>, +path: String, +e: Tree.Entry, +runs: Bool, empty: Bool, +hp: {Sv.found_at(ss, path) == True{} : Bool}) -> {found_all(ss, Sv.refusals(Bool.pick(List<&2, Sv.Obs>, empty, List.append(&2, Sv.Obs, Sv.mode(path, e, runs), [Sv.Obs.Emptied{path}]), Sv.lines.changed(path, e, runs, True{})))) == True{} : Bool}:
  match empty:
    case True{}:
      found_mode(ss, path, Tree.mode_eq(Tree.entry_mode(e), Bool.pick(Tree.Mode, runs, Tree.Executable{}, Tree.Plain{})), [Sv.Obs.Emptied{path}], {==})
    case False{}:
      found_changed(ss, path, e, runs, True{}, hp)

# A file still marked is refused by `record` itself, not among the
# refusals the survey makes.
def found_resolved(+ss: List<&2, Sv.Seen>, +path: String, +e: Tree.Entry, +runs: Bool, empty: Bool, marked: Nat, +hp: {Sv.found_at(ss, path) == True{} : Bool}) -> {found_all(ss, Sv.refusals(Sv.lines.resolved(path, e, runs, True{}, empty, marked))) == True{} : Bool}:
  match marked:
    case 0n:
      found_emptied(ss, path, e, runs, empty, hp)
    case 1n+k:
      found_mode(ss, path, Tree.mode_eq(Tree.entry_mode(e), Bool.pick(Tree.Mode, runs, Tree.Executable{}, Tree.Plain{})), [Sv.Obs.Marked{path, 1n+k}], {==})

def found_lines(+ss: List<&2, Sv.Seen>, +path: String, +e: Tree.Entry, +digest: String, +before: Maybe<&2, String>, +runs: Bool, proposed: Bool, +text: Bool, empty: Bool, +marked: Nat, +hp: {Sv.found_at(ss, path) == True{} : Bool}) -> {found_all(ss, Sv.refusals(Sv.lines(path, e, digest, before, runs, text, proposed, empty, marked))) == True{} : Bool}:
  match proposed:
    case True{}:
      match text:
        case False{}:
          found_changed(ss, path, e, runs, False{}, hp)
        case True{}:
          found_resolved(ss, path, e, runs, empty, marked, hp)
    case False{}:
      found_agreed(ss, path, e, runs, text, Sv.same(before, digest), hp)

def found_held_file(+ss: List<&2, Sv.Seen>, +path: String, e: Tree.Entry, +digest: String, +before: Maybe<&2, String>, +runs: Bool, text: Bool, proposed: Bool, empty: Bool, +marked: Nat, +hp: {Sv.found_at(ss, path) == True{} : Bool}) -> {found_all(ss, Sv.refusals(Sv.held_file(path, e, digest, before, runs, text, proposed, empty, marked))) == True{} : Bool}:
  match e:
    case Tree.Entry{+f, +p, Tree.Link{}, +y, +g, +m}:
      {==}
    case Tree.Entry{+f, +p, Tree.Whole{}, +y, +g, +m}:
      found_whole(ss, path, Tree.Entry{f, p, Tree.Whole{}, y, g, m}, digest, runs, y)
    case Tree.Entry{+f, +p, Tree.Lines{}, +y, +g, +m}:
      found_lines(ss, path, Tree.Entry{f, p, Tree.Lines{}, y, g, m}, digest, before, runs, proposed, text, empty, marked, hp)

def found_held_link(+ss: List<&2, Sv.Seen>, +path: String, +target: String, e: Tree.Entry, shown: Maybe<&2, String>, +before: Maybe<&2, String>, +hp: {Sv.found_at(ss, path) == True{} : Bool}) -> {found_all(ss, Sv.refusals(Sv.held_link(path, target, e, shown, before))) == True{} : Bool}:
  match e:
    case Tree.Entry{+f, +p, Tree.Link{}, +y, +g, +m}:
      found_link(ss, path, target, Some{Tree.Entry{f, p, Tree.Link{}, y, g, m}}, shown, Sv.link_fault(target), False{}, hp)
    case Tree.Entry{+f, +p, Tree.Whole{}, +y, +g, +m}:
      found_dropped(ss, path, Tree.Entry{f, p, Tree.Whole{}, y, g, m}, before, Sv.link(path, target, None{}, None{}, True{}), found_link(ss, path, target, None{}, None{}, Sv.link_fault(target), True{}, hp))
    case Tree.Entry{+f, +p, Tree.Lines{}, +y, +g, +m}:
      found_dropped(ss, path, Tree.Entry{f, p, Tree.Lines{}, y, g, m}, before, Sv.link(path, target, None{}, None{}, True{}), found_link(ss, path, target, None{}, None{}, Sv.link_fault(target), True{}, hp))

def seen_found(s: Sv.Seen, +rest: List<&2, Sv.Seen>) -> {found_all(s <> rest, Sv.refusals(Sv.seen(s))) == True{} : Bool}:
  match s:
    case Sv.Seen{+path, Some{+e}, None{}, +d, +before, +x, +sh, +pr, +mk}:
      found_dropped(Sv.Seen{path, Some{e}, None{}, d, before, x, sh, pr, mk} <> rest, path, e, before, Nil{}, {==})
    case Sv.Seen{+path, None{}, Some{F.Found.Link{+q, +target}}, +d, +before, +x, +sh, +pr, +mk}:
      found_link(Sv.Seen{path, None{}, Some{F.Found.Link{q, target}}, d, before, x, sh, pr, mk} <> rest, path, target, None{}, None{}, Sv.link_fault(target), True{},
        here(path, None{}, F.Found.Link{q, target}, d, before, x, sh, pr, mk, rest))
    case Sv.Seen{+path, None{}, Some{F.Found.File{+q, +runs, +n}}, +d, +before, +x, +sh, +pr, +mk}:
      {==}
    case Sv.Seen{+path, Some{+e}, Some{F.Found.Link{+q, +target}}, +d, +before, +x, +sh, +pr, +mk}:
      found_held_link(Sv.Seen{path, Some{e}, Some{F.Found.Link{q, target}}, d, before, x, sh, pr, mk} <> rest, path, target, e, sh, before,
        here(path, Some{e}, F.Found.Link{q, target}, d, before, x, sh, pr, mk, rest))
    case Sv.Seen{+path, Some{+e}, Some{F.Found.File{+q, +runs, +n}}, +d, +before, +x, +sh, +pr, +mk}:
      found_held_file(Sv.Seen{path, Some{e}, Some{F.Found.File{q, runs, n}}, d, before, x, sh, pr, mk} <> rest, path, e, d, before, runs, x, pr, Nat.is_eq(n, 0n), mk,
        here(path, Some{e}, F.Found.File{q, runs, n}, d, before, x, sh, pr, mk, rest))
    case Sv.Seen{+path, None{}, None{}, +d, +before, +x, +sh, +pr, +mk}:
      {==}

def seens_found(ss: List<&2, Sv.Seen>) -> {found_all(ss, Sv.refusals(Sv.seens(ss))) == True{} : Bool}:
  match ss:
    case Nil{}:
      {==}
    case +s <> +rest:
      %Equal.sym(List<&2, T.Split>, Sv.refusals(List.append(&2, Sv.Obs, Sv.seen(s), Sv.seens(rest))), List.append(&2, T.Split, Sv.refusals(Sv.seen(s)), Sv.refusals(Sv.seens(rest))), refusals_app(Sv.seen(s), Sv.seens(rest))) : {found_all(s <> rest, _) == True{} : Bool}
      found_app(s <> rest, Sv.refusals(Sv.seen(s)), Sv.refusals(Sv.seens(rest)), seen_found(s, rest), found_weaken(Sv.refusals(Sv.seens(rest)), s, rest, seens_found(rest)))

# The drops of a path several files claim refuse nothing.
def dropped_none(+path: String, e: Tree.Entry, +before: Maybe<&2, String>, -xs: List<&2, Sv.Obs>) -> {Sv.refusals(Sv.dropped(path, e, before) <> xs) == Sv.refusals(xs) : List<&2, T.Split>}:
  match e:
    case Tree.Entry{f, p, Tree.Link{}, y, g, m}:
      {==}
    case Tree.Entry{f, p, Tree.Whole{}, y, g, m}:
      {==}
    case Tree.Entry{f, p, Tree.Lines{}, y, g, m}:
      {==}

def claimed_pick(c: Bool, +path: String, +e: Tree.Entry, +later: List<&2, Sv.Obs>, ih: {Sv.refusals(later) == Nil{} : List<&2, T.Split>}) -> {Sv.refusals(Bool.pick(List<&2, Sv.Obs>, c, Sv.dropped(path, e, None{}) <> later, later)) == Nil{} : List<&2, T.Split>}:
  match c:
    case True{}:
      Equal.trans(List<&2, T.Split>, Sv.refusals(Sv.dropped(path, e, None{}) <> later), Sv.refusals(later), Nil{}, dropped_none(path, e, None{}, later), ih)
    case False{}:
      ih

def claimed_none(t: Tree.Tree(), +cs: List<&2, T.Split>, +held: Set()) -> {Sv.refusals(Sv.claimed_drops(t, cs, held)) == Nil{} : List<&2, T.Split>}:
  match t:
    case Nil{}:
      {==}
    case +e <> +rest:
      claimed_pick(Bool.and(Sv.claimed.has(cs, Tree.entry_path(e)), Bool.not(Sv.has(held, Tree.entry_path(e)))), Tree.entry_path(e), e, Sv.claimed_drops(rest, cs, held), claimed_none(rest, cs, held))

def obs_found(+t: Tree.Tree(), +cs: List<&2, T.Split>, +held: Set(), +ss: List<&2, Sv.Seen>) -> {found_all(ss, Sv.refusals(List.append(&2, Sv.Obs, Sv.seens(ss), Sv.claimed_drops(t, cs, held)))) == True{} : Bool}:
  %Equal.sym(List<&2, T.Split>, Sv.refusals(List.append(&2, Sv.Obs, Sv.seens(ss), Sv.claimed_drops(t, cs, held))), List.append(&2, T.Split, Sv.refusals(Sv.seens(ss)), Sv.refusals(Sv.claimed_drops(t, cs, held))), refusals_app(Sv.seens(ss), Sv.claimed_drops(t, cs, held))) : {found_all(ss, _) == True{} : Bool}
  %Equal.sym(List<&2, T.Split>, Sv.refusals(Sv.claimed_drops(t, cs, held)), Nil{}, claimed_none(t, cs, held)) : {found_all(ss, List.append(&2, T.Split, Sv.refusals(Sv.seens(ss)), _)) == True{} : Bool}
  found_app(ss, Sv.refusals(Sv.seens(ss)), Nil{}, seens_found(ss), {==})

# And each of the walk's own refusals is one the walk refused.
def refuses_app(+walked: List<&2, T.Split>, +ss: List<&2, Sv.Seen>, xs: List<&2, T.Split>, +ys: List<&2, T.Split>, +hx: {Sv.refuses_found(walked, ss, xs) == True{} : Bool}, hy: {Sv.refuses_found(walked, ss, ys) == True{} : Bool}) -> {Sv.refuses_found(walked, ss, List.append(&2, T.Split, xs, ys)) == True{} : Bool}:
  match xs:
    case Nil{}:
      hy
    case T.Split{+p, b} <> rest:
      AL.and_intro(Bool.or(Sv.walked_at(walked, p), Sv.found_at(ss, p)), Sv.refuses_found(walked, ss, List.append(&2, T.Split, rest, ys)),
        Comp.and_left(Bool.or(Sv.walked_at(walked, p), Sv.found_at(ss, p)), Sv.refuses_found(walked, ss, rest), hx),
        refuses_app(walked, ss, rest, ys, Comp.and_right(Bool.or(Sv.walked_at(walked, p), Sv.found_at(ss, p)), Sv.refuses_found(walked, ss, rest), hx), hy))

def found_refuses(+walked: List<&2, T.Split>, +ss: List<&2, Sv.Seen>, rs: List<&2, T.Split>, +h: {found_all(ss, rs) == True{} : Bool}) -> {Sv.refuses_found(walked, ss, rs) == True{} : Bool}:
  match rs:
    case Nil{}:
      {==}
    case T.Split{+p, b} <> rest:
      AL.and_intro(Bool.or(Sv.walked_at(walked, p), Sv.found_at(ss, p)), Sv.refuses_found(walked, ss, rest),
        AL.or_right(Sv.walked_at(walked, p), Sv.found_at(ss, p), Comp.and_left(Sv.found_at(ss, p), found_all(ss, rest), h)),
        found_refuses(walked, ss, rest, Comp.and_right(Sv.found_at(ss, p), found_all(ss, rest), h)))

def walked_or(+q: String, +w: Bool, +f: Bool, +p: String, h: {Bool.or(w, f) == True{} : Bool}) -> {Bool.or(Bool.or(String.eq(q, p), w), f) == True{} : Bool}:
  AL.or_cases({Bool.or(Bool.or(String.eq(q, p), w), f) == True{} : Bool}, w, f, h,
    hw => AL.or_left(Bool.or(String.eq(q, p), w), f, AL.or_right(String.eq(q, p), w, hw)),
    hf => AL.or_right(Bool.or(String.eq(q, p), w), f, hf))

def walked_weaken(rs: List<&2, T.Split>, +x: T.Split, +rest: List<&2, T.Split>, +ss: List<&2, Sv.Seen>, +h: {Sv.refuses_found(rest, ss, rs) == True{} : Bool}) -> {Sv.refuses_found(x <> rest, ss, rs) == True{} : Bool}:
  match rs:
    case Nil{}:
      {==}
    case T.Split{+p, b} <> more:
      match x:
        case T.Split{+q, +c}:
          AL.and_intro(Bool.or(Sv.walked_at(T.Split{q, c} <> rest, p), Sv.found_at(ss, p)), Sv.refuses_found(T.Split{q, c} <> rest, ss, more),
            walked_or(q, Sv.walked_at(rest, p), Sv.found_at(ss, p), p, Comp.and_left(Bool.or(Sv.walked_at(rest, p), Sv.found_at(ss, p)), Sv.refuses_found(rest, ss, more), h)),
            walked_weaken(more, T.Split{q, c}, rest, ss, Comp.and_right(Bool.or(Sv.walked_at(rest, p), Sv.found_at(ss, p)), Sv.refuses_found(rest, ss, more), h)))

def walked_head(+q: String, -c: String, -rest: List<&2, T.Split>, -ss: List<&2, Sv.Seen>) -> {Bool.or(Sv.walked_at(T.Split{q, c} <> rest, q), Sv.found_at(ss, q)) == True{} : Bool}:
  %Equal.sym(Bool, String.eq(q, q), True{}, S.eq_refl(q)) : {Bool.or(Bool.or(_, Sv.walked_at(rest, q)), Sv.found_at(ss, q)) == True{} : Bool}
  {==}

def walked_self(ws: List<&2, T.Split>, +ss: List<&2, Sv.Seen>) -> {Sv.refuses_found(ws, ss, ws) == True{} : Bool}:
  match ws:
    case Nil{}:
      {==}
    case T.Split{+q, +c} <> +rest:
      AL.and_intro(Bool.or(Sv.walked_at(T.Split{q, c} <> rest, q), Sv.found_at(ss, q)), Sv.refuses_found(T.Split{q, c} <> rest, ss, rest),
        walked_head(q, c, rest, ss),
        walked_weaken(rest, T.Split{q, c}, rest, ss, walked_self(rest, ss)))

def refused_ok(+t: Tree.Tree(), +held: Set(), +walked: List<&2, T.Split>, +ss: List<&2, Sv.Seen>) -> {Sv.refuses_found(walked, ss, Sv.survey.refused(Sv.survey(t, held, walked, ss))) == True{} : Bool}:
  refuses_app(walked, ss, walked, Sv.refusals(List.append(&2, Sv.Obs, Sv.seens(ss), Sv.claimed_drops(t, Sv.claims(t), held))),
    walked_self(walked, ss),
    found_refuses(walked, ss, Sv.refusals(List.append(&2, Sv.Obs, Sv.seens(ss), Sv.claimed_drops(t, Sv.claims(t), held))), obs_found(t, Sv.claims(t), held, ss)))

# A kind stated
# -------------

def fixed_pick(c: Bool, -msg: String, +f: String, -xs: List<&2, String>, -later: Maybe<&2, String>, -rest: Bool, ih: {Maybe.is_none(&2, String, later) == Bool.and(List.is_empty(&2, String, xs), rest) : Bool}) -> {Maybe.is_none(&2, String, Bool.pick(Maybe<&2, String>, c, Some{msg}, later)) == Bool.and(List.is_empty(&2, String, Rev.keep(c, f, xs)), rest) : Bool}:
  match c:
    case True{}:
      {==}
    case False{}:
      ih

def fixed_ok(+p: String, t: Tree.Tree(), -later: Maybe<&2, String>, -rest: Bool, +ih: {Maybe.is_none(&2, String, later) == rest : Bool}) -> {Maybe.is_none(&2, String, Sv.kind_fixed(p, t, later)) == Bool.and(List.is_empty(&2, String, Tree.at(t, p)), rest) : Bool}:
  match t:
    case Nil{}:
      ih
    case Tree.Entry{+f, +q, +k, +y, +g, +m} <> more:
      fixed_pick(String.eq(q, p), "`" ++ p ++ "` is already recorded as " ++ Tree.kind_show(k) ++ ", and decision 0017 fixes that when a file is added; a file that has to change kind is a `drop` and an `add`, which is a new file with a new identity", f, Tree.at(more, p), Sv.kind_fixed(p, more, later), rest, fixed_ok(p, more, later, rest, ih))

def fault_pick(c: Bool, +p: String, +t: Tree.Tree(), -msg: String, -later: Maybe<&2, String>, -rest: Bool, +ih: {Maybe.is_none(&2, String, later) == rest : Bool}) -> {Maybe.is_none(&2, String, Bool.pick(Maybe<&2, String>, c, Sv.kind_fixed(p, t, later), Some{msg})) == Bool.and(Bool.and(c, List.is_empty(&2, String, Tree.at(t, p))), rest) : Bool}:
  match c:
    case True{}:
      fixed_ok(p, t, later, rest, ih)
    case False{}:
      {==}

def kinds_ok(+only: List<&2, String>, +t: Tree.Tree(), ks: List<&2, T.Split>) -> {Maybe.is_none(&2, String, Sv.kind_fault(only, t, ks)) == Sv.kinds_fresh(only, t, ks) : Bool}:
  match ks:
    case Nil{}:
      {==}
    case T.Split{+p, k} <> rest:
      fault_pick(Sv.covers(only, p), p, t, "`" ++ p ++ "` is not one of the paths this is recording, so saying which kind it is would state nothing; name it as a path too, or drop the restriction", Sv.kind_fault(only, t, rest), Sv.kinds_fresh(only, t, rest), kinds_ok(only, t, rest))

# The `move` lines
# ----------------

def later_none(ms: List<&2, T.Split>, +f: String, +h: {Sv.moved.later(ms, f) == False{} : Bool}) -> {Sv.last_move(ms, f) == None{} : Maybe<&2, String>}:
  match ms:
    case Nil{}:
      {==}
    case T.Split{+g, +to} <> rest:
      %Equal.sym(Maybe<&2, String>, Sv.last_move(rest, f), None{}, later_none(rest, f, AL.or_false_r(String.eq(g, f), Sv.moved.later(rest, f), h))) : {Maybe.or(&2, String, _, Bool.pick(Maybe<&2, String>, String.eq(g, f), Some{to}, None{})) == None{} : Maybe<&2, String>}
      %Equal.sym(Bool, String.eq(g, f), False{}, AL.or_false_l(String.eq(g, f), Sv.moved.later(rest, f), h)) : {Maybe.or(&2, String, None{}, Bool.pick(Maybe<&2, String>, _, Some{to}, None{})) == None{} : Maybe<&2, String>}
      {==}

def final_pick(c: Bool, +g: String, +to: String, +later: List<&2, T.Split>, +f: String, heq: {String.eq(g, f) == False{} : Bool}, ih: {Sv.moved.later(later, f) == False{} : Bool}) -> {Sv.moved.later(Bool.pick(List<&2, T.Split>, c, later, T.Split{g, to} <> later), f) == False{} : Bool}:
  match c:
    case True{}:
      ih
    case False{}:
      AL.or_false(String.eq(g, f), Sv.moved.later(later, f), heq, ih)

def final_later(ms: List<&2, T.Split>, +gone: Set(), +f: String, +h: {Sv.moved.later(ms, f) == False{} : Bool}) -> {Sv.moved.later(Sv.moved.final(ms, gone), f) == False{} : Bool}:
  match ms:
    case Nil{}:
      {==}
    case T.Split{+g, +to} <> +rest:
      final_pick(Bool.or(Sv.has(gone, g), Sv.moved.later(rest, g)), g, to, Sv.moved.final(rest, gone), f,
        AL.or_false_l(String.eq(g, f), Sv.moved.later(rest, f), h),
        final_later(rest, gone, f, AL.or_false_r(String.eq(g, f), Sv.moved.later(rest, f), h)))

def or_keep(m: Maybe<&2, String>, -n: Maybe<&2, String>, +to: String, h: {Sv.maybe_eq(m, Some{to}) == True{} : Bool}) -> {Sv.maybe_eq(Maybe.or(&2, String, m, n), Some{to}) == True{} : Bool}:
  match m:
    case None{}:
      Empty.absurd({Sv.maybe_eq(n, Some{to}) == True{} : Bool}, S.false_true(h))
    case Some{y}:
      h

def moves_weaken(out: List<&2, T.Split>, +x: T.Split, +ms: List<&2, T.Split>, +gone: Set(), +h: {Sv.moves_ok(ms, gone, out) == True{} : Bool}) -> {Sv.moves_ok(x <> ms, gone, out) == True{} : Bool}:
  match out:
    case Nil{}:
      {==}
    case T.Split{+f, +to} <> +rest:
      match x:
        case T.Split{+g, +gt}:
          AL.and_intro(Bool.and(Bool.not(Sv.has(gone, f)), Sv.maybe_eq(Sv.last_move(T.Split{g, gt} <> ms, f), Some{to})), Bool.and(Bool.not(Sv.moved.later(rest, f)), Sv.moves_ok(T.Split{g, gt} <> ms, gone, rest)),
            AL.and_intro(Bool.not(Sv.has(gone, f)), Sv.maybe_eq(Sv.last_move(T.Split{g, gt} <> ms, f), Some{to}),
              Comp.and_left(Bool.not(Sv.has(gone, f)), Sv.maybe_eq(Sv.last_move(ms, f), Some{to}), Comp.and_left(Bool.and(Bool.not(Sv.has(gone, f)), Sv.maybe_eq(Sv.last_move(ms, f), Some{to})), Bool.and(Bool.not(Sv.moved.later(rest, f)), Sv.moves_ok(ms, gone, rest)), h)),
              or_keep(Sv.last_move(ms, f), Bool.pick(Maybe<&2, String>, String.eq(g, f), Some{gt}, None{}), to, Comp.and_right(Bool.not(Sv.has(gone, f)), Sv.maybe_eq(Sv.last_move(ms, f), Some{to}), Comp.and_left(Bool.and(Bool.not(Sv.has(gone, f)), Sv.maybe_eq(Sv.last_move(ms, f), Some{to})), Bool.and(Bool.not(Sv.moved.later(rest, f)), Sv.moves_ok(ms, gone, rest)), h)))),
            AL.and_intro(Bool.not(Sv.moved.later(rest, f)), Sv.moves_ok(T.Split{g, gt} <> ms, gone, rest),
              Comp.and_left(Bool.not(Sv.moved.later(rest, f)), Sv.moves_ok(ms, gone, rest), Comp.and_right(Bool.and(Bool.not(Sv.has(gone, f)), Sv.maybe_eq(Sv.last_move(ms, f), Some{to})), Bool.and(Bool.not(Sv.moved.later(rest, f)), Sv.moves_ok(ms, gone, rest)), h)),
              moves_weaken(rest, T.Split{g, gt}, ms, gone, Comp.and_right(Bool.not(Sv.moved.later(rest, f)), Sv.moves_ok(ms, gone, rest), Comp.and_right(Bool.and(Bool.not(Sv.has(gone, f)), Sv.maybe_eq(Sv.last_move(ms, f), Some{to})), Bool.and(Bool.not(Sv.moved.later(rest, f)), Sv.moves_ok(ms, gone, rest)), h)))))

# The head's own line: the last place it went, since nothing after moves it.
def moved_here(+f: String, +to: String, +rest: List<&2, T.Split>, +h: {Sv.moved.later(rest, f) == False{} : Bool}) -> {Sv.maybe_eq(Sv.last_move(T.Split{f, to} <> rest, f), Some{to}) == True{} : Bool}:
  %Equal.sym(Maybe<&2, String>, Sv.last_move(rest, f), None{}, later_none(rest, f, h)) : {Sv.maybe_eq(Maybe.or(&2, String, _, Bool.pick(Maybe<&2, String>, String.eq(f, f), Some{to}, None{})), Some{to}) == True{} : Bool}
  %Equal.sym(Bool, String.eq(f, f), True{}, S.eq_refl(f)) : {Sv.maybe_eq(Maybe.or(&2, String, None{}, Bool.pick(Maybe<&2, String>, _, Some{to}, None{})), Some{to}) == True{} : Bool}
  S.eq_refl(to)

def moves_pick(c: Bool, +f: String, +to: String, +rest: List<&2, T.Split>, +gone: Set(), +ec: {Bool.or(Sv.has(gone, f), Sv.moved.later(rest, f)) == c : Bool}, +ih: {Sv.moves_ok(rest, gone, Sv.moved.final(rest, gone)) == True{} : Bool}) -> {Sv.moves_ok(T.Split{f, to} <> rest, gone, Bool.pick(List<&2, T.Split>, c, Sv.moved.final(rest, gone), T.Split{f, to} <> Sv.moved.final(rest, gone))) == True{} : Bool}:
  match c:
    case True{}:
      moves_weaken(Sv.moved.final(rest, gone), T.Split{f, to}, rest, gone, ih)
    case False{}:
      AL.and_intro(Bool.and(Bool.not(Sv.has(gone, f)), Sv.maybe_eq(Sv.last_move(T.Split{f, to} <> rest, f), Some{to})), Bool.and(Bool.not(Sv.moved.later(Sv.moved.final(rest, gone), f)), Sv.moves_ok(T.Split{f, to} <> rest, gone, Sv.moved.final(rest, gone))),
        AL.and_intro(Bool.not(Sv.has(gone, f)), Sv.maybe_eq(Sv.last_move(T.Split{f, to} <> rest, f), Some{to}),
          AL.not_true(Sv.has(gone, f), AL.or_false_l(Sv.has(gone, f), Sv.moved.later(rest, f), ec)),
          moved_here(f, to, rest, AL.or_false_r(Sv.has(gone, f), Sv.moved.later(rest, f), ec))),
        AL.and_intro(Bool.not(Sv.moved.later(Sv.moved.final(rest, gone), f)), Sv.moves_ok(T.Split{f, to} <> rest, gone, Sv.moved.final(rest, gone)),
          AL.not_true(Sv.moved.later(Sv.moved.final(rest, gone), f), final_later(rest, gone, f, AL.or_false_r(Sv.has(gone, f), Sv.moved.later(rest, f), ec))),
          moves_weaken(Sv.moved.final(rest, gone), T.Split{f, to}, rest, gone, ih)))

def moves_final_ok(ms: List<&2, T.Split>, +gone: Set()) -> {Sv.moves_ok(ms, gone, Sv.moved.final(ms, gone)) == True{} : Bool}:
  match ms:
    case Nil{}:
      {==}
    case T.Split{+f, +to} <> +rest:
      moves_pick(Bool.or(Sv.has(gone, f), Sv.moved.later(rest, f)), f, to, rest, gone, {==}, moves_final_ok(rest, gone))

# The paths a person names
# ------------------------

def ldisc(xs: List<&2, String>) -> Type:
  match xs:
    case Nil{}:
      Empty
    case x <> rest:
      Unit

def cons_nil(-x: String, -rest: List<&2, String>, e: {x <> rest == Nil{} : List<&2, String>}) -> Empty:
  %e : {ldisc(_) : Type}
  Unit{}

# A path a rule keeps out is refused as kept out, and any other as absent,
# so where neither refusal names one, nothing is unknown.
def kept_pick(s: Bool, -n: String, -one: List<&2, String>, -other: List<&2, String>, e1: {List.is_empty(&2, String, Bool.pick(List<&2, String>, Bool.xor(s, False{}), n <> one, one)) == True{} : Bool}, e2: {List.is_empty(&2, String, Bool.pick(List<&2, String>, Bool.xor(s, True{}), n <> other, other)) == True{} : Bool}) -> Empty:
  match s:
    case True{}:
      S.false_true(e1)
    case False{}:
      S.false_true(e2)

def kept_nil(+rules: List<&2, F.Scope>, u: List<&2, String>, e1: {List.is_empty(&2, String, Sv.kept_out(rules, u, True{})) == True{} : Bool}, e2: {List.is_empty(&2, String, Sv.kept_out(rules, u, False{})) == True{} : Bool}) -> {u == Nil{} : List<&2, String>}:
  match u:
    case Nil{}:
      {==}
    case +n <> +rest:
      Empty.absurd({n <> rest == Nil{} : List<&2, String>}, kept_pick(Bool.or(F.skips(rules, n), F.skips_directory(rules, n)), n, Sv.kept_out(rules, rest, True{}), Sv.kept_out(rules, rest, False{}), e1, e2))

def unknown_pick(c: Bool, +n: String, -later: List<&2, String>, -rest: Bool, e: {Bool.pick(List<&2, String>, c, later, n <> later) == Nil{} : List<&2, String>}, ih: {later == Nil{} : List<&2, String>} -> {rest == True{} : Bool}) -> {Bool.and(c, rest) == True{} : Bool}:
  match c:
    case True{}:
      ih(e)
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, cons_nil(n, later, e))

def unknown_nil(ns: List<&2, String>, +folder: List<&2, String>, +was: List<&2, String>, +placed: List<&2, String>, e: {Sv.unknown(ns, folder, was, placed) == Nil{} : List<&2, String>}) -> {Sv.answered(ns, folder, was, placed) == True{} : Bool}:
  match ns:
    case Nil{}:
      {==}
    case +n <> +rest:
      unknown_pick(Bool.or(Sv.any_beneath(n, folder), Bool.or(Sv.any_beneath(n, was), Sv.any_beneath(n, placed))), n, Sv.unknown(rest, folder, was, placed), Sv.answered(rest, folder, was, placed), e,
        h => unknown_nil(rest, folder, was, placed, h))

def refuse_cond(c: Bool, -r: Main.Refused, -rest: Result<&2, &2, Main.Refused, Unit>, e: {Bool.pick(Result<&2, &2, Main.Refused, Unit>, c, Fail{r}, rest) == Done{Unit{}} : Result<&2, &2, Main.Refused, Unit>}) -> {c == False{} : Bool}:
  match c:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, Blamed.fail_done(Unit, r, Unit{}, e))
    case False{}:
      {==}

def refuse_rest(c: Bool, -r: Main.Refused, -rest: Result<&2, &2, Main.Refused, Unit>, e: {Bool.pick(Result<&2, &2, Main.Refused, Unit>, c, Fail{r}, rest) == Done{Unit{}} : Result<&2, &2, Main.Refused, Unit>}) -> {rest == Done{Unit{}} : Result<&2, &2, Main.Refused, Unit>}:
  match c:
    case True{}:
      Empty.absurd({rest == Done{Unit{}} : Result<&2, &2, Main.Refused, Unit>}, Blamed.fail_done(Unit, r, Unit{}, e))
    case False{}:
      e

def not_false(b: Bool, e: {Bool.not(b) == False{} : Bool}) -> {b == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, S.true_false(e))

def named_ok(+rules: List<&2, F.Scope>, +named: List<&2, String>, +folder: List<&2, String>, +was: List<&2, String>, +placed: List<&2, String>, +e: {Main.named.r(rules, named, folder, was, placed) == Done{Unit{}} : Result<&2, &2, Main.Refused, Unit>}) -> {Sv.answered(named, folder, was, placed) == True{} : Bool}:
  unknown_nil(named, folder, was, placed,
    kept_nil(rules, Sv.unknown(named, folder, was, placed),
      not_false(List.is_empty(&2, String, Sv.kept_out(rules, Sv.unknown(named, folder, was, placed), True{})),
        refuse_cond(Bool.not(List.is_empty(&2, String, Sv.kept_out(rules, Sv.unknown(named, folder, was, placed), True{}))),
          Main.Refused{1, "`history/skipped/` says history does not take " ++ Main.these(Sv.kept_out(rules, Sv.unknown(named, folder, was, placed), True{}), "this", "these") ++ ", and naming " ++ Main.these(Sv.kept_out(rules, Sv.unknown(named, folder, was, placed), True{}), "it", "them") ++ " here does not make " ++ Main.these(Sv.kept_out(rules, Sv.unknown(named, folder, was, placed), True{}), "it", "them") ++ " an exception; remove the rule if " ++ Main.these(Sv.kept_out(rules, Sv.unknown(named, folder, was, placed), True{}), "it is", "they are") ++ " to be recorded:" ++ Main.skips_held.lines(Sv.kept_out(rules, Sv.unknown(named, folder, was, placed), True{}))},
          Bool.pick(Result<&2, &2, Main.Refused, Unit>, Bool.not(List.is_empty(&2, String, Sv.kept_out(rules, Sv.unknown(named, folder, was, placed), False{}))),
            Fail{Main.Refused{1, Main.these(Sv.kept_out(rules, Sv.unknown(named, folder, was, placed), False{}), "this path is", "these paths are") ++ " neither in the folder nor in this history, so there is nothing there to observe; check the spelling, or name no paths at all and record everything the folder says:" ++ Main.skips_held.lines(Sv.kept_out(rules, Sv.unknown(named, folder, was, placed), False{}))}},
            Done{Unit{}}),
          e)),
      not_false(List.is_empty(&2, String, Sv.kept_out(rules, Sv.unknown(named, folder, was, placed), False{})),
        refuse_cond(Bool.not(List.is_empty(&2, String, Sv.kept_out(rules, Sv.unknown(named, folder, was, placed), False{}))),
          Main.Refused{1, Main.these(Sv.kept_out(rules, Sv.unknown(named, folder, was, placed), False{}), "this path is", "these paths are") ++ " neither in the folder nor in this history, so there is nothing there to observe; check the spelling, or name no paths at all and record everything the folder says:" ++ Main.skips_held.lines(Sv.kept_out(rules, Sv.unknown(named, folder, was, placed), False{}))},
          Done{Unit{}},
          refuse_rest(Bool.not(List.is_empty(&2, String, Sv.kept_out(rules, Sv.unknown(named, folder, was, placed), True{}))),
            Main.Refused{1, "`history/skipped/` says history does not take " ++ Main.these(Sv.kept_out(rules, Sv.unknown(named, folder, was, placed), True{}), "this", "these") ++ ", and naming " ++ Main.these(Sv.kept_out(rules, Sv.unknown(named, folder, was, placed), True{}), "it", "them") ++ " here does not make " ++ Main.these(Sv.kept_out(rules, Sv.unknown(named, folder, was, placed), True{}), "it", "them") ++ " an exception; remove the rule if " ++ Main.these(Sv.kept_out(rules, Sv.unknown(named, folder, was, placed), True{}), "it is", "they are") ++ " to be recorded:" ++ Main.skips_held.lines(Sv.kept_out(rules, Sv.unknown(named, folder, was, placed), True{}))},
            Bool.pick(Result<&2, &2, Main.Refused, Unit>, Bool.not(List.is_empty(&2, String, Sv.kept_out(rules, Sv.unknown(named, folder, was, placed), False{}))),
              Fail{Main.Refused{1, Main.these(Sv.kept_out(rules, Sv.unknown(named, folder, was, placed), False{}), "this path is", "these paths are") ++ " neither in the folder nor in this history, so there is nothing there to observe; check the spelling, or name no paths at all and record everything the folder says:" ++ Main.skips_held.lines(Sv.kept_out(rules, Sv.unknown(named, folder, was, placed), False{}))}},
              Done{Unit{}}),
            e)))))

# Where the stated renames put things
# -----------------------------------

def pl_tree(r: Result<&2, &2, Main.Refused, Main.Placed>) -> Tree.Tree():
  match r:
    case Fail{x}:
      Nil{}
    case Done{Main.Placed{t, m}}:
      t

def pl_moved(r: Result<&2, &2, Main.Refused, Main.Placed>) -> List<&2, T.Split>:
  match r:
    case Fail{x}:
      Nil{}
    case Done{Main.Placed{t, m}}:
      m

def placed_end(-t: Tree.Tree(), -moved: List<&2, T.Split>, -t2: Tree.Tree(), -m2: List<&2, T.Split>, -t0: Tree.Tree(), inv: {t == Sv.moved_all(moved, t0) : Tree.Tree()}, +e: {Done{Main.Placed{t, moved}} == Done{Main.Placed{t2, m2}} : Result<&2, &2, Main.Refused, Main.Placed>}) -> {t2 == Sv.moved_all(m2, t0) : Tree.Tree()}:
  %Equal.cong(Result<&2, &2, Main.Refused, Main.Placed>, Tree.Tree(), r => pl_tree(r), Done{Main.Placed{t, moved}}, Done{Main.Placed{t2, m2}}, e) : {_ == Sv.moved_all(m2, t0) : Tree.Tree()}
  %Equal.cong(Result<&2, &2, Main.Refused, Main.Placed>, List<&2, T.Split>, r => pl_moved(r), Done{Main.Placed{t, moved}}, Done{Main.Placed{t2, m2}}, e) : {t == Sv.moved_all(_, t0) : Tree.Tree()}
  inv

def moved_snoc(xs: List<&2, T.Split>, +t: Tree.Tree(), +f: String, +to: String) -> {Sv.moved_all(List.append(&2, T.Split, xs, [T.Split{f, to}]), t) == Sv.relocated(Sv.moved_all(xs, t), f, to) : Tree.Tree()}:
  match xs:
    case Nil{}:
      {==}
    case T.Split{+g, +u} <> rest:
      moved_snoc(rest, Sv.relocated(t, g, u), f, to)

# One more rename done keeps the tree the renames so far make.
def moved_step(+t: Tree.Tree(), +moved: List<&2, T.Split>, +f: String, +to: String, +t0: Tree.Tree(), inv: {t == Sv.moved_all(moved, t0) : Tree.Tree()}) -> {Sv.relocated(t, f, to) == Sv.moved_all(List.append(&2, T.Split, moved, [T.Split{f, to}]), t0) : Tree.Tree()}:
  Equal.trans(Tree.Tree(), Sv.relocated(t, f, to), Sv.relocated(Sv.moved_all(moved, t0), f, to), Sv.moved_all(List.append(&2, T.Split, moved, [T.Split{f, to}]), t0),
    Equal.cong(Tree.Tree(), Tree.Tree(), x => Sv.relocated(x, f, to), t, Sv.moved_all(moved, t0), inv),
    Equal.sym(Tree.Tree(), Sv.moved_all(List.append(&2, T.Split, moved, [T.Split{f, to}]), t0), Sv.relocated(Sv.moved_all(moved, t0), f, to), moved_snoc(moved, t0, f, to)))

def at_moved(ats: List<&2, T.Split>, +t: Tree.Tree(), +moved: List<&2, T.Split>, held: Bool, +t0: Tree.Tree(), -t2: Tree.Tree(), -m2: List<&2, T.Split>, inv: {t == Sv.moved_all(moved, t0) : Tree.Tree()}, +e: {Main.placed.at.r(ats, t, moved, held) == Done{Main.Placed{t2, m2}} : Result<&2, &2, Main.Refused, Main.Placed>}) -> {t2 == Sv.moved_all(m2, t0) : Tree.Tree()}:
  match ats held:
    case Nil{} _:
      placed_end(t, moved, t2, m2, t0, inv, e)
    case T.Split{f, to} <> rest False{}:
      Empty.absurd({t2 == Sv.moved_all(m2, t0) : Tree.Tree()}, Blamed.fail_done(Main.Placed, Main.Refused{1, "`" ++ f ++ "` is not a file this history holds, so nothing can be moved from it"}, Main.Placed{t2, m2}, e))
    case T.Split{+f, +to} <> +rest True{}:
      at_moved(rest, Sv.relocated(t, f, to), List.append(&2, T.Split, moved, [T.Split{f, to}]), Main.placed.holds(Sv.relocated(t, f, to), rest), t0, t2, m2, moved_step(t, moved, f, to, t0, inv), e)

def move_moved(ms: List<&2, T.Split>, +t: Tree.Tree(), +moved: List<&2, T.Split>, at: List<&2, String>, fault: Maybe<&2, String>, +t0: Tree.Tree(), -t2: Tree.Tree(), -m2: List<&2, T.Split>, inv: {t == Sv.moved_all(moved, t0) : Tree.Tree()}, +e: {Main.placed.move.r(ms, t, moved, at, fault) == Done{Main.Placed{t2, m2}} : Result<&2, &2, Main.Refused, Main.Placed>}) -> {t2 == Sv.moved_all(m2, t0) : Tree.Tree()}:
  match ms at fault:
    case Nil{} _ _:
      placed_end(t, moved, t2, m2, t0, inv, e)
    case T.Split{from, to} <> rest Nil{} _:
      Empty.absurd({t2 == Sv.moved_all(m2, t0) : Tree.Tree()}, Blamed.fail_done(Main.Placed, Main.Refused{1, "`" ++ from ++ "` is not a file this history holds, so nothing can be moved from it"}, Main.Placed{t2, m2}, e))
    case T.Split{from, +to} <> +rest +f <> Nil{} None{}:
      move_moved(rest, Sv.relocated(t, f, to), List.append(&2, T.Split, moved, [T.Split{f, to}]), Main.placed.head(Sv.relocated(t, f, to), rest), Main.placed.fault(rest), t0, t2, m2, moved_step(t, moved, f, to, t0, inv), e)
    case T.Split{from, to} <> rest f <> Nil{} Some{because}:
      Empty.absurd({t2 == Sv.moved_all(m2, t0) : Tree.Tree()}, Blamed.fail_done(Main.Placed, Main.Refused{1, "`" ++ to ++ "` cannot be a path here: " ++ because}, Main.Placed{t2, m2}, e))
    case T.Split{+from, to} <> rest +f <> +g <> +more _:
      Empty.absurd({t2 == Sv.moved_all(m2, t0) : Tree.Tree()}, Blamed.fail_done(Main.Placed, Main.Refused{1, Main.contested.msg(from, f <> g <> more)}, Main.Placed{t2, m2}, e))

def placed_bind(+t: Tree.Tree(), +ats: List<&2, T.Split>, +ms: List<&2, T.Split>, r: Result<&2, &2, Main.Refused, Main.Placed>, +er: {Main.placed.at.r(ats, t, Nil{}, Main.placed.holds(t, ats)) == r : Result<&2, &2, Main.Refused, Main.Placed>}, -t2: Tree.Tree(), -m2: List<&2, T.Split>, +e: {Result.bind(&2, &2, Main.Refused, Main.Placed, Main.Placed, r, p => Main.placed.of.r(p, ms)) == Done{Main.Placed{t2, m2}} : Result<&2, &2, Main.Refused, Main.Placed>}) -> {t2 == Sv.moved_all(m2, t) : Tree.Tree()}:
  match r:
    case Fail{x}:
      Empty.absurd({t2 == Sv.moved_all(m2, t) : Tree.Tree()}, Blamed.fail_done(Main.Placed, x, Main.Placed{t2, m2}, e))
    case Done{p}:
      match p:
        case Main.Placed{+t1, +m1}:
          move_moved(ms, t1, m1, Main.placed.head(t1, ms), Main.placed.fault(ms), t, t2, m2, at_moved(ats, t, Nil{}, Main.placed.holds(t, ats), t, t1, m1, {==}, er), e)

# What the renames `record` goes on with make of the position.
def placed_moved(+t: Tree.Tree(), +ats: List<&2, T.Split>, +ms: List<&2, T.Split>, -t2: Tree.Tree(), -m2: List<&2, T.Split>, +e: {Main.placed.r(t, ats, ms) == Done{Main.Placed{t2, m2}} : Result<&2, &2, Main.Refused, Main.Placed>}) -> {t2 == Sv.moved_all(m2, t) : Tree.Tree()}:
  placed_bind(t, ats, ms, Main.placed.at.r(ats, t, Nil{}, Main.placed.holds(t, ats)), {==}, t2, m2, e)

# A rename moves one file's path and nothing else.
def files_relocated(t: Tree.Tree(), +f: String, +to: String) -> {Sv.files(Sv.relocated(t, f, to)) == Sv.files(t) : List<&2, String>}:
  match t:
    case Nil{}:
      {==}
    case Tree.Entry{+fe, p, k, y, g, m} <> rest:
      %files_relocated(rest, f, to) : {fe <> Sv.files(Sv.relocated(rest, f, to)) == fe <> _ : List<&2, String>}
      {==}

def files_moved(ms: List<&2, T.Split>, +t: Tree.Tree()) -> {Sv.files(Sv.moved_all(ms, t)) == Sv.files(t) : List<&2, String>}:
  match ms:
    case Nil{}:
      {==}
    case T.Split{+f, +to} <> rest:
      Equal.trans(List<&2, String>, Sv.files(Sv.moved_all(rest, Sv.relocated(t, f, to))), Sv.files(Sv.relocated(t, f, to)), Sv.files(t), files_moved(rest, Sv.relocated(t, f, to)), files_relocated(t, f, to))

def flip_eq(c: Cmp) -> {Cmp.is_eq(SortL.cflip(c)) == Cmp.is_eq(c) : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

def eq_sym(+a: String, +b: String) -> {String.eq(a, b) == String.eq(b, a) : Bool}:
  Equal.trans(Bool, String.eq(a, b), Cmp.is_eq(String.order(a, b)), String.eq(b, a), S.eq_order(a, b),
    Equal.sym(Bool, String.eq(b, a), Cmp.is_eq(String.order(a, b)),
      Equal.trans(Bool, String.eq(b, a), Cmp.is_eq(String.order(b, a)), Cmp.is_eq(String.order(a, b)), S.eq_order(b, a),
        Equal.trans(Bool, Cmp.is_eq(String.order(b, a)), Cmp.is_eq(SortL.cflip(String.order(a, b))), Cmp.is_eq(String.order(a, b)),
          Equal.cong(Cmp, Bool, c => Cmp.is_eq(c), String.order(b, a), SortL.cflip(String.order(a, b)), SortL.str_flip(a, b)),
          flip_eq(String.order(a, b))))))

def holds_pick(c: Bool, -x: Tree.Entry, -y: Tree.Entry, -l1: Maybe<&2, Tree.Entry>, -l2: Maybe<&2, Tree.Entry>, ih: {Maybe.is_some(&2, Tree.Entry, l1) == Maybe.is_some(&2, Tree.Entry, l2) : Bool}) -> {Maybe.is_some(&2, Tree.Entry, Bool.pick(Maybe<&2, Tree.Entry>, c, Some{x}, l1)) == Maybe.is_some(&2, Tree.Entry, Bool.pick(Maybe<&2, Tree.Entry>, c, Some{y}, l2)) : Bool}:
  match c:
    case True{}:
      {==}
    case False{}:
      ih

def holds_relocated(t: Tree.Tree(), +f: String, +to: String, +g: String) -> {Tree.holds(Sv.relocated(t, f, to), g) == Tree.holds(t, g) : Bool}:
  match t:
    case Nil{}:
      {==}
    case Tree.Entry{+fe, +p, +k, +y, +gt, +m} <> rest:
      holds_pick(String.eq(fe, g), Tree.Entry{fe, Bool.pick(String, String.eq(fe, f), to, p), k, y, gt, m}, Tree.Entry{fe, p, k, y, gt, m}, Tree.lookup(Sv.relocated(rest, f, to), g), Tree.lookup(rest, g), holds_relocated(rest, f, to, g))

# The file named goes where it was said to.
def same_here(+fe: String, +f: String, +g: String, +to: String, -p: String, hc: {String.eq(fe, g) == True{} : Bool}, hs: {String.eq(f, g) == True{} : Bool}) -> {Bool.pick(String, String.eq(fe, f), to, p) == to : String}:
  %Equal.sym(String, fe, g, S.eq_true(fe, g, hc)) : {Bool.pick(String, String.eq(_, f), to, p) == to : String}
  %Equal.sym(String, f, g, S.eq_true(f, g, hs)) : {Bool.pick(String, String.eq(g, _), to, p) == to : String}
  %Equal.sym(Bool, String.eq(g, g), True{}, S.eq_refl(g)) : {Bool.pick(String, _, to, p) == to : String}
  {==}

def same_pick(c: Bool, +fe: String, +f: String, +g: String, +to: String, +p: String, -k: Tree.FileKind, -y: Maybe<&2, String>, -gt: Maybe<&2, Tree.Target>, -m: Tree.Mode, -rest: Tree.Tree(), +ec: {String.eq(fe, g) == c : Bool}, +hs: {String.eq(f, g) == True{} : Bool}, hh: {Maybe.is_some(&2, Tree.Entry, Bool.pick(Maybe<&2, Tree.Entry>, c, Some{Tree.Entry{fe, p, k, y, gt, m}}, Tree.lookup(rest, g))) == True{} : Bool}, ih: {Tree.holds(rest, g) == True{} : Bool} -> {Tree.path(Sv.relocated(rest, f, to), g) == Some{to} : Maybe<&2, String>}) -> {Maybe.map(&2, Tree.Entry, String, e => Tree.entry_path(e), Bool.pick(Maybe<&2, Tree.Entry>, c, Some{Tree.Entry{fe, Bool.pick(String, String.eq(fe, f), to, p), k, y, gt, m}}, Tree.lookup(Sv.relocated(rest, f, to), g))) == Some{to} : Maybe<&2, String>}:
  match c:
    case True{}:
      Equal.cong(String, Maybe<&2, String>, x => Some{x}, Bool.pick(String, String.eq(fe, f), to, p), to, same_here(fe, f, g, to, p, ec, hs))
    case False{}:
      ih(hh)

def relocate_same(t: Tree.Tree(), +f: String, +to: String, +g: String, +hs: {String.eq(f, g) == True{} : Bool}, hh: {Tree.holds(t, g) == True{} : Bool}) -> {Tree.path(Sv.relocated(t, f, to), g) == Some{to} : Maybe<&2, String>}:
  match t:
    case Nil{}:
      Empty.absurd({Tree.path(Sv.relocated(Nil{}, f, to), g) == Some{to} : Maybe<&2, String>}, S.false_true(hh))
    case Tree.Entry{+fe, +p, +k, +y, +gt, +m} <> +rest:
      same_pick(String.eq(fe, g), fe, f, g, to, p, k, y, gt, m, rest, {==}, hs, hh, h => relocate_same(rest, f, to, g, hs, h))

# Any other file stays where it was.
def other_here(+fe: String, +f: String, +g: String, +to: String, +p: String, hc: {String.eq(fe, g) == True{} : Bool}, hn: {String.eq(f, g) == False{} : Bool}) -> {Bool.pick(String, String.eq(fe, f), to, p) == p : String}:
  %Equal.sym(String, fe, g, S.eq_true(fe, g, hc)) : {Bool.pick(String, String.eq(_, f), to, p) == p : String}
  %eq_sym(f, g) : {Bool.pick(String, _, to, p) == p : String}
  %Equal.sym(Bool, String.eq(f, g), False{}, hn) : {Bool.pick(String, _, to, p) == p : String}
  {==}

def other_pick(c: Bool, +fe: String, +f: String, +g: String, +to: String, +p: String, -k: Tree.FileKind, -y: Maybe<&2, String>, -gt: Maybe<&2, Tree.Target>, -m: Tree.Mode, -rest: Tree.Tree(), +ec: {String.eq(fe, g) == c : Bool}, +hn: {String.eq(f, g) == False{} : Bool}, ih: {Tree.path(Sv.relocated(rest, f, to), g) == Tree.path(rest, g) : Maybe<&2, String>}) -> {Maybe.map(&2, Tree.Entry, String, e => Tree.entry_path(e), Bool.pick(Maybe<&2, Tree.Entry>, c, Some{Tree.Entry{fe, Bool.pick(String, String.eq(fe, f), to, p), k, y, gt, m}}, Tree.lookup(Sv.relocated(rest, f, to), g))) == Maybe.map(&2, Tree.Entry, String, e => Tree.entry_path(e), Bool.pick(Maybe<&2, Tree.Entry>, c, Some{Tree.Entry{fe, p, k, y, gt, m}}, Tree.lookup(rest, g))) : Maybe<&2, String>}:
  match c:
    case True{}:
      Equal.cong(String, Maybe<&2, String>, x => Some{x}, Bool.pick(String, String.eq(fe, f), to, p), p, other_here(fe, f, g, to, p, ec, hn))
    case False{}:
      ih

def relocate_other(t: Tree.Tree(), +f: String, +to: String, +g: String, +hn: {String.eq(f, g) == False{} : Bool}) -> {Tree.path(Sv.relocated(t, f, to), g) == Tree.path(t, g) : Maybe<&2, String>}:
  match t:
    case Nil{}:
      {==}
    case Tree.Entry{+fe, +p, +k, +y, +gt, +m} <> +rest:
      other_pick(String.eq(fe, g), fe, f, g, to, p, k, y, gt, m, rest, {==}, hn, relocate_other(rest, f, to, g, hn))

# Done in turn, the renames leave each file at the last place one put it.
def moved_pick(c: Bool, +t: Tree.Tree(), +f: String, +to: String, +g: String, +ec: {String.eq(f, g) == c : Bool}, +hh: {Tree.holds(t, g) == True{} : Bool}) -> {Tree.path(Sv.relocated(t, f, to), g) == Maybe.or(&2, String, Bool.pick(Maybe<&2, String>, c, Some{to}, None{}), Tree.path(t, g)) : Maybe<&2, String>}:
  match c:
    case True{}:
      relocate_same(t, f, to, g, ec, hh)
    case False{}:
      relocate_other(t, f, to, g, ec)

def moved_or(lm: Maybe<&2, String>, -here: Maybe<&2, String>, -step: Maybe<&2, String>, -was: Maybe<&2, String>, hs: {here == Maybe.or(&2, String, step, was) : Maybe<&2, String>}) -> {Maybe.or(&2, String, lm, here) == Maybe.or(&2, String, Maybe.or(&2, String, lm, step), was) : Maybe<&2, String>}:
  match lm:
    case None{}:
      hs
    case Some{x}:
      {==}

def path_moved(ms: List<&2, T.Split>, +t: Tree.Tree(), +g: String, +hh: {Tree.holds(t, g) == True{} : Bool}) -> {Tree.path(Sv.moved_all(ms, t), g) == Maybe.or(&2, String, Sv.last_move(ms, g), Tree.path(t, g)) : Maybe<&2, String>}:
  match ms:
    case Nil{}:
      {==}
    case T.Split{+f, +to} <> +rest:
      Equal.trans(Maybe<&2, String>, Tree.path(Sv.moved_all(rest, Sv.relocated(t, f, to)), g), Maybe.or(&2, String, Sv.last_move(rest, g), Tree.path(Sv.relocated(t, f, to), g)), Maybe.or(&2, String, Maybe.or(&2, String, Sv.last_move(rest, g), Bool.pick(Maybe<&2, String>, String.eq(f, g), Some{to}, None{})), Tree.path(t, g)),
        path_moved(rest, Sv.relocated(t, f, to), g, Equal.trans(Bool, Tree.holds(Sv.relocated(t, f, to), g), Tree.holds(t, g), True{}, holds_relocated(t, f, to, g), hh)),
        moved_or(Sv.last_move(rest, g), Tree.path(Sv.relocated(t, f, to), g), Bool.pick(Maybe<&2, String>, String.eq(f, g), Some{to}, None{}), Tree.path(t, g), moved_pick(String.eq(f, g), t, f, to, g, {==}, hh)))

# What a restricted record looks at
# ---------------------------------

def covered_app(+only: List<&2, String>, xs: List<&2, T.Split>, +ys: List<&2, T.Split>, +hx: {Sv.all_covered(only, xs) == True{} : Bool}, hy: {Sv.all_covered(only, ys) == True{} : Bool}) -> {Sv.all_covered(only, List.append(&2, T.Split, xs, ys)) == True{} : Bool}:
  match xs:
    case Nil{}:
      hy
    case T.Split{+p, b} <> rest:
      AL.and_intro(Sv.covers(only, p), Sv.all_covered(only, List.append(&2, T.Split, rest, ys)), Comp.and_left(Sv.covers(only, p), Sv.all_covered(only, rest), hx),
        covered_app(only, rest, ys, Comp.and_right(Sv.covers(only, p), Sv.all_covered(only, rest), hx), hy))

def refused_pick(c: Bool, +p: String, +b: String, +only: List<&2, String>, +later: List<&2, T.Split>, +ec: {Sv.covers(only, p) == c : Bool}, +ih: {Sv.all_covered(only, later) == True{} : Bool}) -> {Sv.all_covered(only, Bool.pick(List<&2, T.Split>, c, T.Split{p, b} <> later, later)) == True{} : Bool}:
  match c:
    case True{}:
      AL.and_intro(Sv.covers(only, p), Sv.all_covered(only, later), ec, ih)
    case False{}:
      ih

def only_refused_ok(+only: List<&2, String>, rs: List<&2, T.Split>) -> {Sv.all_covered(only, Sv.only.refused(only, rs)) == True{} : Bool}:
  match rs:
    case Nil{}:
      {==}
    case T.Split{+p, +b} <> +rest:
      refused_pick(Sv.covers(only, p), p, b, only, Sv.only.refused(only, rest), {==}, only_refused_ok(only, rest))

# Every surveyed path is covered, so a path a refusal names is.
def seens_covered(+only: List<&2, String>, ss: List<&2, Sv.Seen>) -> Bool:
  match ss:
    case Nil{}:
      True{}
    case Sv.Seen{+path, e, found, d, b, x, sh, pr, mk} <> rest:
      Bool.and(Sv.covers(only, path), seens_covered(only, rest))

def here_covered(+only: List<&2, String>, +path: String, +p: String, heq: {String.eq(path, p) == True{} : Bool}, hc: {Sv.covers(only, path) == True{} : Bool}) -> {Sv.covers(only, p) == True{} : Bool}:
  %S.eq_true(path, p, heq) : {Sv.covers(only, _) == True{} : Bool}
  hc

def at_covered(ss: List<&2, Sv.Seen>, +only: List<&2, String>, +p: String, +hs: {seens_covered(only, ss) == True{} : Bool}, hf: {Sv.found_at(ss, p) == True{} : Bool}) -> {Sv.covers(only, p) == True{} : Bool}:
  match ss:
    case Nil{}:
      Empty.absurd({Sv.covers(only, p) == True{} : Bool}, S.false_true(hf))
    case Sv.Seen{+path, +e, +found, +d, +b, +x, +sh, +pr, +mk} <> +rest:
      AL.or_cases({Sv.covers(only, p) == True{} : Bool}, Bool.and(String.eq(path, p), Maybe.is_some(&2, F.Found, found)), Sv.found_at(rest, p), hf,
        hl => here_covered(only, path, p, Comp.and_left(String.eq(path, p), Maybe.is_some(&2, F.Found, found), hl), Comp.and_left(Sv.covers(only, path), seens_covered(only, rest), hs)),
        hr => at_covered(rest, only, p, Comp.and_right(Sv.covers(only, path), seens_covered(only, rest), hs), hr))

def found_covered(+only: List<&2, String>, +ss: List<&2, Sv.Seen>, rs: List<&2, T.Split>, +hs: {seens_covered(only, ss) == True{} : Bool}, +hf: {found_all(ss, rs) == True{} : Bool}) -> {Sv.all_covered(only, rs) == True{} : Bool}:
  match rs:
    case Nil{}:
      {==}
    case T.Split{+p, b} <> rest:
      AL.and_intro(Sv.covers(only, p), Sv.all_covered(only, rest), at_covered(ss, only, p, hs, Comp.and_left(Sv.found_at(ss, p), found_all(ss, rest), hf)),
        found_covered(only, ss, rest, hs, Comp.and_right(Sv.found_at(ss, p), found_all(ss, rest), hf)))

# What the survey pairs is what the restriction kept.
def heres_covered(+only: List<&2, String>, hs: List<&2, Main.Here>) -> Bool:
  match hs:
    case Nil{}:
      True{}
    case Main.Here{+p, e, f} <> rest:
      Bool.and(Sv.covers(only, p), heres_covered(only, rest))

def status_seens_ok(+only: List<&2, String>, +t0: Tree.Tree(), +dg: Map<&2, String>, +bf: Map<&2, String>, +reads: Map<&2, List<&2, U32>>, +props: List<&2, Main.Proposal>, hs: List<&2, Main.Here>, +h: {heres_covered(only, hs) == True{} : Bool}) -> {seens_covered(only, Main.status.seens(t0, dg, bf, reads, props, hs)) == True{} : Bool}:
  match hs:
    case Nil{}:
      {==}
    case Main.Here{+p, +e, +f} <> +rest:
      AL.and_intro(Sv.covers(only, p), seens_covered(only, Main.status.seens(t0, dg, bf, reads, props, rest)), Comp.and_left(Sv.covers(only, p), heres_covered(only, rest), h),
        status_seens_ok(only, t0, dg, bf, reads, props, rest, Comp.and_right(Sv.covers(only, p), heres_covered(only, rest), h)))

def limited_pick(c: Bool, +only: List<&2, String>, +h: Main.Here, +later: List<&2, Main.Here>, +hh: {heres_covered(only, [h]) == True{} : Bool}, +ih: {heres_covered(only, later) == True{} : Bool}) -> {heres_covered(only, Bool.pick(List<&2, Main.Here>, c, h <> later, later)) == True{} : Bool}:
  match c:
    case True{}:
      match h:
        case Main.Here{+p, +e, +f}:
          AL.and_intro(Sv.covers(only, p), heres_covered(only, later), Comp.and_left(Sv.covers(only, p), True{}, hh), ih)
    case False{}:
      ih

def limited_ok(+only: List<&2, String>, +l: Main.Limit, hs: List<&2, Main.Here>, +h: {heres_covered(only, hs) == True{} : Bool}) -> {heres_covered(only, Main.heres.limited(l, hs)) == True{} : Bool}:
  match hs:
    case Nil{}:
      {==}
    case Main.Here{+p, +e, +f} <> +rest:
      limited_pick(Main.here.wanted(l, Main.Here{p, e, f}), only, Main.Here{p, e, f}, Main.heres.limited(l, rest),
        AL.and_intro(Sv.covers(only, p), True{}, Comp.and_left(Sv.covers(only, p), heres_covered(only, rest), h), {==}),
        limited_ok(only, l, rest, Comp.and_right(Sv.covers(only, p), heres_covered(only, rest), h)))

def entry_covered(only: List<&2, String>, e: Tree.Entry) -> Bool:
  Sv.covers(only, Tree.entry_path(e))

def found_in(only: List<&2, String>, f: F.Found) -> Bool:
  Sv.covers(only, F.found.path(f))

def go_ok(fuel: Nat, xs: List<&2, Tree.Entry>, ys: List<&2, F.Found>, c: Cmp, +only: List<&2, String>, +hx: {SortL.all_at(~Tree.Entry, ~List<&2, String>, ~entry_covered, only, xs) == True{} : Bool}, +hy: {SortL.all_at(~F.Found, ~List<&2, String>, ~found_in, only, ys) == True{} : Bool}) -> {heres_covered(only, Main.here.go(fuel, xs, ys, c)) == True{} : Bool}:
  match fuel xs ys c:
    case 0n Nil{} Nil{} _:
      {==}
    case 0n Nil{} y <> yr _:
      {==}
    case 0n x <> xr Nil{} _:
      {==}
    case 0n x <> xr y <> yr _:
      {==}
    case 1n+f Nil{} Nil{} _:
      {==}
    case 1n+f Nil{} +y <> +yr _:
      AL.and_intro(Sv.covers(only, F.found.path(y)), heres_covered(only, Main.here.go(f, Nil{}, yr, Main.here.cmp(Nil{}, yr))),
        Comp.and_left(found_in(only, y), SortL.all_at(~F.Found, ~List<&2, String>, ~found_in, only, yr), hy),
        go_ok(f, Nil{}, yr, Main.here.cmp(Nil{}, yr), only, hx, Comp.and_right(found_in(only, y), SortL.all_at(~F.Found, ~List<&2, String>, ~found_in, only, yr), hy)))
    case 1n+f +x <> +xr Nil{} LT{}:
      AL.and_intro(Sv.covers(only, Tree.entry_path(x)), heres_covered(only, Main.here.go(f, xr, Nil{}, Main.here.cmp(xr, Nil{}))),
        Comp.and_left(entry_covered(only, x), SortL.all_at(~Tree.Entry, ~List<&2, String>, ~entry_covered, only, xr), hx),
        go_ok(f, xr, Nil{}, Main.here.cmp(xr, Nil{}), only, Comp.and_right(entry_covered(only, x), SortL.all_at(~Tree.Entry, ~List<&2, String>, ~entry_covered, only, xr), hx), hy))
    case 1n+f +x <> +xr Nil{} EQ{}:
      AL.and_intro(Sv.covers(only, Tree.entry_path(x)), heres_covered(only, Main.here.go(f, xr, Nil{}, Main.here.cmp(xr, Nil{}))),
        Comp.and_left(entry_covered(only, x), SortL.all_at(~Tree.Entry, ~List<&2, String>, ~entry_covered, only, xr), hx),
        go_ok(f, xr, Nil{}, Main.here.cmp(xr, Nil{}), only, Comp.and_right(entry_covered(only, x), SortL.all_at(~Tree.Entry, ~List<&2, String>, ~entry_covered, only, xr), hx), hy))
    case 1n+f +x <> +xr Nil{} GT{}:
      AL.and_intro(Sv.covers(only, Tree.entry_path(x)), heres_covered(only, Main.here.go(f, xr, Nil{}, Main.here.cmp(xr, Nil{}))),
        Comp.and_left(entry_covered(only, x), SortL.all_at(~Tree.Entry, ~List<&2, String>, ~entry_covered, only, xr), hx),
        go_ok(f, xr, Nil{}, Main.here.cmp(xr, Nil{}), only, Comp.and_right(entry_covered(only, x), SortL.all_at(~Tree.Entry, ~List<&2, String>, ~entry_covered, only, xr), hx), hy))
    case 1n+f +x <> +xr +y <> +yr EQ{}:
      AL.and_intro(Sv.covers(only, Tree.entry_path(x)), heres_covered(only, Main.here.go(f, xr, yr, Main.here.cmp(xr, yr))),
        Comp.and_left(entry_covered(only, x), SortL.all_at(~Tree.Entry, ~List<&2, String>, ~entry_covered, only, xr), hx),
        go_ok(f, xr, yr, Main.here.cmp(xr, yr), only, Comp.and_right(entry_covered(only, x), SortL.all_at(~Tree.Entry, ~List<&2, String>, ~entry_covered, only, xr), hx), Comp.and_right(found_in(only, y), SortL.all_at(~F.Found, ~List<&2, String>, ~found_in, only, yr), hy)))
    case 1n+f +x <> +xr +y <> +yr LT{}:
      AL.and_intro(Sv.covers(only, Tree.entry_path(x)), heres_covered(only, Main.here.go(f, xr, y <> yr, Main.here.cmp(xr, y <> yr))),
        Comp.and_left(entry_covered(only, x), SortL.all_at(~Tree.Entry, ~List<&2, String>, ~entry_covered, only, xr), hx),
        go_ok(f, xr, y <> yr, Main.here.cmp(xr, y <> yr), only, Comp.and_right(entry_covered(only, x), SortL.all_at(~Tree.Entry, ~List<&2, String>, ~entry_covered, only, xr), hx), hy))
    case 1n+f +x <> +xr +y <> +yr GT{}:
      AL.and_intro(Sv.covers(only, F.found.path(y)), heres_covered(only, Main.here.go(f, x <> xr, yr, Main.here.cmp(x <> xr, yr))),
        Comp.and_left(found_in(only, y), SortL.all_at(~F.Found, ~List<&2, String>, ~found_in, only, yr), hy),
        go_ok(f, x <> xr, yr, Main.here.cmp(x <> xr, yr), only, hx, Comp.and_right(found_in(only, y), SortL.all_at(~F.Found, ~List<&2, String>, ~found_in, only, yr), hy)))

def heres_ok(+only: List<&2, String>, +t: Tree.Tree(), +found: List<&2, F.Found>, +hx: {SortL.all_at(~Tree.Entry, ~List<&2, String>, ~entry_covered, only, t) == True{} : Bool}, +hy: {SortL.all_at(~F.Found, ~List<&2, String>, ~found_in, only, found) == True{} : Bool}) -> {heres_covered(only, Main.heres(t, found, Main.Limit.None{})) == True{} : Bool}:
  limited_ok(only, Main.Limit.None{}, Main.here.go(1n+Nat.add(List.length(&2, Tree.Entry, List.sort(~Tree.Entry, ~(a => b => Main.by_path(a, b)), t)), List.length(&2, F.Found, found)), List.sort(~Tree.Entry, ~(a => b => Main.by_path(a, b)), t), found, Main.here.cmp(List.sort(~Tree.Entry, ~(a => b => Main.by_path(a, b)), t), found)),
    go_ok(1n+Nat.add(List.length(&2, Tree.Entry, List.sort(~Tree.Entry, ~(a => b => Main.by_path(a, b)), t)), List.length(&2, F.Found, found)), List.sort(~Tree.Entry, ~(a => b => Main.by_path(a, b)), t), found, Main.here.cmp(List.sort(~Tree.Entry, ~(a => b => Main.by_path(a, b)), t), found), only,
      SortL.all_sort_at(~Tree.Entry, ~(a => b => Main.by_path(a, b)), ~List<&2, String>, ~entry_covered, only, t, hx), hy))

# Keeping only what a test passes keeps a list that passes.
def kept_first(~A: Data, ~C: Data, ~ok: C -> A -> Bool, +c: C, b: Bool, +x: A, +later: List<&2, A>, +hb: {ok(c, x) == b : Bool}, +hl: {SortL.all_at(~A, ~C, ~ok, c, later) == True{} : Bool}) -> {SortL.all_at(~A, ~C, ~ok, c, Bool.pick(List<&2, A>, b, x <> later, later)) == True{} : Bool}:
  match b:
    case True{}:
      AL.and_intro(ok(c, x), SortL.all_at(~A, ~C, ~ok, c, later), hb, hl)
    case False{}:
      hl

def kept_second(~A: Data, ~C: Data, ~ok: C -> A -> Bool, +c: C, b: Bool, +x: A, +later: List<&2, A>, +hx: {ok(c, x) == True{} : Bool}, +hl: {SortL.all_at(~A, ~C, ~ok, c, later) == True{} : Bool}) -> {SortL.all_at(~A, ~C, ~ok, c, Bool.pick(List<&2, A>, b, later, x <> later)) == True{} : Bool}:
  match b:
    case True{}:
      hl
    case False{}:
      AL.and_intro(ok(c, x), SortL.all_at(~A, ~C, ~ok, c, later), hx, hl)

def only_tree_ok(+only: List<&2, String>, t: Tree.Tree()) -> {SortL.all_at(~Tree.Entry, ~List<&2, String>, ~entry_covered, only, Sv.only.tree(only, t)) == True{} : Bool}:
  match t:
    case Nil{}:
      {==}
    case +e <> +rest:
      kept_first(~Tree.Entry, ~List<&2, String>, ~entry_covered, only, Sv.covers(only, Tree.entry_path(e)), e, Sv.only.tree(only, rest), {==}, only_tree_ok(only, rest))

def only_found_ok(+only: List<&2, String>, fs: List<&2, F.Found>) -> {SortL.all_at(~F.Found, ~List<&2, String>, ~found_in, only, Sv.only.found(only, fs)) == True{} : Bool}:
  match fs:
    case Nil{}:
      {==}
    case +f <> +rest:
      kept_first(~F.Found, ~List<&2, String>, ~found_in, only, Sv.covers(only, F.found.path(f)), f, Sv.only.found(only, rest), {==}, only_found_ok(only, rest))

def unclaimed_ok(+only: List<&2, String>, t: Tree.Tree(), +cs: List<&2, T.Split>, +h: {SortL.all_at(~Tree.Entry, ~List<&2, String>, ~entry_covered, only, t) == True{} : Bool}) -> {SortL.all_at(~Tree.Entry, ~List<&2, String>, ~entry_covered, only, Sv.unclaimed(t, cs)) == True{} : Bool}:
  match t:
    case Nil{}:
      {==}
    case +e <> +rest:
      kept_second(~Tree.Entry, ~List<&2, String>, ~entry_covered, only, Sv.claimed.has(cs, Tree.entry_path(e)), e, Sv.unclaimed(rest, cs),
        Comp.and_left(entry_covered(only, e), SortL.all_at(~Tree.Entry, ~List<&2, String>, ~entry_covered, only, rest), h),
        unclaimed_ok(only, rest, cs, Comp.and_right(entry_covered(only, e), SortL.all_at(~Tree.Entry, ~List<&2, String>, ~entry_covered, only, rest), h)))

def unclaimed_found_ok(+only: List<&2, String>, fs: List<&2, F.Found>, +cs: List<&2, T.Split>, +h: {SortL.all_at(~F.Found, ~List<&2, String>, ~found_in, only, fs) == True{} : Bool}) -> {SortL.all_at(~F.Found, ~List<&2, String>, ~found_in, only, Sv.unclaimed_found(fs, cs)) == True{} : Bool}:
  match fs:
    case Nil{}:
      {==}
    case +f <> +rest:
      kept_second(~F.Found, ~List<&2, String>, ~found_in, only, Sv.claimed.has(cs, F.found.path(f)), f, Sv.unclaimed_found(rest, cs),
        Comp.and_left(found_in(only, f), SortL.all_at(~F.Found, ~List<&2, String>, ~found_in, only, rest), h),
        unclaimed_found_ok(only, rest, cs, Comp.and_right(found_in(only, f), SortL.all_at(~F.Found, ~List<&2, String>, ~found_in, only, rest), h)))

# What a record restricted to some paths refuses is among them.
def restricted_ok(+only: List<&2, String>, +t: Tree.Tree(), +t0: Tree.Tree(), +found: List<&2, F.Found>, +walked: List<&2, T.Split>, +held: Set(), +dg: Map<&2, String>, +bf: Map<&2, String>, +reads: Map<&2, List<&2, U32>>, +props: List<&2, Main.Proposal>, +moves: List<&2, T.Split>) -> {Sv.all_covered(only, Sv.planned.refused(Sv.planned(t, Sv.only.tree(only, t), held, Sv.only.refused(only, walked), Main.status.seens(t0, dg, bf, reads, props, Main.heres(Sv.unclaimed(Sv.only.tree(only, t), Sv.claims(Sv.only.tree(only, t))), Sv.unclaimed_found(Sv.only.found(only, found), Sv.claims(Sv.only.tree(only, t))), Main.Limit.None{})), moves))) == True{} : Bool}:
  covered_app(only, Sv.only.refused(only, walked), Sv.refusals(List.append(&2, Sv.Obs, Sv.seens(Main.status.seens(t0, dg, bf, reads, props, Main.heres(Sv.unclaimed(Sv.only.tree(only, t), Sv.claims(Sv.only.tree(only, t))), Sv.unclaimed_found(Sv.only.found(only, found), Sv.claims(Sv.only.tree(only, t))), Main.Limit.None{}))), Sv.claimed_drops(Sv.only.tree(only, t), Sv.claims(Sv.only.tree(only, t)), held))),
    only_refused_ok(only, walked),
    found_covered(only, Main.status.seens(t0, dg, bf, reads, props, Main.heres(Sv.unclaimed(Sv.only.tree(only, t), Sv.claims(Sv.only.tree(only, t))), Sv.unclaimed_found(Sv.only.found(only, found), Sv.claims(Sv.only.tree(only, t))), Main.Limit.None{})), Sv.refusals(List.append(&2, Sv.Obs, Sv.seens(Main.status.seens(t0, dg, bf, reads, props, Main.heres(Sv.unclaimed(Sv.only.tree(only, t), Sv.claims(Sv.only.tree(only, t))), Sv.unclaimed_found(Sv.only.found(only, found), Sv.claims(Sv.only.tree(only, t))), Main.Limit.None{}))), Sv.claimed_drops(Sv.only.tree(only, t), Sv.claims(Sv.only.tree(only, t)), held))),
      status_seens_ok(only, t0, dg, bf, reads, props, Main.heres(Sv.unclaimed(Sv.only.tree(only, t), Sv.claims(Sv.only.tree(only, t))), Sv.unclaimed_found(Sv.only.found(only, found), Sv.claims(Sv.only.tree(only, t))), Main.Limit.None{}),
        heres_ok(only, Sv.unclaimed(Sv.only.tree(only, t), Sv.claims(Sv.only.tree(only, t))), Sv.unclaimed_found(Sv.only.found(only, found), Sv.claims(Sv.only.tree(only, t))),
          unclaimed_ok(only, Sv.only.tree(only, t), Sv.claims(Sv.only.tree(only, t)), only_tree_ok(only, t)),
          unclaimed_found_ok(only, Sv.only.found(only, found), Sv.claims(Sv.only.tree(only, t)), only_found_ok(only, found)))),
      obs_found(Sv.only.tree(only, t), Sv.claims(Sv.only.tree(only, t)), held, Main.status.seens(t0, dg, bf, reads, props, Main.heres(Sv.unclaimed(Sv.only.tree(only, t), Sv.claims(Sv.only.tree(only, t))), Sv.unclaimed_found(Sv.only.found(only, found), Sv.claims(Sv.only.tree(only, t))), Main.Limit.None{})))))

# The renames `status` offers
# ---------------------------

# No departure is keyed by the digest of nothing.
def full_keys(xs: List<&2, T.Split>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case T.Split{+k, v} <> rest:
      Bool.and(Bool.not(String.eq(k, Sv.EMPTY())), full_keys(rest))

def keyed_full(b: Bool, +d: String, +p: String, +rest: List<&2, T.Split>, +eb: {String.eq(d, Sv.EMPTY()) == b : Bool}, +h: {full_keys(rest) == True{} : Bool}) -> {full_keys(Bool.pick(List<&2, T.Split>, b, rest, T.Split{d, p} <> rest)) == True{} : Bool}:
  match b:
    case True{}:
      h
    case False{}:
      AL.and_intro(Bool.not(String.eq(d, Sv.EMPTY())), full_keys(rest), AL.not_true(String.eq(d, Sv.EMPTY()), eb), h)

def departed_full(os: List<&2, Sv.Obs>) -> {full_keys(Sv.departed(os)) == True{} : Bool}:
  match os:
    case Nil{}:
      {==}
    case Sv.Obs.Dropped{f, +p, Some{+d}} <> +rest:
      keyed_full(String.eq(d, Sv.EMPTY()), d, p, Sv.departed(rest), {==}, departed_full(rest))
    case Sv.Obs.Dropped{f, p, None{}} <> rest:
      departed_full(rest)
    case Sv.Obs.Added{p} <> rest:
      departed_full(rest)
    case Sv.Obs.Edited{p} <> rest:
      departed_full(rest)
    case Sv.Obs.Mode{p} <> rest:
      departed_full(rest)
    case Sv.Obs.Refused{p, why} <> rest:
      departed_full(rest)
    case Sv.Obs.Accept{p} <> rest:
      departed_full(rest)
    case Sv.Obs.Points{p, g, h, s} <> rest:
      departed_full(rest)
    case Sv.Obs.Arrived{p, d} <> rest:
      departed_full(rest)
    case Sv.Obs.Emptied{p} <> rest:
      departed_full(rest)
    case Sv.Obs.Marked{p, n} <> rest:
      departed_full(rest)

# The one arrival of some bytes is where `at_digest` finds it.
def at_pick(c: Bool, +k: String, +v: String, +rest: List<&2, T.Split>, +d: String, +ec: {String.eq(k, d) == c : Bool}, h: {Nat.is_eq(Nat.add(Bool.pick(Nat, c, 1n, 0n), Sv.count(rest, d)), 1n) == True{} : Bool}, ih: {Nat.is_eq(Sv.count(rest, d), 1n) == True{} : Bool} -> {Sv.keyed_at(rest, d, Sv.at_digest(rest, d)) == True{} : Bool}) -> {Bool.or(Bool.and(String.eq(k, d), String.eq(v, Bool.pick(String, c, v, Sv.at_digest(rest, d)))), Sv.keyed_at(rest, d, Bool.pick(String, c, v, Sv.at_digest(rest, d)))) == True{} : Bool}:
  match c:
    case True{}:
      %Equal.sym(Bool, String.eq(k, d), True{}, ec) : {Bool.or(Bool.and(_, String.eq(v, v)), Sv.keyed_at(rest, d, v)) == True{} : Bool}
      %Equal.sym(Bool, String.eq(v, v), True{}, S.eq_refl(v)) : {Bool.or(Bool.and(True{}, _), Sv.keyed_at(rest, d, v)) == True{} : Bool}
      {==}
    case False{}:
      AL.or_right(Bool.and(String.eq(k, d), String.eq(v, Sv.at_digest(rest, d))), Sv.keyed_at(rest, d, Sv.at_digest(rest, d)), ih(h))

def at_found(xs: List<&2, T.Split>, +d: String, h: {Nat.is_eq(Sv.count(xs, d), 1n) == True{} : Bool}) -> {Sv.keyed_at(xs, d, Sv.at_digest(xs, d)) == True{} : Bool}:
  match xs:
    case Nil{}:
      Empty.absurd({False{} == True{} : Bool}, S.false_true(h))
    case T.Split{+k, +v} <> +rest:
      at_pick(String.eq(k, d), k, v, rest, d, {==}, h, e => at_found(rest, d, e))

# Each rename `renames.go` makes, with the departures it walks.
type RCtx is Data:
  RCtx{gs: List<&2, T.Split>, all: List<&2, T.Split>, arr: List<&2, T.Split>}

def rename_good(c: RCtx, r: Sv.Rename) -> Bool:
  match c r:
    case RCtx{+gs, +all, +arr} Sv.Rename{+d, +from, +to}:
      Bool.and(Bool.and(Bool.and(Sv.keyed_at(gs, d, from), Bool.not(String.eq(d, Sv.EMPTY()))), Nat.is_eq(Sv.count(all, d), 1n)), Bool.and(Nat.is_eq(Sv.count(arr, d), 1n), Sv.keyed_at(arr, d, to)))

def good_head(+k: String, +v: String, +gs: List<&2, T.Split>, +all: List<&2, T.Split>, +arr: List<&2, T.Split>, +d: String, +from: String, +to: String, +h: {rename_good(RCtx{gs, all, arr}, Sv.Rename{d, from, to}) == True{} : Bool}) -> {rename_good(RCtx{T.Split{k, v} <> gs, all, arr}, Sv.Rename{d, from, to}) == True{} : Bool}:
  AL.and_intro(Bool.and(Bool.and(Sv.keyed_at(T.Split{k, v} <> gs, d, from), Bool.not(String.eq(d, Sv.EMPTY()))), Nat.is_eq(Sv.count(all, d), 1n)), Bool.and(Nat.is_eq(Sv.count(arr, d), 1n), Sv.keyed_at(arr, d, to)),
    AL.and_intro(Bool.and(Sv.keyed_at(T.Split{k, v} <> gs, d, from), Bool.not(String.eq(d, Sv.EMPTY()))), Nat.is_eq(Sv.count(all, d), 1n),
      AL.and_intro(Sv.keyed_at(T.Split{k, v} <> gs, d, from), Bool.not(String.eq(d, Sv.EMPTY())),
        AL.or_right(Bool.and(String.eq(k, d), String.eq(v, from)), Sv.keyed_at(gs, d, from),
          Comp.and_left(Sv.keyed_at(gs, d, from), Bool.not(String.eq(d, Sv.EMPTY())), Comp.and_left(Bool.and(Sv.keyed_at(gs, d, from), Bool.not(String.eq(d, Sv.EMPTY()))), Nat.is_eq(Sv.count(all, d), 1n), Comp.and_left(Bool.and(Bool.and(Sv.keyed_at(gs, d, from), Bool.not(String.eq(d, Sv.EMPTY()))), Nat.is_eq(Sv.count(all, d), 1n)), Bool.and(Nat.is_eq(Sv.count(arr, d), 1n), Sv.keyed_at(arr, d, to)), h)))),
        Comp.and_right(Sv.keyed_at(gs, d, from), Bool.not(String.eq(d, Sv.EMPTY())), Comp.and_left(Bool.and(Sv.keyed_at(gs, d, from), Bool.not(String.eq(d, Sv.EMPTY()))), Nat.is_eq(Sv.count(all, d), 1n), Comp.and_left(Bool.and(Bool.and(Sv.keyed_at(gs, d, from), Bool.not(String.eq(d, Sv.EMPTY()))), Nat.is_eq(Sv.count(all, d), 1n)), Bool.and(Nat.is_eq(Sv.count(arr, d), 1n), Sv.keyed_at(arr, d, to)), h)))),
      Comp.and_right(Bool.and(Sv.keyed_at(gs, d, from), Bool.not(String.eq(d, Sv.EMPTY()))), Nat.is_eq(Sv.count(all, d), 1n), Comp.and_left(Bool.and(Bool.and(Sv.keyed_at(gs, d, from), Bool.not(String.eq(d, Sv.EMPTY()))), Nat.is_eq(Sv.count(all, d), 1n)), Bool.and(Nat.is_eq(Sv.count(arr, d), 1n), Sv.keyed_at(arr, d, to)), h))),
    Comp.and_right(Bool.and(Bool.and(Sv.keyed_at(gs, d, from), Bool.not(String.eq(d, Sv.EMPTY()))), Nat.is_eq(Sv.count(all, d), 1n)), Bool.and(Nat.is_eq(Sv.count(arr, d), 1n), Sv.keyed_at(arr, d, to)), h))

def good_weaken(rs: List<&2, Sv.Rename>, +x: T.Split, +gs: List<&2, T.Split>, +all: List<&2, T.Split>, +arr: List<&2, T.Split>, +h: {SortL.all_at(~Sv.Rename, ~RCtx, ~rename_good, RCtx{gs, all, arr}, rs) == True{} : Bool}) -> {SortL.all_at(~Sv.Rename, ~RCtx, ~rename_good, RCtx{x <> gs, all, arr}, rs) == True{} : Bool}:
  match rs:
    case Nil{}:
      {==}
    case Sv.Rename{+d, +from, +to} <> +rest:
      match x:
        case T.Split{+k, +v}:
          AL.and_intro(rename_good(RCtx{T.Split{k, v} <> gs, all, arr}, Sv.Rename{d, from, to}), SortL.all_at(~Sv.Rename, ~RCtx, ~rename_good, RCtx{T.Split{k, v} <> gs, all, arr}, rest),
            good_head(k, v, gs, all, arr, d, from, to, Comp.and_left(rename_good(RCtx{gs, all, arr}, Sv.Rename{d, from, to}), SortL.all_at(~Sv.Rename, ~RCtx, ~rename_good, RCtx{gs, all, arr}, rest), h)),
            good_weaken(rest, T.Split{k, v}, gs, all, arr, Comp.and_right(rename_good(RCtx{gs, all, arr}, Sv.Rename{d, from, to}), SortL.all_at(~Sv.Rename, ~RCtx, ~rename_good, RCtx{gs, all, arr}, rest), h)))

def keyed_here(+d: String, +from: String, -rest: List<&2, T.Split>) -> {Sv.keyed_at(T.Split{d, from} <> rest, d, from) == True{} : Bool}:
  %Equal.sym(Bool, String.eq(d, d), True{}, S.eq_refl(d)) : {Bool.or(Bool.and(_, String.eq(from, from)), Sv.keyed_at(rest, d, from)) == True{} : Bool}
  %Equal.sym(Bool, String.eq(from, from), True{}, S.eq_refl(from)) : {Bool.or(Bool.and(True{}, _), Sv.keyed_at(rest, d, from)) == True{} : Bool}
  {==}

def go_pick(c: Bool, +d: String, +from: String, +rest: List<&2, T.Split>, +all: List<&2, T.Split>, +arr: List<&2, T.Split>, +later: List<&2, Sv.Rename>, +ec: {Bool.and(Nat.is_eq(Sv.count(all, d), 1n), Nat.is_eq(Sv.count(arr, d), 1n)) == c : Bool}, +hne: {Bool.not(String.eq(d, Sv.EMPTY())) == True{} : Bool}, +ih: {SortL.all_at(~Sv.Rename, ~RCtx, ~rename_good, RCtx{T.Split{d, from} <> rest, all, arr}, later) == True{} : Bool}) -> {SortL.all_at(~Sv.Rename, ~RCtx, ~rename_good, RCtx{T.Split{d, from} <> rest, all, arr}, Bool.pick(List<&2, Sv.Rename>, c, Sv.Rename{d, from, Sv.at_digest(arr, d)} <> later, later)) == True{} : Bool}:
  match c:
    case True{}:
      AL.and_intro(rename_good(RCtx{T.Split{d, from} <> rest, all, arr}, Sv.Rename{d, from, Sv.at_digest(arr, d)}), SortL.all_at(~Sv.Rename, ~RCtx, ~rename_good, RCtx{T.Split{d, from} <> rest, all, arr}, later),
        AL.and_intro(Bool.and(Bool.and(Sv.keyed_at(T.Split{d, from} <> rest, d, from), Bool.not(String.eq(d, Sv.EMPTY()))), Nat.is_eq(Sv.count(all, d), 1n)), Bool.and(Nat.is_eq(Sv.count(arr, d), 1n), Sv.keyed_at(arr, d, Sv.at_digest(arr, d))),
          AL.and_intro(Bool.and(Sv.keyed_at(T.Split{d, from} <> rest, d, from), Bool.not(String.eq(d, Sv.EMPTY()))), Nat.is_eq(Sv.count(all, d), 1n),
            AL.and_intro(Sv.keyed_at(T.Split{d, from} <> rest, d, from), Bool.not(String.eq(d, Sv.EMPTY())), keyed_here(d, from, rest), hne),
            Comp.and_left(Nat.is_eq(Sv.count(all, d), 1n), Nat.is_eq(Sv.count(arr, d), 1n), ec)),
          AL.and_intro(Nat.is_eq(Sv.count(arr, d), 1n), Sv.keyed_at(arr, d, Sv.at_digest(arr, d)),
            Comp.and_right(Nat.is_eq(Sv.count(all, d), 1n), Nat.is_eq(Sv.count(arr, d), 1n), ec),
            at_found(arr, d, Comp.and_right(Nat.is_eq(Sv.count(all, d), 1n), Nat.is_eq(Sv.count(arr, d), 1n), ec)))),
        ih)
    case False{}:
      ih

def go_good(gs: List<&2, T.Split>, +all: List<&2, T.Split>, +arr: List<&2, T.Split>, +hf: {full_keys(gs) == True{} : Bool}) -> {SortL.all_at(~Sv.Rename, ~RCtx, ~rename_good, RCtx{gs, all, arr}, Sv.renames.go(gs, all, arr)) == True{} : Bool}:
  match gs:
    case Nil{}:
      {==}
    case T.Split{+d, +from} <> +rest:
      go_pick(Bool.and(Nat.is_eq(Sv.count(all, d), 1n), Nat.is_eq(Sv.count(arr, d), 1n)), d, from, rest, all, arr, Sv.renames.go(rest, all, arr), {==},
        Comp.and_left(Bool.not(String.eq(d, Sv.EMPTY())), full_keys(rest), hf),
        good_weaken(Sv.renames.go(rest, all, arr), T.Split{d, from}, rest, all, arr, go_good(rest, all, arr, Comp.and_right(Bool.not(String.eq(d, Sv.EMPTY())), full_keys(rest), hf))))

# The departure found is a witness to the bytes a rename moved.
def bytes_here(+k: String, +v: String, +rest: List<&2, T.Split>, +deps: List<&2, T.Split>, +arrs: List<&2, T.Split>, +d: String, +from: String, +to: String, +hk: {String.eq(k, d) == True{} : Bool}, +hv: {String.eq(v, from) == True{} : Bool}, +hne: {Bool.not(String.eq(d, Sv.EMPTY())) == True{} : Bool}, +hc1: {Nat.is_eq(Sv.count(deps, d), 1n) == True{} : Bool}, +hc2: {Nat.is_eq(Sv.count(arrs, d), 1n) == True{} : Bool}, +ht: {Sv.keyed_at(arrs, d, to) == True{} : Bool}) -> {Sv.bytes_moved(T.Split{k, v} <> rest, deps, arrs, from, to) == True{} : Bool}:
  %Equal.sym(String, k, d, S.eq_true(k, d, hk)) : {Bool.or(Bool.and(Bool.and(Bool.and(String.eq(v, from), Bool.not(String.eq(_, Sv.EMPTY()))), Nat.is_eq(Sv.count(deps, _), 1n)), Bool.and(Nat.is_eq(Sv.count(arrs, _), 1n), Sv.keyed_at(arrs, _, to))), Sv.bytes_moved(rest, deps, arrs, from, to)) == True{} : Bool}
  AL.or_left(Bool.and(Bool.and(Bool.and(String.eq(v, from), Bool.not(String.eq(d, Sv.EMPTY()))), Nat.is_eq(Sv.count(deps, d), 1n)), Bool.and(Nat.is_eq(Sv.count(arrs, d), 1n), Sv.keyed_at(arrs, d, to))), Sv.bytes_moved(rest, deps, arrs, from, to),
    AL.and_intro(Bool.and(Bool.and(String.eq(v, from), Bool.not(String.eq(d, Sv.EMPTY()))), Nat.is_eq(Sv.count(deps, d), 1n)), Bool.and(Nat.is_eq(Sv.count(arrs, d), 1n), Sv.keyed_at(arrs, d, to)),
      AL.and_intro(Bool.and(String.eq(v, from), Bool.not(String.eq(d, Sv.EMPTY()))), Nat.is_eq(Sv.count(deps, d), 1n), AL.and_intro(String.eq(v, from), Bool.not(String.eq(d, Sv.EMPTY())), hv, hne), hc1),
      AL.and_intro(Nat.is_eq(Sv.count(arrs, d), 1n), Sv.keyed_at(arrs, d, to), hc2, ht)))

def moved_intro(ds: List<&2, T.Split>, +deps: List<&2, T.Split>, +arrs: List<&2, T.Split>, +d: String, +from: String, +to: String, hk: {Sv.keyed_at(ds, d, from) == True{} : Bool}, +hne: {Bool.not(String.eq(d, Sv.EMPTY())) == True{} : Bool}, +hc1: {Nat.is_eq(Sv.count(deps, d), 1n) == True{} : Bool}, +hc2: {Nat.is_eq(Sv.count(arrs, d), 1n) == True{} : Bool}, +ht: {Sv.keyed_at(arrs, d, to) == True{} : Bool}) -> {Sv.bytes_moved(ds, deps, arrs, from, to) == True{} : Bool}:
  match ds:
    case Nil{}:
      Empty.absurd({False{} == True{} : Bool}, S.false_true(hk))
    case T.Split{+k, +v} <> +rest:
      AL.or_cases({Sv.bytes_moved(T.Split{k, v} <> rest, deps, arrs, from, to) == True{} : Bool}, Bool.and(String.eq(k, d), String.eq(v, from)), Sv.keyed_at(rest, d, from), hk,
        +hl => bytes_here(k, v, rest, deps, arrs, d, from, to, Comp.and_left(String.eq(k, d), String.eq(v, from), hl), Comp.and_right(String.eq(k, d), String.eq(v, from), hl), hne, hc1, hc2, ht),
        hr => AL.or_right(Bool.and(Bool.and(Bool.and(String.eq(v, from), Bool.not(String.eq(k, Sv.EMPTY()))), Nat.is_eq(Sv.count(deps, k), 1n)), Bool.and(Nat.is_eq(Sv.count(arrs, k), 1n), Sv.keyed_at(arrs, k, to))), Sv.bytes_moved(rest, deps, arrs, from, to),
          moved_intro(rest, deps, arrs, d, from, to, hr, hne, hc1, hc2, ht)))

def map_good(rs: List<&2, Sv.Rename>, +deps: List<&2, T.Split>, +arrs: List<&2, T.Split>, +h: {SortL.all_at(~Sv.Rename, ~RCtx, ~rename_good, RCtx{deps, deps, arrs}, rs) == True{} : Bool}) -> {Sv.renames_ok(deps, arrs, T.map(~Sv.Rename, ~T.Split, ~(r => Sv.rename_pair(r)), rs)) == True{} : Bool}:
  match rs:
    case Nil{}:
      {==}
    case Sv.Rename{+d, +from, +to} <> +rest:
      AL.and_intro(Sv.bytes_moved(deps, deps, arrs, from, to), Sv.renames_ok(deps, arrs, T.map(~Sv.Rename, ~T.Split, ~(r => Sv.rename_pair(r)), rest)),
        moved_intro(deps, deps, arrs, d, from, to,
          Comp.and_left(Sv.keyed_at(deps, d, from), Bool.not(String.eq(d, Sv.EMPTY())), Comp.and_left(Bool.and(Sv.keyed_at(deps, d, from), Bool.not(String.eq(d, Sv.EMPTY()))), Nat.is_eq(Sv.count(deps, d), 1n), Comp.and_left(Bool.and(Bool.and(Sv.keyed_at(deps, d, from), Bool.not(String.eq(d, Sv.EMPTY()))), Nat.is_eq(Sv.count(deps, d), 1n)), Bool.and(Nat.is_eq(Sv.count(arrs, d), 1n), Sv.keyed_at(arrs, d, to)), Comp.and_left(rename_good(RCtx{deps, deps, arrs}, Sv.Rename{d, from, to}), SortL.all_at(~Sv.Rename, ~RCtx, ~rename_good, RCtx{deps, deps, arrs}, rest), h)))),
          Comp.and_right(Sv.keyed_at(deps, d, from), Bool.not(String.eq(d, Sv.EMPTY())), Comp.and_left(Bool.and(Sv.keyed_at(deps, d, from), Bool.not(String.eq(d, Sv.EMPTY()))), Nat.is_eq(Sv.count(deps, d), 1n), Comp.and_left(Bool.and(Bool.and(Sv.keyed_at(deps, d, from), Bool.not(String.eq(d, Sv.EMPTY()))), Nat.is_eq(Sv.count(deps, d), 1n)), Bool.and(Nat.is_eq(Sv.count(arrs, d), 1n), Sv.keyed_at(arrs, d, to)), Comp.and_left(rename_good(RCtx{deps, deps, arrs}, Sv.Rename{d, from, to}), SortL.all_at(~Sv.Rename, ~RCtx, ~rename_good, RCtx{deps, deps, arrs}, rest), h)))),
          Comp.and_right(Bool.and(Sv.keyed_at(deps, d, from), Bool.not(String.eq(d, Sv.EMPTY()))), Nat.is_eq(Sv.count(deps, d), 1n), Comp.and_left(Bool.and(Bool.and(Sv.keyed_at(deps, d, from), Bool.not(String.eq(d, Sv.EMPTY()))), Nat.is_eq(Sv.count(deps, d), 1n)), Bool.and(Nat.is_eq(Sv.count(arrs, d), 1n), Sv.keyed_at(arrs, d, to)), Comp.and_left(rename_good(RCtx{deps, deps, arrs}, Sv.Rename{d, from, to}), SortL.all_at(~Sv.Rename, ~RCtx, ~rename_good, RCtx{deps, deps, arrs}, rest), h))),
          Comp.and_left(Nat.is_eq(Sv.count(arrs, d), 1n), Sv.keyed_at(arrs, d, to), Comp.and_right(Bool.and(Bool.and(Sv.keyed_at(deps, d, from), Bool.not(String.eq(d, Sv.EMPTY()))), Nat.is_eq(Sv.count(deps, d), 1n)), Bool.and(Nat.is_eq(Sv.count(arrs, d), 1n), Sv.keyed_at(arrs, d, to)), Comp.and_left(rename_good(RCtx{deps, deps, arrs}, Sv.Rename{d, from, to}), SortL.all_at(~Sv.Rename, ~RCtx, ~rename_good, RCtx{deps, deps, arrs}, rest), h))),
          Comp.and_right(Nat.is_eq(Sv.count(arrs, d), 1n), Sv.keyed_at(arrs, d, to), Comp.and_right(Bool.and(Bool.and(Sv.keyed_at(deps, d, from), Bool.not(String.eq(d, Sv.EMPTY()))), Nat.is_eq(Sv.count(deps, d), 1n)), Bool.and(Nat.is_eq(Sv.count(arrs, d), 1n), Sv.keyed_at(arrs, d, to)), Comp.and_left(rename_good(RCtx{deps, deps, arrs}, Sv.Rename{d, from, to}), SortL.all_at(~Sv.Rename, ~RCtx, ~rename_good, RCtx{deps, deps, arrs}, rest), h)))),
        map_good(rest, deps, arrs, Comp.and_right(rename_good(RCtx{deps, deps, arrs}, Sv.Rename{d, from, to}), SortL.all_at(~Sv.Rename, ~RCtx, ~rename_good, RCtx{deps, deps, arrs}, rest), h)))

def renames_good(+os: List<&2, Sv.Obs>) -> {Sv.renames_ok(Sv.departed(os), Sv.arrived(os), Sv.renames(Sv.departed(os), Sv.arrived(os))) == True{} : Bool}:
  map_good(List.sort(~Sv.Rename, ~(a => b => Sv.rename_le(a, b)), Sv.renames.go(Sv.departed(os), Sv.departed(os), Sv.arrived(os))), Sv.departed(os), Sv.arrived(os),
    SortL.all_sort_at(~Sv.Rename, ~(a => b => Sv.rename_le(a, b)), ~RCtx, ~rename_good, RCtx{Sv.departed(os), Sv.departed(os), Sv.arrived(os)}, Sv.renames.go(Sv.departed(os), Sv.departed(os), Sv.arrived(os)),
      go_good(Sv.departed(os), Sv.departed(os), Sv.arrived(os), departed_full(os))))

# The position `record` plans from
# --------------------------------

def order_same(t: Tree.Tree(), +k: String) -> {Sv.file_order.from(t, k) == SortL.sorted.from(~Tree.Entry, ~Tree.entry_file, t, k) : Bool}:
  match t:
    case Nil{}:
      {==}
    case +e <> +rest:
      Equal.cong(Bool, Bool, x => Bool.and(String.is_le(k, Tree.entry_file(e)), x), Sv.file_order.from(rest, Tree.entry_file(e)), SortL.sorted.from(~Tree.Entry, ~Tree.entry_file, rest, Tree.entry_file(e)), order_same(rest, Tree.entry_file(e)))

def by_file_ordered(+t: Tree.Tree()) -> {Sv.in_file_order(Sv.by_file(t)) == True{} : Bool}:
  Equal.trans(Bool, Sv.file_order.from(Sv.by_file(t), SNil{}), SortL.sorted.from(~Tree.Entry, ~Tree.entry_file, Sv.by_file(t), SNil{}), True{},
    order_same(Sv.by_file(t), SNil{}), SortL.sort_sorted(~Tree.Entry, ~Tree.entry_file, t))

def by_file_keeps(+t: Tree.Tree(), +f: String) -> {Main.entries.at(f, Sv.by_file(t)) == Main.entries.at(f, t) : Tree.Tree()}:
  Equal.trans(Tree.Tree(), Main.entries.at(f, Sv.by_file(t)), SortL.keyed(~Tree.Entry, ~Tree.entry_file, f, Sv.by_file(t)), Main.entries.at(f, t),
    PairL.kd_at(f, Sv.by_file(t)),
    Equal.trans(Tree.Tree(), SortL.keyed(~Tree.Entry, ~Tree.entry_file, f, Sv.by_file(t)), SortL.keyed(~Tree.Entry, ~Tree.entry_file, f, t), Main.entries.at(f, t),
      SortL.sort_keyed(~Tree.Entry, ~Tree.entry_file, t, f),
      Equal.sym(Tree.Tree(), Main.entries.at(f, t), SortL.keyed(~Tree.Entry, ~Tree.entry_file, f, t), PairL.kd_at(f, t))))

# A link written as a reference
# -----------------------------

def head_r(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{c, rest}:
      Char.is_eq(c, 'r')

def r_not_v(-x: String, -y: String, e: {SCon{'v', x} == SCon{'r', y} : String}) -> Empty:
  S.false_true(Equal.cong(String, Bool, s => head_r(s), SCon{'v', x}, SCon{'r', y}, e))

def tail_of(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{c, rest}:
      rest

def stated_pick(c: Bool, +t: Tree.Tree(), +gone: Set(), +arriving: Set(), +path: String, +target: String, +a: String, +at: String, +er: {Sv.resolved(path, target) == Some{a} : Maybe<&2, String>}, +ec: {Sv.stated(t, gone, arriving, a) == c : Bool}, e: {Bool.pick(String, c, SCon{'r', a}, SCon{'v', target}) == SCon{'r', at} : String}) -> {Sv.lands_on(t, gone, arriving, path, target, at) == True{} : Bool}:
  match c:
    case True{}:
      %Equal.cong(String, String, s => tail_of(s), SCon{'r', a}, SCon{'r', at}, e) : {Sv.lands_on(t, gone, arriving, path, target, _) == True{} : Bool}
      %Equal.sym(Maybe<&2, String>, Sv.resolved(path, target), Some{a}, er) : {Bool.and(Sv.maybe_eq(_, Some{a}), Sv.stated(t, gone, arriving, a)) == True{} : Bool}
      %Equal.sym(Bool, String.eq(a, a), True{}, S.eq_refl(a)) : {Bool.and(_, Sv.stated(t, gone, arriving, a)) == True{} : Bool}
      ec
    case False{}:
      Empty.absurd({Sv.lands_on(t, gone, arriving, path, target, at) == True{} : Bool}, r_not_v(target, at, e))

def observed_of(+t: Tree.Tree(), +gone: Set(), +arriving: Set(), +path: String, +target: String, r: Maybe<&2, String>, +er: {Sv.resolved(path, target) == r : Maybe<&2, String>}, +at: String, e: {Sv.observed.of(t, gone, arriving, target, r) == SCon{'r', at} : String}) -> {Sv.lands_on(t, gone, arriving, path, target, at) == True{} : Bool}:
  match r:
    case None{}:
      Empty.absurd({Sv.lands_on(t, gone, arriving, path, target, at) == True{} : Bool}, r_not_v(target, at, e))
    case Some{+a}:
      stated_pick(Sv.stated(t, gone, arriving, a), t, gone, arriving, path, target, a, at, er, {==}, e)

def observed_ok(+t: Tree.Tree(), +gone: Set(), +arriving: Set(), +path: String, +target: String, +at: String, e: {Sv.observed(t, gone, arriving, path, target) == SCon{'r', at} : String}) -> {Sv.lands_on(t, gone, arriving, path, target, at) == True{} : Bool}:
  observed_of(t, gone, arriving, path, target, Sv.resolved(path, target), {==}, at, e)

# A path claimed once
# -------------------

def sdisc(xs: List<&2, T.Split>) -> Type:
  match xs:
    case Nil{}:
      Empty
    case x <> rest:
      Unit

def split_nil(-x: T.Split, -rest: List<&2, T.Split>, e: {x <> rest == Nil{} : List<&2, T.Split>}) -> Empty:
  %e : {sdisc(_) : Type}
  Unit{}

def empty_nil(xs: List<&2, T.Split>, h: {List.is_empty(&2, T.Split, xs) == True{} : Bool}) -> {xs == Nil{} : List<&2, T.Split>}:
  match xs:
    case Nil{}:
      {==}
    case x <> rest:
      Empty.absurd({x <> rest == Nil{} : List<&2, T.Split>}, S.false_true(h))

def done_cond(c: Bool, -r: Main.Refused, -rest: Result<&2, &2, Main.Refused, Sv.Planned>, -done: Sv.Planned, e: {Bool.pick(Result<&2, &2, Main.Refused, Sv.Planned>, c, Fail{r}, rest) == Done{done} : Result<&2, &2, Main.Refused, Sv.Planned>}) -> {c == False{} : Bool}:
  match c:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, Blamed.fail_done(Sv.Planned, r, done, e))
    case False{}:
      {==}

def cnt(xs: List<&2, String>, +q: String) -> Nat:
  List.length(&2, String, SortL.keyed(~String, ~(s => s), q, xs))

def gt_false_le(a: Nat, b: Nat, e: {Nat.is_gt(a, b) == False{} : Bool}) -> {Nat.is_le(a, b) == True{} : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      Empty.absurd({Nat.is_le(1n+p, 0n) == True{} : Bool}, S.true_false(e))
    case 1n+p 1n+q:
      gt_false_le(p, q, e)

def run_cond(c: Bool, -x: T.Split, -rest: List<&2, T.Split>, e: {Bool.pick(List<&2, T.Split>, c, x <> rest, rest) == Nil{} : List<&2, T.Split>}) -> {c == False{} : Bool}:
  match c:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, split_nil(x, rest, e))
    case False{}:
      {==}

def run_rest(c: Bool, -x: T.Split, -rest: List<&2, T.Split>, e: {Bool.pick(List<&2, T.Split>, c, x <> rest, rest) == Nil{} : List<&2, T.Split>}) -> {rest == Nil{} : List<&2, T.Split>}:
  match c:
    case True{}:
      Empty.absurd({rest == Nil{} : List<&2, T.Split>}, split_nil(x, rest, e))
    case False{}:
      e

def add_succ_r(a: Nat, -b: Nat) -> {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add_succ_r(p, b) : {1n+Nat.add(p, 1n+b) == 1n+_ : Nat}
      {==}

# The end of the paths: the run in hand is the one path left.
def nil_case(c: Bool, +n: Nat, h: {Nat.is_le(n, 1n) == True{} : Bool}) -> {Nat.is_le(Nat.add(Bool.pick(Nat, c, n, 0n), 0n), 1n) == True{} : Bool}:
  match c:
    case True{}:
      %Equal.sym(Nat, Nat.add(n, 0n), n, Comp.add_zero(n)) : {Nat.is_le(_, 1n) == True{} : Bool}
      h
    case False{}:
      {==}

# Another of the run's path: it counts once more.
def same_case(d: Bool, -x: String, +n: Nat, +k: List<&2, String>, ih: {Nat.is_le(Nat.add(Bool.pick(Nat, d, 1n+n, 0n), List.length(&2, String, k)), 1n) == True{} : Bool}) -> {Nat.is_le(Nat.add(Bool.pick(Nat, d, n, 0n), List.length(&2, String, Bool.pick(List<&2, String>, d, x <> k, k))), 1n) == True{} : Bool}:
  match d:
    case True{}:
      %Equal.sym(Nat, Nat.add(n, 1n+List.length(&2, String, k)), 1n+Nat.add(n, List.length(&2, String, k)), add_succ_r(n, List.length(&2, String, k))) : {Nat.is_le(_, 1n) == True{} : Bool}
      ih
    case False{}:
      ih

# A path counted where it is, and not in the run before it.
def one_case(e2: Bool, -x: String, +k: List<&2, String>, ih: {Nat.is_le(Nat.add(Bool.pick(Nat, e2, 1n, 0n), List.length(&2, String, k)), 1n) == True{} : Bool}) -> {Nat.is_le(List.length(&2, String, Bool.pick(List<&2, String>, e2, x <> k, k)), 1n) == True{} : Bool}:
  match e2:
    case True{}:
      ih
    case False{}:
      ih

def cmp_le(c: Cmp, h1: {Cmp.is_le(SortL.cflip(c)) == True{} : Bool}, hne: {Cmp.is_eq(c) == False{} : Bool}) -> {Cmp.is_le(c) == False{} : Bool}:
  match c:
    case LT{}:
      Empty.absurd({True{} == False{} : Bool}, S.false_true(h1))
    case EQ{}:
      Empty.absurd({True{} == False{} : Bool}, S.true_false(hne))
    case GT{}:
      {==}

# No earlier path is at or after a later one it is not.
def antisym(+a: String, +b: String, h1: {String.is_le(a, b) == True{} : Bool}, hne: {String.eq(b, a) == False{} : Bool}) -> {String.is_le(b, a) == False{} : Bool}:
  cmp_le(String.order(b, a),
    Equal.trans(Bool, Cmp.is_le(SortL.cflip(String.order(b, a))), Cmp.is_le(String.order(a, b)), True{},
      Equal.cong(Cmp, Bool, c => Cmp.is_le(c), SortL.cflip(String.order(b, a)), String.order(a, b), Equal.sym(Cmp, String.order(a, b), SortL.cflip(String.order(b, a)), SortL.str_flip(b, a))),
      h1),
    Equal.trans(Bool, Cmp.is_eq(String.order(b, a)), String.eq(b, a), False{}, Equal.sym(Bool, String.eq(b, a), Cmp.is_eq(String.order(b, a)), S.eq_order(b, a)), hne))

# The path of a run that ended: no later path is it.
def diff_case(d: Bool, +path: String, +p: String, +q: String, +n: Nat, +rest: List<&2, String>, +ed: {String.eq(path, q) == d : Bool}, +hne: {String.eq(p, path) == False{} : Bool}, +hle: {String.is_le(path, p) == True{} : Bool}, +hs: {SortL.sorted.from(~String, ~(s => s), rest, p) == True{} : Bool}, +hn: {Nat.is_le(n, 1n) == True{} : Bool}, ih: {Nat.is_le(Nat.add(Bool.pick(Nat, String.eq(p, q), 1n, 0n), cnt(rest, q)), 1n) == True{} : Bool}) -> {Nat.is_le(Nat.add(Bool.pick(Nat, d, n, 0n), List.length(&2, String, Bool.pick(List<&2, String>, String.eq(p, q), p <> SortL.keyed(~String, ~(s => s), q, rest), SortL.keyed(~String, ~(s => s), q, rest)))), 1n) == True{} : Bool}:
  match d:
    case True{}:
      %S.eq_true(path, q, ed) : {Nat.is_le(Nat.add(n, List.length(&2, String, Bool.pick(List<&2, String>, String.eq(p, _), p <> SortL.keyed(~String, ~(s => s), _, rest), SortL.keyed(~String, ~(s => s), _, rest)))), 1n) == True{} : Bool}
      %Equal.sym(Bool, String.eq(p, path), False{}, hne) : {Nat.is_le(Nat.add(n, List.length(&2, String, Bool.pick(List<&2, String>, _, p <> SortL.keyed(~String, ~(s => s), path, rest), SortL.keyed(~String, ~(s => s), path, rest)))), 1n) == True{} : Bool}
      %Equal.sym(List<&2, String>, SortL.keyed(~String, ~(s => s), path, rest), Nil{}, SortL.keyed_none(~String, ~(s => s), rest, p, path, antisym(path, p, hle, hne), hs)) : {Nat.is_le(Nat.add(n, List.length(&2, String, _)), 1n) == True{} : Bool}
      nil_case(True{}, n, hn)
    case False{}:
      one_case(String.eq(p, q), p, SortL.keyed(~String, ~(s => s), q, rest), ih)

def sorted_at(+rest: List<&2, String>, +a: String, +b: String, e: {a == b : String}, h: {SortL.sorted.from(~String, ~(s => s), rest, a) == True{} : Bool}) -> {SortL.sorted.from(~String, ~(s => s), rest, b) == True{} : Bool}:
  %e : {SortL.sorted.from(~String, ~(s => s), rest, _) == True{} : Bool}
  h

def go_same(c: Bool, +p: String, +rest: List<&2, String>, +path: String, +n: Nat, +q: String, +ec: {String.eq(p, path) == c : Bool}, +hs: {SortL.sorted.from(~String, ~(s => s), rest, p) == True{} : Bool}, +hle: {String.is_le(path, p) == True{} : Bool}, +e: {Sv.claims.go(p <> rest, path, n, c) == Nil{} : List<&2, T.Split>}, ihs: @m: Nat -> {SortL.sorted.from(~String, ~(s => s), rest, path) == True{} : Bool} -> {Sv.claims.go(rest, path, m, Sv.heads_eq(rest, path)) == Nil{} : List<&2, T.Split>} -> {Nat.is_le(Nat.add(Bool.pick(Nat, String.eq(path, q), m, 0n), cnt(rest, q)), 1n) == True{} : Bool}, ihd: {Sv.claims.go(rest, p, 1n, Sv.heads_eq(rest, p)) == Nil{} : List<&2, T.Split>} -> {Nat.is_le(Nat.add(Bool.pick(Nat, String.eq(p, q), 1n, 0n), cnt(rest, q)), 1n) == True{} : Bool}) -> {Nat.is_le(Nat.add(Bool.pick(Nat, String.eq(path, q), n, 0n), cnt(p <> rest, q)), 1n) == True{} : Bool}:
  match c:
    case True{}:
      %Equal.sym(String, p, path, S.eq_true(p, path, ec)) : {Nat.is_le(Nat.add(Bool.pick(Nat, String.eq(path, q), n, 0n), List.length(&2, String, Bool.pick(List<&2, String>, String.eq(_, q), p <> SortL.keyed(~String, ~(s => s), q, rest), SortL.keyed(~String, ~(s => s), q, rest)))), 1n) == True{} : Bool}
      same_case(String.eq(path, q), p, n, SortL.keyed(~String, ~(s => s), q, rest), ihs(1n+n, sorted_at(rest, p, path, S.eq_true(p, path, ec), hs), e))
    case False{}:
      diff_case(String.eq(path, q), path, p, q, n, rest, {==}, ec, hle, hs,
        gt_false_le(n, 1n, run_cond(Nat.is_gt(n, 1n), T.Split{path, Nat.show(n)}, Sv.claims.go(rest, p, 1n, Sv.heads_eq(rest, p)), e)),
        ihd(run_rest(Nat.is_gt(n, 1n), T.Split{path, Nat.show(n)}, Sv.claims.go(rest, p, 1n, Sv.heads_eq(rest, p)), e)))

# Walking the sorted paths in runs: where no run is longer than one, no
# path is counted twice.
def go_once(ps: List<&2, String>, +path: String, +n: Nat, +q: String, +hs: {SortL.sorted.from(~String, ~(s => s), ps, path) == True{} : Bool}, e: {Sv.claims.go(ps, path, n, Sv.heads_eq(ps, path)) == Nil{} : List<&2, T.Split>}) -> {Nat.is_le(Nat.add(Bool.pick(Nat, String.eq(path, q), n, 0n), cnt(ps, q)), 1n) == True{} : Bool}:
  match ps:
    case Nil{}:
      nil_case(String.eq(path, q), n, gt_false_le(n, 1n, run_cond(Nat.is_gt(n, 1n), T.Split{path, Nat.show(n)}, Nil{}, e)))
    case +p <> +rest:
      go_same(String.eq(p, path), p, rest, path, n, q, {==},
        Comp.and_right(String.is_le(path, p), SortL.sorted.from(~String, ~(s => s), rest, p), hs),
        Comp.and_left(String.is_le(path, p), SortL.sorted.from(~String, ~(s => s), rest, p), hs),
        e,
        m => h => e2 => go_once(rest, path, m, q, h, e2),
        e3 => go_once(rest, p, 1n, q, Comp.and_right(String.is_le(path, p), SortL.sorted.from(~String, ~(s => s), rest, p), hs), e3))

def claims_once(ps: List<&2, String>, +q: String, +hs: {SortL.sorted.from(~String, ~(s => s), ps, SNil{}) == True{} : Bool}, e: {Sv.claims.of(ps) == Nil{} : List<&2, T.Split>}) -> {Nat.is_le(cnt(ps, q), 1n) == True{} : Bool}:
  match ps:
    case Nil{}:
      {==}
    case +p <> +rest:
      one_case(String.eq(p, q), p, SortL.keyed(~String, ~(s => s), q, rest), go_once(rest, p, 1n, q, Comp.and_right(String.is_le(SNil{}, p), SortL.sorted.from(~String, ~(s => s), rest, p), hs), e))

# The files at a path are as many as the paths it has among them.
def keep_len(c: Bool, -f: String, -x: String, -xs: List<&2, String>, -ys: List<&2, String>, ih: {List.length(&2, String, xs) == List.length(&2, String, ys) : Nat}) -> {List.length(&2, String, Rev.keep(c, f, xs)) == List.length(&2, String, Bool.pick(List<&2, String>, c, x <> ys, ys)) : Nat}:
  match c:
    case True{}:
      Equal.cong(Nat, Nat, m => 1n+m, List.length(&2, String, xs), List.length(&2, String, ys), ih)
    case False{}:
      ih

def at_len(t: Tree.Tree(), +p: String) -> {List.length(&2, String, Tree.at(t, p)) == cnt(Sv.paths(t), p) : Nat}:
  match t:
    case Nil{}:
      {==}
    case Tree.Entry{+f, +q, k, y, g, m} <> +rest:
      keep_len(String.eq(q, p), f, q, Tree.at(rest, p), SortL.keyed(~String, ~(s => s), p, Sv.paths(rest)), at_len(rest, p))

def amo(xs: List<&2, String>, h: {Nat.is_le(List.length(&2, String, xs), 1n) == True{} : Bool}) -> {Tree.at_most_one(xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case x <> Nil{}:
      {==}
    case x <> y <> rest:
      Empty.absurd({False{} == True{} : Bool}, S.false_true(h))

# Where no path is claimed, each holds at most one file.
def path_once_len(+t: Tree.Tree(), +p: String, e: {Sv.claims(t) == Nil{} : List<&2, T.Split>}) -> {Nat.is_le(List.length(&2, String, Tree.at(t, p)), 1n) == True{} : Bool}:
  %Equal.sym(Nat, List.length(&2, String, Tree.at(t, p)), cnt(Sv.paths(t), p), at_len(t, p)) : {Nat.is_le(_, 1n) == True{} : Bool}
  %SortL.sort_keyed(~String, ~(s => s), Sv.paths(t), p) : {Nat.is_le(List.length(&2, String, _), 1n) == True{} : Bool}
  claims_once(List.sort(~String, ~(a => b => String.is_le(a, b)), Sv.paths(t)), p, SortL.sort_sorted(~String, ~(s => s), Sv.paths(t)), e)

def path_once(+t: Tree.Tree(), +p: String, e: {Sv.claims(t) == Nil{} : List<&2, T.Split>}) -> {Tree.at_most_one(Tree.at(t, p)) == True{} : Bool}:
  amo(Tree.at(t, p), path_once_len(t, p, e))

# `record` goes on only where the survey claims no path.
def planned_claims(+looked: Tree.Tree(), pl: Sv.Planned, +accepted: List<&2, String>, -done: Sv.Planned, e: {Main.planned.r(looked, pl, accepted) == Done{done} : Result<&2, &2, Main.Refused, Sv.Planned>}) -> {Sv.planned.claimed(pl) == Nil{} : List<&2, T.Split>}:
  match pl:
    case Sv.Planned{facts, +refused, +claimed, +accept, +emptied, dangles, +obs, links}:
      match dangles:
        case Some{m}:
          Empty.absurd({claimed == Nil{} : List<&2, T.Split>}, Blamed.fail_done(Sv.Planned, Main.Refused{1, m}, done, e))
        case None{}:
          empty_nil(claimed, not_false(List.is_empty(&2, T.Split, claimed),
            done_cond(Bool.not(List.is_empty(&2, T.Split, claimed)), Main.Refused{1, Main.claimed.msg(looked, claimed)},
      Bool.pick(Result<&2, &2, Main.Refused, Sv.Planned>, Bool.not(List.is_empty(&2, T.Split, refused)), Fail{Main.Refused{1, Main.refused.msg(refused)}},
      Bool.pick(Result<&2, &2, Main.Refused, Sv.Planned>, Bool.not(List.is_empty(&2, T.Split, Sv.marked(obs))), Fail{Main.Refused{1, Main.unresolved.msg(Sv.marked(obs))}},
      Bool.pick(Result<&2, &2, Main.Refused, Sv.Planned>, Bool.not(List.is_empty(&2, String, emptied)),
        Fail{Main.Refused{1, "a merge states what each contested file is, and there is no way to state that one is empty; leave " ++ Main.these(emptied, "it", "them") ++ " something and remove it in the revision after, or drop it here:" ++ Main.skips_held.lines(emptied)}},
      Bool.pick(Result<&2, &2, Main.Refused, Sv.Planned>, Bool.not(List.is_empty(&2, String, Main.minus(accept, accepted))),
        Fail{Main.Refused{1, "concurrent work states different bytes for " ++ Main.these(Main.minus(accept, accepted), "one attachment", "these attachments") ++ "; inspect " ++ Main.these(Main.minus(accept, accepted), "it", "them") ++ " and explicitly accept what the folder holds:" ++ Main.accept.lines(Main.minus(accept, accepted))}},
      Bool.pick(Result<&2, &2, Main.Refused, Sv.Planned>, Bool.not(List.is_empty(&2, String, Main.minus(accepted, accept))),
        Fail{Main.Refused{1, Main.these(Main.minus(accepted, accept), "this path is not a contested attachment", "these paths are not contested attachments") ++ "; remove the unnecessary acceptance:" ++ Main.accept.lines(Main.minus(accepted, accept))}},
        Done{Sv.Planned{facts, refused, claimed, accept, emptied, None{}, obs, links}}))))), done, e)))

# A link resolves inside the folder
# ---------------------------------

def ns(c: Char) -> Bool:
  Bool.not(Char.is_eq(c, '/'))

# A component a stack of them may hold: not empty, not `..`, and no `/`.
def comp_ok(+c: String) -> Bool:
  Bool.and(Bool.not(String.is_empty(c)), Bool.and(Bool.not(String.eq(c, "..")), Naming.every(~ns, c)))

def ns_fin(+h: Char, +ps: List<&2, String>, cut: Bool, +ec: {Char.is_eq(h, '/') == cut : Bool}, +hp: {NamingL.all_every(~ns, ps) == True{} : Bool}) -> {NamingL.all_every(~ns, String.split.fin(h, ps, cut)) == True{} : Bool}:
  match cut:
    case True{}:
      hp
    case False{}:
      NamingL.push_ok(~ns, h, ps, AL.not_true(Char.is_eq(h, '/'), ec), hp)

# Splitting at `/` leaves no `/` in any piece.
def split_ns(s: String) -> {NamingL.all_every(~ns, String.split(s, '/')) == True{} : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      ns_fin(h, String.split(t, '/'), Char.is_eq(h, '/'), {==}, split_ns(t))

# The components of a path the format holds are each a component.
def comps_ok(cs: List<&2, String>, +h1: {Sv.component_fault(cs) == None{} : Maybe<&2, String>}, +h2: {NamingL.all_every(~ns, cs) == True{} : Bool}) -> {SortL.all_ok(~String, ~(x => comp_ok(x)), cs) == True{} : Bool}:
  match cs:
    case Nil{}:
      {==}
    case +x <> +rest:
      AL.and_intro(comp_ok(x), SortL.all_ok(~String, ~(x => comp_ok(x)), rest),
        AL.and_intro(Bool.not(String.is_empty(x)), Bool.and(Bool.not(String.eq(x, "..")), Naming.every(~ns, x)),
          AL.not_true(String.is_empty(x), NameL.pick_cond(String.is_empty(x), "it has an empty component", NameL.after_empty(x, rest), h1)),
          AL.and_intro(Bool.not(String.eq(x, "..")), Naming.every(~ns, x),
            AL.not_true(String.eq(x, ".."), AL.or_false_r(String.eq(x, "."), String.eq(x, ".."),
              NameL.pick_cond(NameL.dots(x), "`.` and `..` are not components", Sv.component_fault(rest), NameL.pick_rest(String.is_empty(x), "it has an empty component", NameL.after_empty(x, rest), h1)))),
            Comp.and_left(Naming.every(~ns, x), NamingL.all_every(~ns, rest), h2))),
        comps_ok(rest, NameL.pick_rest(NameL.dots(x), "`.` and `..` are not components", Sv.component_fault(rest), NameL.pick_rest(String.is_empty(x), "it has an empty component", NameL.after_empty(x, rest), h1)),
          Comp.and_right(Naming.every(~ns, x), NamingL.all_every(~ns, rest), h2)))

# The stack of components the fold keeps holds only components.
def inv_m(m: Maybe<&2, List<&2, String>>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{xs}:
      SortL.all_ok(~String, ~(x => comp_ok(x)), xs)

def pop_inv(xs: List<&2, String>, +h: {SortL.all_ok(~String, ~(x => comp_ok(x)), xs) == True{} : Bool}) -> {inv_m(Sv.res.pop(xs)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      Comp.and_right(comp_ok(x), SortL.all_ok(~String, ~(x => comp_ok(x)), rest), h)

def push_inv(+p: String, +xs: List<&2, String>, skip: Bool, up: Bool, +hs: {Bool.or(String.is_empty(p), String.eq(p, ".")) == skip : Bool}, +hu: {String.eq(p, "..") == up : Bool}, +hp: {Naming.every(~ns, p) == True{} : Bool}, +hx: {SortL.all_ok(~String, ~(x => comp_ok(x)), xs) == True{} : Bool}) -> {inv_m(Sv.res.push(p, xs, skip, up)) == True{} : Bool}:
  match skip up:
    case True{} _:
      hx
    case False{} True{}:
      pop_inv(xs, hx)
    case False{} False{}:
      AL.and_intro(comp_ok(p), SortL.all_ok(~String, ~(x => comp_ok(x)), xs),
        AL.and_intro(Bool.not(String.is_empty(p)), Bool.and(Bool.not(String.eq(p, "..")), Naming.every(~ns, p)),
          AL.not_true(String.is_empty(p), AL.or_false_l(String.is_empty(p), String.eq(p, "."), hs)),
          AL.and_intro(Bool.not(String.eq(p, "..")), Naming.every(~ns, p), AL.not_true(String.eq(p, ".."), hu), hp)),
        hx)

def step_inv(+p: String, at: Maybe<&2, List<&2, String>>, +hp: {Naming.every(~ns, p) == True{} : Bool}, +ha: {inv_m(at) == True{} : Bool}) -> {inv_m(Sv.res.step(p, at)) == True{} : Bool}:
  match at:
    case None{}:
      {==}
    case Some{+xs}:
      push_inv(p, xs, Bool.or(String.is_empty(p), String.eq(p, ".")), String.eq(p, ".."), {==}, {==}, hp, ha)

def go_inv(parts: List<&2, String>, +at: Maybe<&2, List<&2, String>>, +hparts: {NamingL.all_every(~ns, parts) == True{} : Bool}, +ha: {inv_m(at) == True{} : Bool}) -> {inv_m(Sv.res.go(parts, at)) == True{} : Bool}:
  match parts:
    case Nil{}:
      ha
    case +p <> +rest:
      go_inv(rest, Sv.res.step(p, at), Comp.and_right(Naming.every(~ns, p), NamingL.all_every(~ns, rest), hparts), step_inv(p, at, Comp.and_left(Naming.every(~ns, p), NamingL.all_every(~ns, rest), hparts), ha))

def dir_inv(xs: List<&2, String>, +h: {SortL.all_ok(~String, ~(x => comp_ok(x)), xs) == True{} : Bool}) -> {SortL.all_ok(~String, ~(x => comp_ok(x)), Sv.res.dir(xs)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      Comp.and_right(comp_ok(x), SortL.all_ok(~String, ~(x => comp_ok(x)), rest), h)

# The link's own directory is where the fold starts.
def init_inv(+link: String, +h: {Sv.path_check(link) == None{} : Maybe<&2, String>}) -> {inv_m(Some{Sv.res.dir(List.reverse(&2, String, String.split(link, '/')))}) == True{} : Bool}:
  dir_inv(List.reverse(&2, String, String.split(link, '/')),
    SortL.all_rev_go(~String, ~(x => comp_ok(x)), String.split(link, '/'), Nil{}, comps_ok(String.split(link, '/'), NameL.path_parts(link, h), split_ns(link)), {==}))

# The components joined with `/` split back into those components.
def pushes(b: String, ps: List<&2, String>) -> List<&2, String>:
  match b:
    case SNil{}:
      ps
    case SCon{c, t}:
      String.split.push(c, pushes(t, ps))

def ns_head(+c: Char, -t: String, h: {Naming.every(~ns, SCon{c, t}) == True{} : Bool}) -> {Char.is_eq(c, '/') == False{} : Bool}:
  AL.not_of_true(Char.is_eq(c, '/'), Comp.and_left(Bool.not(Char.is_eq(c, '/')), Naming.every(~ns, t), h))

def split_lead(b: String, +r: String, +h: {Naming.every(~ns, b) == True{} : Bool}) -> {String.split(b ++ r, '/') == pushes(b, String.split(r, '/')) : List<&2, String>}:
  match b:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %Equal.sym(Bool, Char.is_eq(c, '/'), False{}, ns_head(c, t, h)) : {String.split.fin(c, String.split(t ++ r, '/'), _) == pushes(SCon{c, t}, String.split(r, '/')) : List<&2, String>}
      Equal.cong(List<&2, String>, List<&2, String>, ps => String.split.push(c, ps), String.split(t ++ r, '/'), pushes(t, String.split(r, '/')), split_lead(t, r, Comp.and_right(Bool.not(Char.is_eq(c, '/')), Naming.every(~ns, t), h)))

def pushes_nil(b: String, +s: List<&2, String>) -> {pushes(b, SNil{} <> s) == b <> s : List<&2, String>}:
  match b:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %pushes_nil(t, s) : {String.split.push(c, pushes(t, SNil{} <> s)) == String.split.push(c, _) : List<&2, String>}
      {==}

def split_plain(b: String, +h: {Naming.every(~ns, b) == True{} : Bool}) -> {String.split(b, '/') == [b] : List<&2, String>}:
  match b:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %Equal.sym(Bool, Char.is_eq(c, '/'), False{}, ns_head(c, t, h)) : {String.split.fin(c, String.split(t, '/'), _) == [SCon{c, t}] : List<&2, String>}
      %split_plain(t, Comp.and_right(Bool.not(Char.is_eq(c, '/')), Naming.every(~ns, t), h)) : {String.split.push(c, String.split(t, '/')) == String.split.push(c, _) : List<&2, String>}
      {==}

def split_join(more: List<&2, String>, +b: String, +hb: {Naming.every(~ns, b) == True{} : Bool}, +hm: {NamingL.all_every(~ns, more) == True{} : Bool}) -> {String.split(String.join.go(more, b, "/"), '/') == b <> more : List<&2, String>}:
  match more:
    case Nil{}:
      split_plain(b, hb)
    case +m <> +mr:
      Equal.trans(List<&2, String>, String.split(b ++ SCon{'/', String.join.go(mr, m, "/")}, '/'), pushes(b, SNil{} <> String.split(String.join.go(mr, m, "/"), '/')), b <> m <> mr,
        split_lead(b, SCon{'/', String.join.go(mr, m, "/")}, hb),
        Equal.trans(List<&2, String>, pushes(b, SNil{} <> String.split(String.join.go(mr, m, "/"), '/')), b <> String.split(String.join.go(mr, m, "/"), '/'), b <> m <> mr,
          pushes_nil(b, String.split(String.join.go(mr, m, "/"), '/')),
          Equal.cong(List<&2, String>, List<&2, String>, xs => b <> xs, String.split(String.join.go(mr, m, "/"), '/'), m <> mr,
            split_join(mr, m, Comp.and_left(Naming.every(~ns, m), NamingL.all_every(~ns, mr), hm), Comp.and_right(Naming.every(~ns, m), NamingL.all_every(~ns, mr), hm)))))

# A stack of components joined neither begins with `/` nor holds `..`.
def ok_ns(xs: List<&2, String>, +h: {SortL.all_ok(~String, ~(x => comp_ok(x)), xs) == True{} : Bool}) -> {NamingL.all_every(~ns, xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      AL.and_intro(Naming.every(~ns, x), NamingL.all_every(~ns, rest),
        Comp.and_right(Bool.not(String.eq(x, "..")), Naming.every(~ns, x), Comp.and_right(Bool.not(String.is_empty(x)), Bool.and(Bool.not(String.eq(x, "..")), Naming.every(~ns, x)), Comp.and_left(comp_ok(x), SortL.all_ok(~String, ~(x => comp_ok(x)), rest), h))),
        ok_ns(rest, Comp.and_right(comp_ok(x), SortL.all_ok(~String, ~(x => comp_ok(x)), rest), h)))

def ok_dots(xs: List<&2, String>, +h: {SortL.all_ok(~String, ~(x => comp_ok(x)), xs) == True{} : Bool}) -> {List.any(~&2, ~String, ~(c => String.eq(c, "..")), xs) == False{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      AL.or_false(String.eq(x, ".."), List.any(~&2, ~String, ~(c => String.eq(c, "..")), rest),
        AL.not_of_true(String.eq(x, ".."), Comp.and_left(Bool.not(String.eq(x, "..")), Naming.every(~ns, x), Comp.and_right(Bool.not(String.is_empty(x)), Bool.and(Bool.not(String.eq(x, "..")), Naming.every(~ns, x)), Comp.and_left(comp_ok(x), SortL.all_ok(~String, ~(x => comp_ok(x)), rest), h)))),
        ok_dots(rest, Comp.and_right(comp_ok(x), SortL.all_ok(~String, ~(x => comp_ok(x)), rest), h)))

def start_ok(b: String, more: List<&2, String>, hne: {String.is_empty(b) == False{} : Bool}, +hns: {Naming.every(~ns, b) == True{} : Bool}) -> {String.starts_with(String.join.go(more, b, "/"), "/") == False{} : Bool}:
  match b more:
    case SNil{} _:
      Empty.absurd({String.starts_with(String.join.go(more, SNil{}, "/"), "/") == False{} : Bool}, S.true_false(hne))
    case SCon{+c, +t} Nil{}:
      %Equal.sym(Bool, Char.is_eq(c, '/'), False{}, ns_head(c, t, hns)) : {String.starts_with.if(t, SNil{}, _) == False{} : Bool}
      {==}
    case SCon{+c, +t} m <> mr:
      %Equal.sym(Bool, Char.is_eq(c, '/'), False{}, ns_head(c, t, hns)) : {String.starts_with.if(t ++ SCon{'/', String.join.go(mr, m, "/")}, SNil{}, _) == False{} : Bool}
      {==}

def final_ok(ys: List<&2, String>, +h: {SortL.all_ok(~String, ~(x => comp_ok(x)), ys) == True{} : Bool}) -> {Main.escapes(String.join(ys, "/")) == False{} : Bool}:
  match ys:
    case Nil{}:
      {==}
    case +b <> +more:
      %Equal.sym(List<&2, String>, String.split(String.join.go(more, b, "/"), '/'), b <> more, split_join(more, b, Comp.and_left(Naming.every(~ns, b), NamingL.all_every(~ns, more), ok_ns(b <> more, h)), Comp.and_right(Naming.every(~ns, b), NamingL.all_every(~ns, more), ok_ns(b <> more, h)))) : {Bool.or(String.starts_with(String.join.go(more, b, "/"), "/"), List.any(~&2, ~String, ~(c => String.eq(c, "..")), _)) == False{} : Bool}
      AL.or_false(String.starts_with(String.join.go(more, b, "/"), "/"), List.any(~&2, ~String, ~(c => String.eq(c, "..")), b <> more),
        start_ok(b, more, AL.not_of_true(String.is_empty(b), Comp.and_left(Bool.not(String.is_empty(b)), Bool.and(Bool.not(String.eq(b, "..")), Naming.every(~ns, b)), Comp.and_left(comp_ok(b), SortL.all_ok(~String, ~(x => comp_ok(x)), more), h))),
          Comp.and_left(Naming.every(~ns, b), NamingL.all_every(~ns, more), ok_ns(b <> more, h))),
        ok_dots(b <> more, h))

def joined_ok(xs: List<&2, String>, +h: {SortL.all_ok(~String, ~(x => comp_ok(x)), xs) == True{} : Bool}, -p: String, e: {Sv.res.joined(xs) == Some{p} : Maybe<&2, String>}) -> {Main.escapes(p) == False{} : Bool}:
  match xs:
    case Nil{}:
      Empty.absurd({Main.escapes(p) == False{} : Bool}, NamingL.none_some(p, e))
    case +x <> +rest:
      %NamingL.some_inj(String.join(List.reverse(&2, String, x <> rest), "/"), p, e) : {Main.escapes(_) == False{} : Bool}
      final_ok(List.reverse(&2, String, x <> rest), SortL.all_rev_go(~String, ~(x => comp_ok(x)), x <> rest, Nil{}, h, {==}))

def done_ok(m: Maybe<&2, List<&2, String>>, +hm: {inv_m(m) == True{} : Bool}, -p: String, e: {Sv.res.done(m) == Some{p} : Maybe<&2, String>}) -> {Main.escapes(p) == False{} : Bool}:
  match m:
    case None{}:
      Empty.absurd({Main.escapes(p) == False{} : Bool}, NamingL.none_some(p, e))
    case Some{+xs}:
      joined_ok(xs, hm, p, e)

def res_ok(c: Bool, +m: Maybe<&2, List<&2, String>>, +hm: {inv_m(m) == True{} : Bool}, -p: String, e: {Bool.pick(Maybe<&2, String>, c, None{}, Sv.res.done(m)) == Some{p} : Maybe<&2, String>}) -> {Main.escapes(p) == False{} : Bool}:
  match c:
    case True{}:
      Empty.absurd({Main.escapes(p) == False{} : Bool}, NamingL.none_some(p, e))
    case False{}:
      done_ok(m, hm, p, e)

# A link at a path the format holds resolves inside the folder.
def link_inside(+link: String, +target: String, -p: String, +h: {Sv.path_check(link) == None{} : Maybe<&2, String>}, e: {Sv.resolution(link, target) == Some{p} : Maybe<&2, String>}) -> {Main.escapes(p) == False{} : Bool}:
  res_ok(Bool.or(String.starts_with(target, "/"), String.ends_with(target, "/")), Sv.res.go(String.split(target, '/'), Some{Sv.res.dir(List.reverse(&2, String, String.split(link, '/')))}),
    go_inv(String.split(target, '/'), Some{Sv.res.dir(List.reverse(&2, String, String.split(link, '/')))}, split_ns(target), init_inv(link, h)), p, e)

# The set built from the arriving paths answers as the list does, so the
# survey's arrival check is the list's.
def has_hv(r: Set() & Bool) -> {Sv.has.of(r) == ML.hv(Unit, r) : Bool}:
  match r:
    case (m, b):
      {==}

def member_set(+xs: List<&2, String>, +p: String) -> {Sv.has(Set.from_list(xs), p) == List.contains(~String, ~(a => b => String.eq(a, b)), xs, p) : Bool}:
  Equal.trans(Bool, Sv.has(Set.from_list(xs), p), ML.hv(Unit, Set.has(Set.from_list(xs), p)), List.contains(~String, ~(a => b => String.eq(a, b)), xs, p), has_hv(Set.has(Set.from_list(xs), p)), ML.set_from_list(xs, p))

def arrives_list(+xs: List<&2, String>, fs: List<&2, T.Split>) -> {Sv.arrives_once(Set.from_list(xs), fs) == Sv.arrives_once.list(xs, fs) : Bool}:
  match fs:
    case Nil{}:
      {==}
    case T.Split{+k, +p} <> rest:
      %Equal.sym(Bool, Sv.has(Set.from_list(xs), p), List.contains(~String, ~(a => b => String.eq(a, b)), xs, p), member_set(xs, p)) : {Bool.and(Bool.or(String.eq(k, "added"), Bool.or(String.eq(k, "dropped"), Bool.not(_))), Sv.arrives_once(Set.from_list(xs), rest)) == Bool.and(Bool.or(String.eq(k, "added"), Bool.or(String.eq(k, "dropped"), Bool.not(List.contains(~String, ~(a => b => String.eq(a, b)), xs, p)))), Sv.arrives_once.list(xs, rest)) : Bool}
      %Equal.sym(Bool, Sv.arrives_once(Set.from_list(xs), rest), Sv.arrives_once.list(xs, rest), arrives_list(xs, rest)) : {Bool.and(Bool.or(String.eq(k, "added"), Bool.or(String.eq(k, "dropped"), Bool.not(List.contains(~String, ~(a => b => String.eq(a, b)), xs, p)))), _) == Bool.and(Bool.or(String.eq(k, "added"), Bool.or(String.eq(k, "dropped"), Bool.not(List.contains(~String, ~(a => b => String.eq(a, b)), xs, p)))), Sv.arrives_once.list(xs, rest)) : Bool}
      {==}

