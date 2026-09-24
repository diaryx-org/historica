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
import ./anchor_lemmas.bend as AL
import ./string_lemmas.bend as S
import ./composition_lemmas.bend as Comp

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
        case Sv.Seen{+path, +e, +found, +d, +before, +x, +sh, +pr}:
          AL.and_intro(Sv.found_at(Sv.Seen{path, e, found, d, before, x, sh, pr} <> rest, p), found_all(Sv.Seen{path, e, found, d, before, x, sh, pr} <> rest, more),
            AL.or_right(Bool.and(String.eq(path, p), Maybe.is_some(&2, F.Found, found)), Sv.found_at(rest, p), Comp.and_left(Sv.found_at(rest, p), found_all(rest, more), h)),
            found_weaken(more, Sv.Seen{path, e, found, d, before, x, sh, pr}, rest, Comp.and_right(Sv.found_at(rest, p), found_all(rest, more), h)))

# A surveyed path the folder found something at is one a refusal of it may
# name.
def here(+path: String, -e: Maybe<&2, Tree.Entry>, -f: F.Found, -d: String, -b: Maybe<&2, String>, -x: Bool, -sh: Maybe<&2, String>, -pr: Bool, -rest: List<&2, Sv.Seen>) -> {Sv.found_at(Sv.Seen{path, e, Some{f}, d, b, x, sh, pr} <> rest, path) == True{} : Bool}:
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

def found_lines(+ss: List<&2, Sv.Seen>, +path: String, +e: Tree.Entry, +digest: String, +before: Maybe<&2, String>, +runs: Bool, proposed: Bool, +text: Bool, empty: Bool, +hp: {Sv.found_at(ss, path) == True{} : Bool}) -> {found_all(ss, Sv.refusals(Sv.lines(path, e, digest, before, runs, text, proposed, empty))) == True{} : Bool}:
  match proposed:
    case True{}:
      match text:
        case False{}:
          found_changed(ss, path, e, runs, False{}, hp)
        case True{}:
          found_emptied(ss, path, e, runs, empty, hp)
    case False{}:
      found_agreed(ss, path, e, runs, text, Sv.same(before, digest), hp)

def found_held_file(+ss: List<&2, Sv.Seen>, +path: String, e: Tree.Entry, +digest: String, +before: Maybe<&2, String>, +runs: Bool, text: Bool, proposed: Bool, empty: Bool, +hp: {Sv.found_at(ss, path) == True{} : Bool}) -> {found_all(ss, Sv.refusals(Sv.held_file(path, e, digest, before, runs, text, proposed, empty))) == True{} : Bool}:
  match e:
    case Tree.Entry{+f, +p, Tree.Link{}, +y, +g, +m}:
      {==}
    case Tree.Entry{+f, +p, Tree.Whole{}, +y, +g, +m}:
      found_whole(ss, path, Tree.Entry{f, p, Tree.Whole{}, y, g, m}, digest, runs, y)
    case Tree.Entry{+f, +p, Tree.Lines{}, +y, +g, +m}:
      found_lines(ss, path, Tree.Entry{f, p, Tree.Lines{}, y, g, m}, digest, before, runs, proposed, text, empty, hp)

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
    case Sv.Seen{+path, Some{+e}, None{}, +d, +before, +x, +sh, +pr}:
      found_dropped(Sv.Seen{path, Some{e}, None{}, d, before, x, sh, pr} <> rest, path, e, before, Nil{}, {==})
    case Sv.Seen{+path, None{}, Some{F.Found.Link{+q, +target}}, +d, +before, +x, +sh, +pr}:
      found_link(Sv.Seen{path, None{}, Some{F.Found.Link{q, target}}, d, before, x, sh, pr} <> rest, path, target, None{}, None{}, Sv.link_fault(target), True{},
        here(path, None{}, F.Found.Link{q, target}, d, before, x, sh, pr, rest))
    case Sv.Seen{+path, None{}, Some{F.Found.File{+q, +runs, +n}}, +d, +before, +x, +sh, +pr}:
      {==}
    case Sv.Seen{+path, Some{+e}, Some{F.Found.Link{+q, +target}}, +d, +before, +x, +sh, +pr}:
      found_held_link(Sv.Seen{path, Some{e}, Some{F.Found.Link{q, target}}, d, before, x, sh, pr} <> rest, path, target, e, sh, before,
        here(path, Some{e}, F.Found.Link{q, target}, d, before, x, sh, pr, rest))
    case Sv.Seen{+path, Some{+e}, Some{F.Found.File{+q, +runs, +n}}, +d, +before, +x, +sh, +pr}:
      found_held_file(Sv.Seen{path, Some{e}, Some{F.Found.File{q, runs, n}}, d, before, x, sh, pr} <> rest, path, e, d, before, runs, x, pr, Nat.is_eq(n, 0n),
        here(path, Some{e}, F.Found.File{q, runs, n}, d, before, x, sh, pr, rest))
    case Sv.Seen{+path, None{}, None{}, +d, +before, +x, +sh, +pr}:
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
