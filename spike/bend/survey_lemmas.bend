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
import ./anchor_lemmas.bend as AL
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
