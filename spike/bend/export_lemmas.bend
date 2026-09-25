# What `export` promises of a copy. Its folder has every path the target's
# tree places, each once and at its own path, whatever the file is; every
# bookmark it is given is shared and finds what it names in the copy; and
# every rule file it is given states a shared rule.
import Base
import ./export.bend as Export
import ./receive.bend as Receive
import ./prune.bend as Prune
import ./prune_lemmas.bend as PruneL
import ./arrange.bend as Arrange
import ./commands.bend as Main
import ./store.bend as Store
import ./bookmark.bend as Bm
import ./text.bend as T
import ./tree.bend as Tree
import ./revision.bend as Rev
import ./ops.bend as Ops
import ./string_lemmas.bend as S
import ./folder.bend as Folder

# The folder
# ----------

def ref_path(+path: String, found: Maybe<&2, String>) -> {Export.outcome.path(Export.lay.reference(path, found)) == path : String}:
  match found:
    case None{}:
      {==}
    case Some{to}:
      {==}

def link_path(+path: String, +t: Tree.Tree(), target: Maybe<&2, Tree.Target>) -> {Export.outcome.path(Export.lay.link(path, t, target)) == path : String}:
  match target:
    case None{}:
      {==}
    case Some{Tree.Verbatim{s}}:
      {==}
    case Some{Tree.Reference{+f}}:
      ref_path(path, Tree.path(t, f))

def absent_path(+path: String, +d: String, forgotten: Bool) -> {Export.outcome.path(Export.lay.absent(path, d, forgotten)) == path : String}:
  match forgotten:
    case True{}:
      {==}
    case False{}:
      {==}

def held_path(+path: String, +d: String, found: Maybe<&2, String>, forgotten: Bool, r: Bool) -> {Export.outcome.path(Export.lay.held(path, d, found, forgotten, r)) == path : String}:
  match found:
    case Some{from}:
      {==}
    case None{}:
      absent_path(path, d, forgotten)

def whole_path(+path: String, payload: Maybe<&2, String>, +ps: List<&2, T.Split>, +bs: List<&2, Prune.Body>, r: Bool) -> {Export.outcome.path(Export.lay.whole(path, payload, ps, bs, r)) == path : String}:
  match payload:
    case None{}:
      {==}
    case Some{+d}:
      held_path(path, d, Export.split.find(ps, d), Export.forgets(bs, d), r)

def lines_path(+path: String, content: Result<&2, &2, String, List<&2, Ops.Item>>, r: Bool) -> {Export.outcome.path(Export.lay.lines(path, content, r)) == path : String}:
  match content:
    case Fail{e}:
      {==}
    case Done{items}:
      {==}

def entry_path(+path: String, e: Tree.Entry, +t: Tree.Tree(), +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +id: String, +ps: List<&2, T.Split>, +bs: List<&2, Prune.Body>) -> {Export.outcome.path(Export.lay.entry(path, e, t, fs, ds, id, ps, bs)) == path : String}:
  match e:
    case Tree.Entry{+file, p, kind, payload, target, mode}:
      match kind:
        case Tree.Link{}:
          link_path(path, t, target)
        case Tree.Whole{}:
          whole_path(path, payload, ps, bs, Export.runs(mode))
        case Tree.Lines{}:
          lines_path(path, Main.content(fs, ds, id, file), Export.runs(mode))

def one_path(p: Export.Placed, +t: Tree.Tree(), +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +id: String, +ps: List<&2, T.Split>, +bs: List<&2, Prune.Body>) -> {Export.outcome.path(Export.lay.one(p, t, fs, ds, id, ps, bs)) == Export.placed.path(p) : String}:
  match p:
    case Export.Placed{+path, es}:
      match es:
        case Nil{}:
          {==}
        case e <> Nil{}:
          entry_path(path, e, t, fs, ds, id, ps, bs)
        case e <> f <> more:
          {==}

# Every path placed gets one outcome, at that path, in order: a folder laid
# out without a refusal holds each path the tree places, and no other.
def laid(ps: List<&2, Export.Placed>, +t: Tree.Tree(), +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +id: String, +pays: List<&2, T.Split>, +bs: List<&2, Prune.Body>) -> {Export.outcome.paths(Export.lay(ps, t, fs, ds, id, pays, bs)) == Export.placed.paths(ps) : List<&2, String>}:
  match ps:
    case Nil{}:
      {==}
    case +p <> +rest:
      %Equal.sym(String, Export.outcome.path(Export.lay.one(p, t, fs, ds, id, pays, bs)), Export.placed.path(p), one_path(p, t, fs, ds, id, pays, bs)) : {_ <> Export.outcome.paths(Export.lay(rest, t, fs, ds, id, pays, bs)) == Export.placed.path(p) <> Export.placed.paths(rest) : List<&2, String>}
      %Equal.sym(List<&2, String>, Export.outcome.paths(Export.lay(rest, t, fs, ds, id, pays, bs)), Export.placed.paths(rest), laid(rest, t, fs, ds, id, pays, bs)) : {Export.placed.path(p) <> _ == Export.placed.path(p) <> Export.placed.paths(rest) : List<&2, String>}
      {==}

# Bookmarks
# ---------

def withheld_travels(t: Export.Travel, +pt: Export.Pointed, ih: {Export.travels(Export.travel.names(t), pt) == True{} : Bool}) -> {Export.travels(Export.travel.names(Export.travel.withheld(t)), pt) == True{} : Bool}:
  match t:
    case Export.Travel{ns, w, y}:
      ih

def held_travels(+n: String, +g: Bm.Target, +pt: Export.Pointed, h: Bool, e: {Export.pointed.holds(pt, g) == h : Bool}, t: Export.Travel, ih: {Export.travels(Export.travel.names(t), pt) == True{} : Bool}) -> {Export.travels(Export.travel.names(Export.travel.held(Bm.Bookmark{n, g, False{}}, h, t)), pt) == True{} : Bool}:
  match h:
    case True{}:
      match t:
        case Export.Travel{+ns, w, y}:
          %Equal.sym(Bool, Export.pointed.holds(pt, g), True{}, e) : {Bool.and(Bool.and(Bool.not(False{}), _), Export.travels(ns, pt)) == True{} : Bool}
          %Equal.sym(Bool, Export.travels(ns, pt), True{}, ih) : {Bool.and(Bool.and(Bool.not(False{}), True{}), _) == True{} : Bool}
          {==}
    case False{}:
      match t:
        case Export.Travel{ns, w, y}:
          ih

def push_travels(b: Bm.Bookmark, +pt: Export.Pointed, t: Export.Travel, ih: {Export.travels(Export.travel.names(t), pt) == True{} : Bool}) -> {Export.travels(Export.travel.names(Export.travel.push(b, pt, t)), pt) == True{} : Bool}:
  match b:
    case Bm.Bookmark{+n, +g, p}:
      match p:
        case True{}:
          withheld_travels(t, pt, ih)
        case False{}:
          held_travels(n, g, pt, Export.pointed.holds(pt, g), {==}, t, ih)

# Every bookmark the copy is given is shared, and finds what it names.
def names(bs: List<&2, Bm.Bookmark>, +pt: Export.Pointed) -> {Export.travels(Export.travel.names(Export.travel.of(bs, pt)), pt) == True{} : Bool}:
  match bs:
    case Nil{}:
      {==}
    case b <> +rest:
      push_travels(b, pt, Export.travel.of(rest, pt), names(rest, pt))

# Rules
# -----

def all_shared(rs: List<&2, Receive.Ruled>) -> Bool:
  match rs:
    case Nil{}:
      True{}
    case Receive.Ruled{f, +line, l} <> rest:
      Bool.and(Bool.not(String.starts_with(line, "private")), all_shared(rest))

def keep_shared(c: Bool, +f: String, +line: String, +l: String, rest: List<&2, Receive.Ruled>, ec: {String.starts_with(line, "private") == c : Bool}, ih: {all_shared(Export.rules.shared(rest)) == True{} : Bool}) -> {all_shared(Tree.keep(~Receive.Ruled, Bool.not(c), Receive.Ruled{f, line, l}, Export.rules.shared(rest))) == True{} : Bool}:
  match c:
    case True{}:
      ih
    case False{}:
      %Equal.sym(Bool, String.starts_with(line, "private"), False{}, ec) : {Bool.and(Bool.not(_), all_shared(Export.rules.shared(rest))) == True{} : Bool}
      ih

def shared_all(rs: List<&2, Receive.Ruled>) -> {all_shared(Export.rules.shared(rs)) == True{} : Bool}:
  match rs:
    case Nil{}:
      {==}
    case Receive.Ruled{+f, +line, +l} <> +rest:
      keep_shared(String.starts_with(line, "private"), f, line, l, rest, {==}, shared_all(rest))

def written_step(dup: Bool, +chosen: String, +line: String, rest: List<&2, Receive.Ruled>, +existing: Set(), +done: List<&2, String>, +taken: List<&2, String>, hl: {Bool.not(String.starts_with(line, "private")) == True{} : Bool}, ih: {Export.lines.shared(Receive.rules.written(rest, existing, line <> done, Bool.pick(List<&2, String>, dup, taken, chosen <> taken))) == True{} : Bool}) -> {Export.lines.shared(Tree.keep(~T.Split, Bool.not(dup), T.Split{chosen, line}, Receive.rules.written(rest, existing, line <> done, Bool.pick(List<&2, String>, dup, taken, chosen <> taken)))) == True{} : Bool}:
  match dup:
    case True{}:
      ih
    case False{}:
      %Equal.sym(Bool, Bool.not(String.starts_with(line, "private")), True{}, hl) : {Bool.and(_, Export.lines.shared(Receive.rules.written(rest, existing, line <> done, chosen <> taken))) == True{} : Bool}
      ih

# What `rules.written` files states only what it was given: a list of
# shared rules comes out as files of shared rules, whatever labels it takes.
def written_shared(rs: List<&2, Receive.Ruled>, +existing: Set(), +done: List<&2, String>, +taken: List<&2, String>, +h: {all_shared(rs) == True{} : Bool}) -> {Export.lines.shared(Receive.rules.written(rs, existing, done, taken)) == True{} : Bool}:
  match rs:
    case Nil{}:
      {==}
    case Receive.Ruled{f, +line, +label} <> +rest:
      +chosen = Bool.pick(String, Bool.or(Arrange.has(existing, label), Rev.member(taken, label)), Receive.rule.digest_label(line), label)
      written_step(Rev.member(done, line), chosen, line, rest, existing, done, taken,
        PruneL.and_l(Bool.not(String.starts_with(line, "private")), all_shared(rest), h),
        written_shared(rest, existing, line <> done, Bool.pick(List<&2, String>, Rev.member(done, line), taken, chosen <> taken), PruneL.and_r(Bool.not(String.starts_with(line, "private")), all_shared(rest), h)))

# Every rule file the copy is given states a shared rule.
def rules(+rs: List<&2, Receive.Ruled>) -> {Export.lines.shared(Export.rules.files(rs)) == True{} : Bool}:
  written_shared(Export.rules.shared(rs), Set.from_list(["README.txt"]), Nil{}, Nil{}, shared_all(rs))

# Catching a folder up
# --------------------

def and_tt(a: Bool, b: Bool, ea: {a == True{} : Bool}, eb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  match a:
    case True{}:
      eb
    case False{}:
      Empty.absurd({Bool.and(False{}, b) == True{} : Bool}, S.false_true(ea))

def or_r(a: Bool, -b: Bool, e: {b == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      e

# A write or a link at a path lands where what the walk found there is
# what `s` is.
def over_at(+put: Export.Put, +path: String, -s: Maybe<&2, Export.Seen>, +ss: List<&2, Export.Seen>, +whole: Bool, +rs: List<&2, Export.Rec>, ep: {Export.put.path(put) == path : String}, es: {Export.seen.find(ss, path) == s : Maybe<&2, Export.Seen>}, h: {Export.over.ok(whole, rs, path, Export.held.digest(s)) == True{} : Bool}) -> {Export.over.ok(whole, rs, Export.put.path(put), Export.held.digest(Export.seen.find(ss, Export.put.path(put)))) == True{} : Bool}:
  %Equal.sym(String, Export.put.path(put), path, ep) : {Export.over.ok(whole, rs, _, Export.held.digest(Export.seen.find(ss, _))) == True{} : Bool}
  %Equal.sym(Maybe<&2, Export.Seen>, Export.seen.find(ss, path), s, es) : {Export.over.ok(whole, rs, path, Export.held.digest(_)) == True{} : Bool}
  h

# Over a file whose bytes some revision records, and nowhere else.
def over_file(r: Bool, link: Bool, +put: Export.Put, +path: String, +p: String, +d: String, +runs: Bool, +ss: List<&2, Export.Seen>, +whole: Bool, +rs: List<&2, Export.Rec>, er: {Export.recorded(whole, rs, path, d) == r : Bool}, ep: {Export.put.path(put) == path : String}, es: {Export.seen.find(ss, path) == Some{Export.Seen.File{p, d, runs}} : Maybe<&2, Export.Seen>}) -> {Export.step.safe(Bool.pick(Export.Step, r, Bool.pick(Export.Step, link, Export.Step.Link{put}, Export.Step.Write{put, True{}}), Export.Step.Refuse{path, Export.UNRECORDED()}), ss, whole, rs) == True{} : Bool}:
  match r:
    case True{}:
      match link:
        case True{}:
          over_at(put, path, Some{Export.Seen.File{p, d, runs}}, ss, whole, rs, ep, es, er)
        case False{}:
          over_at(put, path, Some{Export.Seen.File{p, d, runs}}, ss, whole, rs, ep, es, er)
    case False{}:
      {==}

# Keeping, or setting a mode, writes nothing over.
def same_safe(eq: Bool, runs: Bool, wanted: Bool, +path: String, +over: Export.Step, +ss: List<&2, Export.Seen>, +whole: Bool, +rs: List<&2, Export.Rec>, ho: {Export.step.safe(over, ss, whole, rs) == True{} : Bool}) -> {Export.step.safe(Export.step.same(path, eq, runs, wanted, over), ss, whole, rs) == True{} : Bool}:
  match eq:
    case True{}:
      match runs wanted:
        case True{} True{}:
          {==}
        case True{} False{}:
          {==}
        case False{} True{}:
          {==}
        case False{} False{}:
          {==}
    case False{}:
      ho

def link_same(q: Bool, +put: Export.Put, +path: String, +p: String, +t: String, +ss: List<&2, Export.Seen>, +whole: Bool, +rs: List<&2, Export.Rec>, ep: {Export.put.path(put) == path : String}, es: {Export.seen.find(ss, path) == Some{Export.Seen.Link{p, t}} : Maybe<&2, Export.Seen>}) -> {Export.step.safe(Bool.pick(Export.Step, q, Export.Step.Keep{}, Export.Step.Link{put}), ss, whole, rs) == True{} : Bool}:
  match q:
    case True{}:
      {==}
    case False{}:
      over_at(put, path, Some{Export.Seen.Link{p, t}}, ss, whole, rs, ep, es, {==})

def absent_safe(pr: Export.Probe, link: Bool, +put: Export.Put, +path: String, +ss: List<&2, Export.Seen>, +whole: Bool, +rs: List<&2, Export.Rec>, ep: {Export.put.path(put) == path : String}, es: {Export.seen.find(ss, path) == None{} : Maybe<&2, Export.Seen>}) -> {Export.step.safe(Export.step.absent(put, path, pr, link), ss, whole, rs) == True{} : Bool}:
  match pr link:
    case Export.Probe.Nothing{} True{}:
      over_at(put, path, None{}, ss, whole, rs, ep, es, {==})
    case Export.Probe.Nothing{} False{}:
      over_at(put, path, None{}, ss, whole, rs, ep, es, {==})
    case Export.Probe.Dir{} _:
      {==}
    case Export.Probe.Other{} True{}:
      {==}
    case Export.Probe.Other{} False{}:
      {==}

def seen_link(lk: Bool, +put: Export.Put, +path: String, +p: String, +t: String, +ss: List<&2, Export.Seen>, +whole: Bool, +rs: List<&2, Export.Rec>, ep: {Export.put.path(put) == path : String}, es: {Export.seen.find(ss, path) == Some{Export.Seen.Link{p, t}} : Maybe<&2, Export.Seen>}) -> {Export.step.safe(Bool.pick(Export.Step, lk, Bool.pick(Export.Step, String.eq(t, Export.put.target(put)), Export.Step.Keep{}, Export.Step.Link{put}), Export.Step.Refuse{path, "a symbolic link stands there"}), ss, whole, rs) == True{} : Bool}:
  match lk:
    case True{}:
      link_same(String.eq(t, Export.put.target(put)), put, path, p, t, ss, whole, rs, ep, es)
    case False{}:
      {==}

def seen_file(lk: Bool, +put: Export.Put, +path: String, +p: String, +d: String, +runs: Bool, +ss: List<&2, Export.Seen>, +whole: Bool, +rs: List<&2, Export.Rec>, ep: {Export.put.path(put) == path : String}, es: {Export.seen.find(ss, path) == Some{Export.Seen.File{p, d, runs}} : Maybe<&2, Export.Seen>}) -> {Export.step.safe(Bool.pick(Export.Step, lk, Bool.pick(Export.Step, Export.recorded(whole, rs, path, d), Bool.pick(Export.Step, lk, Export.Step.Link{put}, Export.Step.Write{put, True{}}), Export.Step.Refuse{path, Export.UNRECORDED()}), Export.step.same(path, String.eq(d, Export.put.digest(put)), runs, Export.put.runs(put), Bool.pick(Export.Step, Export.recorded(whole, rs, path, d), Bool.pick(Export.Step, lk, Export.Step.Link{put}, Export.Step.Write{put, True{}}), Export.Step.Refuse{path, Export.UNRECORDED()}))), ss, whole, rs) == True{} : Bool}:
  match lk:
    case True{}:
      over_file(Export.recorded(whole, rs, path, d), True{}, put, path, p, d, runs, ss, whole, rs, {==}, ep, es)
    case False{}:
      same_safe(String.eq(d, Export.put.digest(put)), runs, Export.put.runs(put), path, Bool.pick(Export.Step, Export.recorded(whole, rs, path, d), Bool.pick(Export.Step, False{}, Export.Step.Link{put}, Export.Step.Write{put, True{}}), Export.Step.Refuse{path, Export.UNRECORDED()}), ss, whole, rs,
        over_file(Export.recorded(whole, rs, path, d), False{}, put, path, p, d, runs, ss, whole, rs, {==}, ep, es))

# One path the tree places: whatever stands there, the step writes over a
# regular file only where some revision records its bytes.
def held_safe(+put: Export.Put, +path: String, +lk: Bool, s: Maybe<&2, Export.Seen>, pr: Export.Probe, +ss: List<&2, Export.Seen>, +whole: Bool, +rs: List<&2, Export.Rec>, ep: {Export.put.path(put) == path : String}, es: {Export.seen.find(ss, path) == s : Maybe<&2, Export.Seen>}) -> {Export.step.safe(Export.step.held(put, path, lk, s, pr, whole, rs), ss, whole, rs) == True{} : Bool}:
  match s:
    case None{}:
      absent_safe(pr, lk, put, path, ss, whole, rs, ep, es)
    case Some{Export.Seen.Link{+p, +t}}:
      seen_link(lk, put, path, p, t, ss, whole, rs, ep, es)
    case Some{Export.Seen.File{+p, +d, +runs}}:
      seen_file(lk, put, path, p, d, runs, ss, whole, rs, ep, es)

def step_safe(o: Export.Outcome, +ss: List<&2, Export.Seen>, +dirs: Set(), +others: Set(), +whole: Bool, +rs: List<&2, Export.Rec>) -> {Export.step.safe(Export.step.of(o, ss, dirs, others, whole, rs), ss, whole, rs) == True{} : Bool}:
  match o:
    case Export.Outcome.Refused{p, b}:
      {==}
    case Export.Outcome.Laid{+put}:
      held_safe(put, Export.put.path(put), Export.is.link(put), Export.seen.find(ss, Export.put.path(put)), Export.probe.of(Arrange.has(dirs, Export.put.path(put)), Arrange.has(others, Export.put.path(put))), ss, whole, rs, {==}, {==})

# The folder's plan writes over no work nothing has recorded.
def steps_safe(os: List<&2, Export.Outcome>, +ss: List<&2, Export.Seen>, +dirs: Set(), +others: Set(), +whole: Bool, +rs: List<&2, Export.Rec>) -> {Export.steps.safe(Export.steps(os, ss, dirs, others, whole, rs), ss, whole, rs) == True{} : Bool}:
  match os:
    case Nil{}:
      {==}
    case +o <> +rest:
      and_tt(Export.step.safe(Export.step.of(o, ss, dirs, others, whole, rs), ss, whole, rs), Export.steps.safe(Export.steps(rest, ss, dirs, others, whole, rs), ss, whole, rs),
        step_safe(o, ss, dirs, others, whole, rs), steps_safe(rest, ss, dirs, others, whole, rs))

# Removing
# --------

def and_r(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      Empty.absurd({b == True{} : Bool}, S.false_true(e))

def and_l(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, S.false_true(e))

# A path with something to remove at it among the walk's entries still has
# it with one more entry in front.
def removed_more(ps: List<&2, String>, +s: Export.Seen, +rest: List<&2, Export.Seen>, +whole: Bool, +rs: List<&2, Export.Rec>, +h: {Export.removed.ok(ps, rest, whole, rs) == True{} : Bool}) -> {Export.removed.ok(ps, s <> rest, whole, rs) == True{} : Bool}:
  match ps:
    case Nil{}:
      {==}
    case +p <> +more:
      and_tt(Export.witness(s <> rest, p, whole, rs), Export.removed.ok(more, s <> rest, whole, rs),
        or_r(Bool.and(String.eq(Export.seen.path(s), p), Export.seen.gone(s, whole, rs)), Export.witness(rest, p, whole, rs), and_l(Export.witness(rest, p, whole, rs), Export.removed.ok(more, rest, whole, rs), h)),
        removed_more(more, s, rest, whole, rs, and_r(Export.witness(rest, p, whole, rs), Export.removed.ok(more, rest, whole, rs), h)))

def removed_step(c: Bool, +s: Export.Seen, +rest: List<&2, Export.Seen>, +placed: Set(), +whole: Bool, +rs: List<&2, Export.Rec>, +ec: {Bool.and(Bool.not(Arrange.has(placed, Export.seen.path(s))), Export.seen.gone(s, whole, rs)) == c : Bool}, +ih: {Export.removed.ok(Export.removes(rest, placed, whole, rs), rest, whole, rs) == True{} : Bool}) -> {Export.removed.ok(Tree.keep(~String, c, Export.seen.path(s), Export.removes(rest, placed, whole, rs)), s <> rest, whole, rs) == True{} : Bool}:
  match c:
    case True{}:
      +gone = and_r(Bool.not(Arrange.has(placed, Export.seen.path(s))), Export.seen.gone(s, whole, rs), ec)
      and_tt(Export.witness(s <> rest, Export.seen.path(s), whole, rs), Export.removed.ok(Export.removes(rest, placed, whole, rs), s <> rest, whole, rs),
        %Equal.sym(Bool, String.eq(Export.seen.path(s), Export.seen.path(s)), True{}, S.eq_refl(Export.seen.path(s))) : {Bool.or(Bool.and(_, Export.seen.gone(s, whole, rs)), Export.witness(rest, Export.seen.path(s), whole, rs)) == True{} : Bool}
        %Equal.sym(Bool, Export.seen.gone(s, whole, rs), True{}, gone) : {Bool.or(Bool.and(True{}, _), Export.witness(rest, Export.seen.path(s), whole, rs)) == True{} : Bool}
        {==},
        removed_more(Export.removes(rest, placed, whole, rs), s, rest, whole, rs, ih))
    case False{}:
      removed_more(Export.removes(rest, placed, whole, rs), s, rest, whole, rs, ih)

# Everything the folder's plan removes is something the walk found that
# some revision records, or that the export's own output is.
def removes_safe(ss: List<&2, Export.Seen>, +placed: Set(), +whole: Bool, +rs: List<&2, Export.Rec>) -> {Export.removed.ok(Export.removes(ss, placed, whole, rs), ss, whole, rs) == True{} : Bool}:
  match ss:
    case Nil{}:
      {==}
    case +s <> +rest:
      removed_step(Bool.and(Bool.not(Arrange.has(placed, Export.seen.path(s))), Export.seen.gone(s, whole, rs)), s, rest, placed, whole, rs, {==}, removes_safe(rest, placed, whole, rs))
