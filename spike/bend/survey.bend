# What the folder says against a position, as `record::survey` finds it and
# `status` prints it: which files arrived, left, changed, changed mode or
# were pointed elsewhere, which paths nothing here can take, and which
# arrivals hold exactly the bytes of a departure.
#
# Pure: every question the folder and the store answer is asked in
# `commands.bend` and handed in, one path at a time, as a `Seen`.
#
# Decision 0011 observes everything except a rename, so a file somebody
# moved with `mv` is an `added` and a `dropped`, and `renames` is where the
# survey says it noticed. Decision 0017 fixes a file's kind when it is
# added, so a path that changed between a link and a file is also a `drop`
# and an `add`.

import Base
import ./text.bend as T
import ./tree.bend as Tree
import ./folder.bend as Folder

# One path, as the position and the folder hold it, with what was learned
# about it: the folder's digest of a regular file, the digest the position's
# content has (`None` for a link, or where the parents being joined leave
# it differently), whether the folder's bytes are UTF-8 where they had to
# be read, what a recorded link spells where the last `update` wrote it,
# and whether the parents being joined leave a file of lines differently.
type Seen is Data:
  Seen{path: String, entry: Maybe<&2, Tree.Entry>, found: Maybe<&2, Folder.Found>,
       digest: String, before: Maybe<&2, String>, text: Bool, shown: Maybe<&2, String>, proposed: Bool}

# What one path contributes.
type Obs is Data:
  Obs.Added{path: String}
  Obs.Dropped{file: String, path: String, content: Maybe<&2, String>}
  Obs.Edited{path: String}
  Obs.Mode{path: String}
  Obs.Refused{path: String, because: String}
  Obs.Accept{path: String}
  Obs.Points{path: String, target: String, held: Maybe<&2, Tree.Entry>, shown: Maybe<&2, String>}
  Obs.Arrived{path: String, digest: String}
  Obs.Emptied{path: String}

# The digest of no bytes at all: every empty file has it, so it matches
# nothing.
def EMPTY() -> String:
  "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"

# Links
# -----

# `format::check_link_target`: why a string cannot be a link's target.
def link_fault(+target: String) -> Maybe<&2, String>:
  Bool.pick(Maybe<&2, String>, String.is_empty(target), Some{"it is empty, and a link with no target is not a link"},
  Bool.pick(Maybe<&2, String>, String.starts_with(target, "file:"), Some{"it begins with `file:`, which is how this format spells a link to a file it holds; rename it, or point it somewhere else"},
  Bool.pick(Maybe<&2, String>, Bool.or(String.starts_with(target, " "), String.ends_with(target, " ")), Some{"it has leading or trailing space, which a header value cannot keep"},
  Bool.pick(Maybe<&2, String>, List.any(~&2, ~Char, ~Folder.is_control, String.to_list(target)), Some{"it holds a control character, and a header is one line"}, None{}))))

def link.checked(+path: String, +target: String, held: Maybe<&2, Tree.Entry>, shown: Maybe<&2, String>, fresh: Bool, fault: Maybe<&2, String>) -> List<&2, Obs>:
  match fault:
    case Some{because}:
      [Obs.Refused{path, "it points at a target this format cannot hold: " ++ because}]
    case None{}:
      Bool.pick(List<&2, Obs>, fresh, [Obs.Added{path}, Obs.Points{path, target, None{}, None{}}], [Obs.Points{path, target, held, shown}])

# A link in the folder: refused for a target the format cannot hold, and
# otherwise pointing somewhere, which is resolved once the whole folder is
# known.
def link(+path: String, +target: String, held: Maybe<&2, Tree.Entry>, shown: Maybe<&2, String>, fresh: Bool) -> List<&2, Obs>:
  link.checked(path, target, held, shown, fresh, link_fault(target))

# Regular files
# -------------

def mode(+path: String, e: Tree.Entry, +runs: Bool) -> List<&2, Obs>:
  Bool.pick(List<&2, Obs>, Tree.mode_eq(Tree.entry_mode(e), Bool.pick(Tree.Mode, runs, Tree.Executable{}, Tree.Plain{})), Nil{}, [Obs.Mode{path}])

def same(a: Maybe<&2, String>, +b: String) -> Bool:
  match a:
    case None{}:
      False{}
    case Some{x}:
      String.eq(x, b)

# A file of bytes is settled by its digest; two parents stating different
# bytes leave nothing to settle it by, and a person has to accept a side.
def whole(+path: String, +e: Tree.Entry, +digest: String, +runs: Bool, payload: Maybe<&2, String>) -> List<&2, Obs>:
  match payload:
    case None{}:
      List.append(&2, Obs, mode(path, e, runs), [Obs.Accept{path}, Obs.Edited{path}])
    case Some{p}:
      List.append(&2, Obs, mode(path, e, runs), Bool.pick(List<&2, Obs>, String.eq(p, digest), Nil{}, [Obs.Edited{path}]))

# A file of lines is settled by its digest too, and is read only where that
# differs: a file recorded as lines that is no longer UTF-8 is refused, and
# says nothing about its mode either.
def lines.changed(+path: String, +e: Tree.Entry, +runs: Bool, +text: Bool) -> List<&2, Obs>:
  match text:
    case True{}:
      List.append(&2, Obs, mode(path, e, runs), [Obs.Edited{path}])
    case False{}:
      [Obs.Refused{path, "recorded as lines and no longer UTF-8 text; drop it and add it again"}]

def lines.agreed(+path: String, +e: Tree.Entry, +digest: String, +before: Maybe<&2, String>, +runs: Bool, +text: Bool) -> List<&2, Obs>:
  Bool.pick(List<&2, Obs>, same(before, digest), mode(path, e, runs), lines.changed(path, e, runs, text))

# Where the parents being joined leave a file of lines differently, the
# merge owes a resolution of whatever the folder holds, so there is no
# digest to settle it by — except that the grammar has no resolution of
# nothing, so an emptied file states no edit, and `record` refuses it: it
# is a merge and a deletion at once, and the deletion belongs in the
# revision after. Marker lines the renderer wrote, which `record` refuses
# too, are not modelled here.
def lines.proposed(+path: String, +e: Tree.Entry, +runs: Bool, +text: Bool, empty: Bool) -> List<&2, Obs>:
  match text:
    case False{}:
      lines.changed(path, e, runs, text)
    case True{}:
      Bool.pick(List<&2, Obs>, empty, List.append(&2, Obs, mode(path, e, runs), [Obs.Emptied{path}]), lines.changed(path, e, runs, text))

def lines(+path: String, +e: Tree.Entry, +digest: String, +before: Maybe<&2, String>, +runs: Bool, +text: Bool, proposed: Bool, empty: Bool) -> List<&2, Obs>:
  match proposed:
    case True{}:
      lines.proposed(path, e, runs, text, empty)
    case False{}:
      lines.agreed(path, e, digest, before, runs, text)

def dropped(+path: String, e: Tree.Entry, +before: Maybe<&2, String>) -> Obs:
  match e:
    case Tree.Entry{f, p, Tree.Link{}, y, g, m}:
      Obs.Dropped{f, path, None{}}
    case Tree.Entry{f, p, Tree.Whole{}, y, g, m}:
      Obs.Dropped{f, path, y}
    case Tree.Entry{f, p, Tree.Lines{}, y, g, m}:
      Obs.Dropped{f, path, before}

# A regular file the position holds: of the kind it was added as, or a link
# there before, which is a drop and an add.
def held_file(+path: String, +e: Tree.Entry, +digest: String, +before: Maybe<&2, String>, +runs: Bool, +text: Bool, proposed: Bool, empty: Bool) -> List<&2, Obs>:
  match e:
    case Tree.Entry{f, p, Tree.Link{}, y, g, m}:
      [Obs.Dropped{f, path, None{}}, Obs.Added{path}, Obs.Arrived{path, digest}]
    case Tree.Entry{f, p, Tree.Whole{}, y, g, m}:
      whole(path, e, digest, runs, y)
    case Tree.Entry{f, p, Tree.Lines{}, y, g, m}:
      lines(path, e, digest, before, runs, text, proposed, empty)

# A link the position holds a file at: a drop and an add again.
def held_link(+path: String, +target: String, +e: Tree.Entry, shown: Maybe<&2, String>, +before: Maybe<&2, String>) -> List<&2, Obs>:
  match e:
    case Tree.Entry{f, p, Tree.Link{}, y, g, m}:
      link(path, target, Some{e}, shown, False{})
    case other:
      dropped(path, other, before) <> link(path, target, None{}, None{}, True{})

# One path: the position's side against the folder's.
def seen(s: Seen) -> List<&2, Obs>:
  match s:
    case Seen{+path, Some{+e}, None{}, digest, before, text, shown, proposed}:
      [dropped(path, e, before)]
    case Seen{+path, None{}, Some{Folder.Found.Link{q, +target}}, digest, before, text, shown, proposed}:
      link(path, target, None{}, None{}, True{})
    case Seen{+path, None{}, Some{Folder.Found.File{q, runs, n}}, +digest, before, text, shown, proposed}:
      [Obs.Added{path}, Obs.Arrived{path, digest}]
    case Seen{+path, Some{+e}, Some{Folder.Found.Link{q, +target}}, digest, before, text, shown, proposed}:
      held_link(path, target, e, shown, before)
    case Seen{+path, Some{+e}, Some{Folder.Found.File{q, runs, +n}}, +digest, before, text, shown, proposed}:
      held_file(path, e, digest, before, runs, text, proposed, Nat.is_eq(n, 0n))
    case Seen{path, None{}, None{}, digest, before, text, shown, proposed}:
      Nil{}

def seens(ss: List<&2, Seen>) -> List<&2, Obs>:
  match ss:
    case Nil{}:
      Nil{}
    case s <> rest:
      List.append(&2, Obs, seen(s), seens(rest))

# Claims
# ------

# Paths more than one file of the position claims: decision 0008 lets a
# merge leave one, and 0012's `--at` is how a person settles it. With how
# many claim each, in path order.
def entry_le(a: Tree.Entry, b: Tree.Entry) -> Bool:
  String.is_le(Tree.entry_path(a), Tree.entry_path(b))

def claims.run(+path: String, +n: Nat, +rest: List<&2, T.Split>) -> List<&2, T.Split>:
  Bool.pick(List<&2, T.Split>, Nat.is_gt(n, 1n), T.Split{path, Nat.show(n)} <> rest, rest)

def heads_eq(ps: List<&2, String>, +path: String) -> Bool:
  match ps:
    case Nil{}:
      False{}
    case p <> rest:
      String.eq(p, path)

# Runs of one path, counted: `same` says whether the next path is `path`.
def claims.go(ps: List<&2, String>, +path: String, n: Nat, same: Bool) -> List<&2, T.Split>:
  match ps same:
    case Nil{} _:
      claims.run(path, n, Nil{})
    case p <> +rest True{}:
      claims.go(rest, path, 1n+n, heads_eq(rest, path))
    case +p <> +rest False{}:
      claims.run(path, n, claims.go(rest, p, 1n, heads_eq(rest, p)))

def paths(es: List<&2, Tree.Entry>) -> List<&2, String>:
  match es:
    case Nil{}:
      Nil{}
    case e <> rest:
      Tree.entry_path(e) <> paths(rest)

def claims.of(ps: List<&2, String>) -> List<&2, T.Split>:
  match ps:
    case Nil{}:
      Nil{}
    case +p <> +rest:
      claims.go(rest, p, 1n, heads_eq(rest, p))

def claims(+t: Tree.Tree()) -> List<&2, T.Split>:
  claims.of(List.sort(~String, ~(a => b => String.is_le(a, b)), paths(t)))

# A path several files claim and the folder does not hold: each of them is
# gone.
def claimed.has(cs: List<&2, T.Split>, +path: String) -> Bool:
  match cs:
    case Nil{}:
      False{}
    case T.Split{p, n} <> rest:
      Bool.or(String.eq(p, path), claimed.has(rest, path))

def has.of(r: Set() & Bool) -> Bool:
  (s, b) = r
  b

def has(+s: Set(), +key: String) -> Bool:
  has.of(Set.has(s, key))

def claimed_drops(t: Tree.Tree(), +cs: List<&2, T.Split>, +held: Set()) -> List<&2, Obs>:
  match t:
    case Nil{}:
      Nil{}
    case +e <> rest:
      +path = Tree.entry_path(e)
      +later = claimed_drops(rest, cs, held)
      Bool.pick(List<&2, Obs>, Bool.and(claimed.has(cs, path), Bool.not(has(held, path))), dropped(path, e, None{}) <> later, later)

# Everything else is unclaimed, and is what the survey pairs by path.
def unclaimed(t: Tree.Tree(), +cs: List<&2, T.Split>) -> Tree.Tree():
  match t:
    case Nil{}:
      Nil{}
    case +e <> rest:
      +later = unclaimed(rest, cs)
      Bool.pick(Tree.Tree(), claimed.has(cs, Tree.entry_path(e)), later, e <> later)

def unclaimed_found(fs: List<&2, Folder.Found>, +cs: List<&2, T.Split>) -> List<&2, Folder.Found>:
  match fs:
    case Nil{}:
      Nil{}
    case +f <> rest:
      +later = unclaimed_found(rest, cs)
      Bool.pick(List<&2, Folder.Found>, claimed.has(cs, Folder.found.path(f)), later, f <> later)

# Projections
# -----------

def added(os: List<&2, Obs>) -> List<&2, String>:
  match os:
    case Nil{}:
      Nil{}
    case Obs.Added{p} <> rest:
      p <> added(rest)
    case o <> rest:
      added(rest)

def edited(os: List<&2, Obs>) -> List<&2, String>:
  match os:
    case Nil{}:
      Nil{}
    case Obs.Edited{p} <> rest:
      p <> edited(rest)
    case o <> rest:
      edited(rest)

def modes(os: List<&2, Obs>) -> List<&2, String>:
  match os:
    case Nil{}:
      Nil{}
    case Obs.Mode{p} <> rest:
      p <> modes(rest)
    case o <> rest:
      modes(rest)

def accepts(os: List<&2, Obs>) -> List<&2, String>:
  match os:
    case Nil{}:
      Nil{}
    case Obs.Accept{p} <> rest:
      p <> accepts(rest)
    case o <> rest:
      accepts(rest)

def refusals(os: List<&2, Obs>) -> List<&2, T.Split>:
  match os:
    case Nil{}:
      Nil{}
    case Obs.Refused{p, b} <> rest:
      T.Split{p, b} <> refusals(rest)
    case o <> rest:
      refusals(rest)

def dropped_paths(os: List<&2, Obs>) -> List<&2, String>:
  match os:
    case Nil{}:
      Nil{}
    case Obs.Dropped{f, p, c} <> rest:
      p <> dropped_paths(rest)
    case o <> rest:
      dropped_paths(rest)

def dropped_files(os: List<&2, Obs>) -> List<&2, String>:
  match os:
    case Nil{}:
      Nil{}
    case Obs.Dropped{f, p, c} <> rest:
      f <> dropped_files(rest)
    case o <> rest:
      dropped_files(rest)

# What a dropped file held and an arrival holds, by digest, where it is
# not nothing.
def keyed(+d: String, +path: String, +rest: List<&2, T.Split>) -> List<&2, T.Split>:
  Bool.pick(List<&2, T.Split>, String.eq(d, EMPTY()), rest, T.Split{d, path} <> rest)

def departed(os: List<&2, Obs>) -> List<&2, T.Split>:
  match os:
    case Nil{}:
      Nil{}
    case Obs.Dropped{f, +p, Some{+d}} <> rest:
      keyed(d, p, departed(rest))
    case o <> rest:
      departed(rest)

def arrived(os: List<&2, Obs>) -> List<&2, T.Split>:
  match os:
    case Nil{}:
      Nil{}
    case Obs.Arrived{+p, +d} <> rest:
      keyed(d, p, arrived(rest))
    case o <> rest:
      arrived(rest)

def without.pick(b: Bool, +x: String, +later: List<&2, String>) -> List<&2, String>:
  Bool.pick(List<&2, String>, b, later, x <> later)

def without(xs: List<&2, String>, +out: Set()) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case +x <> rest:
      without.pick(has(out, x), x, without(rest, out))

def sorted(+xs: List<&2, String>) -> List<&2, String>:
  List.sort(~String, ~(a => b => String.is_le(a, b)), xs)

# Links
# -----

# `record::resolution`: where a link's target lands as a store path, folded
# lexically against the link's own directory; `None` outside the folder,
# for an absolute target, and for one naming a directory.
def res.pop(xs: List<&2, String>) -> Maybe<&2, List<&2, String>>:
  match xs:
    case Nil{}:
      None{}
    case x <> rest:
      Some{rest}

def res.push(+p: String, xs: List<&2, String>, skip: Bool, up: Bool) -> Maybe<&2, List<&2, String>>:
  match skip up:
    case True{} _:
      Some{xs}
    case False{} True{}:
      res.pop(xs)
    case False{} False{}:
      Some{p <> xs}

def res.step(+p: String, at: Maybe<&2, List<&2, String>>) -> Maybe<&2, List<&2, String>>:
  match at:
    case None{}:
      None{}
    case Some{xs}:
      res.push(p, xs, Bool.or(String.is_empty(p), String.eq(p, ".")), String.eq(p, ".."))

def res.go(parts: List<&2, String>, at: Maybe<&2, List<&2, String>>) -> Maybe<&2, List<&2, String>>:
  match parts:
    case Nil{}:
      at
    case +p <> rest:
      res.go(rest, res.step(p, at))

def res.joined(xs: List<&2, String>) -> Maybe<&2, String>:
  match xs:
    case Nil{}:
      None{}
    case +some:
      Some{String.join(List.reverse(&2, String, some), "/")}

def res.done(at: Maybe<&2, List<&2, String>>) -> Maybe<&2, String>:
  match at:
    case None{}:
      None{}
    case Some{xs}:
      res.joined(xs)

def res.dir(xs: List<&2, String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> rest:
      rest

def resolution(+link: String, +target: String) -> Maybe<&2, String>:
  Bool.pick(Maybe<&2, String>, Bool.or(String.starts_with(target, "/"), String.ends_with(target, "/")), None{},
    res.done(res.go(String.split(target, '/'), Some{res.dir(List.reverse(&2, String, String.split(link, '/')))})))

# Whether the tree this revision states holds a path: a file the position
# keeps there, or one arriving.
def any_kept(fs: List<&2, String>, +gone: Set()) -> Bool:
  match fs:
    case Nil{}:
      False{}
    case +f <> rest:
      Bool.or(Bool.not(has(gone, f)), any_kept(rest, gone))

def stated(+t: Tree.Tree(), +gone: Set(), +arriving: Set(), +at: String) -> Bool:
  Bool.or(has(arriving, at), any_kept(Tree.at(t, at), gone))

# What the folder's link says, spelled so it compares with what the tree
# says: `r` and a path for a reference, `v` and the string otherwise.
def observed.of(+t: Tree.Tree(), +gone: Set(), +arriving: Set(), +target: String, r: Maybe<&2, String>) -> String:
  match r:
    case None{}:
      "v" ++ target
    case Some{+at}:
      Bool.pick(String, stated(t, gone, arriving, at), "r" ++ at, "v" ++ target)

def observed(+t: Tree.Tree(), +gone: Set(), +arriving: Set(), +path: String, +target: String) -> String:
  observed.of(t, gone, arriving, target, resolution(path, target))

# What the position's link says, the same way: nothing where it holds no
# link, or where the file a reference names is going.
def recorded.target(+t: Tree.Tree(), +gone: Set(), g: Maybe<&2, Tree.Target>) -> Maybe<&2, String>:
  match g:
    case None{}:
      None{}
    case Some{Tree.Verbatim{s}}:
      Some{"v" ++ s}
    case Some{Tree.Reference{+named}}:
      Bool.pick(Maybe<&2, String>, has(gone, named), None{}, Maybe.map(&2, String, String, p => "r" ++ p, Tree.path(t, named)))

def recorded(+t: Tree.Tree(), +gone: Set(), held: Maybe<&2, Tree.Entry>) -> Maybe<&2, String>:
  match held:
    case None{}:
      None{}
    case Some{e}:
      recorded.target(t, gone, Tree.entry_target(e))

# What the last `update` wrote for the recorded link, unless the file it
# names is going: a string equal to that is nobody's observation.
def standing.target(+gone: Set(), g: Maybe<&2, Tree.Target>, shown: Maybe<&2, String>) -> Maybe<&2, String>:
  match g:
    case Some{Tree.Reference{+named}}:
      Bool.pick(Maybe<&2, String>, has(gone, named), None{}, shown)
    case _:
      shown

def standing(+gone: Set(), held: Maybe<&2, Tree.Entry>, shown: Maybe<&2, String>) -> Maybe<&2, String>:
  match held:
    case None{}:
      None{}
    case Some{e}:
      standing.target(gone, Tree.entry_target(e), shown)

def maybe_eq(a: Maybe<&2, String>, b: Maybe<&2, String>) -> Bool:
  match a b:
    case None{} None{}:
      True{}
    case Some{x} Some{y}:
      String.eq(x, y)
    case _ _:
      False{}

def retargeted(+t: Tree.Tree(), +gone: Set(), +arriving: Set(), +path: String, +target: String, +held: Maybe<&2, Tree.Entry>, shown: Maybe<&2, String>) -> Bool:
  Bool.pick(Bool, same(standing(gone, held, shown), target), False{},
    Bool.not(maybe_eq(recorded(t, gone, held), Some{observed(t, gone, arriving, path, target)})))

def links(+t: Tree.Tree(), +gone: Set(), +arriving: Set(), os: List<&2, Obs>) -> List<&2, String>:
  match os:
    case Nil{}:
      Nil{}
    case Obs.Points{+p, +target, +held, shown} <> rest:
      +later = links(t, gone, arriving, rest)
      Bool.pick(List<&2, String>, retargeted(t, gone, arriving, p, target, held, shown), p <> later, later)
    case o <> rest:
      links(t, gone, arriving, rest)

# Renames
# -------

def count(xs: List<&2, T.Split>, +d: String) -> Nat:
  match xs:
    case Nil{}:
      0n
    case T.Split{k, v} <> rest:
      Nat.add(Bool.pick(Nat, String.eq(k, d), 1n, 0n), count(rest, d))

def at_digest(xs: List<&2, T.Split>, +d: String) -> String:
  match xs:
    case Nil{}:
      SNil{}
    case T.Split{k, +v} <> rest:
      Bool.pick(String, String.eq(k, d), v, at_digest(rest, d))

type Rename is Data:
  Rename{digest: String, from: String, to: String}

# `record::renames`: a dropped path and an added path holding the same
# bytes, one to one, in digest order.
def renames.go(gs: List<&2, T.Split>, +all: List<&2, T.Split>, +arr: List<&2, T.Split>) -> List<&2, Rename>:
  match gs:
    case Nil{}:
      Nil{}
    case T.Split{+d, +from} <> rest:
      +later = renames.go(rest, all, arr)
      Bool.pick(List<&2, Rename>, Bool.and(Nat.is_eq(count(all, d), 1n), Nat.is_eq(count(arr, d), 1n)), Rename{d, from, at_digest(arr, d)} <> later, later)

def rename_le(a: Rename, b: Rename) -> Bool:
  match a b:
    case Rename{x, f, t} Rename{y, g, u}:
      String.is_le(x, y)

def rename_pair(r: Rename) -> T.Split:
  match r:
    case Rename{d, from, to}:
      T.Split{from, to}

def renames(+gs: List<&2, T.Split>, +arr: List<&2, T.Split>) -> List<&2, T.Split>:
  T.map(~Rename, ~T.Split, ~(r => rename_pair(r)), List.sort(~Rename, ~(a => b => rename_le(a, b)), renames.go(gs, gs, arr)))

# The survey
# ----------

# What `status` prints of it: the facts by kind and then path, what nothing
# here can take, the paths several files claim with how many, the byte
# payloads a person has to accept, and the renames it noticed.
type Survey is Data:
  Survey{facts: List<&2, T.Split>, refused: List<&2, T.Split>, claimed: List<&2, T.Split>, accept: List<&2, String>, renames: List<&2, T.Split>}

def fact(+kind: String, ps: List<&2, String>) -> List<&2, T.Split>:
  match ps:
    case Nil{}:
      Nil{}
    case p <> rest:
      T.Split{kind, p} <> fact(kind, rest)

# A file being added carries its content, mode and target in with it, and
# needs no second line (`LAWS.status_says_an_arrival_once`).
def facts.with(+arriving: Set(), +os: List<&2, Obs>, +links: List<&2, String>) -> List<&2, T.Split>:
  List.append(&2, T.Split, fact("added", sorted(added(os))),
  List.append(&2, T.Split, fact("dropped", sorted(dropped_paths(os))),
  List.append(&2, T.Split, fact("edited", without(sorted(edited(os)), arriving)),
  List.append(&2, T.Split, fact("mode", without(sorted(modes(os)), arriving)),
    fact("link", without(sorted(links), arriving))))))

def facts(+os: List<&2, Obs>, +links: List<&2, String>) -> List<&2, T.Split>:
  facts.with(Set.from_list(added(os)), os, links)

# What that law asks of the facts: a line other than an `added` or a
# `dropped` names no path arriving.
def arrives_once(+arriving: Set(), fs: List<&2, T.Split>) -> Bool:
  match fs:
    case Nil{}:
      True{}
    case T.Split{+k, +p} <> rest:
      Bool.and(Bool.or(String.eq(k, "added"), Bool.or(String.eq(k, "dropped"), Bool.not(has(arriving, p)))), arrives_once(arriving, rest))

def of(+t: Tree.Tree(), +cs: List<&2, T.Split>, walked: List<&2, T.Split>, +os: List<&2, Obs>) -> Survey:
  +gone = Set.from_list(dropped_files(os))
  +arriving = Set.from_list(added(os))
  Survey{facts(os, links(t, gone, arriving, os)), List.append(&2, T.Split, walked, refusals(os)), cs, accepts(os), renames(departed(os), arrived(os))}

# The survey of a folder against a position `t`: `held` is every path the
# folder holds, `walked` what its walk refused, and `ss` every path neither
# side lets several files claim.
def survey(+t: Tree.Tree(), +held: Set(), walked: List<&2, T.Split>, ss: List<&2, Seen>) -> Survey:
  +cs = claims(t)
  of(t, cs, walked, List.append(&2, Obs, seens(ss), claimed_drops(t, cs, held)))

def survey.refused(s: Survey) -> List<&2, T.Split>:
  match s:
    case Survey{facts, refused, claimed, accept, renames}:
      refused

# What `LAWS.status_refuses_what_the_folder_holds` asks of the refusals:
# each names a path the walk refused, or one a surveyed path found in the
# folder.
def walked_at(ws: List<&2, T.Split>, +p: String) -> Bool:
  match ws:
    case Nil{}:
      False{}
    case T.Split{q, b} <> rest:
      Bool.or(String.eq(q, p), walked_at(rest, p))

def found_at(ss: List<&2, Seen>, +p: String) -> Bool:
  match ss:
    case Nil{}:
      False{}
    case Seen{path, e, found, d, b, x, sh, pr} <> rest:
      Bool.or(Bool.and(String.eq(path, p), Maybe.is_some(&2, Folder.Found, found)), found_at(rest, p))

def refuses_found(+walked: List<&2, T.Split>, +ss: List<&2, Seen>, rs: List<&2, T.Split>) -> Bool:
  match rs:
    case Nil{}:
      True{}
    case T.Split{+p, b} <> rest:
      Bool.and(Bool.or(walked_at(walked, p), found_at(ss, p)), refuses_found(walked, ss, rest))

# Whether the folder says nothing the position does not.
def is_quiet(s: Survey) -> Bool:
  match s:
    case Survey{facts, refused, claimed, accept, renames}:
      Bool.and(Bool.and(List.is_empty(&2, T.Split, facts), List.is_empty(&2, T.Split, refused)), Bool.and(List.is_empty(&2, T.Split, claimed), List.is_empty(&2, String, accept)))

# Recording
# ---------

# `record --dry-run` surveys as `status` does, with what a person states
# beside the folder: which paths to look at, where a file several claim
# goes (`--at`), and the renames nothing can observe (`--move`). And what
# `status` describes, `record` refuses.

# `format::check_path`: why a path a person typed cannot be one. Unicode
# normal form C is not here, as nowhere in this port.
def component_fault(cs: List<&2, String>) -> Maybe<&2, String>:
  match cs:
    case Nil{}:
      None{}
    case +c <> rest:
      Bool.pick(Maybe<&2, String>, String.is_empty(c), Some{"it has an empty component"},
      Bool.pick(Maybe<&2, String>, Bool.or(String.eq(c, "."), String.eq(c, "..")), Some{"`.` and `..` are not components"}, component_fault(rest)))

def path_check(+p: String) -> Maybe<&2, String>:
  Bool.pick(Maybe<&2, String>, String.is_empty(p), Some{"it is empty"},
  Bool.pick(Maybe<&2, String>, String.starts_with(p, "/"), Some{"it begins with `/`, and a path is relative to the repository root"},
  Bool.pick(Maybe<&2, String>, String.ends_with(p, "/"), Some{"it ends with `/`, and a path names a file rather than a directory"},
  Bool.pick(Maybe<&2, String>, Bool.or(String.starts_with(p, " "), String.ends_with(p, " ")), Some{"it has leading or trailing space"},
  Bool.pick(Maybe<&2, String>, List.any(~&2, ~Char, ~Folder.is_control, String.to_list(p)), Some{"it holds a control character"},
    component_fault(String.split(p, '/')))))))

# `Restriction::covers`: a path named, or one beneath a named directory;
# every path where none is named.
def beneath(+named: String, +path: String) -> Bool:
  Bool.or(String.eq(path, named), String.starts_with(path, named ++ "/"))

def covers.any(ns: List<&2, String>, +path: String) -> Bool:
  match ns:
    case Nil{}:
      False{}
    case +n <> rest:
      Bool.or(beneath(n, path), covers.any(rest, path))

def covers(only: List<&2, String>, +path: String) -> Bool:
  match only:
    case Nil{}:
      True{}
    case +some:
      covers.any(some, path)

def any_beneath(+named: String, ps: List<&2, String>) -> Bool:
  match ps:
    case Nil{}:
      False{}
    case +p <> rest:
      Bool.or(beneath(named, p), any_beneath(named, rest))

def only.tree(+only: List<&2, String>, t: Tree.Tree()) -> Tree.Tree():
  match t:
    case Nil{}:
      Nil{}
    case +e <> rest:
      +later = only.tree(only, rest)
      Bool.pick(Tree.Tree(), covers(only, Tree.entry_path(e)), e <> later, later)

def only.found(+only: List<&2, String>, fs: List<&2, Folder.Found>) -> List<&2, Folder.Found>:
  match fs:
    case Nil{}:
      Nil{}
    case +f <> rest:
      +later = only.found(only, rest)
      Bool.pick(List<&2, Folder.Found>, covers(only, Folder.found.path(f)), f <> later, later)

def only.refused(+only: List<&2, String>, rs: List<&2, T.Split>) -> List<&2, T.Split>:
  match rs:
    case Nil{}:
      Nil{}
    case T.Split{+p, +b} <> rest:
      +later = only.refused(only, rest)
      Bool.pick(List<&2, T.Split>, covers(only, p), T.Split{p, b} <> later, later)

# A named path nothing answers to — not the folder, not the position, not
# where the stated renames put things — and whether a rule keeps it out,
# since the two have different fixes.
def unknown(ns: List<&2, String>, +folder: List<&2, String>, +was: List<&2, String>, +placed: List<&2, String>) -> List<&2, String>:
  match ns:
    case Nil{}:
      Nil{}
    case +n <> rest:
      +later = unknown(rest, folder, was, placed)
      Bool.pick(List<&2, String>, Bool.or(any_beneath(n, folder), Bool.or(any_beneath(n, was), any_beneath(n, placed))), later, n <> later)

def kept_out(+rules: List<&2, Folder.Scope>, ns: List<&2, String>, +keep: Bool) -> List<&2, String>:
  match ns:
    case Nil{}:
      Nil{}
    case +n <> rest:
      +later = kept_out(rules, rest, keep)
      Bool.pick(List<&2, String>, Bool.xor(Bool.or(Folder.skips(rules, n), Folder.skips_directory(rules, n)), Bool.not(keep)), n <> later, later)

# Where the stated renames put each file: the position's tree, with one
# file's path changed.
def placed.entry(e: Tree.Entry, +file: String, +to: String) -> Tree.Entry:
  match e:
    case Tree.Entry{+f, p, k, y, g, m}:
      Tree.Entry{f, Bool.pick(String, String.eq(f, file), to, p), k, y, g, m}

def relocated(t: Tree.Tree(), +file: String, +to: String) -> Tree.Tree():
  match t:
    case Nil{}:
      Nil{}
    case e <> rest:
      placed.entry(e, file, to) <> relocated(rest, file, to)

def by_file(+t: Tree.Tree()) -> Tree.Tree():
  List.sort(~Tree.Entry, ~(a => b => String.is_le(Tree.entry_file(a), Tree.entry_file(b))), t)

# A kind stated too late, or for a path nobody is looking at.
def kind_fixed(+p: String, t: Tree.Tree(), later: Maybe<&2, String>) -> Maybe<&2, String>:
  match t:
    case Nil{}:
      later
    case +e <> rest:
      Bool.pick(Maybe<&2, String>, String.eq(Tree.entry_path(e), p),
        Some{"`" ++ p ++ "` is already recorded as " ++ Tree.kind_show(Tree.entry_kind(e)) ++ ", and decision 0017 fixes that when a file is added; a file that has to change kind is a `drop` and an `add`, which is a new file with a new identity"},
        kind_fixed(p, rest, later))

def kind_fault(+only: List<&2, String>, +t: Tree.Tree(), ks: List<&2, T.Split>) -> Maybe<&2, String>:
  match ks:
    case Nil{}:
      None{}
    case T.Split{+p, k} <> rest:
      Bool.pick(Maybe<&2, String>, covers(only, p), kind_fixed(p, t, kind_fault(only, t, rest)),
        Some{"`" ++ p ++ "` is not one of the paths this is recording, so saying which kind it is would state nothing; name it as a path too, or drop the restriction"})

# What that refusal asks of the kinds a person states: each for a path the
# record is looking at, where no file of the position is
# (`LAWS.record_states_a_kind_only_for_an_arrival`).
def kinds_fresh(+only: List<&2, String>, +t: Tree.Tree(), ks: List<&2, T.Split>) -> Bool:
  match ks:
    case Nil{}:
      True{}
    case T.Split{+p, k} <> rest:
      Bool.and(Bool.and(covers(only, p), List.is_empty(&2, String, Tree.at(t, p))), kinds_fresh(only, t, rest))

# Each file moved, where it went last, unless the file is going.
def moved.later(ms: List<&2, T.Split>, +file: String) -> Bool:
  match ms:
    case Nil{}:
      False{}
    case T.Split{f, to} <> rest:
      Bool.or(String.eq(f, file), moved.later(rest, file))

def moved.paths(ms: List<&2, T.Split>, +gone: Set()) -> List<&2, String>:
  match ms:
    case Nil{}:
      Nil{}
    case T.Split{+f, +to} <> +rest:
      +later = moved.paths(rest, gone)
      Bool.pick(List<&2, String>, Bool.or(has(gone, f), moved.later(rest, f)), later, to <> later)

# Each file moved and where it went last, unless the file is going: the
# `move` lines, in the order the renames were stated.
def moved.final(ms: List<&2, T.Split>, +gone: Set()) -> List<&2, T.Split>:
  match ms:
    case Nil{}:
      Nil{}
    case T.Split{+f, +to} <> +rest:
      +later = moved.final(rest, gone)
      Bool.pick(List<&2, T.Split>, Bool.or(has(gone, f), moved.later(rest, f)), later, T.Split{f, to} <> later)

# What that law asks of the `move` lines (`LAWS.record_moves_each_file_once`):
# each is for a file not going, at the last place the renames put it, and
# no file has two.
def last_move(ms: List<&2, T.Split>, +file: String) -> Maybe<&2, String>:
  match ms:
    case Nil{}:
      None{}
    case T.Split{+f, +to} <> rest:
      Maybe.or(&2, String, last_move(rest, file), Bool.pick(Maybe<&2, String>, String.eq(f, file), Some{to}, None{}))

def moves_ok(+ms: List<&2, T.Split>, +gone: Set(), out: List<&2, T.Split>) -> Bool:
  match out:
    case Nil{}:
      True{}
    case T.Split{+f, +to} <> +rest:
      Bool.and(Bool.and(Bool.not(has(gone, f)), maybe_eq(last_move(ms, f), Some{to})), Bool.and(Bool.not(moved.later(rest, f)), moves_ok(ms, gone, rest)))

def emptied(os: List<&2, Obs>) -> List<&2, String>:
  match os:
    case Nil{}:
      Nil{}
    case Obs.Emptied{p} <> rest:
      p <> emptied(rest)
    case o <> rest:
      emptied(rest)

def pointed(os: List<&2, Obs>) -> List<&2, String>:
  match os:
    case Nil{}:
      Nil{}
    case Obs.Points{p, t, h, s} <> rest:
      p <> pointed(rest)
    case o <> rest:
      pointed(rest)

# What each link in the folder points at, by path.
def pointing(os: List<&2, Obs>) -> List<&2, T.Split>:
  match os:
    case Nil{}:
      Nil{}
    case Obs.Points{p, t, h, s} <> rest:
      T.Split{p, t} <> pointing(rest)
    case o <> rest:
      pointing(rest)

def dropped_at(os: List<&2, Obs>, +file: String) -> String:
  match os:
    case Nil{}:
      SNil{}
    case Obs.Dropped{+f, +p, c} <> rest:
      Bool.pick(String, String.eq(f, file), p, dropped_at(rest, file))
    case o <> rest:
      dropped_at(rest, file)

# A link this record is not looking at, whose target is going: no
# restatement can reach it.
def dangle.target(+link: String, g: Maybe<&2, Tree.Target>, +gone: Set(), +os: List<&2, Obs>, later: Maybe<&2, String>) -> Maybe<&2, String>:
  match g:
    case Some{Tree.Reference{+named}}:
      Bool.pick(Maybe<&2, String>, has(gone, named),
        Some{"`" ++ dropped_at(os, named) ++ "` is going, and `" ++ link ++ "` is a link to it that this record is not looking at; name `" ++ link ++ "` too, so its target can be written down as the string it will be"},
        later)
    case _:
      later

def dangle(t: Tree.Tree(), +gone: Set(), +pointing: Set(), +os: List<&2, Obs>) -> Maybe<&2, String>:
  match t:
    case Nil{}:
      None{}
    case Tree.Entry{+f, +p, k, y, g, m} <> rest:
      +later = dangle(rest, gone, pointing, os)
      Bool.pick(Maybe<&2, String>, Bool.or(has(gone, f), has(pointing, p)), later, dangle.target(p, g, gone, os, later))

# What that refusal asks of the position: no link of it names a file going,
# unless the link is going too or the folder's link at its path is one the
# record restates (`LAWS.record_refuses_a_dangling_link`).
def names_gone(g: Maybe<&2, Tree.Target>, +gone: Set()) -> Bool:
  match g:
    case Some{Tree.Reference{+named}}:
      has(gone, named)
    case _:
      False{}

def anchored(t: Tree.Tree(), +gone: Set(), +pointing: Set()) -> Bool:
  match t:
    case Nil{}:
      True{}
    case Tree.Entry{+f, +p, k, y, g, m} <> rest:
      Bool.and(Bool.or(Bool.or(has(gone, f), has(pointing, p)), Bool.not(names_gone(g, gone))), anchored(rest, gone, pointing))

# What `record --dry-run` prints: `status`'s facts, with a line for each
# file moved.
def facts.recorded(+arriving: Set(), +os: List<&2, Obs>, +links: List<&2, String>, +moved: List<&2, String>) -> List<&2, T.Split>:
  List.append(&2, T.Split, fact("added", sorted(added(os))),
  List.append(&2, T.Split, fact("moved", sorted(moved)),
  List.append(&2, T.Split, fact("dropped", sorted(dropped_paths(os))),
  List.append(&2, T.Split, fact("edited", without(sorted(edited(os)), arriving)),
  List.append(&2, T.Split, fact("mode", without(sorted(modes(os)), arriving)),
    fact("link", without(sorted(links), arriving)))))))

# The survey `record` plans from, and what it refuses: the paths several
# files claim, what nothing here can take, what a merge would empty, the
# contested bytes to accept, and a link left dangling.
# Alongside them, what writing the record needs beyond the facts it
# prints: every observation, and the paths whose links it states.
type Planned is Data:
  Planned{facts: List<&2, T.Split>, refused: List<&2, T.Split>, claimed: List<&2, T.Split>, accept: List<&2, String>, emptied: List<&2, String>, dangles: Maybe<&2, String>, obs: List<&2, Obs>, links: List<&2, String>}

# `t` is every file where the renames put it, in identifier order, and
# `looked` the part of it the restriction covers.
def planned(+t: Tree.Tree(), +looked: Tree.Tree(), +held: Set(), walked: List<&2, T.Split>, ss: List<&2, Seen>, +moves: List<&2, T.Split>) -> Planned:
  +cs = claims(looked)
  +os = List.append(&2, Obs, seens(ss), claimed_drops(looked, cs, held))
  +gone = Set.from_list(dropped_files(os))
  +arriving = Set.from_list(added(os))
  +ls = links(t, gone, arriving, os)
  Planned{facts.recorded(arriving, os, ls, moved.paths(moves, gone)), List.append(&2, T.Split, walked, refusals(os)), cs, sorted(accepts(os)), emptied(os), dangle(t, gone, Set.from_list(pointed(os)), os), os, ls}

def planned.dangles(pl: Planned) -> Maybe<&2, String>:
  match pl:
    case Planned{facts, refused, claimed, accept, emptied, dangles, obs, links}:
      dangles

def planned.refused(pl: Planned) -> List<&2, T.Split>:
  match pl:
    case Planned{facts, refused, claimed, accept, emptied, dangles, obs, links}:
      refused

# The files a plan drops, and the paths of the folder's links it observes.
def planned.gone(pl: Planned) -> Set():
  match pl:
    case Planned{facts, refused, claimed, accept, emptied, dangles, obs, links}:
      Set.from_list(dropped_files(obs))

def planned.pointing(pl: Planned) -> Set():
  match pl:
    case Planned{facts, refused, claimed, accept, emptied, dangles, obs, links}:
      Set.from_list(pointed(obs))
