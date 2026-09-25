# `update`: the folder catches up with the store.
#
# Decision 0030. The store can move ahead of the folder — a revision
# arrives, a merge is recorded, a run is abandoned — and `update` makes the
# folder hold the tree at a head: each file of lines as the text `cat`
# prints, each file of bytes as the payload the store holds, each link
# pointing where the tree says, each with its mode; and what the head does
# not hold is removed where some revision records its bytes. Nothing any
# revision does not record is ever written over or removed: a file in the
# way refuses the whole update, and a stray at a path the head does not hold
# stays where it is.
#
# As in the Rust tool, deciding and doing are a pair: `plan` works out what
# every path takes from what the store and the folder say, `effects` lists
# what carrying it out does, and the IO below performs exactly that list,
# so `--dry-run` and the real thing name the same files
# (`update_dry_run_names_what_it_does`). What the plan decides is what the
# laws are about (`update_lands`, `update_spares_the_unrecorded`,
# `update_touches_only_the_target`), stated against what `cat` reads from
# the store and what the walk found rather than the plan's own entries; the
# effects are four writes that decide nothing — `Store.put`, `Store.lay`,
# `Store.link` and `Store.chmod` — and `Store.remove`.

import Base
import ./text.bend as T
import ./ops.bend as Ops
import ./revision.bend as Rev
import ./store.bend as Store
import ./tree.bend as Tree
import ./utf8.bend as Utf8
import ./sha256.bend as Sha
import ./bookmark.bend as Bm
import ./folder.bend as Folder
import ./commands.bend as Main

# Arguments
# ---------

# `update [<target>] [-n|--dry-run]`, read as the Rust tool reads it: the
# flag anywhere, one target at most, and any other word beginning with `-`
# refused.
type UpdateCmd is Data:
  UpdateCmd{target: Maybe<&2, String>, dry: Bool}

# What a word is to `update`: the dry-run flag, another flag, or a target.
type UWord is Data:
  UWord.Dry{}
  UWord.Flag{}
  UWord.Word{}

def uword.of(dry: Bool, flag: Bool) -> UWord:
  match dry:
    case True{}:
      UWord.Dry{}
    case False{}:
      Bool.pick(UWord, flag, UWord.Flag{}, UWord.Word{})

def uword(ws: List<&2, String>) -> UWord:
  match ws:
    case Nil{}:
      UWord.Word{}
    case +w <> rest:
      uword.of(Bool.or(String.eq(w, "-n"), String.eq(w, "--dry-run")), String.starts_with(w, "-"))

# `k` is what the first word is.
def args.go(ws: List<&2, String>, target: Maybe<&2, String>, dry: Bool, k: UWord) -> Result<&2, &2, Main.Refused, UpdateCmd>:
  match ws target k:
    case Nil{} _ _:
      Done{UpdateCmd{target, dry}}
    case w <> +rest _ UWord.Dry{}:
      args.go(rest, target, True{}, uword(rest))
    case w <> rest _ UWord.Flag{}:
      Fail{Main.Refused{2, "`" ++ w ++ "` is not an `update` option"}}
    case w <> +rest None{} UWord.Word{}:
      args.go(rest, Some{w}, dry, uword(rest))
    case w <> rest Some{t} UWord.Word{}:
      Fail{Main.Refused{2, "`update` takes one target, and `" ++ w ++ "` is a second"}}

def args.r(+ws: List<&2, String>) -> Result<&2, &2, Main.Refused, UpdateCmd>:
  args.go(ws, None{}, False{}, uword(ws))

# What `update`'s words say, read plainly: a dry run where `-n` or
# `--dry-run` is among them, and the target the word that does not begin
# with `-`. `LAWS.update_reads_its_words` holds `args.r` to it.
def uargs.dry(ws: List<&2, String>) -> Bool:
  match ws:
    case Nil{}:
      False{}
    case +w <> rest:
      Bool.or(Bool.or(String.eq(w, "-n"), String.eq(w, "--dry-run")), uargs.dry(rest))

def uargs.target(ws: List<&2, String>) -> Maybe<&2, String>:
  match ws:
    case Nil{}:
      None{}
    case +w <> rest:
      Bool.pick(Maybe<&2, String>, String.starts_with(w, "-"), uargs.target(rest), Some{w})

# The plan
# --------

# What the folder holds at a path: a file the walk took, with its digest and
# whether it can be run; a link, and where it points; or, where the walk
# took nothing, what its directory's listing says stands there — a
# directory, a link whose target cannot be read, something else, or
# nothing at all.
type Held is Data:
  Held.File{digest: String, runs: Bool}
  Held.Link{target: String}
  Held.Dir{}
  Held.Unread{}
  Held.Other{}
  Held.Nothing{}

# What the target records at a path one file holds: the text of a file of
# lines, the payload of a file of bytes and where the store has it, or
# where a link points, spelled for the folder — or why none of them can be
# given, which refuses before the folder is asked.
type Wants is Data:
  Wants.Lines{text: String, mode: Tree.Mode}
  Wants.Whole{payload: String, at: String, mode: Tree.Mode}
  Wants.Link{target: String}
  Wants.No{because: String}

# What one path takes: nothing, its bytes written, its mode set, its link
# made — or a refusal, which stops the whole update.
type Step is Data:
  Step.Refuse{because: String}
  Step.Keep{}
  Step.Write{}
  Step.Mode{}
  Step.Link{}

def UNRECORDED() -> String:
  "it holds work nothing has recorded"

def runs(m: Tree.Mode) -> Bool:
  match m:
    case Tree.Executable{}:
      True{}
    case Tree.Plain{}:
      False{}

# What a file of lines hashes to once written: the digest of its text.
def text_digest(+text: String) -> String:
  Sha.digest(Utf8.encode(text))

# A file the target records, against what the folder holds: the same bytes
# need at most their mode; other bytes are written over only where some
# revision records them; and nothing but nothing is a place to write.
def decide.file(+digest: String, +mode: Tree.Mode, h: Held, +recorded: List<&2, String>) -> Step:
  match h:
    case Held.File{+d, r}:
      Bool.pick(Step, String.eq(d, digest),
        Bool.pick(Step, Bool.xor(r, runs(mode)), Step.Mode{}, Step.Keep{}),
        Bool.pick(Step, Rev.member(recorded, d), Step.Write{}, Step.Refuse{UNRECORDED()}))
    case Held.Link{t}:
      Step.Refuse{"a symbolic link stands there"}
    case Held.Unread{}:
      Step.Refuse{"a symbolic link stands there"}
    case Held.Dir{}:
      Step.Refuse{"a directory stands there"}
    case Held.Other{}:
      Step.Refuse{"something stands there the walk did not offer"}
    case Held.Nothing{}:
      Step.Write{}

# A link the target records: one pointing there already is kept, and any
# other link is pointed there; a file is replaced only where its bytes are
# recorded, and anything the walk did not take is not replaced at all.
def decide.link(+target: String, h: Held, +recorded: List<&2, String>) -> Step:
  match h:
    case Held.Link{+t}:
      Bool.pick(Step, String.eq(t, target), Step.Keep{}, Step.Link{})
    case Held.File{+d, r}:
      Bool.pick(Step, Rev.member(recorded, d), Step.Link{}, Step.Refuse{UNRECORDED()})
    case Held.Nothing{}:
      Step.Link{}
    case Held.Dir{}:
      Step.Refuse{"a directory stands there"}
    case Held.Unread{}:
      Step.Refuse{UNRECORDED()}
    case Held.Other{}:
      Step.Refuse{UNRECORDED()}

# `recorded` is every digest some revision records for a file that has
# been at the path.
def decide(w: Wants, h: Held, +recorded: List<&2, String>) -> Step:
  match w:
    case Wants.Lines{+text, +mode}:
      decide.file(text_digest(text), mode, h, recorded)
    case Wants.Whole{+p, at, +mode}:
      decide.file(p, mode, h, recorded)
    case Wants.Link{+t}:
      decide.link(t, h, recorded)
    case Wants.No{b}:
      Step.Refuse{b}

# One path the target's tree holds with one file, and what the plan needs
# to decide it.
type Look is Data:
  Look{path: String, wants: Wants, held: Held, recorded: List<&2, String>}

# A path the walk took that the target does not hold, with every digest —
# or, for a link, every spelling — some revision records there, and whether
# a current head holds the path.
type Gone is Data:
  Gone{path: String, held: Held, recorded: List<&2, String>, tracked: Bool}

# What becomes of such a path: removed, where its content is recorded;
# left and said to be, where a head tracks it; and otherwise left in
# silence, a stray nobody recorded, exactly as before the update.
type Leaving is Data:
  Leaving.Remove{}
  Leaving.Leave{}
  Leaving.Stay{}

def leaving.of(held: Bool, tracked: Bool) -> Leaving:
  match held:
    case True{}:
      Leaving.Remove{}
    case False{}:
      Bool.pick(Leaving, tracked, Leaving.Leave{}, Leaving.Stay{})

def leaving(h: Held, +recorded: List<&2, String>, tracked: Bool) -> Leaving:
  match h:
    case Held.File{+d, r}:
      leaving.of(Rev.member(recorded, d), tracked)
    case Held.Link{+t}:
      leaving.of(Rev.member(recorded, t), tracked)
    case _:
      Leaving.Stay{}

type Decided is Data:
  Decided{path: String, wants: Wants, held: Held, recorded: List<&2, String>, step: Step}

type Went is Data:
  Went{path: String, held: Held, recorded: List<&2, String>, leaving: Leaving}

def decided.one(l: Look) -> Decided:
  match l:
    case Look{p, +w, +h, +rs}:
      Decided{p, w, h, rs, decide(w, h, rs)}

def decided(ls: List<&2, Look>) -> List<&2, Decided>:
  match ls:
    case Nil{}:
      Nil{}
    case l <> rest:
      decided.one(l) <> decided(rest)

def went.one(g: Gone) -> Went:
  match g:
    case Gone{p, +h, +rs, t}:
      Went{p, h, rs, leaving(h, rs, t)}

def went(gs: List<&2, Gone>) -> List<&2, Went>:
  match gs:
    case Nil{}:
      Nil{}
    case g <> rest:
      went.one(g) <> went(rest)

# The paths the steps refuse, each with why.
def refusals(ds: List<&2, Decided>) -> List<&2, T.Split>:
  match ds:
    case Nil{}:
      Nil{}
    case Decided{p, w, h, rs, Step.Refuse{b}} <> rest:
      T.Split{p, b} <> refusals(rest)
    case d <> rest:
      refusals(rest)

# Refusals in path order and then by reason, each once: the Rust tool
# collects them, sorts and deduplicates before it says any.
def split_le(+a: T.Split, +b: T.Split) -> Bool:
  match a b:
    case T.Split{+p, +x} T.Split{+q, +y}:
      Bool.or(String.is_lt(p, q), Bool.and(String.eq(p, q), String.is_le(x, y)))

def split_eq(a: T.Split, b: T.Split) -> Bool:
  match a b:
    case T.Split{p, x} T.Split{q, y}:
      Bool.and(String.eq(p, q), String.eq(x, y))

def splits.distinct.keep(+a: T.Split, rest: List<&2, T.Split>, same: Bool) -> List<&2, T.Split>:
  match same:
    case True{}:
      rest
    case False{}:
      a <> rest

def splits.distinct(xs: List<&2, T.Split>) -> List<&2, T.Split>:
  match xs:
    case +a <> +b <> rest:
      splits.distinct.keep(a, splits.distinct(b <> rest), split_eq(a, b))
    case other:
      other

def sorted_refusals(+xs: List<&2, T.Split>) -> List<&2, T.Split>:
  splits.distinct(List.sort(~T.Split, ~(a => b => split_le(a, b)), xs))

# What one update does, decided before anything is done: a step for each
# path the target holds with one file, and what becomes of each path it
# does not.
type Plan is Data:
  Plan{steps: List<&2, Decided>, gone: List<&2, Went>}

def plan.of(steps: List<&2, Decided>, gone: List<&2, Went>, +refused: List<&2, T.Split>) -> Result<&2, &2, List<&2, T.Split>, Plan>:
  match refused:
    case Nil{}:
      Done{Plan{steps, gone}}
    case +some:
      Fail{sorted_refusals(some)}

# All or nothing, decision 0030's rule: `tree` is what the target's tree
# refuses before the folder is consulted, and one refusal anywhere stops
# every write.
def plan(tree: List<&2, T.Split>, looks: List<&2, Look>, gones: List<&2, Gone>) -> Result<&2, &2, List<&2, T.Split>, Plan>:
  +steps = decided(looks)
  plan.of(steps, went(gones), List.append(&2, T.Split, tree, refusals(steps)))

# What a plan leaves
# ------------------

# What a path holds once its step is done: the bytes written, with the mode
# the target records; the mode set; the link made. This is a model of the
# host's writes, not a proof about them: it says what `Store.put` and
# `Store.lay` are taken to leave (the bytes asked for), what `Store.chmod`
# leaves (the bit asked for) and what `Store.link` leaves (a link pointing
# where it was asked to). Every law below that speaks of
# the folder after an update — `update_lands`, `update_again_keeps`,
# `update_settles_exactly_what_stays` — speaks of it through this model.
# That the effects do what it says is RUNTIME.md's contract for them, and
# `check.py` holds it by comparing the whole folder after each `update` with
# the Rust tool's; nothing here proves it.
def wants.digest(w: Wants) -> String:
  match w:
    case Wants.Lines{+text, m}:
      text_digest(text)
    case Wants.Whole{p, at, m}:
      p
    case Wants.Link{t}:
      t
    case Wants.No{b}:
      b

def wants.runs(w: Wants) -> Bool:
  match w:
    case Wants.Lines{t, m}:
      runs(m)
    case Wants.Whole{p, at, m}:
      runs(m)
    case _:
      False{}

def after.written(+w: Wants, link: Bool) -> Held:
  match link:
    case True{}:
      Held.Link{wants.digest(w)}
    case False{}:
      Held.File{wants.digest(w), wants.runs(w)}

def after.moded(+w: Wants, h: Held) -> Held:
  match h:
    case Held.File{d, r}:
      Held.File{d, wants.runs(w)}
    case other:
      other

def after(+w: Wants, h: Held, s: Step) -> Held:
  match s:
    case Step.Write{}:
      after.written(w, False{})
    case Step.Link{}:
      after.written(w, True{})
    case Step.Mode{}:
      after.moded(w, h)
    case _:
      h

# Whether a path holds what the target records: a file of lines or of bytes
# its digest and its mode, a link its target.
def lands.file(+digest: String, +r: Bool, h: Held) -> Bool:
  match h:
    case Held.File{d, x}:
      Bool.and(String.eq(d, digest), Bool.not(Bool.xor(x, r)))
    case _:
      False{}

def lands.link(+target: String, h: Held) -> Bool:
  match h:
    case Held.Link{t}:
      String.eq(t, target)
    case _:
      False{}

def lands(w: Wants, h: Held) -> Bool:
  match w:
    case Wants.Lines{+text, +m}:
      lands.file(text_digest(text), runs(m), h)
    case Wants.Whole{+p, at, +m}:
      lands.file(p, runs(m), h)
    case Wants.Link{+t}:
      lands.link(t, h)
    case Wants.No{b}:
      False{}

# Every path a plan steps through holds, once it is done, what the target
# records there.
def lands_all(ds: List<&2, Decided>) -> Bool:
  match ds:
    case Nil{}:
      True{}
    case Decided{p, +w, h, rs, s} <> rest:
      Bool.and(lands(w, after(w, h, s)), lands_all(rest))

# Whether a step writes over what stood at a path, and whether a removal
# takes it away: what decision 0030 allows only for bytes some revision
# records.
def replaces(s: Step) -> Bool:
  match s:
    case Step.Write{}:
      True{}
    case Step.Link{}:
      True{}
    case _:
      False{}

# A file a step writes over holds bytes the history of its path records —
# the plan's own check, which `touches.recorded` below restates in the
# store's terms.
def spared.file(h: Held, +recorded: List<&2, String>) -> Bool:
  match h:
    case Held.File{+d, r}:
      Rev.member(recorded, d)
    case _:
      True{}

def spared.step(h: Held, +recorded: List<&2, String>, touched: Bool) -> Bool:
  match touched:
    case True{}:
      spared.file(h, recorded)
    case False{}:
      True{}

# Reading the target
# ------------------

# The target's tree by path: each path with every file that claims it, in
# path order, and under one path in file order.
type Placing is Data:
  Placing{path: String, files: List<&2, Tree.Entry>}

def placings.put(+e: Tree.Entry, ps: List<&2, Placing>) -> List<&2, Placing>:
  match ps:
    case Nil{}:
      [Placing{Tree.entry_path(e), [e]}]
    case Placing{+p, +fs} <> +rest:
      Bool.pick(List<&2, Placing>, String.eq(p, Tree.entry_path(e)), Placing{p, e <> fs} <> rest, Placing{Tree.entry_path(e), [e]} <> Placing{p, fs} <> rest)

def placings.go(es: List<&2, Tree.Entry>) -> List<&2, Placing>:
  match es:
    case Nil{}:
      Nil{}
    case +e <> rest:
      placings.put(e, placings.go(rest))

def placings(+t: Tree.Tree()) -> List<&2, Placing>:
  placings.go(List.sort(~Tree.Entry, ~(a => b => String.is_le(Tree.entry_path(a), Tree.entry_path(b))), t))

def placing.path(p: Placing) -> String:
  match p:
    case Placing{path, fs}:
      path

# Every directory a path of the tree is beneath.
def dirs.go(parts: List<&2, String>, +at: String, out: List<&2, String>) -> List<&2, String>:
  match parts:
    case Nil{}:
      out
    case p <> Nil{}:
      out
    case +p <> rest:
      +d = Folder.joined(at, p)
      dirs.go(rest, d, d <> out)

def dirs(ps: List<&2, Placing>) -> List<&2, String>:
  match ps:
    case Nil{}:
      Nil{}
    case Placing{+p, fs} <> rest:
      List.append(&2, String, dirs.go(String.split(p, '/'), SNil{}, Nil{}), dirs(rest))

def has(r: Set() & Bool) -> Bool:
  (s, b) = r
  b

def refuse.if(+path: String, +because: String, hit: Bool) -> List<&2, T.Split>:
  Bool.pick(List<&2, T.Split>, hit, [T.Split{path, because}], Nil{})

# What the walk refused, where the tree needs to write at it or beneath it.
def refuse.walked(+path: String, rs: List<&2, T.Split>) -> List<&2, T.Split>:
  match rs:
    case Nil{}:
      Nil{}
    case T.Split{+q, +b} <> rest:
      List.append(&2, T.Split, refuse.if(path, "the folder cannot offer what stands at " ++ q ++ ": " ++ b, Bool.or(String.eq(path, q), String.starts_with(path, q ++ "/"))), refuse.walked(path, rest))

# What the tree itself refuses at one path, before the folder is asked:
# two files at it, a directory of another file, the store, a rule in
# `skipped/`, and what the walk could not offer there.
def refuse.placing(+ds: Set(), +rules: List<&2, Folder.Scope>, +walked: List<&2, T.Split>, pl: Placing) -> List<&2, T.Split>:
  match pl:
    case Placing{+p, fs}:
      List.concat(&2, T.Split, [
        refuse.if(p, "two files hold this path; record the move that settles it first", Nat.is_gt(List.length(&2, Tree.Entry, fs), 1n)),
        refuse.if(p, "it is also a directory of another file here, and a folder cannot hold both", has(Set.has(ds, p))),
        refuse.if(p, "it would write a working file into the store", Bool.or(String.eq(p, "history"), String.starts_with(p, "history/"))),
        refuse.if(p, "a `skip` rule in history/skipped.txt covers it, so the walk could never offer it back", Folder.skips(rules, p)),
        refuse.walked(p, walked)])

def refuse.tree(+ds: Set(), +rules: List<&2, Folder.Scope>, +walked: List<&2, T.Split>, ps: List<&2, Placing>) -> List<&2, T.Split>:
  match ps:
    case Nil{}:
      Nil{}
    case pl <> rest:
      List.append(&2, T.Split, refuse.placing(ds, rules, walked, pl), refuse.tree(ds, rules, walked, rest))

# The one file at each path one file holds.
def single(ps: List<&2, Placing>) -> List<&2, Tree.Entry>:
  match ps:
    case Nil{}:
      Nil{}
    case Placing{p, [e]} <> rest:
      e <> single(rest)
    case pl <> rest:
      single(rest)

# A link's target spelled for the folder, relative to the link's own
# directory where it names a file of the tree: `update::materialise`, with
# nothing for a file the tree does not hold.
def materialise(+t: Tree.Tree(), +at: String, g: Tree.Target) -> Maybe<&2, String>:
  match g:
    case Tree.Verbatim{s}:
      Some{s}
    case Tree.Reference{+named}:
      Maybe.map(&2, String, String, to => Main.relative_path(Main.directory_of(at), to), Tree.path(t, named))

def wants.lines(+m: Tree.Mode, r: Result<&2, &2, String, List<&2, Ops.Item>>) -> Wants:
  match r:
    case Done{items}:
      Wants.Lines{Ops.text(items), m}
    case Fail{e}:
      Wants.No{e}

def wants.held(+d: String, +m: Tree.Mode, +at: String) -> Wants:
  Bool.pick(Wants, String.is_empty(at), Wants.No{"this store does not hold the content " ++ d ++ "; receive the rest first"}, Wants.Whole{d, at, m})

def wants.whole(+located: Map<&2, String>, +m: Tree.Mode, y: Maybe<&2, String>) -> Wants:
  match y:
    case None{}:
      Wants.No{"concurrent revisions each state its whole content, and neither is a winner"}
    case Some{+d}:
      wants.held(d, m, Main.stat_of(d, Map.get(String, SNil{}, located, d)))

def wants.spelled(s: Maybe<&2, String>) -> Wants:
  match s:
    case None{}:
      Wants.No{"it names a file this tree does not hold"}
    case Some{x}:
      Wants.Link{x}

def wants.link(+t: Tree.Tree(), +p: String, g: Maybe<&2, Tree.Target>) -> Wants:
  match g:
    case None{}:
      Wants.No{"it is a link that names nowhere"}
    case Some{x}:
      wants.spelled(materialise(t, p, x))

# What the target records for one file: `store.content` at the target for
# a file of lines, which is what `cat` prints; the payload, where the store
# has it, for a file of bytes; and a link's target, spelled.
def wants.of(+fs: List<&2, Main.Full>, +oldest: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +located: Map<&2, String>, +id: String, +t: Tree.Tree(), e: Tree.Entry) -> Wants:
  match e:
    case Tree.Entry{+f, p, Tree.Lines{}, y, g, +m}:
      wants.lines(m, Main.content.found(fs, ds, id, f, Main.content_of(Main.contents.go(oldest, ds, f, Nil{}), id)))
    case Tree.Entry{f, p, Tree.Whole{}, y, g, +m}:
      wants.whole(located, m, y)
    case Tree.Entry{f, +p, Tree.Link{}, y, g, m}:
      wants.link(t, p, g)

# Reading the folder
# ------------------

# What the walk took, by path.
def found.map(fs: List<&2, Folder.Found>, +dg: Map<&2, String>, m: Map<&2, Maybe<&2, Held>>) -> Map<&2, Maybe<&2, Held>>:
  match fs:
    case Nil{}:
      m
    case Folder.Found.File{+p, r, n} <> rest:
      found.map(rest, dg, Map.set(&2, Maybe<&2, Held>, m, p, Some{Held.File{Main.status.folder_digest(dg, p), r}}))
    case Folder.Found.Link{+p, t} <> rest:
      found.map(rest, dg, Map.set(&2, Maybe<&2, Held>, m, p, Some{Held.Link{t}}))

def took(r: Map<&2, Maybe<&2, Held>> & Maybe<&2, Held>) -> Maybe<&2, Held>:
  (m, h) = r
  h

def taken(+m: Map<&2, Maybe<&2, Held>>, +p: String) -> Maybe<&2, Held>:
  took(Map.get(Maybe<&2, Held>, None{}, m, p))

# What one line of a directory's listing says stands at `name`, if it
# names it: `l` lines are read with the line after them.
def stood.f(+name: String, cut: Maybe<&2, T.Split>) -> Maybe<&2, Held>:
  match cut:
    case Some{T.Split{size, n}}:
      Bool.pick(Maybe<&2, Held>, String.eq(n, name), Some{Held.Other{}}, None{})
    case None{}:
      None{}

def stood.line(+line: String, +name: String) -> Maybe<&2, Held>:
  +k = String.take(line, 1n)
  +rest = String.drop(line, 2n)
  +named = String.eq(rest, name)
  Bool.pick(Maybe<&2, Held>, Bool.and(String.eq(k, "d"), named), Some{Held.Dir{}},
  Bool.pick(Maybe<&2, Held>, Bool.and(String.eq(k, "L"), named), Some{Held.Unread{}},
  Bool.pick(Maybe<&2, Held>, Bool.and(String.eq(k, "o"), named), Some{Held.Other{}},
  Bool.pick(Maybe<&2, Held>, String.eq(k, "f"), stood.f(name, T.split_once(String.drop(rest, 2n))), None{}))))

def stood.link(+line: String) -> Maybe<&2, String>:
  Bool.pick(Maybe<&2, String>, String.starts_with(line, "l "), Some{String.drop(line, 2n)}, None{})

def stood.first(m: Maybe<&2, Held>, later: Held) -> Held:
  match m:
    case Some{h}:
      h
    case None{}:
      later

# `link` is the link whose target this line is.
def stood.go(ls: List<&2, String>, +name: String, link: Maybe<&2, String>) -> Held:
  match ls link:
    case Nil{} _:
      Held.Nothing{}
    case l <> rest Some{n}:
      Bool.pick(Held, String.eq(n, name), Held.Link{l}, stood.go(rest, name, None{}))
    case +l <> rest None{}:
      stood.first(stood.line(l, name), stood.go(rest, name, stood.link(l)))

def listing.text(r: Result<&1, &1, U32 & String, String>) -> String:
  match r:
    case Done{t}:
      t
    case Fail{e}:
      SNil{}

# Each directory's listing, by directory: a directory that is not there
# lists nothing.
def listings(+repo: String, ds: List<&2, String>, m: Map<&2, String>) -> IO(Map<&2, String>):
  match ds:
    case Nil{}:
      IO.pure(Map<&2, String>, m)
    case +d <> rest:
      do IO<Map<&2, String>>:
        r : Result<&1, &1, U32 & String, String> <- Store.listing_of(Folder.joined(repo, d))
        listings(repo, rest, Map.set(&2, String, m, d, listing.text(r)))

# What the folder holds at a path: what the walk took, or else what the
# listing of its directory says.
def held.of(+ls: Map<&2, String>, +p: String, h: Maybe<&2, Held>) -> Held:
  match h:
    case Some{x}:
      x
    case None{}:
      stood.go(String.split(Main.stat_of(p, Map.get(String, SNil{}, ls, Main.directory_of(p))), '\n'), Folder.last_component(p), None{})

def untaken(+m: Map<&2, Maybe<&2, Held>>, es: List<&2, Tree.Entry>) -> List<&2, String>:
  match es:
    case Nil{}:
      Nil{}
    case +e <> rest:
      +later = untaken(m, rest)
      Bool.pick(List<&2, String>, Maybe.is_none(&2, Held, taken(m, Tree.entry_path(e))), Main.directory_of(Tree.entry_path(e)) <> later, later)

# What some revision records
# --------------------------

# Every file some revision put at a path, by an `add` or a `move`.
def at_path(+path: String, cut: Maybe<&2, T.Split>) -> Bool:
  match cut:
    case Some{T.Split{f, p}}:
      String.eq(p, path)
    case None{}:
      False{}

def files_at.facts(hs: List<&2, Rev.Header>, +path: String) -> List<&2, String>:
  match hs:
    case Nil{}:
      Nil{}
    case Rev.Header{+k, +v} <> rest:
      Rev.keep(Bool.and(Bool.or(String.eq(k, "add"), String.eq(k, "move")), at_path(path, T.split_once(v))), T.word(v), files_at.facts(rest, path))

def files_at(fs: List<&2, Main.Full>, +path: String) -> List<&2, String>:
  match fs:
    case Nil{}:
      Nil{}
    case f <> rest:
      List.append(&2, String, files_at.facts(Main.facts_of(f), path), files_at(rest, path))

# Whether a revision states anything of a file's content: it added it,
# stated its content, or joined parents, which gives content no single
# edit stated.
def said.some(s: Main.Said) -> Bool:
  match s:
    case Main.Nothing{}:
      False{}
    case _:
      True{}

def touches(+file: String, f: Main.Full) -> Bool:
  match f:
    case Main.Full{i, c, +parents, s, a, w, rb, rv, +facts, m}:
      Bool.or(Rev.member(Rev.files_of(facts, "add"), file), Bool.or(said.some(Main.said(facts, file)), Nat.is_gt(List.length(&2, String, parents), 1n)))

def recorded.lines(r: Result<&2, &2, String, List<&2, Ops.Item>>) -> Maybe<&2, String>:
  match r:
    case Done{items}:
      Some{Ops.state_digest(items)}
    case Fail{e}:
      None{}

# `store.content_at_heads`: what one file hashes to at a revision, of
# lines or of bytes; a link has no bytes.
def recorded.entry(+fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +cs: List<&2, Main.Contents>, +id: String, +file: String, e: Maybe<&2, Tree.Entry>) -> Maybe<&2, String>:
  match e:
    case Some{Tree.Entry{f, p, Tree.Lines{}, y, g, m}}:
      recorded.lines(Main.content.found(fs, ds, id, file, Main.content_of(cs, id)))
    case Some{Tree.Entry{f, p, Tree.Whole{}, y, g, m}}:
      y
    case _:
      None{}

def recorded.tree(+fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +cs: List<&2, Main.Contents>, +id: String, +file: String, t: Result<&2, &2, Main.Refused, Tree.Tree()>) -> Maybe<&2, String>:
  match t:
    case Done{t2}:
      recorded.entry(fs, ds, cs, id, file, Tree.lookup(t2, file))
    case Fail{e}:
      None{}

def push(m: Maybe<&2, String>, rest: List<&2, String>) -> List<&2, String>:
  match m:
    case Some{x}:
      x <> rest
    case None{}:
      rest

def recorded.revs(rs: List<&2, Main.Full>, +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +cs: List<&2, Main.Contents>, +file: String) -> List<&2, String>:
  match rs:
    case Nil{}:
      Nil{}
    case +f <> rest:
      +later = recorded.revs(rest, fs, ds, cs, file)
      Bool.pick(List<&2, String>, touches(file, f), push(recorded.tree(fs, ds, cs, Main.id_of(f), file, Main.tree.r(fs, Main.id_of(f))), later), later)

def recorded.files(xs: List<&2, String>, +fs: List<&2, Main.Full>, +oldest: List<&2, Main.Full>, +ds: List<&2, Store.Doc>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case +x <> rest:
      List.append(&2, String, recorded.revs(fs, fs, ds, Main.contents.go(oldest, ds, x, Nil{}), x), recorded.files(rest, fs, oldest, ds))

# Decision 0030's rule, asked of the whole store: every digest some
# revision records for a file that has been at the path — superseded and
# abandoned revisions included, since what matters is whether the bytes
# can be had back.
def recorded(+fs: List<&2, Main.Full>, +oldest: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +path: String) -> List<&2, String>:
  recorded.files(Main.sorted_distinct(files_at(fs, path)), fs, oldest, ds)

# The link each revision recorded at the path, spelled as `update` would
# have laid it then.
def spelled.link(+file: String, cut: Maybe<&2, T.Split>) -> Maybe<&2, String>:
  match cut:
    case Some{T.Split{f, t}}:
      Bool.pick(Maybe<&2, String>, String.eq(f, file), Some{t}, None{})
    case None{}:
      None{}

def spelled.stated(hs: List<&2, Rev.Header>, +file: String) -> List<&2, String>:
  match hs:
    case Nil{}:
      Nil{}
    case Rev.Header{+k, v} <> rest:
      +later = spelled.stated(rest, file)
      Bool.pick(List<&2, String>, String.eq(k, "link"), push(spelled.link(file, T.split_once(v)), later), later)

def spelled.at(+file: String, +stated: String, t: Result<&2, &2, Main.Refused, Tree.Tree()>) -> Maybe<&2, String>:
  match t:
    case Done{+t2}:
      Maybe.bind(&2, String, String, Tree.path(t2, file), at => materialise(t2, at, Tree.target_of(stated)))
    case Fail{e}:
      None{}

def spelled.each(ts: List<&2, String>, +fs: List<&2, Main.Full>, +file: String, +id: String) -> List<&2, String>:
  match ts:
    case Nil{}:
      Nil{}
    case +t <> rest:
      push(spelled.at(file, t, Main.tree.r(fs, id)), spelled.each(rest, fs, file, id))

def spelled.revs(rs: List<&2, Main.Full>, +fs: List<&2, Main.Full>, +file: String) -> List<&2, String>:
  match rs:
    case Nil{}:
      Nil{}
    case +f <> rest:
      List.append(&2, String, spelled.each(spelled.stated(Main.facts_of(f), file), fs, file, Main.id_of(f)), spelled.revs(rest, fs, file))

def spelled.files(xs: List<&2, String>, +fs: List<&2, Main.Full>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case +x <> rest:
      List.append(&2, String, spelled.revs(fs, fs, x), spelled.files(rest, fs))

def spelled(+fs: List<&2, Main.Full>, +path: String) -> List<&2, String>:
  spelled.files(Main.sorted_distinct(files_at(fs, path)), fs)

# The target
# ----------

def spelled.id(+fs: List<&2, Main.Full>, +bs: List<&2, Bm.Bookmark>, +id: String) -> String:
  String.take(id, 12n) ++ Main.names_at(bs, Main.history(fs), id)

def heads.sorted(+fs: List<&2, Main.Full>) -> List<&2, String>:
  List.sort(~String, ~(a => b => String.is_le(a, b)), Main.current_heads(Main.history(fs)))

# The head the folder is to hold: the one named, or the one there is.
def target.none(+fs: List<&2, Main.Full>, +bs: List<&2, Bm.Bookmark>, heads: List<&2, String>) -> Result<&2, &2, Main.Refused, String>:
  match heads:
    case Nil{}:
      Fail{Main.Refused{1, "nothing is recorded here yet"}}
    case only <> Nil{}:
      Done{only}
    case +several:
      Fail{Main.Refused{1, "this store has " ++ Nat.show(List.length(&2, String, several)) ++ " heads, so nothing here is `the` latest; name the one the folder should hold:" ++ Main.described(fs, bs, several)}}

def target.r(+fs: List<&2, Main.Full>, +bs: List<&2, Bm.Bookmark>, t: Maybe<&2, String>) -> Result<&2, &2, Main.Refused, String>:
  match t:
    case None{}:
      target.none(fs, bs, heads.sorted(fs))
    case Some{+s}:
      do Result<&2, &2, Main.Refused, String>:
        f : Main.Full <- Main.resolved.r(fs, bs, s)
        return Main.id_of(f)

# The folder is only ever given a head, which is what lets nothing remember
# where it stands.
def head.r(+fs: List<&2, Main.Full>, +bs: List<&2, Bm.Bookmark>, +id: String) -> Result<&2, &2, Main.Refused, Unit>:
  Bool.pick(Result<&2, &2, Main.Refused, Unit>, Rev.member(heads.sorted(fs), id), Done{Unit{}},
    Fail{Main.Refused{1, spelled.id(fs, bs, id) ++ " is not a head, and the folder only ever holds one; reading the past is `show` and `cat`, and going back is `abandon`. the heads:" ++ Main.described(fs, bs, heads.sorted(fs))}})

# Printing
# --------

def step.write(s: Step) -> Bool:
  match s:
    case Step.Write{}:
      True{}
    case _:
      False{}

def step.mode(s: Step) -> Bool:
  match s:
    case Step.Mode{}:
      True{}
    case _:
      False{}

def step.link(s: Step) -> Bool:
  match s:
    case Step.Link{}:
      True{}
    case _:
      False{}

def stepping(~pick: Step -> Bool, ds: List<&2, Decided>) -> List<&2, Decided>:
  match ds:
    case Nil{}:
      Nil{}
    case Decided{p, w, h, rs, +s} <> rest:
      Tree.keep(~Decided, pick(s), Decided{p, w, h, rs, s}, stepping(~pick, rest))

def decided.path(d: Decided) -> String:
  match d:
    case Decided{p, w, h, rs, s}:
      p

def wants.mode(w: Wants) -> String:
  match w:
    case Wants.Lines{t, m}:
      Tree.mode_show(m)
    case Wants.Whole{p, at, m}:
      Tree.mode_show(m)
    case _:
      "plain"

def wants.target(w: Wants) -> String:
  match w:
    case Wants.Link{t}:
      t
    case _:
      SNil{}

def leaving.remove(l: Leaving) -> Bool:
  match l:
    case Leaving.Remove{}:
      True{}
    case _:
      False{}

def leaving.leave(l: Leaving) -> Bool:
  match l:
    case Leaving.Leave{}:
      True{}
    case _:
      False{}

def going(~pick: Leaving -> Bool, ws: List<&2, Went>) -> List<&2, String>:
  match ws:
    case Nil{}:
      Nil{}
    case Went{+p, h, rs, +l} <> rest:
      Rev.keep(pick(l), p, going(~pick, rest))

def writes(ds: List<&2, Decided>) -> List<&2, Decided>:
  stepping(~(s => step.write(s)), ds)

def modes(ds: List<&2, Decided>) -> List<&2, Decided>:
  stepping(~(s => step.mode(s)), ds)

def links(ds: List<&2, Decided>) -> List<&2, Decided>:
  stepping(~(s => step.link(s)), ds)

def removes(ws: List<&2, Went>) -> List<&2, String>:
  going(~(l => leaving.remove(l)), ws)

def leaves(ws: List<&2, Went>) -> List<&2, String>:
  going(~(l => leaving.leave(l)), ws)

# Whether there is nothing to do: the folder holds the target already.
def settled(+p: Plan) -> Bool:
  match p:
    case Plan{+ds, +ws}:
      Bool.and(Bool.and(List.is_empty(&2, Decided, writes(ds)), List.is_empty(&2, String, removes(ws))), Bool.and(List.is_empty(&2, Decided, modes(ds)), List.is_empty(&2, Decided, links(ds))))

def said.paths(+verb: String, ps: List<&2, String>) -> List<&2, String>:
  match ps:
    case Nil{}:
      Nil{}
    case p <> rest:
      (Main.pad(verb, 7n) ++ " " ++ p) <> said.paths(verb, rest)

def said.modes(+verb: String, ds: List<&2, Decided>) -> List<&2, String>:
  match ds:
    case Nil{}:
      Nil{}
    case Decided{+p, w, h, rs, s} <> rest:
      (Main.pad(verb, 7n) ++ " " ++ p ++ "  (" ++ wants.mode(w) ++ ")") <> said.modes(verb, rest)

def said.links(+verb: String, ds: List<&2, Decided>) -> List<&2, String>:
  match ds:
    case Nil{}:
      Nil{}
    case Decided{+p, w, h, rs, s} <> rest:
      (Main.pad(verb, 7n) ++ " " ++ p ++ "  (" ++ wants.target(w) ++ ")") <> said.links(verb, rest)

def said.leaves(ps: List<&2, String>) -> List<&2, String>:
  T.map(~String, ~String, ~(p => "left " ++ p ++ " alone: " ++ UNRECORDED()), ps)

# `--dry-run`: the plan, and nothing done.
def said.dry(+spelled: String, +p: Plan) -> List<&2, String>:
  match p:
    case Plan{+ds, +ws}:
      List.concat(&2, String, [said.paths("write", T.map(~Decided, ~String, ~(d => decided.path(d)), writes(ds))), said.paths("remove", removes(ws)), said.modes("mode", modes(ds)), said.links("link", links(ds)), said.leaves(leaves(ws)),
        Bool.pick(List<&2, String>, settled(Plan{ds, ws}), ["the folder already holds " ++ spelled], Nil{})])

def said.settled(+spelled: String, p: Plan) -> List<&2, String>:
  match p:
    case Plan{ds, ws}:
      List.append(&2, String, said.leaves(leaves(ws)), ["the folder already holds " ++ spelled])

# Doing it
# --------

def done.r(r: Result<&1, &1, U32 & String, String>) -> Result<&2, &2, Main.Refused, String>:
  match r:
    case Done{x}:
      Done{x}
    case Fail{Tuple{code, msg}}:
      Fail{Main.Refused{1, msg}}

def done.io(r: Result<&1, &1, U32 & String, String>) -> IO(String):
  Main.refused.io(String, done.r(r))

# Where a path is in the folder, as the Rust tool's update asks it: a file
# the walk found where the folder spells it, since decision 0033 lets a
# folder spell a name decomposed that the tree spells composed, and an
# update rewrites the file there rather than laying another beside it; and
# any other path joined on as the tree spells it.
def spelt.of(r: Map<&2, String> & String) -> String:
  (m, s) = r
  s

def spelt(+dm: Map<&2, String>, +p: String) -> String:
  spelt.of(Map.get(String, p, dm, p))

def spelt.all(+dm: Map<&2, String>, ps: List<&2, String>) -> List<&2, String>:
  match ps:
    case Nil{}:
      Nil{}
    case +p <> rest:
      spelt(dm, p) <> spelt.all(dm, rest)

def disk(+repo: String, +dm: Map<&2, String>, +p: String) -> String:
  Folder.joined(repo, spelt(dm, p))

def removed.one(+p: String, answer: String) -> List<&2, String>:
  Bool.pick(List<&2, String>, String.eq(answer, "removed"), [p], Nil{})

# The bit set after the bytes land, and said where it was not already so.
def chmod.said(+p: String, +w: Wants, was: String) -> List<&2, String>:
  Bool.pick(List<&2, String>, Bool.xor(String.eq(was, "1"), wants.runs(w)), [Main.pad("mode", 7n) ++ " " ++ p ++ "  (" ++ wants.mode(w) ++ ")"], Nil{})

def chmod(+repo: String, +dm: Map<&2, String>, +p: String, +w: Wants) -> IO(List<&2, String>):
  do IO<List<&2, String>>:
    r : Result<&1, &1, U32 & String, String> <- Store.chmodded(disk(repo, dm, p) ++ "\n" ++ Bool.pick(String, wants.runs(w), "1", "0"))
    was : String <- done.io(r)
    return chmod.said(p, w, was)

def write.one(+repo: String, +dm: Map<&2, String>, +p: String, w: Wants) -> IO(Result<&1, &1, U32 & String, String>):
  match w:
    case Wants.Lines{text, m}:
      Store.put_text(disk(repo, dm, p) ++ "\n" ++ text)
    case Wants.Whole{d, at, m}:
      Store.laid(at ++ "\n" ++ disk(repo, dm, p) ++ "\n" ++ d)
    case _:
      IO.pure(Result<&1, &1, U32 & String, String>, Done{SNil{}})

# What carrying out a plan does to the folder, as `apply` performs it:
# each removal, then each file written (its mode set after the bytes land),
# each link made, and each mode set on bytes already right — one write of
# the host's each, in that order, and nothing decided between them.
# `LAWS.update_dry_run_names_what_it_does` holds the dry run to this list,
# and `LAWS.update_touches_only_the_target` says where in the folder it
# reaches.
type Effect is Data:
  Effect.Remove{path: String}
  Effect.Write{path: String, wants: Wants}
  Effect.Link{path: String, target: String}
  Effect.Mode{path: String, wants: Wants}

def effects.removes(ps: List<&2, String>) -> List<&2, Effect>:
  match ps:
    case Nil{}:
      Nil{}
    case p <> rest:
      Effect.Remove{p} <> effects.removes(rest)

def effects.writes(ds: List<&2, Decided>) -> List<&2, Effect>:
  match ds:
    case Nil{}:
      Nil{}
    case Decided{p, w, h, rs, s} <> rest:
      Effect.Write{p, w} <> effects.writes(rest)

def effects.links(ds: List<&2, Decided>) -> List<&2, Effect>:
  match ds:
    case Nil{}:
      Nil{}
    case Decided{p, w, h, rs, s} <> rest:
      Effect.Link{p, wants.target(w)} <> effects.links(rest)

def effects.modes(ds: List<&2, Decided>) -> List<&2, Effect>:
  match ds:
    case Nil{}:
      Nil{}
    case Decided{p, w, h, rs, s} <> rest:
      Effect.Mode{p, w} <> effects.modes(rest)

def effects(p: Plan) -> List<&2, Effect>:
  match p:
    case Plan{+ds, ws}:
      List.concat(&2, Effect, [effects.removes(removes(ws)), effects.writes(writes(ds)), effects.links(links(ds)), effects.modes(modes(ds))])

# The dry run read back
# ---------------------
#
# What `LAWS.update_dry_run_names_what_it_does` reads the dry run with, and
# names the effects with: a line beginning with a verb, padded as the Rust
# tool pads it, is read as what follows the verb — a path written or
# removed, a path and the mode it is set to, a path and where its link
# points, or the target the folder already holds.
type Named is Data:
  Named{writes: List<&2, String>, removes: List<&2, String>, modes: List<&2, String>, links: List<&2, String>, settled: List<&2, String>}

def dry.as(+l: String, +verb: String, rest: List<&2, String>) -> List<&2, String>:
  Rev.keep(String.starts_with(l, verb), String.drop(l, String.length(verb)), rest)

def dry.line(+l: String, r: Named) -> Named:
  match r:
    case Named{a, b, c, d, x}:
      Named{dry.as(l, "write   ", a), dry.as(l, "remove  ", b), dry.as(l, "mode    ", c), dry.as(l, "link    ", d), dry.as(l, "the folder already holds ", x)}

def dry.read(ls: List<&2, String>) -> Named:
  match ls:
    case Nil{}:
      Named{Nil{}, Nil{}, Nil{}, Nil{}, Nil{}}
    case +l <> rest:
      dry.line(l, dry.read(rest))

# Each effect as the dry run names it: a mode by what the bit is set to, a
# link by where the host is asked to point it.
def effect.named(e: Effect, r: Named) -> Named:
  match e r:
    case Effect.Write{p, w} Named{a, b, c, d, x}:
      Named{p <> a, b, c, d, x}
    case Effect.Remove{p} Named{a, b, c, d, x}:
      Named{a, p <> b, c, d, x}
    case Effect.Mode{p, +w} Named{a, b, c, d, x}:
      Named{a, b, (p ++ "  (" ++ Bool.pick(String, wants.runs(w), "executable", "plain") ++ ")") <> c, d, x}
    case Effect.Link{p, t} Named{a, b, c, d, x}:
      Named{a, b, c, (p ++ "  (" ++ t ++ ")") <> d, x}

def effects.named(es: List<&2, Effect>) -> Named:
  match es:
    case Nil{}:
      Named{Nil{}, Nil{}, Nil{}, Nil{}, Nil{}}
    case e <> rest:
      effect.named(e, effects.named(rest))

def named.settled(r: Named, y: List<&2, String>) -> Named:
  match r:
    case Named{a, b, c, d, x}:
      Named{a, b, c, d, y}

# The effects, named; and the folder said to hold the target already
# exactly where there are none.
def effects.read(+spelled: String, +es: List<&2, Effect>) -> Named:
  named.settled(effects.named(es), Bool.pick(List<&2, String>, List.is_empty(&2, Effect, es), [spelled], Nil{}))

# What the host said as the effects were performed: the paths it removed,
# and the mode lines owed by the files written and by the modes set.
type Carried is Data:
  Carried{removed: List<&2, String>, wset: List<&2, String>, mset: List<&2, String>}

def carried.removed(+p: String, +answer: String, c: Carried) -> Carried:
  match c:
    case Carried{r, w, m}:
      Carried{List.append(&2, String, removed.one(p, answer), r), w, m}

def carried.wset(set: List<&2, String>, c: Carried) -> Carried:
  match c:
    case Carried{r, w, m}:
      Carried{r, List.append(&2, String, set, w), m}

def carried.mset(set: List<&2, String>, c: Carried) -> Carried:
  match c:
    case Carried{r, w, m}:
      Carried{r, w, List.append(&2, String, set, m)}

# Each effect in turn. A removal takes away each directory it empties up to
# the folder itself — the directories above the path as the tree spells it,
# which is where the Rust tool tidies; a file written has its bit set after.
def perform(+repo: String, +dm: Map<&2, String>, es: List<&2, Effect>) -> IO(Carried):
  match es:
    case Nil{}:
      IO.pure(Carried, Carried{Nil{}, Nil{}, Nil{}})
    case Effect.Remove{+p} <> rest:
      do IO<Carried>:
        r : Result<&1, &1, U32 & String, String> <- Store.removed(repo ++ "\n" ++ disk(repo, dm, p) ++ "\n" ++ Folder.joined(repo, p))
        a : String <- done.io(r)
        more : Carried <- perform(repo, dm, rest)
        return carried.removed(p, a, more)
    case Effect.Write{+p, +w} <> rest:
      do IO<Carried>:
        r : Result<&1, &1, U32 & String, String> <- write.one(repo, dm, p, w)
        a : String <- done.io(r)
        set : List<&2, String> <- chmod(repo, dm, p, w)
        more : Carried <- perform(repo, dm, rest)
        return carried.wset(set, more)
    case Effect.Link{+p, +t} <> rest:
      do IO<Carried>:
        r : Result<&1, &1, U32 & String, String> <- Store.linked(disk(repo, dm, p) ++ "\n" ++ t)
        a : String <- done.io(r)
        perform(repo, dm, rest)
    case Effect.Mode{+p, +w} <> rest:
      do IO<Carried>:
        set : List<&2, String> <- chmod(repo, dm, p, w)
        more : Carried <- perform(repo, dm, rest)
        return carried.mset(set, more)

# A written file that does not read back as what was written: the folder
# folds two of the tree's paths onto one file, decision 0027's case, and
# cannot hold this tree.
def folded(ds: List<&2, Decided>, stats: List<&2, String>) -> List<&2, String>:
  match ds stats:
    case Decided{+p, w, h, rs, s} <> rest +st <> more:
      Rev.keep(Bool.not(String.eq(T.word(st), wants.digest(w))), p, folded(rest, more))
    case _ _:
      Nil{}

def folded.r(fs: List<&2, String>) -> Result<&2, &2, Main.Refused, Unit>:
  match fs:
    case Nil{}:
      Done{Unit{}}
    case +some:
      Fail{Main.Refused{1, "this folder folds paths the tree holds apart, and cannot represent it:" ++ String.concat(T.map(~String, ~String, ~(p => "\n  " ++ p), some))}}

def applied.lines(+paths: List<&2, String>, +spelled: String, ds: List<&2, Decided>, ws: List<&2, Went>, fold: List<&2, String>, c: Carried) -> List<&2, String>:
  match c:
    case Carried{removed, wset, mset}:
      List.concat(&2, String, [said.paths("wrote", paths), said.paths("removed", removed), wset, mset, said.links("linked", links(ds)), said.leaves(leaves(ws)),
        Bool.pick(List<&2, String>, List.is_empty(&2, String, fold), ["the folder holds " ++ spelled], Nil{})])

def apply(+repo: String, +dm: Map<&2, String>, +spelled: String, p: Plan) -> IO(Unit):
  match p:
    case Plan{+ds, +ws}:
      +written = writes(ds)
      +paths = T.map(~Decided, ~String, ~(d => decided.path(d)), written)
      do IO<Unit>:
        c : Carried <- perform(repo, dm, effects(Plan{ds, ws}))
        stats : List<&2, String> <- Store.stats(repo, spelt.all(dm, paths))
        +fold : List<&2, String> = folded(written, stats)
        Main.print_lines(applied.lines(paths, spelled, ds, ws, fold, c))
        Main.refused.io(Unit, folded.r(fold))

def done.plan(+repo: String, +dm: Map<&2, String>, +spelled: String, +dry: Bool, +p: Plan) -> IO(Unit):
  match dry:
    case True{}:
      Main.print_lines(said.dry(spelled, p))
    case False{}:
      Bool.pick(IO(Unit), settled(p), Main.print_lines(said.settled(spelled, p)), apply(repo, dm, spelled, p))

def refused.lines(rs: List<&2, T.Split>) -> String:
  match rs:
    case Nil{}:
      SNil{}
    case T.Split{p, b} <> rest:
      "\n  " ++ p ++ ": " ++ b ++ refused.lines(rest)

def planned.r(r: Result<&2, &2, List<&2, T.Split>, Plan>) -> Result<&2, &2, Main.Refused, Plan>:
  match r:
    case Done{p}:
      Done{p}
    case Fail{rs}:
      Fail{Main.Refused{1, "the folder cannot take this tree whole, so nothing was written:" ++ refused.lines(rs)}}

# The command
# -----------

# What the store says the folder should hold
# ------------------------------------------
#
# The laws about `update` are stated against the store's own readings, not
# the plan's: what `cat <target> <path>` reads, the payload and mode the
# target's tree names, where `cat` says a link points; and, for what may be
# written over or taken away, what `cat` of any revision the store holds
# reads for any file of it.

# A path holding a file with these bytes and this bit, or a link pointing
# here.
def holds.bytes(h: Held, +digest: String, +x: Bool) -> Bool:
  match h:
    case Held.File{d, r}:
      Bool.and(String.eq(d, digest), Bool.not(Bool.xor(r, x)))
    case _:
      False{}

def holds.lines(h: Held, +x: Bool, r: Result<&2, &2, String, List<&2, Ops.Item>>) -> Bool:
  match r:
    case Done{items}:
      holds.bytes(h, Sha.digest(Utf8.encode(Ops.text(items))), x)
    case Fail{e}:
      False{}

def holds.payload(h: Held, +x: Bool, y: Maybe<&2, String>) -> Bool:
  match y:
    case Some{+d}:
      holds.bytes(h, d, x)
    case None{}:
      False{}

def holds.link(h: Held, +spelled: String) -> Bool:
  match h:
    case Held.Link{s}:
      String.eq(s, spelled)
    case _:
      False{}

def holds.target(h: Held, +t: Tree.Tree(), +at: String, g: Maybe<&2, Tree.Target>) -> Bool:
  match g:
    case Some{x}:
      holds.link(h, Main.materialise(t, at, x))
    case None{}:
      False{}

def executable(m: Tree.Mode) -> Bool:
  match m:
    case Tree.Executable{}:
      True{}
    case Tree.Plain{}:
      False{}

# Whether a path holds what the target records for one file of its tree:
# the bytes `cat` of the target reads for a file of lines, from the
# documents `ds`, or the payload its tree names for a file of bytes, each
# with the tree's mode; or, for a link, a link pointing where `cat` says it
# points.
def reads(+fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +id: String, +t: Tree.Tree(), e: Tree.Entry, h: Held) -> Bool:
  match e:
    case Tree.Entry{+f, p, Tree.Lines{}, y, g, m}:
      holds.lines(h, executable(m), Main.content(fs, ds, id, f))
    case Tree.Entry{f, p, Tree.Whole{}, y, g, m}:
      holds.payload(h, executable(m), y)
    case Tree.Entry{f, +p, Tree.Link{}, y, g, m}:
      holds.target(h, t, p, g)

# Once the plan is carried out, each path the target's tree holds one file
# at holds what the target records there, and the plan's step at it is
# the one for that path. What a step leaves is `after`'s reading of the
# effects.
def holds.go(+fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +id: String, +t: Tree.Tree(), es: List<&2, Tree.Entry>, steps: List<&2, Decided>) -> Bool:
  match es steps:
    case Nil{} Nil{}:
      True{}
    case +e <> er Decided{+p, +w, +h, rs, +s} <> sr:
      Bool.and(Bool.and(String.eq(p, Tree.entry_path(e)), reads(fs, ds, id, t, e, after(w, h, s))), holds.go(fs, ds, id, t, er, sr))
    case _ _:
      False{}

def holds(+fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +id: String, +t: Tree.Tree(), p: Plan) -> Bool:
  match p:
    case Plan{steps, gone}:
      holds.go(fs, ds, id, t, single(placings(t)), steps)

# Whether `cat` of a revision the store holds reads exactly these bytes for
# some file of its tree, or its tree names them as a file's payload: bytes
# that can be had back.
def records.lines(+d: String, r: Result<&2, &2, String, List<&2, Ops.Item>>) -> Bool:
  match r:
    case Done{items}:
      String.eq(Sha.digest(Utf8.encode(Ops.text(items))), d)
    case Fail{e}:
      False{}

def records.payload(+d: String, y: Maybe<&2, String>) -> Bool:
  match y:
    case Some{x}:
      String.eq(x, d)
    case None{}:
      False{}

def entry.records(+fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +id: String, e: Tree.Entry, +d: String) -> Bool:
  match e:
    case Tree.Entry{+f, p, Tree.Lines{}, y, g, m}:
      records.lines(d, Main.content(fs, ds, id, f))
    case Tree.Entry{f, p, Tree.Whole{}, y, g, m}:
      records.payload(d, y)
    case Tree.Entry{f, p, Tree.Link{}, y, g, m}:
      False{}

def tree.records(+fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +id: String, t: Tree.Tree(), +d: String) -> Bool:
  match t:
    case Nil{}:
      False{}
    case e <> rest:
      Bool.or(entry.records(fs, ds, id, e, d), tree.records(fs, ds, id, rest, d))

def rev.records(+fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +id: String, r: Result<&2, &2, Main.Refused, Tree.Tree()>, +d: String) -> Bool:
  match r:
    case Done{t}:
      tree.records(fs, ds, id, t, d)
    case Fail{e}:
      False{}

def recoverable.go(rs: List<&2, Main.Full>, +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +d: String) -> Bool:
  match rs:
    case Nil{}:
      False{}
    case +f <> rest:
      Bool.or(rev.records(fs, ds, Main.id_of(f), Main.tree.r(fs, Main.id_of(f)), d), recoverable.go(rest, fs, ds, d))

def recoverable(+fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +d: String) -> Bool:
  recoverable.go(fs, fs, ds, d)

# A file whose bytes can be had back; anything else is not asked about here.
def held.recoverable(+fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, h: Held) -> Bool:
  match h:
    case Held.File{+d, r}:
      recoverable(fs, ds, d)
    case _:
      True{}

# Every file a plan writes over, or takes away, holds bytes that can be had
# back from a revision the store holds.
def touched.steps(+fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, steps: List<&2, Decided>) -> Bool:
  match steps:
    case Nil{}:
      True{}
    case Decided{p, w, +h, rs, s} <> rest:
      Bool.and(Bool.or(Bool.not(replaces(s)), held.recoverable(fs, ds, h)), touched.steps(fs, ds, rest))

def touched.gone(+fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, ws: List<&2, Went>) -> Bool:
  match ws:
    case Nil{}:
      True{}
    case Went{p, +h, rs, l} <> rest:
      Bool.and(Bool.or(Bool.not(leaving.remove(l)), held.recoverable(fs, ds, h)), touched.gone(fs, ds, rest))

def touches.recorded(+fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, p: Plan) -> Bool:
  match p:
    case Plan{steps, gone}:
      Bool.and(touched.steps(fs, ds, steps), touched.gone(fs, ds, gone))

# Where an update reaches in the folder: a write, a link or a mode set at a
# path the target's tree holds; and a removal only at a path it does not
# hold, where the walk found a file whose bytes some revision records for
# a file history put at that path — `cat` of that revision reads them for
# it, or its tree names them as its payload — or found a link.
# `LAWS.update_touches_only_the_target` holds every effect to it.
def tree.has(t: Tree.Tree(), +p: String) -> Bool:
  match t:
    case Nil{}:
      False{}
    case e <> rest:
      Bool.or(String.eq(Tree.entry_path(e), p), tree.has(rest, p))

# `cat` of the revision `id` reads these bytes for the file `x`, or its
# tree names them as that file's payload.
def reads.as(+fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +id: String, +x: String, m: Maybe<&2, Tree.Entry>, +d: String) -> Bool:
  match m:
    case Some{Tree.Entry{f, p, Tree.Lines{}, y, g, mo}}:
      records.lines(d, Main.content(fs, ds, id, x))
    case Some{Tree.Entry{f, p, Tree.Whole{}, y, g, mo}}:
      records.payload(d, y)
    case _:
      False{}

def rev.reads.as(+fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +id: String, +x: String, r: Result<&2, &2, Main.Refused, Tree.Tree()>, +d: String) -> Bool:
  match r:
    case Done{t}:
      reads.as(fs, ds, id, x, Tree.lookup(t, x), d)
    case Fail{e}:
      False{}

def revs.read.as(rs: List<&2, Main.Full>, +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +x: String, +d: String) -> Bool:
  match rs:
    case Nil{}:
      False{}
    case +f <> rest:
      Bool.or(rev.reads.as(fs, ds, Main.id_of(f), x, Main.tree.r(fs, Main.id_of(f)), d), revs.read.as(rest, fs, ds, x, d))

def files.read.as(xs: List<&2, String>, +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +d: String) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case +x <> rest:
      Bool.or(revs.read.as(fs, fs, ds, x, d), files.read.as(rest, fs, ds, d))

# Some revision records these bytes for a file some revision put at `p`,
# by an `add` or a `move`.
def recorded.there(+fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +p: String, +d: String) -> Bool:
  files.read.as(files_at(fs, p), fs, ds, d)

# The walk found, at `p`, a file whose bytes — the digest the host gave for
# it — some revision records there, or a link.
def found.recorded(found: List<&2, Folder.Found>, +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +dg: Map<&2, String>, +p: String) -> Bool:
  match found:
    case Nil{}:
      False{}
    case Folder.Found.File{+q, r, n} <> rest:
      Bool.or(Bool.and(String.eq(q, p), recorded.there(fs, ds, p, Main.status.folder_digest(dg, p))), found.recorded(rest, fs, ds, dg, p))
    case Folder.Found.Link{+q, t} <> rest:
      Bool.or(String.eq(q, p), found.recorded(rest, fs, ds, dg, p))

def reaches(+fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +t: Tree.Tree(), +found: List<&2, Folder.Found>, +dg: Map<&2, String>, e: Effect) -> Bool:
  match e:
    case Effect.Write{p, w}:
      tree.has(t, p)
    case Effect.Link{p, x}:
      tree.has(t, p)
    case Effect.Mode{p, w}:
      tree.has(t, p)
    case Effect.Remove{+p}:
      Bool.and(Bool.not(tree.has(t, p)), found.recorded(found, fs, ds, dg, p))

def confined(+fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +t: Tree.Tree(), +found: List<&2, Folder.Found>, +dg: Map<&2, String>, es: List<&2, Effect>) -> Bool:
  match es:
    case Nil{}:
      True{}
    case e <> rest:
      Bool.and(reaches(fs, ds, t, found, dg, e), confined(fs, ds, t, found, dg, rest))

# Whether a step refuses the whole update.
def refuses(s: Step) -> Bool:
  match s:
    case Step.Refuse{b}:
      True{}
    case _:
      False{}

# Whether a path holds the same thing as another reading of it.
def held.same(a: Held, b: Held) -> Bool:
  match a b:
    case Held.File{+d, +r} Held.File{+e, +x}:
      Bool.and(String.eq(d, e), Bool.not(Bool.xor(r, x)))
    case Held.Link{+s} Held.Link{+t}:
      String.eq(s, t)
    case Held.Dir{} Held.Dir{}:
      True{}
    case Held.Unread{} Held.Unread{}:
      True{}
    case Held.Other{} Held.Other{}:
      True{}
    case Held.Nothing{} Held.Nothing{}:
      True{}
    case _ _:
      False{}

# Carrying a plan out would change nothing: every path it steps through
# would hold, after its step, what it held before, and nothing would be
# taken away.
def unchanged.steps(ds: List<&2, Decided>) -> Bool:
  match ds:
    case Nil{}:
      True{}
    case Decided{p, +w, +h, rs, s} <> rest:
      Bool.and(held.same(after(w, h, s), h), unchanged.steps(rest))

def unchanged.gone(ws: List<&2, Went>) -> Bool:
  match ws:
    case Nil{}:
      True{}
    case Went{p, h, rs, l} <> rest:
      Bool.and(Bool.not(leaving.remove(l)), unchanged.gone(rest))

def unchanged(p: Plan) -> Bool:
  match p:
    case Plan{steps, gone}:
      Bool.and(unchanged.steps(steps), unchanged.gone(gone))

# What one path the tree holds with one file wants, and what the folder
# holds there, before it is known whether the digests some revision records
# are needed to decide it.
type Pre is Data:
  Pre{path: String, wants: Wants, held: Held}

def pres(+fs: List<&2, Main.Full>, +oldest: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +located: Map<&2, String>, +id: String, +t: Tree.Tree(), +hm: Map<&2, Maybe<&2, Held>>, +ls: Map<&2, String>, es: List<&2, Tree.Entry>) -> List<&2, Pre>:
  match es:
    case Nil{}:
      Nil{}
    case +e <> rest:
      Pre{Tree.entry_path(e), wants.of(fs, oldest, ds, located, id, t, e), held.of(ls, Tree.entry_path(e), taken(hm, Tree.entry_path(e)))} <> pres(fs, oldest, ds, located, id, t, hm, ls, rest)

# Whether deciding a path asks what history records there: only where the
# folder holds a file that is not already what the target wants.
def asks.file(+w: Wants, h: Held) -> Bool:
  match h:
    case Held.File{d, r}:
      Bool.not(String.eq(d, wants.digest(w)))
    case _:
      False{}

def asks(ps: List<&2, Pre>) -> List<&2, String>:
  match ps:
    case Nil{}:
      Nil{}
    case Pre{+p, +w, h} <> rest:
      Rev.keep(asks.file(w, h), p, asks(rest))

def gone.paths(fs: List<&2, Folder.Found>, +placed: Set()) -> List<&2, String>:
  match fs:
    case Nil{}:
      Nil{}
    case +f <> rest:
      Rev.keep(Bool.not(has(Set.has(placed, Folder.found.path(f)))), Folder.found.path(f), gone.paths(rest, placed))

def recorded.took(r: Map<&2, List<&2, String>> & List<&2, String>) -> List<&2, String>:
  (m, x) = r
  x

def recorded.of(+rec: Map<&2, List<&2, String>>, +p: String) -> List<&2, String>:
  recorded.took(Map.get(List<&2, String>, Nil{}, rec, p))

# What history records at each path asked about, in the order asked.
type Rec is Data:
  Rec{path: String, digests: List<&2, String>}

def recorded.in(rs: List<&2, Rec>, +p: String) -> List<&2, String>:
  match rs:
    case Nil{}:
      Nil{}
    case Rec{+q, ds} <> rest:
      Bool.pick(List<&2, String>, String.eq(q, p), ds, recorded.in(rest, p))

def looks(ps: List<&2, Pre>, +rec: List<&2, Rec>) -> List<&2, Look>:
  match ps:
    case Nil{}:
      Nil{}
    case Pre{+p, w, h} <> rest:
      Look{p, w, h, recorded.in(rec, p)} <> looks(rest, rec)

def gone.held(h: Maybe<&2, Held>) -> Held:
  match h:
    case Some{x}:
      x
    case None{}:
      Held.Nothing{}

def is_link(h: Maybe<&2, Held>) -> Bool:
  match h:
    case Some{Held.Link{t}}:
      True{}
    case _:
      False{}

# A file is asked after by its digest, and a link by its spelling.
def gone.recorded(h: Held, digests: List<&2, String>, spellings: List<&2, String>) -> List<&2, String>:
  match h:
    case Held.File{d, r}:
      digests
    case Held.Link{t}:
      spellings
    case _:
      Nil{}

def gones(ps: List<&2, String>, +hm: Map<&2, Maybe<&2, Held>>, +rec: List<&2, Rec>, +links: Map<&2, List<&2, String>>, +tracked: Set()) -> List<&2, Gone>:
  match ps:
    case Nil{}:
      Nil{}
    case +p <> rest:
      +h = gone.held(taken(hm, p))
      Gone{p, h, gone.recorded(h, recorded.in(rec, p), recorded.of(links, p)), has(Set.has(tracked, p))} <> gones(rest, hm, rec, links, tracked)

def gone.links(ps: List<&2, String>, +hm: Map<&2, Maybe<&2, Held>>) -> List<&2, String>:
  match ps:
    case Nil{}:
      Nil{}
    case +p <> rest:
      Rev.keep(is_link(taken(hm, p)), p, gone.links(rest, hm))

def recorded.list(ps: List<&2, String>, +fs: List<&2, Main.Full>, +oldest: List<&2, Main.Full>, +ds: List<&2, Store.Doc>) -> List<&2, Rec>:
  match ps:
    case Nil{}:
      Nil{}
    case +p <> rest:
      Rec{p, recorded(fs, oldest, ds, p)} <> recorded.list(rest, fs, oldest, ds)

def spelled.map(ps: List<&2, String>, +fs: List<&2, Main.Full>, m: Map<&2, List<&2, String>>) -> Map<&2, List<&2, String>>:
  match ps:
    case Nil{}:
      m
    case +p <> rest:
      spelled.map(rest, fs, Map.set(&2, List<&2, String>, m, p, spelled(fs, p)))

# Where the store has each payload, as a path; nothing for one it does not.
def located.at(+root: String, +a: String) -> String:
  Bool.pick(String, Bool.or(String.is_empty(a), String.eq(a, "-")), SNil{}, root ++ "/" ++ a)

def located.map(+root: String, ds: List<&2, String>, at: List<&2, String>, m: Map<&2, String>) -> Map<&2, String>:
  match ds at:
    case d <> rest +a <> more:
      located.map(root, rest, more, Map.set(&2, String, m, d, located.at(root, a)))
    case _ _:
      m

def payloads(es: List<&2, Tree.Entry>) -> List<&2, String>:
  match es:
    case Nil{}:
      Nil{}
    case Tree.Entry{f, p, Tree.Whole{}, Some{d}, g, m} <> rest:
      d <> payloads(rest)
    case e <> rest:
      payloads(rest)

def lined(es: List<&2, Tree.Entry>) -> List<&2, String>:
  match es:
    case Nil{}:
      Nil{}
    case Tree.Entry{f, p, Tree.Lines{}, y, g, m} <> rest:
      f <> lined(rest)
    case e <> rest:
      lined(rest)

def regular(fs: List<&2, Folder.Found>) -> List<&2, String>:
  match fs:
    case Nil{}:
      Nil{}
    case Folder.Found.File{p, r, n} <> rest:
      p <> regular(rest)
    case f <> rest:
      regular(rest)

def wanted_all(+fs: List<&2, Main.Full>, xs: List<&2, String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case +x <> rest:
      List.append(&2, String, Main.wanted(fs, x), wanted_all(fs, rest))

def files_all(+fs: List<&2, Main.Full>, ps: List<&2, String>) -> List<&2, String>:
  match ps:
    case Nil{}:
      Nil{}
    case +p <> rest:
      List.append(&2, String, files_at(fs, p), files_all(fs, rest))

def tracked.of(r: Result<&2, &2, Main.Refused, Tree.Tree()>) -> List<&2, String>:
  match r:
    case Done{t}:
      T.map(~Tree.Entry, ~String, ~(e => Tree.entry_path(e)), t)
    case Fail{e}:
      Nil{}

# Every path a current head holds: a file the folder has at one of them and
# the target does not is said to be left, where it is not removed.
def tracked(+fs: List<&2, Main.Full>, hs: List<&2, String>) -> List<&2, String>:
  match hs:
    case Nil{}:
      Nil{}
    case +h <> rest:
      List.append(&2, String, tracked.of(Main.tree.r(fs, h)), tracked(fs, rest))

# Every document the contents asked for name, and every document the
# resolutions among those keep items of.
def fetched(+root: String, digests: List<&2, String>) -> IO(List<&2, Store.Doc>):
  do IO<List<&2, Store.Doc>>:
    ds : List<&2, Store.Doc> <- Store.fetch(root, Main.sorted_distinct(digests))
    +ds2 : List<&2, Store.Doc> = ds
    more : List<&2, Store.Doc> <- Store.fetch(root, Main.kept_digests(ds2))
    return List.append(&2, Store.Doc, ds2, more)

# What the plan is decided from, before history is asked: the tree by
# path, what the folder holds at each (the walk, `found`, with the host's
# digest of each file in `dg`, and a directory's listing where the walk
# took nothing, `ls`), what each path of the tree wants — its content from
# the documents `ds`, a payload where the store has it (`located`) — and
# the paths the walk took that the tree does not hold.
type Planning is Data:
  Planning{placings: List<&2, Placing>, held: Map<&2, Maybe<&2, Held>>, pres: List<&2, Pre>, gone: List<&2, String>}

def planning(+fs: List<&2, Main.Full>, +id: String, +t: Tree.Tree(), +found: List<&2, Folder.Found>, +dg: Map<&2, String>, +ls: Map<&2, String>, +located: Map<&2, String>, +ds: List<&2, Store.Doc>) -> Planning:
  +pls = placings(t)
  +hm = found.map(found, dg, Map.new(&2, Maybe<&2, Held>))
  Planning{pls, hm, pres(fs, List.reverse(&2, Main.Full, Main.presentation(fs)), ds, located, id, t, hm, ls, single(pls)), gone.paths(found, Set.from_list(T.map(~Placing, ~String, ~(p => placing.path(p)), pls)))}

# Where history has to be asked what it records: each path of the tree
# where the folder's bytes are not the target's, and each path the target
# does not hold.
def planning.asked(pl: Planning) -> List<&2, String>:
  match pl:
    case Planning{pls, hm, +ps, +gp}:
      List.append(&2, String, asks(ps), gp)

# The plan, from that and from what history records: what the documents
# fetched for it (`more`, beside `ds`) say each revision holds at each path
# asked about, the links revisions stated there, and which paths a current
# head tracks; `rs` are the rules of `skipped/` and `walked` what the walk
# refused. Pure: what `update.at` asks the host for, it hands in.
def plan.with(pl: Planning, +fs: List<&2, Main.Full>, +rs: List<&2, Folder.Scope>, +walked: List<&2, T.Split>, +ds: List<&2, Store.Doc>, +more: List<&2, Store.Doc>) -> Result<&2, &2, List<&2, T.Split>, Plan>:
  match pl:
    case Planning{+pls, +hm, +ps, +gp}:
      +rec = recorded.list(List.append(&2, String, asks(ps), gp), fs, List.reverse(&2, Main.Full, Main.presentation(fs)), List.append(&2, Store.Doc, ds, more))
      plan(refuse.tree(Set.from_list(dirs(pls)), rs, walked, pls), looks(ps, rec), gones(gp, hm, rec, spelled.map(gone.links(gp, hm), fs, Map.new(&2, List<&2, String>)), Set.from_list(tracked(fs, heads.sorted(fs)))))

# Everything `update` decides, from what it read.
def plan.from(+fs: List<&2, Main.Full>, +id: String, +t: Tree.Tree(), +rs: List<&2, Folder.Scope>, +walked: List<&2, T.Split>, +found: List<&2, Folder.Found>, +dg: Map<&2, String>, +ls: Map<&2, String>, +located: Map<&2, String>, +ds: List<&2, Store.Doc>, +more: List<&2, Store.Doc>) -> Result<&2, &2, List<&2, T.Split>, Plan>:
  plan.with(planning(fs, id, t, found, dg, ls, located, ds), fs, rs, walked, ds, more)

def update.at(+r: String, +fs: List<&2, Main.Full>, +bs: List<&2, Bm.Bookmark>, +id: String, +dry: Bool) -> IO(Unit):
  +repo = Main.repository(r)
  +spelled = spelled.id(fs, bs, id)
  do IO<Unit>:
    rules : List<&2, Folder.Scope> <- Folder.rules(r)
    +rs : List<&2, Folder.Scope> = rules
    w : Folder.Walked <- Folder.walk.all(repo, rs)
    +w2 : Folder.Walked = w
    Main.refused.io(Unit, head.r(fs, bs, id))
    t : Tree.Tree() <- Main.refused.io(Tree.Tree(), Main.tree.r(fs, id))
    +t2 : Tree.Tree() = t
    +found : List<&2, Folder.Found> = Folder.walked.found(w2)
    +files : List<&2, String> = regular(found)
    +walked : List<&2, String> = Main.found_paths(found)
    disk : List<&2, String> <- Folder.on_disk.all(repo, walked)
    +dm : Map<&2, String> = Main.stats.map(walked, disk, Map.new(&2, String))
    stats : List<&2, String> <- Store.stats(repo, spelt.all(dm, files))
    +dg : Map<&2, String> = Main.stats.map(files, stats, Map.new(&2, String))
    +one : List<&2, Tree.Entry> = single(placings(t2))
    ls : Map<&2, String> <- listings(repo, Main.sorted_distinct(untaken(found.map(found, dg, Map.new(&2, Maybe<&2, Held>)), one)), Map.new(&2, String))
    +ls2 : Map<&2, String> = ls
    +pay : List<&2, String> = Main.sorted_distinct(payloads(one))
    at : List<&2, String> <- Store.located(r, pay)
    +located : Map<&2, String> = located.map(r, pay, at, Map.new(&2, String))
    ds : List<&2, Store.Doc> <- fetched(r, wanted_all(fs, lined(one)))
    +ds2 : List<&2, Store.Doc> = ds
    +pl : Planning = planning(fs, id, t2, found, dg, ls2, located, ds2)
    more : List<&2, Store.Doc> <- fetched(r, wanted_all(fs, Main.sorted_distinct(files_all(fs, planning.asked(pl)))))
    p : Plan <- Main.refused.io(Plan, planned.r(plan.with(pl, fs, rs, Folder.walked.refused(w2), ds2, more)))
    done.plan(repo, dm, spelled, dry, p)

def update.of(+r: String, +fs: List<&2, Main.Full>, +bs: List<&2, Bm.Bookmark>, c: UpdateCmd) -> IO(Unit):
  match c:
    case UpdateCmd{t, +dry}:
      do IO<Unit>:
        id : String <- Main.refused.io(String, target.r(fs, bs, t))
        update.at(r, fs, bs, id, dry)

# `update [<target>] [-n|--dry-run]`: the store is found before the words
# are read, as the Rust tool finds it, and opened after.
def update(+args: List<&2, String>) -> IO(Unit):
  do IO<Unit>:
    root : String <- Store.root()
    +r : String = root
    c : UpdateCmd <- Main.refused.io(UpdateCmd, args.r(args))
    rs : List<&2, Store.Doc> <- Store.revisions(r)
    bs : List<&2, Bm.Bookmark> <- Main.bookmarks(r)
    update.of(r, Main.fulls(r, rs), bs, c)
