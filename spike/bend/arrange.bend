# `arrange [-n|--dry-run] [--refile]`: the names decision 0006 made
# deterministic, given to the files a store already holds.
#
# A revision is named by its month, its day and the first line of its
# message, with a change's first letters or its own digest's where two
# would meet — `naming::stems` over the whole store — and each file of
# content is filed under the stem of the revision that names it, at the
# path it had there. Nothing's bytes change, so no identity moves: this is
# renaming and nothing else. A revision is renamed where it sits, since a
# folder a person put one in is one they meant; `--refile` files it under
# its month instead, which is how a store written flat catches up.
#
# What is decided here is decided before anything moves, in the order the
# Rust tool walks the store — by path, a component at a time — and a dry run
# prints the plan the real run acts on. Acting, each rename asks once more
# whether its new name is free, since two files holding one document want
# one name and only the first gets it.

import Base
import ./text.bend as T
import ./revision.bend as Rev
import ./store.bend as Store
import ./tree.bend as Tree
import ./naming.bend as Naming
import ./bookmark.bend as Bm
import ./commands.bend as Main

# The words
# ---------

# What `arrange` was asked: to plan rather than act, and to refile.
type ArrangeCmd is Data:
  ArrangeCmd{dry: Bool, refile: Bool}

def is_dry(+w: String) -> Bool:
  Bool.or(String.eq(w, "-n"), String.eq(w, "--dry-run"))

def is_refile(+w: String) -> Bool:
  String.eq(w, "--refile")

# A word `arrange` knows.
def is_flag(+w: String) -> Bool:
  Bool.or(is_dry(w), is_refile(w))

def any_dry(ws: List<&2, String>) -> Bool:
  match ws:
    case Nil{}:
      False{}
    case +w <> rest:
      Bool.or(is_dry(w), any_dry(rest))

def any_refile(ws: List<&2, String>) -> Bool:
  match ws:
    case Nil{}:
      False{}
    case +w <> rest:
      Bool.or(is_refile(w), any_refile(rest))

# The first word that is not a flag, which the Rust tool names in refusing.
def first_other(ws: List<&2, String>) -> Maybe<&2, String>:
  match ws:
    case Nil{}:
      None{}
    case +w <> rest:
      Bool.pick(Maybe<&2, String>, is_flag(w), first_other(rest), Some{w})

def args.of(+dry: Bool, +refile: Bool, extra: Maybe<&2, String>) -> Result<&2, &2, Main.Refused, ArrangeCmd>:
  match extra:
    case Some{x}:
      Fail{Main.Refused{2, "`arrange` takes no arguments, and `" ++ x ++ "` is one"}}
    case None{}:
      Done{ArrangeCmd{dry, refile}}

# Every flag wherever it stands, and any other word refused.
def args.r(+ws: List<&2, String>) -> Result<&2, &2, Main.Refused, ArrangeCmd>:
  args.of(any_dry(ws), any_refile(ws), first_other(ws))

# Every word a flag, which is what `args.r` accepting a command line says.
def all_flags(ws: List<&2, String>) -> Bool:
  match ws:
    case Nil{}:
      True{}
    case +w <> rest:
      Bool.and(is_flag(w), all_flags(rest))

# The store, as the Rust tool opens it
# -----------------------------------

# A path as a key that sorts the way the Rust tool's walk does: by
# component, so `a/b` comes before `a b` — a separator sorting below every
# character a name can hold, which `\0` is and `/` is not.
def walk_key(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, rest}:
      SCon{Bool.pick(Char, Char.is_eq(c, '/'), Char.from_u32(0), c), walk_key(rest)}

def walk_le(+a: String, +b: String) -> Bool:
  String.is_le(walk_key(a), walk_key(b))

def walked(+ps: List<&2, String>) -> List<&2, String>:
  List.sort(~String, ~(a => b => walk_le(a, b)), ps)

def claims_revision(+p: String) -> Bool:
  String.ends_with(p, ".rev.txt")

def claims_operation(+p: String) -> Bool:
  String.ends_with(p, ".ops.txt")

# The revision documents of `revisions/`: the files there claiming to be
# one, as the Rust tool's loader reads it.
def revision_docs(ds: List<&2, Store.Doc>) -> List<&2, Store.Doc>:
  match ds:
    case Nil{}:
      Nil{}
    case +d <> rest:
      Tree.keep(~Store.Doc, claims_revision(Store.path_of(d)), d, revision_docs(rest))

def doc_le(+a: Store.Doc, +b: Store.Doc) -> Bool:
  walk_le(Store.path_of(a), Store.path_of(b))

def parse_fault(+path: String, r: Result<&2, &2, String, Rev.Rev>) -> Maybe<&2, Main.Refused>:
  match r:
    case Fail{e}:
      Some{Main.Refused{1, path ++ ": " ++ e}}
    case Done{x}:
      None{}

def first_fault(ds: List<&2, Store.Doc>) -> Maybe<&2, Main.Refused>:
  match ds:
    case Nil{}:
      None{}
    case Store.Doc{+path, id, size, +text} <> rest:
      Maybe.or(&2, Main.Refused, parse_fault(path, Rev.parse(text)), first_fault(rest))

def opened.of(found: Maybe<&2, Main.Refused>) -> Result<&2, &2, Main.Refused, Unit>:
  match found:
    case Some{r}:
      Fail{r}
    case None{}:
      Done{Unit{}}

# The Rust tool refuses to open a store with a revision document that does
# not parse, naming the first in its walk — `ds` is in the walk's order —
# where the other commands here pass it over.
def opened.r(ds: List<&2, Store.Doc>) -> Result<&2, &2, Main.Refused, Unit>:
  opened.of(first_fault(revision_docs(ds)))

def parses(d: Store.Doc) -> Bool:
  match d:
    case Store.Doc{path, id, size, text}:
      Bool.not(Main.rev.fails(Rev.parse(text)))

def all_parse(ds: List<&2, Store.Doc>) -> Bool:
  match ds:
    case Nil{}:
      True{}
    case +d <> rest:
      Bool.and(parses(d), all_parse(rest))

def dedup(fs: List<&2, Main.Full>, +prev: String) -> List<&2, Main.Full>:
  match fs:
    case Nil{}:
      Nil{}
    case +f <> rest:
      Main.keep_full(Bool.not(String.eq(Main.id_of(f), prev)), f, dedup(rest, Main.id_of(f)))

def full_le(+a: Main.Full, +b: Main.Full) -> Bool:
  String.is_le(Main.id_of(a), Main.id_of(b))

# Each revision once, however many files hold it: two copies of one
# document are one revision, which is what the Rust tool's map by digest
# makes of them.
def distinct(+fs: List<&2, Main.Full>) -> List<&2, Main.Full>:
  dedup(List.sort(~Main.Full, ~(a => b => full_le(a, b)), fs), SNil{})

# Stems
# -----

def base_of(f: Main.Full) -> String:
  match f:
    case Main.Full{id, +change, parents, supersedes, author, +when, revised_by, revised, facts, +message}:
      Naming.compose(when, message, change)

def named_of(f: Main.Full) -> String:
  match f:
    case Main.Full{id, +change, parents, supersedes, author, +when, revised_by, revised, facts, +message}:
      Naming.compose(when, message, change) ++ " " ++ String.take(change, Naming.CHANGE_CHARS())

# The three tiers: the base where no other revision has it, the change's
# first letters where no other of those does, and the digest's too.
def stem.tier(+base: String, +named: String, +id: String, +bases: Nat, +nameds: Nat) -> String:
  Bool.pick(String, Nat.is_le(bases, 1n), base,
    Bool.pick(String, Nat.is_le(nameds, 1n), named, named ++ " " ++ String.take(id, Naming.DIGEST_CHARS())))

def stems.go(fs: List<&2, Main.Full>, +bases: List<&2, String>, +nameds: List<&2, String>) -> List<&2, T.Split>:
  match fs:
    case Nil{}:
      Nil{}
    case +f <> rest:
      +b = base_of(f)
      +n = named_of(f)
      T.Split{Main.id_of(f), stem.tier(b, n, Main.id_of(f), Naming.count(bases, b), Naming.count(nameds, n))} <> stems.go(rest, bases, nameds)

# `naming::stems`: what every revision is filed under, by digest, over the
# revisions given — each once.
def stems(+fs: List<&2, Main.Full>) -> List<&2, T.Split>:
  stems.go(fs, T.map(~Main.Full, ~String, ~(f => base_of(f)), fs), T.map(~Main.Full, ~String, ~(f => named_of(f)), fs))

def lookup(ss: List<&2, T.Split>, +key: String) -> Maybe<&2, String>:
  match ss:
    case Nil{}:
      None{}
    case T.Split{+k, +v} <> rest:
      Bool.pick(Maybe<&2, String>, String.eq(k, key), Some{v}, lookup(rest, key))

# The filename half of a stem: a rename in place keeps the directory.
def leaf(+stem: String) -> String:
  Naming.last(stem)

# Content
# -------

# One revision's claim on a file of content: the digest it names, itself,
# the path the file had there, and whether it is an operation document.
type Claim is Data:
  Claim{held: String, rev: String, path: String, doc: Bool}

def claim.held(c: Claim) -> String:
  match c:
    case Claim{held, r, p, d}:
      held

def cmp.then(c: Cmp, next: Bool) -> Bool:
  match c:
    case LT{}:
      True{}
    case EQ{}:
      next
    case GT{}:
      False{}

def bool.le(a: Bool, b: Bool) -> Bool:
  match a:
    case False{}:
      True{}
    case True{}:
      b

# By digest, then by the smallest revision, then by path, then a payload
# before a document: the claim that wins is the first of its digest.
def claim.le(a: Claim, b: Claim) -> Bool:
  match a b:
    case Claim{+h1, +r1, +p1, d1} Claim{+h2, +r2, +p2, d2}:
      cmp.then(String.order(h1, h2), cmp.then(String.order(r1, r2), cmp.then(String.order(p1, p2), bool.le(d1, d2))))

def claim.push(+rev: String, +held: String, path: Maybe<&2, String>, doc: Bool, rest: List<&2, Claim>) -> List<&2, Claim>:
  match path:
    case None{}:
      rest
    case Some{p}:
      Claim{held, rev, p, doc} <> rest

# Each file a revision names content for, at the path its tree gives it or
# the one it was added at.
def claims.of(fs: List<&2, Tree.Fact>, +rev: String, +t: Tree.Tree(), +adds: List<&2, Tree.Fact>, +doc: Bool) -> List<&2, Claim>:
  match fs:
    case Nil{}:
      Nil{}
    case Tree.Fact{+file, +held} <> rest:
      claim.push(rev, held, Maybe.or(&2, String, Tree.path(t, file), Tree.stated(adds, file)), doc, claims.of(rest, rev, t, adds, doc))

def names_content(+hs: List<&2, Rev.Header>) -> Bool:
  Bool.not(Bool.and(Bool.and(List.is_empty(&2, Tree.Fact, Tree.facts_of(hs, "edit")), List.is_empty(&2, Tree.Fact, Tree.facts_of(hs, "text"))), List.is_empty(&2, Tree.Fact, Tree.facts_of(hs, "bytes"))))

def claims.rev(+id: String, +hs: List<&2, Rev.Header>, t: Result<&2, &2, Main.Refused, Tree.Tree()>) -> Result<&2, &2, Main.Refused, List<&2, Claim>>:
  match t:
    case Fail{e}:
      Fail{e}
    case Done{+tree}:
      +adds = Tree.facts_of(hs, "add")
      Done{List.append(&2, Claim, claims.of(Tree.facts_of(hs, "edit"), id, tree, adds, True{}), List.append(&2, Claim, claims.of(Tree.facts_of(hs, "text"), id, tree, adds, False{}), claims.of(Tree.facts_of(hs, "bytes"), id, tree, adds, False{})))}

def claims.join(a: Result<&2, &2, Main.Refused, List<&2, Claim>>, b: Result<&2, &2, Main.Refused, List<&2, Claim>>) -> Result<&2, &2, Main.Refused, List<&2, Claim>>:
  match a b:
    case Fail{e} _:
      Fail{e}
    case Done{x} Fail{e}:
      Fail{e}
    case Done{x} Done{y}:
      Done{List.append(&2, Claim, x, y)}

# Every claim every revision makes, its tree materialised to find the
# paths; a tree that does not materialise refuses the whole arranging.
def claims.all(us: List<&2, Main.Full>, +fs: List<&2, Main.Full>) -> Result<&2, &2, Main.Refused, List<&2, Claim>>:
  match us:
    case Nil{}:
      Done{Nil{}}
    case +f <> rest:
      +hs = Main.facts_of(f)
      +id = Main.id_of(f)
      claims.join(Bool.pick(Result<&2, &2, Main.Refused, List<&2, Claim>>, names_content(hs), claims.rev(id, hs, Main.tree.r(fs, id)), Done{Nil{}}), claims.all(rest, fs))

# The first claim of each digest, in a list sorted by `claim.le`.
def firsts(cs: List<&2, Claim>, +prev: String) -> List<&2, Claim>:
  match cs:
    case Nil{}:
      Nil{}
    case +c <> rest:
      Tree.keep(~Claim, Bool.not(String.eq(claim.held(c), prev)), c, firsts(rest, claim.held(c)))

# A winning claim with the stem of the revision it names: where it is filed.
type Stemmed is Data:
  Stemmed{stem: String, filing: Naming.Filing}

def stemmed.push(found: Maybe<&2, String>, c: Claim, rest: List<&2, Stemmed>) -> List<&2, Stemmed>:
  match found c:
    case None{} _:
      rest
    case Some{s} Claim{h, r, p, d}:
      Stemmed{s, Naming.Filing{h, p, d}} <> rest

def stemmed.all(cs: List<&2, Claim>, +ss: List<&2, T.Split>) -> List<&2, Stemmed>:
  match cs:
    case Nil{}:
      Nil{}
    case Claim{+h, +r, +p, +d} <> rest:
      stemmed.push(lookup(ss, r), Claim{h, r, p, d}, stemmed.all(rest, ss))

def stemmed.stem(s: Stemmed) -> String:
  match s:
    case Stemmed{stem, f}:
      stem

def under_stem(xs: List<&2, Stemmed>, +stem: String) -> List<&2, Naming.Filing>:
  match xs:
    case Nil{}:
      Nil{}
    case Stemmed{+s, +f} <> rest:
      Tree.keep(~Naming.Filing, String.eq(s, stem), f, under_stem(rest, stem))

def prefixed(ns: List<&2, T.Split>, +stem: String) -> List<&2, T.Split>:
  match ns:
    case Nil{}:
      Nil{}
    case T.Split{h, n} <> rest:
      T.Split{h, stem ++ "/" ++ n} <> prefixed(rest, stem)

def filed.each(stems: List<&2, String>, +xs: List<&2, Stemmed>) -> List<&2, T.Split>:
  match stems:
    case Nil{}:
      Nil{}
    case +s <> rest:
      List.append(&2, T.Split, prefixed(Naming.filed(under_stem(xs, s)), s), filed.each(rest, xs))

# `operation_names`: where each file of content belongs, by digest — the
# stem of the revision whose claim wins, then the path, filed as `naming`
# files one revision's content, so what `arrange` makes of a store is what
# `record` would have written into it.
def operation_names(+fs: List<&2, Main.Full>, +ss: List<&2, T.Split>) -> Result<&2, &2, Main.Refused, List<&2, T.Split>>:
  do Result<&2, &2, Main.Refused, List<&2, T.Split>>:
    cs : List<&2, Claim> <- claims.all(distinct(fs), fs)
    +won : List<&2, Stemmed> = stemmed.all(firsts(List.sort(~Claim, ~(a => b => claim.le(a, b)), cs), SNil{}), ss)
    return filed.each(Main.sorted_distinct(T.map(~Stemmed, ~String, ~(x => stemmed.stem(x)), won)), won)

# The plan
# --------

# What becomes of one file: moved to its name, already at it, left because
# the name is taken, or — in `operations/` — named by no revision.
type Placing is Data:
  Placing.Rename{from: String, to: String}
  Placing.Already{path: String}
  Placing.Occupied{path: String, holder: String}
  Placing.Unnamed{path: String}

def found(p: Set() & Bool) -> Bool:
  (s, b) = p
  b

def has(+s: Set(), +key: String) -> Bool:
  found(Set.has(s, key))

# Every path the store holds, and every directory those sit in: whatever
# is there, as the Rust tool's `look` asks before it plans a rename.
def taken(+ls: List<&2, String>) -> Set():
  Set.from_list(List.append(&2, String, ls, List.concat(&2, String, T.map(~String, ~List<&2, String>, ~(n => Naming.prefixes(n)), ls))))

def place(+taken: Set(), +path: String, +target: String) -> Placing:
  Bool.pick(Placing, String.eq(path, target), Placing.Already{path},
    Bool.pick(Placing, has(taken, target), Placing.Occupied{path, target}, Placing.Rename{path, target}))

# Where a revision document goes: under its month where it is refiled, and
# otherwise beside where it is, under the stem's filename half.
def rev.target(refile: Bool, +path: String, +stem: String) -> String:
  match refile:
    case True{}:
      "revisions/" ++ stem ++ ".rev.txt"
    case False{}:
      String.append(Naming.head(path), leaf(stem) ++ ".rev.txt")

def rev.placed(+refile: Bool, +taken: Set(), +path: String, stem: Maybe<&2, String>) -> Result<&2, &2, Main.Refused, Placing>:
  match stem:
    case None{}:
      Fail{Main.Refused{1, path ++ " changed while it was being arranged"}}
    case Some{+s}:
      Done{place(taken, path, rev.target(refile, path, s))}

def placed.cons(p: Result<&2, &2, Main.Refused, Placing>, rest: Result<&2, &2, Main.Refused, List<&2, Placing>>) -> Result<&2, &2, Main.Refused, List<&2, Placing>>:
  match p rest:
    case Fail{e} _:
      Fail{e}
    case Done{x} Fail{e}:
      Fail{e}
    case Done{x} Done{xs}:
      Done{x <> xs}

# Each revision document, in the walk's order, with its digest.
def revs.placed(ds: List<&2, T.Split>, +refile: Bool, +taken: Set(), +ss: List<&2, T.Split>) -> Result<&2, &2, Main.Refused, List<&2, Placing>>:
  match ds:
    case Nil{}:
      Done{Nil{}}
    case T.Split{+path, +id} <> rest:
      placed.cons(rev.placed(refile, taken, path, lookup(ss, id)), revs.placed(rest, refile, taken, ss))

def op.placed(+taken: Set(), +path: String, name: Maybe<&2, String>) -> Placing:
  match name:
    case None{}:
      Placing.Unnamed{path}
    case Some{n}:
      place(taken, path, "operations/" ++ n)

# Each file of `operations/`, in the walk's order, with its digest.
def ops.placed(ds: List<&2, T.Split>, +taken: Set(), +names: List<&2, T.Split>) -> List<&2, Placing>:
  match ds:
    case Nil{}:
      Nil{}
    case T.Split{+path, +id} <> rest:
      op.placed(taken, path, lookup(names, id)) <> ops.placed(rest, taken, names)

# What arranging will do, in the two directories, before anything moves.
type Arrangement is Data:
  Arrangement{revs: List<&2, Placing>, ops: List<&2, Placing>}

def arrangement.revs(a: Arrangement) -> List<&2, Placing>:
  match a:
    case Arrangement{revs, ops}:
      revs

def arrangement.placed(+held: Set(), +ops: List<&2, T.Split>, +names: List<&2, T.Split>, rp: Result<&2, &2, Main.Refused, List<&2, Placing>>) -> Result<&2, &2, Main.Refused, Arrangement>:
  match rp:
    case Fail{e}:
      Fail{e}
    case Done{ps}:
      Done{Arrangement{ps, ops.placed(ops, held, names)}}

def arrangement.named(+refile: Bool, +held: Set(), +ss: List<&2, T.Split>, +revs: List<&2, T.Split>, +ops: List<&2, T.Split>, names: Result<&2, &2, Main.Refused, List<&2, T.Split>>) -> Result<&2, &2, Main.Refused, Arrangement>:
  match names:
    case Fail{e}:
      Fail{e}
    case Done{+ns}:
      arrangement.placed(held, ops, ns, revs.placed(revs, refile, held, ss))

def arrangement.stemmed(+refile: Bool, +held: Set(), +ss: List<&2, T.Split>, +fs: List<&2, Main.Full>, +revs: List<&2, T.Split>, +ops: List<&2, T.Split>) -> Result<&2, &2, Main.Refused, Arrangement>:
  arrangement.named(refile, held, ss, revs, ops, operation_names(fs, ss))

# `Store::arrangement`: `revs` and `ops` are each directory's files, a path
# and its digest, in the walk's order; `ls` is every path the two hold.
# The names of content are worked out first, as the Rust tool works them,
# so a tree that will not materialise is the refusal a store gets first.
def arrangement.r(+refile: Bool, +fs: List<&2, Main.Full>, +revs: List<&2, T.Split>, +ops: List<&2, T.Split>, +ls: List<&2, String>) -> Result<&2, &2, Main.Refused, Arrangement>:
  arrangement.stemmed(refile, taken(ls), stems(distinct(fs)), fs, revs, ops)

# Every rename a plan holds goes from one path to another that nothing was
# at: arranging never plans to write over a file.
def rename_safe(+held: Set(), p: Placing) -> Bool:
  match p:
    case Placing.Rename{+from, +to}:
      Bool.and(Bool.not(String.eq(from, to)), Bool.not(has(held, to)))
    case _:
      True{}

def renames_safe(ps: List<&2, Placing>, +held: Set()) -> Bool:
  match ps:
    case Nil{}:
      True{}
    case +p <> rest:
      Bool.and(rename_safe(held, p), renames_safe(rest, held))

# A rename that keeps a revision in the directory it sits in.
def in_place(p: Placing) -> Bool:
  match p:
    case Placing.Rename{+from, +to}:
      String.starts_with(to, Naming.head(from))
    case _:
      True{}

def all_in_place(ps: List<&2, Placing>) -> Bool:
  match ps:
    case Nil{}:
      True{}
    case +p <> rest:
      Bool.and(in_place(p), all_in_place(rest))

def plan_safe(+held: Set(), a: Arrangement) -> Bool:
  match a:
    case Arrangement{+revs, +ops}:
      Bool.and(renames_safe(revs, held), renames_safe(ops, held))

# Acting
# ------

# What happened to one directory's files: the renames done, in order; the
# files already named; those left, planned or found taken, in that order;
# and the files no revision names.
type Came is Data:
  Came{renamed: List<&2, T.Split>, already: Nat, occupied: List<&2, T.Split>, unnamed: Nat}

def done.renamed(ps: List<&2, Placing>) -> List<&2, T.Split>:
  match ps:
    case Nil{}:
      Nil{}
    case Placing.Rename{f, t} <> rest:
      T.Split{f, t} <> done.renamed(rest)
    case p <> rest:
      done.renamed(rest)

def done.occupied(ps: List<&2, Placing>) -> List<&2, T.Split>:
  match ps:
    case Nil{}:
      Nil{}
    case Placing.Occupied{f, h} <> rest:
      T.Split{f, h} <> done.occupied(rest)
    case p <> rest:
      done.occupied(rest)

def done.already(ps: List<&2, Placing>) -> Nat:
  match ps:
    case Nil{}:
      0n
    case Placing.Already{f} <> rest:
      1n+done.already(rest)
    case p <> rest:
      done.already(rest)

def done.unnamed(ps: List<&2, Placing>) -> Nat:
  match ps:
    case Nil{}:
      0n
    case Placing.Unnamed{f} <> rest:
      1n+done.unnamed(rest)
    case p <> rest:
      done.unnamed(rest)

# The plan, as a dry run reports it: every rename as planned.
def planned(+ps: List<&2, Placing>) -> Came:
  Came{done.renamed(ps), done.already(ps), done.occupied(ps), done.unnamed(ps)}

# How many files one directory's report counts: renamed, already arranged,
# left, and named by no revision.
def tally(c: Came) -> Nat:
  match c:
    case Came{rs, a, os, u}:
      Nat.add(List.length(&2, T.Split, rs), Nat.add(a, Nat.add(List.length(&2, T.Split, os), u)))

def arrangement.ops(a: Arrangement) -> List<&2, Placing>:
  match a:
    case Arrangement{revs, ops}:
      ops

# Whether a plan's report counts each file of each directory once.
def accounted(+a: Arrangement, +revs: List<&2, T.Split>, +ops: List<&2, T.Split>) -> Bool:
  Bool.and(Nat.is_eq(tally(planned(arrangement.revs(a))), List.length(&2, T.Split, revs)), Nat.is_eq(tally(planned(arrangement.ops(a))), List.length(&2, T.Split, ops)))

# What a rename the host was asked for came to: `moved` is a rename done,
# and a new name already there — `both`, or `there` where the old is gone
# too — is a file left, as the Rust tool leaves it when its second look
# finds the name taken.
type Moved is Data:
  Moved.Renamed{}
  Moved.Left{}
  Moved.Failed{msg: String}

def moved.of(r: Result<&1, &1, U32 & String, String>) -> Moved:
  match r:
    case Fail{Tuple{code, msg}}:
      Moved.Failed{msg}
    case Done{"moved"}:
      Moved.Renamed{}
    case Done{"neither"}:
      Moved.Failed{"nothing is at the path being arranged"}
    case Done{other}:
      Moved.Left{}

def parent_of(+p: String) -> String:
  +h = Naming.head(p)
  String.take(h, Nat.sub(String.length(h), 1n))

# One rename, carried out: moved, then the directories it emptied tidied up
# to the store's own; or left where the name has filled since the plan.
def act.one(+root: String, +dir: String, +from: String, +to: String, m: Moved) -> IO(Maybe<&2, Bool>):
  match m:
    case Moved.Renamed{}:
      do IO<Maybe<&2, Bool>>:
        t : Result<&1, &1, U32 & String, String> <- Store.tidied(root ++ "/" ++ dir ++ "\n" ++ root ++ "/" ++ parent_of(from))
        return Some{True{}}
    case Moved.Left{}:
      IO.pure(Maybe<&2, Bool>, Some{False{}})
    case Moved.Failed{msg}:
      Main.die(Maybe<&2, Bool>, 1, msg)

def act.push(did: Maybe<&2, Bool>, +from: String, +to: String, d: Came) -> Came:
  match did d:
    case Some{True{}} Came{rs, a, os, u}:
      Came{List.append(&2, T.Split, rs, [T.Split{from, to}]), a, os, u}
    case Some{False{}} Came{rs, a, os, u}:
      Came{rs, a, List.append(&2, T.Split, os, [T.Split{from, to}]), u}
    case None{} d2:
      d2

def acted(rs: List<&2, T.Split>, +root: String, +dir: String, d: Came) -> IO(Came):
  match rs:
    case Nil{}:
      IO.pure(Came, d)
    case T.Split{+from, +to} <> rest:
      do IO<Came>:
        m : Result<&1, &1, U32 & String, String> <- Store.moved(root ++ "\n" ++ from ++ "\n" ++ to)
        did : Maybe<&2, Bool> <- act.one(root, dir, from, to, moved.of(m))
        acted(rest, root, dir, act.push(did, from, to, d))

# The plan carried out, each rename in order: what it came to, the renames
# done, and the files found taken after those the plan left.
def act(+ps: List<&2, Placing>, +root: String, +dir: String) -> IO(Came):
  acted(done.renamed(ps), root, dir, Came{Nil{}, done.already(ps), done.occupied(ps), done.unnamed(ps)})

# The report
# ----------

# A store path as the directory being arranged sees it: relative to that
# directory, so two files sharing a name are told apart by their folders.
def shown(+p: String, +dir: String) -> String:
  Maybe.default(&2, String, T.strip_prefix(p, dir ++ "/"), p)

def said.renames(rs: List<&2, T.Split>, +dir: String, +verb: String) -> List<&2, String>:
  match rs:
    case Nil{}:
      Nil{}
    case T.Split{+f, +t} <> rest:
      (verb ++ " " ++ shown(f, dir) ++ "  ->  " ++ shown(t, dir)) <> said.renames(rest, dir, verb)

def said.left(os: List<&2, T.Split>, +dir: String, +kind: String) -> List<&2, String>:
  match os:
    case Nil{}:
      Nil{}
    case T.Split{+p, +h} <> rest:
      ("left " ++ shown(p, dir) ++ ": " ++ shown(h, dir) ++ " already holds this " ++ kind) <> said.left(rest, dir, kind)

def said.count(+n: Nat, +what: String) -> String:
  Bool.pick(String, Nat.is_eq(n, 0n), SNil{}, ", " ++ Nat.show(n) ++ " " ++ what)

# What one directory came to: each rename, each file left, and the tally,
# under the directory's whole path.
def said(+root: String, +dir: String, +kind: String, +dry: Bool, d: Came) -> List<&2, String>:
  match d:
    case Came{+rs, +a, +os, +u}:
      List.append(&2, String, said.renames(rs, dir, Bool.pick(String, dry, "would rename", "renamed")),
        List.append(&2, String, said.left(os, dir, kind),
          [root ++ "/" ++ dir ++ ": " ++ Nat.show(List.length(&2, T.Split, rs)) ++ " " ++ Bool.pick(String, dry, "to rename", "renamed") ++ ", " ++ Nat.show(a) ++ " already arranged" ++ said.count(List.length(&2, T.Split, os), "left as duplicates") ++ said.count(u, "named by no revision")]))

def print_lines(ls: List<&2, String>) -> IO(Unit):
  match ls:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case l <> rest:
      do IO<Unit>:
        IO.print(l)
        print_lines(rest)

# The command
# -----------

def arrange.run(dry: Bool, +r: String, +revs: List<&2, Placing>, +ops: List<&2, Placing>) -> IO(Unit):
  match dry:
    case True{}:
      print_lines(List.append(&2, String, said(r, "revisions", "revision", True{}, planned(revs)), said(r, "operations", "document", True{}, planned(ops))))
    case False{}:
      do IO<Unit>:
        dr : Came <- act(revs, r, "revisions")
        dop : Came <- act(ops, r, "operations")
        print_lines(List.append(&2, String, said(r, "revisions", "revision", False{}, dr), said(r, "operations", "document", False{}, dop)))

def arrange.planned(+dry: Bool, +r: String, a: Arrangement) -> IO(Unit):
  match a:
    case Arrangement{+revs, +ops}:
      arrange.run(dry, r, revs, ops)

def arrange.of(c: ArrangeCmd, +r: String, +fs: List<&2, Main.Full>, +revs: List<&2, T.Split>, +ops: List<&2, T.Split>, +ls: List<&2, String>) -> IO(Unit):
  match c:
    case ArrangeCmd{+dry, +refile}:
      do IO<Unit>:
        plan : Arrangement <- Main.refused.io(Arrangement, arrangement.r(refile, fs, revs, ops, ls))
        arrange.planned(dry, r, plan)

def rev.digests(+root: String, ds: List<&2, Store.Doc>) -> List<&2, T.Split>:
  match ds:
    case Nil{}:
      Nil{}
    case Store.Doc{+path, +id, size, text} <> rest:
      Tree.keep(~T.Split, claims_revision(path), T.Split{Store.relative(root, path), id}, rev.digests(root, rest))

def rev.digests.any(+root: String, ds: List<&2, Store.Doc>) -> List<&2, T.Split>:
  match ds:
    case Nil{}:
      Nil{}
    case Store.Doc{+path, +id, size, text} <> rest:
      T.Split{Store.relative(root, path), id} <> rev.digests.any(root, rest)

def split_le(+a: T.Split, +b: T.Split) -> Bool:
  match a b:
    case T.Split{+p, i} T.Split{+q, j}:
      walk_le(p, q)

def in_operations(ls: List<&2, String>, +documents: Bool) -> List<&2, String>:
  match ls:
    case Nil{}:
      Nil{}
    case +l <> rest:
      Rev.keep(Bool.and(String.starts_with(l, "operations/"), Bool.not(Bool.xor(claims_operation(l), documents))), l, in_operations(rest, documents))

def stat.digest(+stat: String) -> String:
  T.word(stat)

def zip.stats(ps: List<&2, String>, stats: List<&2, String>) -> List<&2, T.Split>:
  match ps stats:
    case p <> pr s <> sr:
      T.Split{p, stat.digest(s)} <> zip.stats(pr, sr)
    case _ _:
      Nil{}

# What each file of `operations/` is, by digest, in the walk's order: an
# operation document read and hashed here, a payload hashed by the host,
# which is what `check` asks of one.
def op.digests(+r: String, +ls: List<&2, String>) -> IO(List<&2, T.Split>):
  +payloads = in_operations(ls, False{})
  do IO<List<&2, T.Split>>:
    docs : List<&2, Store.Doc> <- Store.read_docs(Store.under(r, in_operations(ls, True{})))
    stats : List<&2, String> <- Store.stats(r, payloads)
    return List.sort(~T.Split, ~(a => b => split_le(a, b)), List.append(&2, T.Split, rev.digests.any(r, docs), zip.stats(payloads, stats)))

def arrange(+args: List<&2, String>) -> IO(Unit):
  do IO<Unit>:
    cmd : ArrangeCmd <- Main.refused.io(ArrangeCmd, args.r(args))
    root : String <- Store.root()
    +r : String = root
    rs : List<&2, Store.Doc> <- Store.revisions(r)
    +rs2 : List<&2, Store.Doc> = rs
    Main.refused.io(Unit, opened.r(List.sort(~Store.Doc, ~(a => b => doc_le(a, b)), rs2)))
    bs : List<&2, Bm.Bookmark> <- Main.bookmarks(r)
    ls : List<&2, String> <- Store.listing(r)
    +ls2 : List<&2, String> = ls
    ops : List<&2, T.Split> <- op.digests(r, ls2)
    arrange.of(cmd, r, Main.fulls(r, revision_docs(rs2)), List.sort(~T.Split, ~(a => b => split_le(a, b)), rev.digests(r, rs2)), ops, ls2)
