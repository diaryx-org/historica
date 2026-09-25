# `skip`: the rules saying what history does not take, listed and written
# as the Rust tool lists and writes them.
#
# With no arguments it prints each rule `history/skipped/` states, with its
# kind and the file stating it, in the order the loader walks them — by
# path component, so `build/all.txt` comes before `build.txt`. With paths
# and `--name`s it writes a rule for each, one to a file (decision 0045): a
# path is relative to the repository, a directory is a path that is one or
# that ends in `/`, and a name is one component in which `*` is any run of
# characters. `--private` makes every rule it writes one whose own text an
# `export` leaves out.
#
# Refused, in the Rust tool's words and order: a path outside the
# repository, or the repository itself, as each path is read; a value with
# space at either end or a line break in it, a name holding a `/` or
# nothing but `*`, `--suffix`, and any other flag; and then, once the store
# is open, any rule covering a file some head holds (decision 0011) — a
# rule cannot take back what is recorded. A rule already stated is said
# so rather than written twice.
#
# Where a rule is written is its label (`Rule::label`): the path, scrubbed
# of control characters, as a file — `<path>.txt`, `<path>/all.txt` for a
# directory, `name <pattern>.txt` for a name — or, where that cannot be a
# file here, or is another rule's already, the first twelve characters of
# the rule's own digest.

import Base
import ./commands.bend as Main
import ./store.bend as Store
import ./folder.bend as Folder
import ./naming.bend as Naming
import ./identity.bend as Identity
import ./revision.bend as Rev
import ./tree.bend as Tree
import ./sha256.bend as Sha
import ./utf8.bend as Utf8
import ./text.bend as T
import ./bookmark.bend as Bm

# A rule: what it matches, and whether its text stays out of an export.
type Rule is Data:
  Rule{scope: Folder.Scope, private: Bool}

def under(sc: Folder.Scope) -> Bool:
  match sc:
    case Folder.Scope.Under{v}:
      True{}
    case Folder.Scope.NameUnder{p}:
      True{}
    case _:
      False{}

def named(sc: Folder.Scope) -> Bool:
  match sc:
    case Folder.Scope.Name{p}:
      True{}
    case Folder.Scope.NameUnder{p}:
      True{}
    case _:
      False{}

def value(sc: Folder.Scope) -> String:
  match sc:
    case Folder.Scope.Path{v}:
      v
    case Folder.Scope.Under{v}:
      v
    case Folder.Scope.Name{p}:
      p
    case Folder.Scope.NameUnder{p}:
      p

def key(+name: Bool, private: Bool) -> String:
  match private:
    case True{}:
      Bool.pick(String, name, "private-name", "private")
    case False{}:
      Bool.pick(String, name, "skip-name", "skip")

# The line a rule's file holds, which `Folder.rule_in` reads back.
def show(r: Rule) -> String:
  match r:
    case Rule{+sc, p}:
      key(named(sc), p) ++ " " ++ value(sc) ++ Bool.pick(String, under(sc), "/", SNil{})

def scope.eq(a: Folder.Scope, b: Folder.Scope) -> Bool:
  match a b:
    case Folder.Scope.Path{x} Folder.Scope.Path{y}:
      String.eq(x, y)
    case Folder.Scope.Under{x} Folder.Scope.Under{y}:
      String.eq(x, y)
    case Folder.Scope.Name{x} Folder.Scope.Name{y}:
      String.eq(x, y)
    case Folder.Scope.NameUnder{x} Folder.Scope.NameUnder{y}:
      String.eq(x, y)
    case _ _:
      False{}

def rule.eq(a: Rule, b: Rule) -> Bool:
  match a b:
    case Rule{x, p} Rule{y, q}:
      Bool.and(scope.eq(x, y), Bool.not(Bool.xor(p, q)))

def held(rs: List<&2, Rule>, +r: Rule) -> Bool:
  match rs:
    case Nil{}:
      False{}
    case +x <> rest:
      Bool.or(rule.eq(x, r), held(rest, r))

# Labels
# ------

def natural(sc: Folder.Scope) -> String:
  match sc:
    case Folder.Scope.Path{v}:
      Naming.scrubbed(v) ++ ".txt"
    case Folder.Scope.Under{v}:
      Naming.scrubbed(v) ++ "/all.txt"
    case Folder.Scope.Name{p}:
      "name " ++ Naming.scrubbed(p) ++ ".txt"
    case Folder.Scope.NameUnder{p}:
      "name " ++ Naming.scrubbed(p) ++ "/all.txt"

def component.ok(+c: String) -> Bool:
  Bool.and(Bool.not(String.is_empty(c)), Nat.is_le(List.length(&2, U32, Utf8.encode(c)), 200n))

def has_star(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{'*', t}:
      True{}
    case SCon{c, t}:
      has_star(t)

# Whether a label is one this directory can carry: not a name the platform
# writes or the note `init` wrote, not `all.txt` for a rule that is not a
# directory's, no `*`, and every component a name a filesystem takes.
def spellable(+sc: Folder.Scope, +n: String) -> Bool:
  +last = Folder.last_component(n)
  Bool.and(Bool.not(Bool.or(Folder.platform_name(last), String.eq(n, "README.txt"))),
    Bool.and(Bool.not(Bool.and(String.eq(last, "all.txt"), Bool.not(under(sc)))),
      Bool.and(Bool.not(has_star(n)), List.all(~&2, ~String, ~(c => component.ok(c)), String.split(n, '/')))))

def digest_label(+r: Rule) -> String:
  String.take(Sha.digest(Utf8.encode(show(r))), 12n) ++ ".txt"

# `Rule::label`.
def label(+r: Rule) -> String:
  match r:
    case Rule{+sc, p}:
      Bool.pick(String, spellable(sc, natural(sc)), natural(sc), digest_label(r))

# The command line
# ----------------

# What the words said: the rules asked for, as they were read.
type Asked is Data:
  Asked{scopes: List<&2, Folder.Scope>, private: Bool}

type Word is Data:
  Word.Private{}
  Word.Name{}
  Word.Suffix{}
  Word.Flag{}
  Word.Path{}

def word.of(+w: String) -> Word:
  Bool.pick(Word, String.eq(w, "--private"), Word.Private{},
  Bool.pick(Word, String.eq(w, "--name"), Word.Name{},
  Bool.pick(Word, String.eq(w, "--suffix"), Word.Suffix{},
  Bool.pick(Word, String.starts_with(w, "--"), Word.Flag{}, Word.Path{}))))

def word(args: List<&2, String>) -> Word:
  match args:
    case Nil{}:
      Word.Path{}
    case +w <> rest:
      word.of(w)

def has_break(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{'\n', t}:
      True{}
    case SCon{c, t}:
      has_break(t)

# `usable`: a value the file can hold.
def usable.r(+v: String) -> Result<&2, &2, Main.Refused, String>:
  Bool.pick(Result<&2, &2, Main.Refused, String>, Folder.untrimmed(v),
    Fail{Main.Refused{2, "`" ++ v ++ "` cannot be a rule: a value is not empty and carries no leading or trailing space"}},
    Bool.pick(Result<&2, &2, Main.Refused, String>, has_break(v), Fail{Main.Refused{2, "a rule is one line, and this value holds a line break"}}, Done{v}))

def unslash_one(+n: String) -> String:
  Bool.pick(String, String.ends_with(n, "/"), String.take(n, Nat.sub(String.length(n), 1n)), n)

def name.pattern.r(+n: String, +under: Bool, p: Result<&2, &2, String, String>) -> Result<&2, &2, Main.Refused, Folder.Scope>:
  match p:
    case Fail{because}:
      Fail{Main.Refused{2, "`" ++ n ++ "` cannot be a name to match: " ++ because}}
    case Done{+v}:
      Done{Bool.pick(Folder.Scope, under, Folder.Scope.NameUnder{v}, Folder.Scope.Name{v})}

# `name_scope`: one trailing `/` parts a directory's name from a file's.
def name.scope.r(+n: String) -> Result<&2, &2, Main.Refused, Folder.Scope>:
  +under = String.ends_with(n, "/")
  do Result<&2, &2, Main.Refused, Folder.Scope>:
    v : String <- usable.r(unslash_one(n))
    name.pattern.r(n, under, Folder.pattern(v))

# Where a path a person typed sits, relative to the repository: the
# components past the repository's own, as `strip_prefix` finds them, of
# the path as it really is where it exists and as typed where it does not.
def drop.n(n: Nat, xs: List<&2, String>) -> List<&2, String>:
  match n xs:
    case 0n _:
      xs
    case 1n+k Nil{}:
      Nil{}
    case 1n+k x <> rest:
      drop.n(k, rest)

def inside.r(+path: String, +repo: String, +settled: String) -> Result<&2, &2, Main.Refused, String>:
  +rc = Identity.components(repo)
  +sc = Identity.components(settled)
  +spelled = String.join(drop.n(List.length(&2, String, rc), sc), "/")
  Bool.pick(Result<&2, &2, Main.Refused, String>, Identity.prefix(rc, sc),
    Bool.pick(Result<&2, &2, Main.Refused, String>, String.is_empty(spelled),
      Fail{Main.Refused{1, "that is the repository itself, and skipping all of it would leave history nothing to hold"}},
      Done{spelled}),
    Fail{Main.Refused{1, "`" ++ path ++ "` is not inside this repository, and a rule names what history would otherwise take"}})

def settled(+full: String, r: Result<&1, &1, U32 & String, String>) -> String:
  match r:
    case Done{real}:
      real
    case Fail{e}:
      full

# `trim_end_matches('/')`: `Folder.trim_slashes` walks the reversed path.
def trim_slashes(+p: String) -> String:
  Folder.trim_slashes(String.reverse(p))

def path.scoped(+relative: String, +directory: Bool) -> Result<&2, &2, Main.Refused, Folder.Scope>:
  do Result<&2, &2, Main.Refused, Folder.Scope>:
    v : String <- usable.r(relative)
    +v2 : String = v
    return Bool.pick(Folder.Scope, directory, Folder.Scope.Under{v2}, Folder.Scope.Path{v2})

def is_dir(r: Result<&1, &1, U32 & String, String>) -> Bool:
  match r:
    case Done{x}:
      True{}
    case Fail{e}:
      False{}

def path.dir(+relative: String, +slashed: Bool, +repo: String) -> IO(Result<&2, &2, Main.Refused, Folder.Scope>):
  do IO<Result<&2, &2, Main.Refused, Folder.Scope>>:
    listed : Result<&1, &1, U32 & String, String> <- Store.listing_of(Identity.joined(repo, relative))
    return path.scoped(relative, Bool.or(slashed, is_dir(listed)))

def path.inside(+slashed: Bool, +repo: String, r: Result<&2, &2, Main.Refused, String>) -> IO(Result<&2, &2, Main.Refused, Folder.Scope>):
  match r:
    case Fail{x}:
      IO.pure(Result<&2, &2, Main.Refused, Folder.Scope>, Fail{x})
    case Done{+relative}:
      path.dir(relative, slashed, repo)

# `path_scope`: the store found — a path is relative to the repository
# around it — and the path read against it.
def path.scope(+path: String) -> IO(Result<&2, &2, Main.Refused, Folder.Scope>):
  +trimmed = trim_slashes(path)
  do IO<Result<&2, &2, Main.Refused, Folder.Scope>>:
    root : String <- Store.root()
    +repo : String = Main.repository(root)
    +full : String = Identity.joined(repo, trimmed)
    real : Result<&1, &1, U32 & String, String> <- Store.really(full)
    path.inside(Bool.not(String.eq(trimmed, path)), repo, inside.r(trimmed, repo, settled(full, real)))

def asked.add(a: Asked, sc: Folder.Scope) -> Asked:
  match a:
    case Asked{ss, p}:
      Asked{List.append(&2, Folder.Scope, ss, [sc]), p}

def asked.private(a: Asked) -> Asked:
  match a:
    case Asked{ss, p}:
      Asked{ss, True{}}

# The words, in order, each refused where it stands; a path is read against
# the store as it comes, as the Rust tool reads it.
def args.go(args: List<&2, String>, a: Asked, k: Word) -> IO(Asked):
  match args k:
    case Nil{} _:
      IO.pure(Asked, a)
    case w <> +rest Word.Private{}:
      args.go(rest, asked.private(a), word(rest))
    case w <> Nil{} Word.Name{}:
      Main.die(Asked, 2, "`--name` wants a name to match")
    case w <> +n <> +rest Word.Name{}:
      do IO<Asked>:
        sc : Folder.Scope <- Main.refused.io(Folder.Scope, name.scope.r(n))
        args.go(rest, asked.add(a, sc), word(rest))
    case w <> rest Word.Suffix{}:
      Main.die(Asked, 2, "`--suffix` is retired: an ending is `--name` and `*` and the ending, matched against a file's own name")
    case w <> rest Word.Flag{}:
      Main.die(Asked, 2, "`" ++ w ++ "` is not an argument `skip` takes")
    case +w <> +rest Word.Path{}:
      do IO<Asked>:
        r : Result<&2, &2, Main.Refused, Folder.Scope> <- path.scope(w)
        sc : Folder.Scope <- Main.refused.io(Folder.Scope, r)
        args.go(rest, asked.add(a, sc), word(rest))

def rules.of(ss: List<&2, Folder.Scope>, +p: Bool) -> List<&2, Rule>:
  match ss:
    case Nil{}:
      Nil{}
    case sc <> rest:
      Rule{sc, p} <> rules.of(rest, p)

def wanted(a: Asked) -> List<&2, Rule>:
  match a:
    case Asked{ss, +p}:
      rules.of(ss, p)

# The rules the store states
# --------------------------

# A rule and the file of `skipped/` stating it.
type Stating is Data:
  Stating{rule: Rule, file: String}

def stating.rule(s: Stating) -> Rule:
  match s:
    case Stating{r, f}:
      r

# Which key the one rule line of a file has: whether the rule is private.
def private.line(ls: List<&2, String>) -> Bool:
  match ls:
    case Nil{}:
      False{}
    case +l <> rest:
      Bool.pick(Bool, Bool.or(String.is_empty(l), String.starts_with(l, "#")), private.line(rest),
        Bool.or(String.starts_with(l, "private "), String.starts_with(l, "private-name ")))

def stated.of(+file: String, +text: String, st: Folder.Stated) -> List<&2, Stating>:
  match st:
    case Folder.Stated.One{sc}:
      [Stating{Rule{sc, private.line(Folder.lines.trimmed(String.split(text, '\n')))}, file}]
    case _:
      Nil{}

# The loader's walk is by path component, which a sorted listing is not
# where a name holds a character before `/`.
def before(a: List<&2, String>, b: List<&2, String>) -> Bool:
  match a b:
    case Nil{} _:
      True{}
    case x <> more Nil{}:
      False{}
    case +x <> more +y <> rest:
      Bool.pick(Bool, String.eq(x, y), before(more, rest), String.is_le(x, y))

def walked(ps: List<&2, String>) -> List<&2, String>:
  List.sort(~String, ~(a => b => before(String.split(a, '/'), String.split(b, '/'))), ps)

# Each rule once, as `Skipped::stated` keeps them: the first file stating
# it is the one named. Whether the next is one already kept is asked by the
# caller, so each branch is walked once.
def once.dup(ss: List<&2, Stating>, +seen: List<&2, Rule>) -> Bool:
  match ss:
    case Nil{}:
      False{}
    case Stating{+r, f} <> rest:
      held(seen, r)

def once(ss: List<&2, Stating>, +seen: List<&2, Rule>, dup: Bool) -> List<&2, Stating>:
  match ss dup:
    case Nil{} _:
      Nil{}
    case Stating{r, f} <> +rest True{}:
      once(rest, seen, once.dup(rest, seen))
    case Stating{+r, f} <> +rest False{}:
      Stating{r, f} <> once(rest, r <> seen, once.dup(rest, r <> seen))

# Whether each rule is new against every rule before it, and against
# `seen` (`LAWS.skip_lists_each_rule_once`).
def fresh.stated(ss: List<&2, Stating>, +seen: List<&2, Rule>) -> Bool:
  match ss:
    case Nil{}:
      True{}
    case Stating{+r, f} <> rest:
      Bool.and(Bool.not(held(seen, r)), fresh.stated(rest, r <> seen))

# Whether each rule is one neither `had` nor any rule before it states
# (`LAWS.skip_writes_what_is_new`).
def fresh.rules(rs: List<&2, Rule>, +had: List<&2, Rule>, +before: List<&2, Rule>) -> Bool:
  match rs:
    case Nil{}:
      True{}
    case +r <> rest:
      Bool.and(Bool.not(Bool.or(held(had, r), held(before, r))), fresh.rules(rest, had, List.append(&2, Rule, before, [r])))

def stated.go(+root: String, ps: List<&2, String>) -> IO(List<&2, Stating>):
  match ps:
    case Nil{}:
      IO.pure(List<&2, Stating>, Nil{})
    case +p <> rest:
      do IO<List<&2, Stating>>:
        text : String <- Store.read_text(root ++ "/" ++ p)
        +text2 : String = text
        +here : List<&2, Stating> = stated.of(String.drop(p, 8n), text2, Folder.rule_in(text2))
        later : List<&2, Stating> <- stated.go(root, rest)
        return List.append(&2, Stating, here, later)

def stated(+root: String) -> IO(List<&2, Stating>):
  do IO<List<&2, Stating>>:
    ps : List<&2, String> <- Store.skipped_paths(root)
    ss : List<&2, Stating> <- stated.go(root, walked(Folder.rules.kept(ps)))
    +ss2 : List<&2, Stating> = ss
    return once(ss2, Nil{}, once.dup(ss2, Nil{}))

# Listing
# -------

def listed(ss: List<&2, Stating>) -> String:
  match ss:
    case Nil{}:
      SNil{}
    case Stating{Rule{+sc, +p}, f} <> rest:
      show(Rule{sc, p}) ++ "\n  " ++ Bool.pick(String, p, "private", "shared") ++ "  history/skipped/" ++ f ++ "\n" ++ listed(rest)

# Writing
# -------

# Every path some head holds that a wanted rule covers, each once, sorted.
def covering(rs: List<&2, Rule>, +path: String) -> Bool:
  match rs:
    case Nil{}:
      False{}
    case Rule{sc, p} <> rest:
      Bool.or(Folder.covers(sc, path), covering(rest, path))

def covered.of(+rs: List<&2, Rule>, es: Tree.Tree(), +had: List<&2, String>) -> List<&2, String>:
  match es:
    case Nil{}:
      had
    case +e <> rest:
      +p = Tree.entry_path(e)
      covered.of(rs, rest, Bool.pick(List<&2, String>, Bool.and(covering(rs, p), Bool.not(Rev.member(had, p))), List.append(&2, String, had, [p]), had))

def covered.go(+fs: List<&2, Main.Full>, +rs: List<&2, Rule>, hs: List<&2, String>, +had: List<&2, String>) -> Result<&2, &2, Main.Refused, List<&2, String>>:
  match hs:
    case Nil{}:
      Done{had}
    case +h <> rest:
      do Result<&2, &2, Main.Refused, List<&2, String>>:
        t : Tree.Tree() <- Main.tree.r(fs, h)
        covered.go(fs, rs, rest, covered.of(rs, t, had))

def covered.said(ps: List<&2, String>) -> String:
  match ps:
    case Nil{}:
      SNil{}
    case p <> rest:
      "\n  " ++ p ++ covered.said(rest)

# Decision 0011, asked of every head: a rule is a fact about the
# repository, so a path any line of work holds is one it cannot cover.
def covered.r(+fs: List<&2, Main.Full>, +rs: List<&2, Rule>) -> Result<&2, &2, Main.Refused, Unit>:
  do Result<&2, &2, Main.Refused, Unit>:
    ps : List<&2, String> <- covered.go(fs, rs, Rev.heads(Main.history(fs)), Nil{})
    +sorted : List<&2, String> = List.sort(~String, ~(a => b => String.is_le(a, b)), ps)
    +n : Nat = List.length(&2, String, sorted)
    +one : Bool = Nat.is_eq(n, 1n)
    Bool.pick(Result<&2, &2, Main.Refused, Unit>, Nat.is_eq(n, 0n), Done{Unit{}},
      Fail{Main.Refused{1, "history already holds " ++ Bool.pick(String, one, "a file this would skip", Nat.show(n) ++ " files this would skip") ++ ", and a rule cannot take back what is recorded; delete the " ++ Bool.pick(String, one, "file", "files") ++ " and record that, which is what removing a file from the tree means, and `forget` is what removes recorded content:" ++ covered.said(sorted)}})

# Which wanted rules are new, and which the store — or an earlier word —
# already states.
type Sorted is Data:
  Sorted{fresh: List<&2, Rule>, already: List<&2, Rule>}

def sorted.dup(rs: List<&2, Rule>, +had: List<&2, Rule>, +fresh: List<&2, Rule>) -> Bool:
  match rs:
    case Nil{}:
      False{}
    case +r <> rest:
      Bool.or(held(had, r), held(fresh, r))

def sorted.go(rs: List<&2, Rule>, +had: List<&2, Rule>, +fresh: List<&2, Rule>, +already: List<&2, Rule>, dup: Bool) -> Sorted:
  match rs dup:
    case Nil{} _:
      Sorted{fresh, already}
    case +r <> +rest True{}:
      sorted.go(rest, had, fresh, List.append(&2, Rule, already, [r]), sorted.dup(rest, had, fresh))
    case +r <> +rest False{}:
      +more = List.append(&2, Rule, fresh, [r])
      sorted.go(rest, had, more, already, sorted.dup(rest, had, more))

def sorted.fresh(s: Sorted) -> List<&2, Rule>:
  match s:
    case Sorted{f, a}:
      f

def again.label(+r: Rule, w: Result<&1, &1, U32 & String, String>) -> IO(String):
  match w:
    case Fail{Tuple{+code, msg}}:
      Bool.pick(IO(String), U32.is_eq(code, 5), IO.pure(String, digest_label(r)), Main.die(String, 1, msg))
    case Done{x}:
      IO.pure(String, digest_label(r))

def again(+r: Rule, +root: String) -> IO(String):
  do IO<String>:
    w : Result<&1, &1, U32 & String, String> <- Store.filed(root ++ "/skipped/" ++ digest_label(r) ++ "\n" ++ show(r) ++ "\n")
    again.label(r, w)

# A label another file already has — different bytes, which `Store.once`
# refuses with `EIO` — yields to the rule's digest.
def written.label(+r: Rule, +natural: String, +root: String, w: Result<&1, &1, U32 & String, String>) -> IO(String):
  match w:
    case Done{x}:
      IO.pure(String, natural)
    case Fail{Tuple{+code, msg}}:
      Bool.pick(IO(String), U32.is_eq(code, 5), again(r, root), Main.die(String, 1, msg))

# `add_skipped`: each rule filed once under its label, or where that file
# is another rule's, under its digest.
def write.go(+root: String, rs: List<&2, Rule>) -> IO(String):
  match rs:
    case Nil{}:
      IO.pure(String, SNil{})
    case +r <> rest:
      +n = label(r)
      do IO<String>:
        w : Result<&1, &1, U32 & String, String> <- Store.filed(root ++ "/skipped/" ++ n ++ "\n" ++ show(r) ++ "\n")
        l : String <- written.label(r, n, root, w)
        more : String <- write.go(root, rest)
        return show(r) ++ "\n  history/skipped/" ++ l ++ "\n" ++ more

def already.said(rs: List<&2, Rule>) -> String:
  match rs:
    case Nil{}:
      SNil{}
    case +r <> rest:
      "already there: " ++ show(r) ++ "\n" ++ already.said(rest)

def write.sorted(+root: String, s: Sorted) -> IO(String):
  match s:
    case Sorted{fresh, +already}:
      do IO<String>:
        written : String <- write.go(root, fresh)
        return written ++ already.said(already)

def write(+root: String, +fs: List<&2, Main.Full>, +rs: List<&2, Rule>, +ss: List<&2, Stating>) -> IO(Unit):
  do IO<Unit>:
    Main.refused.io(Unit, covered.r(fs, rs))
    +had : List<&2, Rule> = T.map(~Stating, ~Rule, ~(x => stating.rule(x)), ss)
    +s : Sorted = sorted.go(rs, had, Nil{}, Nil{}, sorted.dup(rs, had, Nil{}))
    said : String <- write.sorted(root, s)
    IO.write(said)

# `skip [--private] <path>... [--name <name>]`, or with no arguments the
# rules there are.
def skip(+args: List<&2, String>) -> IO(Unit):
  do IO<Unit>:
    a : Asked <- args.go(args, Asked{Nil{}, False{}}, word(args))
    +rs : List<&2, Rule> = wanted(a)
    root : String <- Store.root()
    +r : String = root
    docs : List<&2, Store.Doc> <- Store.revisions(r)
    bs : List<&2, Bm.Bookmark> <- Main.bookmarks(r)
    ss : List<&2, Stating> <- stated(r)
    +ss2 : List<&2, Stating> = ss
    Bool.pick(IO(Unit), List.is_empty(&2, Rule, rs), IO.write(listed(ss2)), write(r, Main.fulls(r, docs), rs, ss2))
