# The tree, run: every corpus chain replays into the file set the crate's
# tests state, the three invalid documents the parser accepts are refused
# by the tree for their own stated reason, the graph merge agrees with the
# linear replay on every chain, and the hand-built graphs of `tree.rs`'s
# unit tests resolve as decision 0008 says.
#
#   cd historica/spike/bend && bend corpus_tree.bend

import Base
import ./utf8.bend as Utf8
import ./sha256.bend as Sha
import ./revision.bend as Rev
import ./tree.bend as Tree

def corpus() -> String:
  "../../tests/corpus/"

def verdict(ok: Bool, what: String) -> IO(Unit):
  match ok:
    case True{}:
      IO.print("ok    " ++ what)
    case False{}:
      IO.die(Unit, 1, "FAIL  " ++ what)

# Reading
# -------

def parsed.of(what: String, r: Result<&2, &2, String, Rev.Rev>) -> IO(Rev.Rev):
  match r:
    case Fail{e}:
      IO.die(Rev.Rev, 1, "FAIL  " ++ what ++ " refused: " ++ e)
    case Done{doc}:
      IO.pure(Rev.Rev, doc)

def parsed(what: String, +s: String) -> IO(Rev.Rev):
  parsed.of(what, Rev.parse(s))

# One corpus document as an event: hashed for its identity, parsed for
# what it says.
def event(+name: String) -> IO(Tree.Ev):
  do IO<Tree.Ev>:
    bs : List<&2, U32> <- Utf8.read_file(corpus() ++ name)
    +bs2 : List<&2, U32> = bs
    doc : Rev.Rev <- parsed(name, Utf8.decode(bs2))
    return Tree.Ev{Sha.digest(bs2), doc}

def events(names: List<&2, String>) -> IO(List<&2, Tree.Ev>):
  match names:
    case Nil{}:
      IO.pure(List<&2, Tree.Ev>, Nil{})
    case name <> rest:
      do IO<List<&2, Tree.Ev>>:
        e : Tree.Ev <- event(name)
        more : List<&2, Tree.Ev> <- events(rest)
        return e <> more

def docs(es: List<&2, Tree.Ev>) -> List<&2, Rev.Rev>:
  match es:
    case Nil{}:
      Nil{}
    case Tree.Ev{id, doc} <> rest:
      doc <> docs(rest)

# A hand-built revision: the given parents, sorted, and the given facts.
def parent_lines(ps: List<&2, String>) -> String:
  match ps:
    case Nil{}:
      ""
    case p <> rest:
      "parent " ++ p ++ "\n" ++ parent_lines(rest)

def revision(parents: List<&2, String>, facts: String) -> String:
  "historica\nchange qpvuntsmwlrkzxonmvtplsyq\n" ++ parent_lines(Tree.sorted_ids(parents)) ++ "author Adam Harris <adam@example.com>\nwhen 2025-08-19T00:47:11-06:00\n" ++ facts ++ "\nm"

def built(+s: String) -> IO(Tree.Ev):
  do IO<Tree.Ev>:
    doc : Rev.Rev <- parsed("a hand-built revision", s)
    return Tree.Ev{Sha.digest(Utf8.encode(s)), doc}

def id_of(s: String) -> String:
  Sha.digest(Utf8.encode(s))

# Results
# -------

def tree_of(what: String, r: Result<&2, &2, Tree.Fault, Tree.Tree()>) -> IO(Tree.Tree()):
  match r:
    case Fail{e}:
      IO.die(Tree.Tree(), 1, "FAIL  " ++ what ++ " refused: " ++ Tree.fault_show(e))
    case Done{t}:
      IO.pure(Tree.Tree(), t)

def merged_of(what: String, r: Result<&2, &2, Tree.Fault, Tree.Merged>) -> IO(Tree.Merged):
  match r:
    case Fail{e}:
      IO.die(Tree.Merged, 1, "FAIL  " ++ what ++ " refused: " ++ Tree.fault_show(e))
    case Done{m}:
      IO.pure(Tree.Merged, m)

def refused_with.of(what: String, +expected: String, r: Result<&2, &2, Tree.Fault, Tree.Tree()>) -> IO(Unit):
  match r:
    case Done{t}:
      verdict(False{}, what ++ " accepted")
    case Fail{e}:
      +shown : String = Tree.fault_show(e)
      verdict(String.eq(shown, expected), what ++ " refused: " ++ shown)

def refused_with(what: String, expected: Tree.Fault, r: Result<&2, &2, Tree.Fault, Tree.Tree()>) -> IO(Unit):
  refused_with.of(what, Tree.fault_show(expected), r)

def merge_refused_with.of(what: String, +expected: String, r: Result<&2, &2, Tree.Fault, Tree.Merged>) -> IO(Unit):
  match r:
    case Done{m}:
      verdict(False{}, what ++ " accepted")
    case Fail{e}:
      +shown : String = Tree.fault_show(e)
      verdict(String.eq(shown, expected), what ++ " refused: " ++ shown)

def merge_refused_with(what: String, expected: Tree.Fault, r: Result<&2, &2, Tree.Fault, Tree.Merged>) -> IO(Unit):
  merge_refused_with.of(what, Tree.fault_show(expected), r)

def path_is(t: Tree.Tree(), +file: String, +expected: String) -> Bool:
  Tree.maybe_str_eq(Tree.path(t, file), Some{expected})

def no_path(t: Tree.Tree(), +file: String) -> Bool:
  Maybe.is_none(&2, String, Tree.path(t, file))

def kind_is.of(found: Maybe<&2, Tree.FileKind>, k: Tree.FileKind) -> Bool:
  match found:
    case None{}:
      False{}
    case Some{held}:
      Tree.kind_eq(held, k)

def kind_is(t: Tree.Tree(), +file: String, k: Tree.FileKind) -> Bool:
  kind_is.of(Tree.kind(t, file), k)

def mode_is.of(found: Maybe<&2, Tree.Mode>, m: Tree.Mode) -> Bool:
  match found:
    case None{}:
      False{}
    case Some{held}:
      Tree.mode_eq(held, m)

def mode_is(t: Tree.Tree(), +file: String, m: Tree.Mode) -> Bool:
  mode_is.of(Tree.mode(t, file), m)

def target_is.of(found: Maybe<&2, Tree.Entry>, g: Tree.Target) -> Bool:
  match found:
    case None{}:
      False{}
    case Some{e}:
      Tree.maybe_target_eq(Tree.entry_target(e), Some{g})

def target_is(t: Tree.Tree(), +file: String, g: Tree.Target) -> Bool:
  target_is.of(Tree.lookup(t, file), g)

def payload_is.of(found: Maybe<&2, Tree.Entry>, y: String) -> Bool:
  match found:
    case None{}:
      False{}
    case Some{e}:
      Tree.maybe_str_eq(Tree.entry_payload(e), Some{y})

def payload_is(t: Tree.Tree(), +file: String, y: String) -> Bool:
  payload_is.of(Tree.lookup(t, file), y)

def trees_eq(a: Tree.Tree(), b: Tree.Tree()) -> Bool:
  match a b:
    case Nil{} Nil{}:
      True{}
    case x <> xs y <> ys:
      Bool.and(Tree.entry_eq(x, y), trees_eq(xs, ys))
    case _ _:
      False{}

def same_ids(+xs: List<&2, String>, +ys: List<&2, String>) -> Bool:
  Bool.and(Rev.subset(xs, ys), Rev.subset(ys, xs))

def contests_shown(cs: List<&2, Tree.Contest>) -> List<&2, String>:
  match cs:
    case Nil{}:
      Nil{}
    case c <> rest:
      Tree.contest_show(c) <> contests_shown(rest)

def contested_is.of(shown: List<&2, String>, expected: List<&2, String>) -> Bool:
  match shown expected:
    case Nil{} Nil{}:
      True{}
    case x <> xs y <> ys:
      Bool.and(String.eq(x, y), contested_is.of(xs, ys))
    case _ _:
      False{}

def contested_is(m: Tree.Merged, +expected: List<&2, String>) -> Bool:
  contested_is.of(contests_shown(Tree.merged_contested(m)), expected)

# The graph merge and the linear replay agree on a chain, tree for tree.
def agree(+what: String, +es: List<&2, Tree.Ev>) -> IO(Unit):
  do IO<Unit>:
    linear : Tree.Tree() <- tree_of(what ++ " replays", Tree.replay(docs(es)))
    graph : Tree.Merged <- merged_of(what ++ " merges", Tree.merge(es))
    +m : Tree.Merged = graph
    verdict(Bool.and(trees_eq(linear, Tree.merged_tree(m)), List.is_empty(&2, Tree.Contest, Tree.merged_contested(m))), what ++ ": the merge is the replay, and nothing was contested")

# The tree corpus
# ---------------

def ENTRY() -> String:
  "nrqvtkzlmwyxsptonvqrklmz"

def README() -> String:
  "swtlmnkqvzyrxopwstlnmkqv"

def tree_corpus() -> IO(Unit):
  do IO<Unit>:
    +es : List<&2, Tree.Ev> <- events(["tree/revisions/01-start.rev.txt", "tree/revisions/02-entry.rev.txt", "tree/revisions/03-move.rev.txt", "tree/revisions/04-drop.rev.txt"])
    +history : List<&2, Rev.Rev> = docs(es)
    started : Tree.Tree() <- tree_of("tree/01", Tree.replay(List.take(&2, Rev.Rev, history, 1n)))
    +t1 : Tree.Tree() = started
    verdict(Bool.and(Nat.is_eq(Tree.size(t1), 2n), Bool.and(path_is(t1, ENTRY(), "notes/2025-08-19.md"), path_is(t1, README(), "README.md"))), "tree: the root adds two files at their paths")
    edited : Tree.Tree() <- tree_of("tree/02", Tree.replay(List.take(&2, Rev.Rev, history, 2n)))
    verdict(trees_eq(edited, t1), "tree: a revision that only edits leaves the file set untouched")
    moved : Tree.Tree() <- tree_of("tree/03", Tree.replay(List.take(&2, Rev.Rev, history, 3n)))
    +t3 : Tree.Tree() = moved
    verdict(Bool.and(path_is(t3, README(), "docs/README.md"), Bool.and(List.is_empty(&2, String, Tree.at(t3, "README.md")), same_ids(Tree.at(t3, "docs/README.md"), [README()]))), "tree: a rename keeps the file and moves the path")
    dropped : Tree.Tree() <- tree_of("tree/04", Tree.replay(history))
    +t4 : Tree.Tree() = dropped
    verdict(Bool.and(Nat.is_eq(Tree.size(t4), 1n), Bool.and(no_path(t4, ENTRY()), same_ids(Tree.files(t4), [README()]))), "tree: a dropped file stops existing")
    verdict(Bool.and(Nat.is_eq(List.length(&2, String, Tree.operations_for(history, README())), 1n), Nat.is_eq(List.length(&2, String, Tree.operations_for(history, ENTRY())), 1n)), "tree: a rename and a drop keep everything recorded against the file")
    agree("tree", es)

# The links corpus
# ----------------

def CURRENT() -> String:
  "lqxstvnmpkwyzrolvtsqnkxm"

def JULY() -> String:
  "nrqvtkzlmwyxsptonvqrklmz"

def CONFIG() -> String:
  "ptkwnrvzlmyxqsotnkwlpvzr"

def AUGUST() -> String:
  "swtlmnkqvzyrxopwstlnmkqv"

def links_invalid.doc(+what: String, +after_02: Tree.Tree(), expected: Tree.Fault, e: Tree.Ev) -> IO(Unit):
  match e:
    case Tree.Ev{id, doc}:
      refused_with("links/invalid/" ++ what, expected, Tree.apply(after_02, doc))

def links_corpus() -> IO(Unit):
  do IO<Unit>:
    +es : List<&2, Tree.Ev> <- events(["links/revisions/01-start.rev.txt", "links/revisions/02-august.rev.txt", "links/revisions/03-renamed.rev.txt", "links/revisions/04-gone.rev.txt"])
    +history : List<&2, Rev.Rev> = docs(es)
    started : Tree.Tree() <- tree_of("links/01", Tree.replay(List.take(&2, Rev.Rev, history, 1n)))
    +t1 : Tree.Tree() = started
    verdict(Bool.and(kind_is(t1, CURRENT(), Tree.Link{}), Bool.and(target_is(t1, CURRENT(), Tree.Reference{JULY()}), Bool.and(target_is(t1, CONFIG(), Tree.Verbatim{"/etc/journal"}), kind_is(t1, JULY(), Tree.Lines{})))), "links: a link is a link, and points at a file or a string")
    pointed : Tree.Tree() <- tree_of("links/02", Tree.replay(List.take(&2, Rev.Rev, history, 2n)))
    +t2 : Tree.Tree() = pointed
    verdict(target_is(t2, CURRENT(), Tree.Reference{AUGUST()}), "links: a retarget is a `link` line and nothing else")
    renamed : Tree.Tree() <- tree_of("links/03", Tree.replay(List.take(&2, Rev.Rev, history, 3n)))
    +t3 : Tree.Tree() = renamed
    verdict(Bool.and(path_is(t3, AUGUST(), "2026/08.md"), target_is(t3, CURRENT(), Tree.Reference{AUGUST()})), "links: renaming the target changes nothing about the link")
    gone : Tree.Tree() <- tree_of("links/04", Tree.replay(history))
    +t4 : Tree.Tree() = gone
    verdict(Bool.and(no_path(t4, AUGUST()), target_is(t4, CURRENT(), Tree.Verbatim{"2026/08.md"})), "links: a drop with the link restated verbatim is ordinary")
    edit_a_link : Tree.Ev <- event("links/invalid/edit-a-link.rev.txt")
    links_invalid.doc("edit-a-link.rev.txt", t2, Tree.WrongKind{"edit", CURRENT(), Tree.Link{}}, edit_a_link)
    plain : Tree.Ev <- event("links/invalid/link-a-plain-file.rev.txt")
    links_invalid.doc("link-a-plain-file.rev.txt", t2, Tree.WrongKind{"link", JULY(), Tree.Lines{}}, plain)
    referenced : Tree.Ev <- event("links/invalid/drop-a-referenced-file.rev.txt")
    links_invalid.doc("drop-a-referenced-file.rev.txt", t2, Tree.Dangling{CURRENT(), AUGUST()}, referenced)
    agree("links", es)

# The modes and whole corpora
# ---------------------------

def RUN() -> String:
  "nrqvtkzlmwyxsptonvqrklmz"

def modes_corpus() -> IO(Unit):
  do IO<Unit>:
    +es : List<&2, Tree.Ev> <- events(["modes/revisions/01-start.rev.txt", "modes/revisions/02-runnable.rev.txt", "modes/revisions/03-plain.rev.txt"])
    +history : List<&2, Rev.Rev> = docs(es)
    started : Tree.Tree() <- tree_of("modes/01", Tree.replay(List.take(&2, Rev.Rev, history, 1n)))
    verdict(mode_is(started, RUN(), Tree.Plain{}), "modes: a file no `mode` line has named is plain")
    runnable : Tree.Tree() <- tree_of("modes/02", Tree.replay(List.take(&2, Rev.Rev, history, 2n)))
    verdict(mode_is(runnable, RUN(), Tree.Executable{}), "modes: a `mode` line makes it executable")
    plain : Tree.Tree() <- tree_of("modes/03", Tree.replay(history))
    verdict(mode_is(plain, RUN(), Tree.Plain{}), "modes: and another makes it plain again")
    agree("modes", es)

def PHOTO() -> String:
  "swtlmnkqvzyrxopwstlnmkqv"

def whole_corpus() -> IO(Unit):
  do IO<Unit>:
    +es : List<&2, Tree.Ev> <- events(["whole/revisions/01-start.rev.txt", "whole/revisions/02-crop.rev.txt"])
    +history : List<&2, Rev.Rev> = docs(es)
    started : Tree.Tree() <- tree_of("whole/01", Tree.replay(List.take(&2, Rev.Rev, history, 1n)))
    +t1 : Tree.Tree() = started
    verdict(Bool.and(kind_is(t1, PHOTO(), Tree.Whole{}), payload_is(t1, PHOTO(), "8aea125239f85ba50f847a76880a4de4ac5c60326270c6f7a2c019b789f6e6ff")), "whole: a file added with `bytes` is bytes, holding that payload")
    cropped : Tree.Tree() <- tree_of("whole/02", Tree.replay(history))
    verdict(payload_is(cropped, PHOTO(), "779674f0ffa8fe7af9f7f1a70484aa894d5ddb02d757f5eb2632c24c073cb81c"), "whole: a later `bytes` replaces the payload")
    agree("whole", es)

def merged_corpus() -> IO(Unit):
  do IO<Unit>:
    +es : List<&2, Tree.Ev> <- events(["merged/revisions/01-root.rev.txt", "merged/revisions/02-left.rev.txt", "merged/revisions/03-right.rev.txt", "merged/revisions/04-merge.rev.txt", "merged/revisions/05-after.rev.txt"])
    m : Tree.Merged <- merged_of("merged", Tree.merge(es))
    +m2 : Tree.Merged = m
    verdict(Bool.and(Nat.is_eq(Tree.size(Tree.merged_tree(m2)), 2n), List.is_empty(&2, Tree.Contest, Tree.merged_contested(m2))), "merged: two branches editing one file contest nothing about the tree")

# The unit tests of `tree.rs`
# ---------------------------

def ONE() -> String:
  "lqxstvnmpkwyzrolvtsqnkxm"

def TWO() -> String:
  "ptkwnrvzlmyxqsotnkwlpvzr"

def DIGEST() -> String:
  "1e4e224e93380a25d4cd1be85d35db37f4064be4388822eba250894c6d6daa0d"

def linear_units() -> IO(Unit):
  do IO<Unit>:
    root : Tree.Ev <- built(revision(Nil{}, "add " ++ ONE() ++ " notes/one.md\n"))
    t : Tree.Tree() <- tree_of("a root", Tree.replay(docs([root])))
    +t1 : Tree.Tree() = t
    verdict(Bool.and(Nat.is_eq(Tree.size(t1), 1n), Bool.and(path_is(t1, ONE(), "notes/one.md"), same_ids(Tree.at(t1, "notes/one.md"), [ONE()]))), "a root revision starts from no files at all")
    a : Tree.Ev <- built(revision(Nil{}, "add " ++ ONE() ++ " a.md\nadd " ++ TWO() ++ " b.md\n"))
    swap : Tree.Ev <- built(revision(Nil{}, "move " ++ ONE() ++ " b.md\nmove " ++ TWO() ++ " a.md\n"))
    swapped : Tree.Tree() <- tree_of("a swap", Tree.replay(docs([a, swap])))
    +t2 : Tree.Tree() = swapped
    verdict(Bool.and(path_is(t2, ONE(), "b.md"), path_is(t2, TWO(), "a.md")), "two files may exchange their paths in one revision")
    added : Tree.Ev <- built(revision(Nil{}, "add " ++ ONE() ++ " a.md\n"))
    drop : Tree.Ev <- built(revision(Nil{}, "drop " ++ ONE() ++ "\n"))
    reuse : Tree.Ev <- built(revision(Nil{}, "add " ++ TWO() ++ " a.md\n"))
    +added2 : Tree.Ev = added
    +drop2 : Tree.Ev = drop
    emptied : Tree.Tree() <- tree_of("a drop", Tree.replay(docs([added2, drop2])))
    verdict(Nat.is_eq(Tree.size(emptied), 0n), "a dropped file stops existing")
    reused : Tree.Tree() <- tree_of("reuse", Tree.replay(docs([added2, drop2, reuse])))
    verdict(path_is(reused, TWO(), "a.md"), "and the path it held is free for a different file")
    orphan : Tree.Ev <- built(revision(Nil{}, "move " ++ ONE() ++ " b.md\n"))
    refused_with("an orphan move", Tree.Unknown{"move", ONE()}, Tree.replay(docs([orphan])))
    edited : Tree.Ev <- built(revision(Nil{}, "edit " ++ ONE() ++ " " ++ DIGEST() ++ "\n"))
    refused_with("an orphan edit", Tree.Unknown{"edit", ONE()}, Tree.replay(docs([edited])))
    +added3 : Tree.Ev = added2
    refused_with("adding twice", Tree.AddedTwice{ONE()}, Tree.replay(docs([added3, added3])))
    other : Tree.Ev <- built(revision(Nil{}, "add " ++ TWO() ++ " a.md\n"))
    refused_with("one line of history never puts two files at one path", Tree.PathTaken{"a.md", TWO(), ONE()}, Tree.replay(docs([added3, other])))

def lower(+a: String, +b: String) -> String:
  Bool.pick(String, String.is_le(a, b), a, b)

def graph_units() -> IO(Unit):
  do IO<Unit>:
    +root_text : String = revision(Nil{}, "add " ++ ONE() ++ " notes.md\n")
    root : Tree.Ev <- built(root_text)
    +root2 : Tree.Ev = root
    +dropped_text : String = revision([id_of(root_text)], "drop " ++ ONE() ++ "\n")
    dropped : Tree.Ev <- built(dropped_text)
    +dropped2 : Tree.Ev = dropped
    edited : Tree.Ev <- built(revision([id_of(root_text)], "edit " ++ ONE() ++ " " ++ DIGEST() ++ "\n"))
    survived : Tree.Merged <- merged_of("drop versus edit", Tree.merge([root2, dropped2, edited]))
    +m1 : Tree.Merged = survived
    verdict(Bool.and(path_is(Tree.merged_tree(m1), ONE(), "notes.md"), contested_is(m1, ["dropped " ++ ONE() ++ " by " ++ id_of(dropped_text)])), "a drop concurrent with an edit loses and is reported")
    taken : Tree.Merged <- merged_of("a drop alone", Tree.merge([root2, dropped2]))
    +m2 : Tree.Merged = taken
    verdict(Bool.and(Nat.is_eq(Tree.size(Tree.merged_tree(m2)), 0n), contested_is(m2, Nil{})), "a drop nothing contests takes the file")
    +here_text : String = revision([id_of(root_text)], "move " ++ ONE() ++ " here.md\n")
    +there_text : String = revision([id_of(root_text)], "move " ++ ONE() ++ " there.md\n")
    here : Tree.Ev <- built(here_text)
    there : Tree.Ev <- built(there_text)
    +here2 : Tree.Ev = here
    moved : Tree.Merged <- merged_of("two moves", Tree.merge([root2, here2, there]))
    +m3 : Tree.Merged = moved
    +lower_path : String = Bool.pick(String, String.is_le(id_of(here_text), id_of(there_text)), "here.md", "there.md")
    +higher_path : String = Bool.pick(String, String.is_le(id_of(here_text), id_of(there_text)), "there.md", "here.md")
    verdict(Bool.and(path_is(Tree.merged_tree(m3), ONE(), lower_path), contested_is(m3, ["moved " ++ ONE() ++ " to " ++ lower_path ++ " " ++ higher_path])), "two concurrent moves resolve to the lower digest")
    again : Tree.Ev <- built(revision([id_of(here_text)], "move " ++ ONE() ++ " there.md\n"))
    chained : Tree.Merged <- merged_of("a move after a move", Tree.merge([root2, here2, again]))
    +m4 : Tree.Merged = chained
    verdict(Bool.and(path_is(Tree.merged_tree(m4), ONE(), "there.md"), contested_is(m4, Nil{})), "a later move replaces an earlier one without contest")
    mine : Tree.Ev <- built(revision([id_of(root_text)], "add " ++ TWO() ++ " theirs.md\n"))
    theirs : Tree.Ev <- built(revision([id_of(root_text)], "move " ++ ONE() ++ " theirs.md\n"))
    shared : Tree.Merged <- merged_of("one path, two files", Tree.merge([root2, mine, theirs]))
    +m5 : Tree.Merged = shared
    verdict(Bool.and(Nat.is_eq(List.length(&2, String, Tree.at(Tree.merged_tree(m5), "theirs.md")), 2n), contested_is(m5, ["path theirs.md held by " ++ ONE() ++ " " ++ TWO()])), "two files claiming one path both keep their identities")
    child : Tree.Ev <- built(here_text)
    merge_refused_with("an undelivered parent", Tree.Undelivered{id_of(root_text), id_of(here_text)}, Tree.merge([child]))

def main() -> IO(Unit):
  do IO<Unit>:
    tree_corpus()
    links_corpus()
    modes_corpus()
    whole_corpus()
    merged_corpus()
    linear_units()
    graph_units()
