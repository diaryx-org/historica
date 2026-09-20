# historica, in Bend: the readable core of the format, over the documents
# you hand it. Base has no way to list a directory, so every command takes
# the paths of the documents it reads.
#
#   bend main.bend -- log     history/revisions/*/*.rev.txt
#   bend main.bend -- check   history/revisions/*/*.rev.txt history/operations/*/*/*
#   bend main.bend -- replay  <first.ops.txt> <next.ops.txt> ...
#   bend main.bend -- diff    <parent file> <child file>
#
# Or compile it: `bend main.bend -o historica-bend`.

import Base
import ./utf8.bend as Utf8
import ./sha256.bend as Sha
import ./text.bend as T
import ./ops.bend as Ops
import ./revision.bend as Rev

# One document read from disk: its path, its bytes' digest, and its text.
type Doc is Data:
  Doc{path: String, id: String, text: String}

def doc_of(path: String, +bs: List<&2, U32>) -> Doc:
  Doc{path, Sha.digest(bs), Utf8.decode(bs)}

def read_doc(+path: String) -> IO(Doc):
  do IO<Doc>:
    bs : List<&2, U32> <- Utf8.read_file(path)
    return doc_of(path, bs)

def read_docs(paths: List<&2, String>) -> IO(List<&2, Doc>):
  match paths:
    case Nil{}:
      IO.pure(List<&2, Doc>, Nil{})
    case p <> rest:
      do IO<List<&2, Doc>>:
        d : Doc <- read_doc(p)
        ds : List<&2, Doc> <- read_docs(rest)
        return d <> ds

# log
# ---

# A revision with what the log prints of it.
type Entry is Data:
  Entry{id: String, change: String, author: String, when: String, message: String}

def entry(d: Doc, parsed: Result<&2, &2, String, Rev.Rev>) -> Maybe<&2, Entry>:
  match d parsed:
    case Doc{path, id, text} Done{Rev.Rev{change, parents, supersedes, author, when, rb, r, facts, message}}:
      Some{Entry{id, change, author, when, message}}
    case _ _:
      None{}

def push_entry(e: Maybe<&2, Entry>, rest: List<&2, Entry>) -> List<&2, Entry>:
  match e:
    case None{}:
      rest
    case Some{x}:
      x <> rest

def entries(ds: List<&2, Doc>) -> List<&2, Entry>:
  match ds:
    case Nil{}:
      Nil{}
    case Doc{path, id, +text} <> rest:
      push_entry(entry(Doc{path, id, text}, Rev.parse(text)), entries(rest))

def revision_of(d: Doc, parsed: Result<&2, &2, String, Rev.Rev>) -> Maybe<&2, Rev.Revision>:
  match d parsed:
    case Doc{path, id, text} Done{r}:
      Some{Rev.of_doc(id, r)}
    case _ _:
      None{}

def add_revision(h: Rev.History(), r: Maybe<&2, Rev.Revision>) -> Rev.History():
  match r:
    case None{}:
      h
    case Some{rev}:
      Rev.insert(h, rev)

def history(ds: List<&2, Doc>, h: Rev.History()) -> Rev.History():
  match ds:
    case Nil{}:
      h
    case Doc{path, id, +text} <> rest:
      history(rest, add_revision(h, revision_of(Doc{path, id, text}, Rev.parse(text))))

def first_line.of(parts: List<&2, String>) -> String:
  match parts:
    case Nil{}:
      SNil{}
    case h <> t:
      h

def first_line(s: String) -> String:
  first_line.of(String.split(s, '\n'))

def when_of(e: Entry) -> String:
  match e:
    case Entry{id, change, author, when, message}:
      when

def later(a: Entry, b: Entry) -> Bool:
  String.is_ge(when_of(a), when_of(b))

def marks(+id: String, +heads: List<&2, String>, +gone: List<&2, String>) -> String:
  Bool.pick(String, Rev.member(heads, id), "  (head)", SNil{}) ++ Bool.pick(String, Rev.member(gone, id), "  (superseded)", SNil{})

def print_entry(e: Entry, +heads: List<&2, String>, +gone: List<&2, String>) -> IO(Unit):
  match e:
    case Entry{+id, change, author, when, message}:
      do IO<Unit>:
        IO.print(String.take(change, 8n) ++ "  " ++ String.take(id, 8n) ++ marks(id, heads, gone))
        IO.print("    " ++ author ++ "  " ++ when)
        IO.print("    " ++ first_line(message))
        IO.print(SNil{})

def print_entries(es: List<&2, Entry>, +heads: List<&2, String>, +gone: List<&2, String>) -> IO(Unit):
  match es:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case e <> rest:
      do IO<Unit>:
        print_entry(e, heads, gone)
        print_entries(rest, heads, gone)

def print_missing(ids: List<&2, String>) -> IO(Unit):
  match ids:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case id <> rest:
      do IO<Unit>:
        IO.print("missing parent " ++ String.take(id, 12n) ++ ": named, and not among these documents")
        print_missing(rest)

def log.of(+ds: List<&2, Doc>) -> IO(Unit):
  +h = history(ds, Rev.empty())
  do IO<Unit>:
    print_entries(List.sort(~Entry, ~(a => b => later(a, b)), entries(ds)), Rev.heads(h), Rev.superseded(h))
    print_missing(Rev.missing_parents(h))

def log(paths: List<&2, String>) -> IO(Unit):
  do IO<Unit>:
    ds : List<&2, Doc> <- read_docs(paths)
    log.of(ds)

# check
# -----

# What a file in a store is, told by its name: a revision, an operation
# document, or a payload, which has no grammar and only a digest.
def check_rev(+id: String, parsed: Result<&2, &2, String, Rev.Rev>) -> String:
  match parsed:
    case Fail{e}:
      "refused  " ++ String.take(id, 12n) ++ "  " ++ e
    case Done{r}:
      "revision " ++ String.take(id, 12n) ++ "  change " ++ String.take(Rev.change_of(Rev.of_doc(id, r)), 8n)

def result_note(r: Maybe<&2, String>) -> String:
  match r:
    case None{}:
      SNil{}
    case Some{d}:
      ", producing " ++ String.take(d, 12n)

def check_ops.of(+id: String, parsed: Result<&2, &2, String, Ops.Doc>) -> String:
  match parsed:
    case Fail{e}:
      "refused  " ++ String.take(id, 12n) ++ "  " ++ e
    case Done{Ops.Doc{forgets, result, ops}}:
      "edit     " ++ String.take(id, 12n) ++ "  " ++ Nat.show(List.length(&2, Ops.Op, ops)) ++ " operations" ++ result_note(result)

def doc_id(d: Doc) -> String:
  match d:
    case Doc{path, id, text}:
      id

def doc_text(d: Doc) -> String:
  match d:
    case Doc{path, id, text}:
      text

def doc_path(d: Doc) -> String:
  match d:
    case Doc{path, id, text}:
      path

def check_doc.of(+d: Doc, is_rev: Bool, is_ops: Bool) -> String:
  match is_rev:
    case True{}:
      check_rev(doc_id(d), Rev.parse(doc_text(d)))
    case False{}:
      Bool.pick(String, is_ops, check_ops.of(doc_id(d), Ops.parse(doc_text(d))), "payload  " ++ String.take(doc_id(d), 12n) ++ "  " ++ Nat.show(List.length(&2, U32, Utf8.encode(doc_text(d)))) ++ " bytes")

def check_doc(+d: Doc) -> IO(Unit):
  IO.print(check_doc.of(d, String.ends_with(doc_path(d), ".rev.txt"), String.ends_with(doc_path(d), ".ops.txt")) ++ "  " ++ doc_path(d))

def check_docs(ds: List<&2, Doc>) -> IO(Unit):
  match ds:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case d <> rest:
      do IO<Unit>:
        check_doc(d)
        check_docs(rest)

def check(paths: List<&2, String>) -> IO(Unit):
  do IO<Unit>:
    ds : List<&2, Doc> <- read_docs(paths)
    +ds2 : List<&2, Doc> = ds
    check_docs(ds2)
    print_missing(Rev.missing_parents(history(ds2, Rev.empty())))

# replay
# ------

def replay.step(state: Result<&2, &2, String, List<&2, Ops.Item>>, parsed: Result<&2, &2, String, Ops.Doc>) -> Result<&2, &2, String, List<&2, Ops.Item>>:
  do Result<&2, &2, String, List<&2, Ops.Item>>:
    items : List<&2, Ops.Item> <- state
    doc : Ops.Doc <- parsed
    Ops.apply(items, doc)

# A document that is not an operation document is a payload: the file
# created whole, which decision 0017 makes the same as an insert at 0.
def replay.doc(state: Result<&2, &2, String, List<&2, Ops.Item>>, text: String, is_ops: Bool) -> Result<&2, &2, String, List<&2, Ops.Item>>:
  match is_ops:
    case True{}:
      replay.step(state, Ops.parse(text))
    case False{}:
      Done{Ops.from_text(text)}

def replay.go(ds: List<&2, Doc>, state: Result<&2, &2, String, List<&2, Ops.Item>>) -> Result<&2, &2, String, List<&2, Ops.Item>>:
  match ds:
    case Nil{}:
      state
    case Doc{path, id, text} <> rest:
      replay.go(rest, replay.doc(state, text, String.ends_with(path, ".ops.txt")))

def replay.print(r: Result<&2, &2, String, List<&2, Ops.Item>>) -> IO(Unit):
  match r:
    case Fail{e}:
      IO.die(Unit, 1, e)
    case Done{items}:
      IO.write(Ops.text(items))

def replay(paths: List<&2, String>) -> IO(Unit):
  do IO<Unit>:
    ds : List<&2, Doc> <- read_docs(paths)
    replay.print(replay.go(ds, Done{Nil{}}))

# diff
# ----

def diff.print(d: Maybe<&2, Ops.Doc>) -> IO(Unit):
  match d:
    case None{}:
      IO.print("the two files agree")
    case Some{doc}:
      IO.write(Ops.write(doc))

def diff(parent: String, child: String) -> IO(Unit):
  do IO<Unit>:
    p : Doc <- read_doc(parent)
    c : Doc <- read_doc(child)
    diff.print(Ops.diff(Ops.from_text(doc_text(p)), Ops.from_text(doc_text(c))))

# main
# ----

def usage() -> IO(Unit):
  IO.die(Unit, 2, "usage: log <rev docs..> | check <docs..> | replay <ops docs..> | diff <parent> <child>")

def dispatch(args: List<&2, String>) -> IO(Unit):
  match args:
    case "log" <> paths:
      log(paths)
    case "check" <> paths:
      check(paths)
    case "replay" <> paths:
      replay(paths)
    case "diff" <> parent <> child <> Nil{}:
      diff(parent, child)
    case _:
      usage()

def reusable(xs: List<&1, String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case h <> t:
      h <> reusable(t)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    dispatch(reusable(args))
