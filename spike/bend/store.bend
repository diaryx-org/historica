# Where the store is and what it holds: the two questions Base cannot answer,
# asked of the host through the adapter in `ffi/`. `RUNTIME.md` says why the
# boundary sits here and nowhere lower.
#
# Both effects answer a `Result` and decide nothing: the Bend side reads the
# documents, parses them, and says what they mean.

import Base
import ./utf8.bend as Utf8
import ./sha256.bend as Sha

# The `history` directory holding a `historica.txt`, here or above `from`;
# an empty `from` is the current directory.
def Store.locate(from: String) -> IO(Result<&1, &1, U32 & String, String>):
  import "./ffi/store_locate.c"
  import "./ffi/store_locate.js"

# Every file under `revisions/` and `operations/`, relative to the root,
# sorted, one per line.
def Store.list(root: String) -> IO(Result<&1, &1, U32 & String, String>):
  import "./ffi/store_list.c"
  import "./ffi/store_list.js"

# One document read from disk: where it was, the digest of its bytes — the
# only name it has — how many bytes, and its text. A payload of bytes that
# is not UTF-8 decodes to something, and the count is of the bytes.
type Doc is Data:
  Doc{path: String, id: String, size: Nat, text: String}

def doc_of(path: String, +bs: List<&2, U32>) -> Doc:
  Doc{path, Sha.digest(bs), List.length(&2, U32, bs), Utf8.decode(bs)}

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

def path_of(d: Doc) -> String:
  match d:
    case Doc{path, id, size, text}:
      path

def id_of(d: Doc) -> String:
  match d:
    case Doc{path, id, size, text}:
      id

def size_of(d: Doc) -> Nat:
  match d:
    case Doc{path, id, size, text}:
      size

def text_of(d: Doc) -> String:
  match d:
    case Doc{path, id, size, text}:
      text

# The listing, as paths under the root; the empty line an empty listing is.
def under(+root: String, ls: List<&2, String>) -> List<&2, String>:
  match ls:
    case Nil{}:
      Nil{}
    case SNil{} <> rest:
      under(root, rest)
    case l <> rest:
      (root ++ "/" ++ l) <> under(root, rest)

def root() -> IO(String):
  IO.try(String, Store.locate(SNil{}))

# Every document the store at `root` holds, read.
def documents(+root: String) -> IO(List<&2, Doc>):
  do IO<List<&2, Doc>>:
    listing : String <- IO.try(String, Store.list(root))
    read_docs(under(root, String.lines(listing)))

# The relative path of a document under the root, and which directory it is
# in: what `revisions/` holds is a revision, whatever its name.
def relative.of(+path: String, cut: Nat, inside: Bool) -> String:
  match inside:
    case True{}:
      String.drop(path, cut)
    case False{}:
      path

def relative(+root: String, +path: String) -> String:
  relative.of(path, 1n+String.length(root), String.starts_with(path, root ++ "/"))

def in_revisions(+root: String, +path: String) -> Bool:
  String.starts_with(relative(root, path), "revisions/")

def main() -> IO(Unit):
  do IO<Unit>:
    r : String <- root()
    +here : String = r
    ds : List<&2, Doc> <- documents(here)
    IO.print(here ++ ": " ++ Nat.show(List.length(&2, Doc, ds)) ++ " documents")
