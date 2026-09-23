# Where the store is and what it holds: the questions Base cannot answer,
# asked of the host through the adapter in `ffi/`. `RUNTIME.md` says why the
# boundary sits here and nowhere lower.
#
# None of these effects decides anything: the Bend side reads the documents,
# hashes them, parses them, and says what they mean.
#
# What is read is what a command needs. A store's `revisions/` is small and
# every command wants the whole of it; its `operations/` holds the payloads,
# which are most of the bytes a store has and are not a command's business
# unless it was asked for one. So a revision is read by its path, and an
# operation document is read only once some revision has named it — found by
# the digest it is named by, which is `Store.at`'s question and decision
# 0036's answer.

import Base
import ./utf8.bend as Utf8
import ./sha256.bend as Sha

# The `history` directory holding a `historica.txt`, here or above `from`;
# an empty `from` is the current directory.
def Store.locate(from: String) -> IO(Result<&1, &1, U32 & String, String>):
  import "./ffi/store_locate.c"
  import "./ffi/store_locate.js"

# Every file under `revisions/` and `operations/`, relative to the root,
# sorted, one per line: the root, then — to walk fewer — the document
# directories wanted, a line each.
def Store.list(query: String) -> IO(Result<&1, &1, U32 & String, String>):
  import "./ffi/store_list.c"
  import "./ffi/store_list.js"

# Where the bytes with each digest are: the root, then a digest a line, and
# back a path a line — relative to the root, or `-` for a digest this store
# holds nothing for. A path, never a document: what is at it is read and
# hashed here, and refused where its bytes are not the bytes asked for.
def Store.at(query: String) -> IO(Result<&1, &1, U32 & String, String>):
  import "./ffi/store_at.c"
  import "./ffi/store_at.js"

# The digest and the byte count of each file: the root, then a path a line,
# and back `<digest> <size>` a line, or `- 0` for a file that will not read.
# For the one thing with no grammar — a payload, whose bytes say nothing a
# reader here would parse — so that `check` can name it without Bend reading
# fifty megabytes to say how many there are.
def Store.digests(query: String) -> IO(Result<&1, &1, U32 & String, String>):
  import "./ffi/store_digests.c"
  import "./ffi/store_digests.js"

# One directory of the folder beside the store, an entry a line in name
# order, each saying what it is without following it: `d <name>`,
# `f <x> <size> <name>`, `l <name>` and its target on the next line, `L`
# for a link whose target cannot be spelled, `o` for anything else, `u` for
# a name that is not UTF-8. What is tracked is decided here, by `folder.bend`.
def Store.folder(dir: String) -> IO(Result<&1, &1, U32 & String, String>):
  import "./ffi/store_folder.c"
  import "./ffi/store_folder.js"

# One document read from disk: where it was, the digest of its bytes — the
# only name it has — how many bytes, and its text. A payload of bytes that
# is not UTF-8 decodes to something, and the count is of the bytes.
type Doc is Data:
  Doc{path: String, id: String, size: Nat, text: String}

# The byte count is walked once, here, and handed to the hash and the
# decoder, which would otherwise each walk the list again to find it.
def doc_of.sized(path: String, +bs: List<&2, U32>, +n: Nat) -> Doc:
  Doc{path, Sha.digest.sized(bs, n), n, Utf8.decode.sized(bs, n)}

def doc_of(path: String, +bs: List<&2, U32>) -> Doc:
  doc_of.sized(path, bs, List.length(&2, U32, bs))

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

# A listing without the empty line an empty listing is.
def kept(ls: List<&2, String>) -> List<&2, String>:
  match ls:
    case Nil{}:
      Nil{}
    case SNil{} <> rest:
      kept(rest)
    case l <> rest:
      l <> kept(rest)

# Every path the store holds, relative to the root, sorted.
def listing(+root: String) -> IO(List<&2, String>):
  do IO<List<&2, String>>:
    text : String <- IO.try(String, Store.list(root))
    return kept(String.lines(text))

# Every revision document the store holds, read and named by its own bytes.
# The whole of `revisions/` and none of `operations/`: this is the graph, and
# there is no command that does not want the whole of it. Only `revisions/`
# is listed, too — `operations/` is most of a store's paths, and a listing
# crosses the boundary a character a cell.
def revisions(+root: String) -> IO(List<&2, Doc>):
  do IO<List<&2, Doc>>:
    text : String <- IO.try(String, Store.list(root ++ "\nrevisions"))
    read_docs(under(root, String.lines(text)))

# Every file under `names/`, relative to the root, sorted: what may be a
# bookmark. A bookmark is not named by its digest, so what is read here is
# text and nothing more; `bookmark.bend` says which files are bookmarks.
def name_paths(+root: String) -> IO(List<&2, String>):
  do IO<List<&2, String>>:
    text : String <- IO.try(String, Store.list(root ++ "\nnames"))
    return kept(String.lines(text))

# The rule files of `skipped/`, relative to the root, in path order.
def skipped_paths(+root: String) -> IO(List<&2, String>):
  do IO<List<&2, String>>:
    text : String <- IO.try(String, Store.list(root ++ "\nskipped"))
    return kept(String.lines(text))

# One directory of the folder, as `Store.folder` lists it.
def listing_of(dir: String) -> IO(Result<&1, &1, U32 & String, String>):
  Store.folder(dir)

def read_text(path: String) -> IO(String):
  do IO<String>:
    bs : List<&2, U32> <- Utf8.read_file(path)
    return Utf8.decode(bs)

# The documents these digests name, read — and hashed here, so that a path
# the host offered for a digest is believed only where its bytes are that
# digest. A digest the store holds nothing for yields no document, which is
# what the caller reports.
def at.paths(+root: String, ps: List<&2, String>) -> List<&2, String>:
  match ps:
    case Nil{}:
      Nil{}
    case "-" <> rest:
      at.paths(root, rest)
    case SNil{} <> rest:
      at.paths(root, rest)
    case p <> rest:
      (root ++ "/" ++ p) <> at.paths(root, rest)

def fetch.of(+root: String, digests: List<&2, String>) -> IO(List<&2, Doc>):
  do IO<List<&2, Doc>>:
    answer : String <- IO.try(String, Store.at(root ++ "\n" ++ String.join(digests, "\n")))
    read_docs(at.paths(root, String.split(answer, '\n')))

def fetch(+root: String, digests: List<&2, String>) -> IO(List<&2, Doc>):
  match digests:
    case Nil{}:
      IO.pure(List<&2, Doc>, Nil{})
    case +some:
      fetch.of(root, some)

# Where the bytes with each of these digests are, relative to the root, or
# `-`: the host's answer, not yet believed.
def located(+root: String, digests: List<&2, String>) -> IO(List<&2, String>):
  match digests:
    case Nil{}:
      IO.pure(List<&2, String>, Nil{})
    case +some:
      do IO<List<&2, String>>:
        answer : String <- IO.try(String, Store.at(root ++ "\n" ++ String.join(some, "\n")))
        return String.split(answer, '\n')

# `<digest> <size>` for each of these paths, in the order they were given.
def stats.of(+root: String, paths: List<&2, String>) -> IO(List<&2, String>):
  do IO<List<&2, String>>:
    answer : String <- IO.try(String, Store.digests(root ++ "\n" ++ String.join(paths, "\n")))
    return String.split(answer, '\n')

def stats(+root: String, paths: List<&2, String>) -> IO(List<&2, String>):
  match paths:
    case Nil{}:
      IO.pure(List<&2, String>, Nil{})
    case +some:
      stats.of(root, some)

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
    ls : List<&2, String> <- listing(here)
    IO.print(here ++ ": " ++ Nat.show(List.length(&2, String, ls)) ++ " documents")
