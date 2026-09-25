# Every revision a command reads is one a document of `revisions/` spells:
# filed there under the digest it is known by, and what `Rev.write` writes,
# byte for byte, from what the revision says. `fulls` keeps the documents
# the parser accepts and nothing else, and the writer reproduces what the
# parser accepted (`LAWS.revision_write_parse`).
import Base
import ./revision.bend as Rev
import ./store.bend as Store
import ./commands.bend as Main
import ./string_lemmas.bend as S
import ./anchor_lemmas.bend as AL
import ./revision_lemmas.bend as RevL
import ./composition_lemmas.bend as Comp

# Where `LAWS.revisions_read_are_their_documents` looks: whether one of the
# documents is filed under `revisions/` with the revision's digest and is
# what `Rev.write` writes of what the revision says.
def filed(+root: String, ds: List<&2, Store.Doc>, +f: Main.Full) -> Bool:
  match ds:
    case Nil{}:
      False{}
    case Store.Doc{+path, +id, size, +text} <> rest:
      Bool.or(Bool.and(Store.in_revisions(root, path), Bool.and(String.eq(id, Main.id_of(f)), String.eq(Rev.write(Main.full.rev(f)), text))), filed(root, rest, f))

def all_filed(+root: String, +ds: List<&2, Store.Doc>, fs: List<&2, Main.Full>) -> Bool:
  match fs:
    case Nil{}:
      True{}
    case +f <> rest:
      Bool.and(filed(root, ds, f), all_filed(root, ds, rest))

# One more document leaves every revision filed.
def filed_weak(+root: String, +d: Store.Doc, +ds: List<&2, Store.Doc>, +f: Main.Full, h: {filed(root, ds, f) == True{} : Bool}) -> {filed(root, d <> ds, f) == True{} : Bool}:
  match d:
    case Store.Doc{+path, +id, +size, +text}:
      AL.or_right(Bool.and(Store.in_revisions(root, path), Bool.and(String.eq(id, Main.id_of(f)), String.eq(Rev.write(Main.full.rev(f)), text))), filed(root, ds, f), h)

def all_weak(+root: String, +d: Store.Doc, +ds: List<&2, Store.Doc>, fs: List<&2, Main.Full>, +h: {all_filed(root, ds, fs) == True{} : Bool}) -> {all_filed(root, d <> ds, fs) == True{} : Bool}:
  match fs:
    case Nil{}:
      {==}
    case +f <> +rest:
      AL.and_intro(filed(root, d <> ds, f), all_filed(root, d <> ds, rest),
        filed_weak(root, d, ds, f, Comp.and_left(filed(root, ds, f), all_filed(root, ds, rest), h)),
        all_weak(root, d, ds, rest, Comp.and_right(filed(root, ds, f), all_filed(root, ds, rest), h)))

# A document of `revisions/` the parser accepts spells the revision read
# from it.
def head_filed(+root: String, +path: String, +id: String, +size: Nat, +text: String, +rest: List<&2, Store.Doc>, +change: String, +parents: List<&2, String>, +supersedes: List<&2, String>, +author: String, +when: String, +revised_by: Maybe<&2, String>, +revised: Maybe<&2, String>, +facts: List<&2, Rev.Header>, +message: String, +e: {Rev.parse(text) == Done{Rev.Rev{change, parents, supersedes, author, when, revised_by, revised, facts, message}} : Result<&2, &2, String, Rev.Rev>}, +ein: {Store.in_revisions(root, path) == True{} : Bool}) -> {filed(root, Store.Doc{path, id, size, text} <> rest, Main.Full{id, change, parents, supersedes, author, when, revised_by, revised, facts, message}) == True{} : Bool}:
  +sw = Equal.sym(String, Rev.write(Rev.Rev{change, parents, supersedes, author, when, revised_by, revised, facts, message}), text, RevL.write_parse(text, Rev.Rev{change, parents, supersedes, author, when, revised_by, revised, facts, message}, e))
  AL.or_left(Bool.and(Store.in_revisions(root, path), Bool.and(String.eq(id, id), String.eq(Rev.write(Rev.Rev{change, parents, supersedes, author, when, revised_by, revised, facts, message}), text))), filed(root, rest, Main.Full{id, change, parents, supersedes, author, when, revised_by, revised, facts, message}),
    AL.and_intro(Store.in_revisions(root, path), Bool.and(String.eq(id, id), String.eq(Rev.write(Rev.Rev{change, parents, supersedes, author, when, revised_by, revised, facts, message}), text)), ein,
      AL.and_intro(String.eq(id, id), String.eq(Rev.write(Rev.Rev{change, parents, supersedes, author, when, revised_by, revised, facts, message}), text), S.eq_refl(id),
        (%sw : {String.eq(_, text) == True{} : Bool}; S.eq_refl(text)))))

# One document read: a revision where it is filed under `revisions/` and
# parses, nothing otherwise.
def parsed_step(+root: String, +path: String, +id: String, +size: Nat, +text: String, +rest: List<&2, Store.Doc>, p: Result<&2, &2, String, Rev.Rev>, +ep: {Rev.parse(text) == p : Result<&2, &2, String, Rev.Rev>}, +ein: {Store.in_revisions(root, path) == True{} : Bool}, +ih: {all_filed(root, rest, Main.fulls(root, rest)) == True{} : Bool}) -> {all_filed(root, Store.Doc{path, id, size, text} <> rest, Main.push_full(Main.full(id, p), Main.fulls(root, rest))) == True{} : Bool}:
  match p:
    case Fail{x}:
      all_weak(root, Store.Doc{path, id, size, text}, rest, Main.fulls(root, rest), ih)
    case Done{Rev.Rev{+change, +parents, +supersedes, +author, +when, +revised_by, +revised, +facts, +message}}:
      AL.and_intro(filed(root, Store.Doc{path, id, size, text} <> rest, Main.Full{id, change, parents, supersedes, author, when, revised_by, revised, facts, message}), all_filed(root, Store.Doc{path, id, size, text} <> rest, Main.fulls(root, rest)),
        head_filed(root, path, id, size, text, rest, change, parents, supersedes, author, when, revised_by, revised, facts, message, ep, ein),
        all_weak(root, Store.Doc{path, id, size, text}, rest, Main.fulls(root, rest), ih))

def doc_step(+root: String, +path: String, +id: String, +size: Nat, +text: String, +rest: List<&2, Store.Doc>, b: Bool, +eb: {Store.in_revisions(root, path) == b : Bool}, +ih: {all_filed(root, rest, Main.fulls(root, rest)) == True{} : Bool}) -> {all_filed(root, Store.Doc{path, id, size, text} <> rest, Main.push_full(Bool.pick(Maybe<&2, Main.Full>, b, Main.full(id, Rev.parse(text)), None{}), Main.fulls(root, rest))) == True{} : Bool}:
  match b:
    case True{}:
      parsed_step(root, path, id, size, text, rest, Rev.parse(text), {==}, eb, ih)
    case False{}:
      all_weak(root, Store.Doc{path, id, size, text}, rest, Main.fulls(root, rest), ih)

# Every revision `fulls` reads is one a document of `revisions/` spells.
def fulls_filed(+root: String, ds: List<&2, Store.Doc>) -> {all_filed(root, ds, Main.fulls(root, ds)) == True{} : Bool}:
  match ds:
    case Nil{}:
      {==}
    case Store.Doc{+path, +id, +size, +text} <> +rest:
      doc_step(root, path, id, size, text, rest, Store.in_revisions(root, path), {==}, fulls_filed(root, rest))
