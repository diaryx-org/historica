# Every revision a command reads is one a document of `revisions/` spells,
# and every document there that reads as a revision is read. A document
# the parser accepts is the revision `Rev.write` writes back byte for byte
# (`LAWS.revision_write_parse`); one it refuses only for a path not in
# normal form C is read with its causal headers and, in place of its
# facts, the refusal every reader of the whole of it meets.
import Base
import ./revision.bend as Rev
import ./store.bend as Store
import ./commands.bend as Main
import ./string_lemmas.bend as S
import ./anchor_lemmas.bend as AL
import ./revision_lemmas.bend as RevL
import ./composition_lemmas.bend as Comp

# The Rust tool's words for a path not in normal form C, at line `n`.
def refusal(+path: String, +n: Nat, +q: String) -> String:
  path ++ ": line " ++ Nat.show(n) ++ ": `" ++ q ++ "` is not a path (it is not in Unicode normal form C, which is the one spelling a store records); write components separated by `/`, relative to the repository root"

# Facts that are one refusal and nothing else, under the key no document
# can have.
def unread.is(hs: List<&2, Rev.Header>, +m: String) -> Bool:
  match hs:
    case Rev.Header{k, v} <> Nil{}:
      Bool.and(String.is_empty(k), String.eq(v, m))
    case _:
      False{}

# A revision read with other facts than its own: what it says, with these
# facts put back.
def restored(f: Main.Full, facts: List<&2, Rev.Header>) -> Rev.Rev:
  match f:
    case Main.Full{id, change, parents, supersedes, author, when, revised_by, revised, fs, message}:
      Rev.Rev{change, parents, supersedes, author, when, revised_by, revised, facts, message}

def mended.parsed(+text: String, +m: String, +f: Main.Full, p: Result<&2, &2, String, Rev.Rev>) -> Bool:
  match p:
    case Fail{e}:
      False{}
    case Done{Rev.Rev{change, parents, supersedes, author, when, revised_by, revised, facts, message}}:
      Bool.and(String.eq(Rev.write(restored(f, facts)), Rev.mended(text)), unread.is(Main.facts_of(f), m))

def mended.of(+path: String, +text: String, +f: Main.Full, u: Maybe<&2, Rev.Unnormal>) -> Bool:
  match u:
    case None{}:
      False{}
    case Some{Rev.Unnormal{+n, +q}}:
      mended.parsed(text, refusal(path, n, q), f, Rev.parse(Rev.mended(text)))

# How a document at `path` spells a revision read from it: `Rev.write`
# writes the revision back as the document, byte for byte; or the document
# names a path not in normal form C at some line, the revision's facts are
# the refusal naming that path and line, and the revision with the facts
# of the document its paths mended put back writes that mended document.
def spelled(+path: String, +text: String, +f: Main.Full) -> Bool:
  Bool.or(String.eq(Rev.write(Main.full.rev(f)), text), mended.of(path, text, f, Rev.unnormal(text)))

def filed(+root: String, ds: List<&2, Store.Doc>, +f: Main.Full) -> Bool:
  match ds:
    case Nil{}:
      False{}
    case Store.Doc{+path, +id, size, +text} <> rest:
      Bool.or(Bool.and(Store.in_revisions(root, path), Bool.and(String.eq(id, Main.id_of(f)), spelled(path, text, f))), filed(root, rest, f))

def all_filed(+root: String, +ds: List<&2, Store.Doc>, fs: List<&2, Main.Full>) -> Bool:
  match fs:
    case Nil{}:
      True{}
    case +f <> rest:
      Bool.and(filed(root, ds, f), all_filed(root, ds, rest))

# A document read whole: one the parser accepts, or one it refuses only
# for a path not in normal form C that it accepts once that path is
# mended.
def readable.of(p: Result<&2, &2, String, Rev.Rev>, u: Maybe<&2, Rev.Unnormal>, pm: Result<&2, &2, String, Rev.Rev>) -> Bool:
  Bool.or(Result.is_done(&2, &2, String, Rev.Rev, p), Bool.and(Maybe.is_some(&2, Rev.Unnormal, u), Result.is_done(&2, &2, String, Rev.Rev, pm)))

def readable(+text: String) -> Bool:
  readable.of(Rev.parse(text), Rev.unnormal(text), Rev.parse(Rev.mended(text)))

# Whether some revision read is known by `id` and spelled by the document.
def found(+path: String, +id: String, +text: String, fs: List<&2, Main.Full>) -> Bool:
  match fs:
    case Nil{}:
      False{}
    case +f <> rest:
      Bool.or(Bool.and(String.eq(Main.id_of(f), id), spelled(path, text, f)), found(path, id, text, rest))

# Every document of `revisions/` that reads whole is read.
def all_read(+root: String, ds: List<&2, Store.Doc>, +fs: List<&2, Main.Full>) -> Bool:
  match ds:
    case Nil{}:
      True{}
    case Store.Doc{+path, +id, size, +text} <> rest:
      Bool.and(Bool.or(Bool.not(Bool.and(Store.in_revisions(root, path), readable(text))), found(path, id, text, fs)), all_read(root, rest, fs))

# What the parser accepts is spelled.
def head_spelled(+path: String, +id: String, +text: String, +change: String, +parents: List<&2, String>, +supersedes: List<&2, String>, +author: String, +when: String, +revised_by: Maybe<&2, String>, +revised: Maybe<&2, String>, +facts: List<&2, Rev.Header>, +message: String, +e: {Rev.parse(text) == Done{Rev.Rev{change, parents, supersedes, author, when, revised_by, revised, facts, message}} : Result<&2, &2, String, Rev.Rev>}) -> {spelled(path, text, Main.Full{id, change, parents, supersedes, author, when, revised_by, revised, facts, message}) == True{} : Bool}:
  +sw = Equal.sym(String, Rev.write(Rev.Rev{change, parents, supersedes, author, when, revised_by, revised, facts, message}), text, RevL.write_parse(text, Rev.Rev{change, parents, supersedes, author, when, revised_by, revised, facts, message}, e))
  AL.or_left(String.eq(Rev.write(Rev.Rev{change, parents, supersedes, author, when, revised_by, revised, facts, message}), text), mended.of(path, text, Main.Full{id, change, parents, supersedes, author, when, revised_by, revised, facts, message}, Rev.unnormal(text)),
    (%sw : {String.eq(_, text) == True{} : Bool}; S.eq_refl(text)))

# What is refused only for a path not in normal form C is spelled as the
# refusal, over what the mended document says.
def unread_spelled(+path: String, +id: String, +text: String, +n: Nat, +q: String, +change: String, +parents: List<&2, String>, +supersedes: List<&2, String>, +author: String, +when: String, +revised_by: Maybe<&2, String>, +revised: Maybe<&2, String>, +facts: List<&2, Rev.Header>, +message: String, +eu: {Rev.unnormal(text) == Some{Rev.Unnormal{n, q}} : Maybe<&2, Rev.Unnormal>}, +ep: {Rev.parse(Rev.mended(text)) == Done{Rev.Rev{change, parents, supersedes, author, when, revised_by, revised, facts, message}} : Result<&2, &2, String, Rev.Rev>}) -> {spelled(path, text, Main.Full{id, change, parents, supersedes, author, when, revised_by, revised, [Rev.Header{SNil{}, refusal(path, n, q)}], message}) == True{} : Bool}:
  AL.or_right(String.eq(Rev.write(Main.full.rev(Main.Full{id, change, parents, supersedes, author, when, revised_by, revised, [Rev.Header{SNil{}, refusal(path, n, q)}], message})), text), mended.of(path, text, Main.Full{id, change, parents, supersedes, author, when, revised_by, revised, [Rev.Header{SNil{}, refusal(path, n, q)}], message}, Rev.unnormal(text)),
    (%Equal.sym(Maybe<&2, Rev.Unnormal>, Rev.unnormal(text), Some{Rev.Unnormal{n, q}}, eu) : {mended.of(path, text, Main.Full{id, change, parents, supersedes, author, when, revised_by, revised, [Rev.Header{SNil{}, refusal(path, n, q)}], message}, _) == True{} : Bool};
     %Equal.sym(Result<&2, &2, String, Rev.Rev>, Rev.parse(Rev.mended(text)), Done{Rev.Rev{change, parents, supersedes, author, when, revised_by, revised, facts, message}}, ep) : {mended.parsed(text, refusal(path, n, q), Main.Full{id, change, parents, supersedes, author, when, revised_by, revised, [Rev.Header{SNil{}, refusal(path, n, q)}], message}, _) == True{} : Bool};
     %Equal.sym(String, Rev.write(Rev.Rev{change, parents, supersedes, author, when, revised_by, revised, facts, message}), Rev.mended(text), RevL.write_parse(Rev.mended(text), Rev.Rev{change, parents, supersedes, author, when, revised_by, revised, facts, message}, ep)) : {Bool.and(String.eq(_, Rev.mended(text)), unread.is([Rev.Header{SNil{}, refusal(path, n, q)}], refusal(path, n, q))) == True{} : Bool};
     AL.and_intro(String.eq(Rev.mended(text), Rev.mended(text)), String.eq(refusal(path, n, q), refusal(path, n, q)), S.eq_refl(Rev.mended(text)), S.eq_refl(refusal(path, n, q)))))

# One more document leaves every revision filed.
def filed_weak(+root: String, +d: Store.Doc, +ds: List<&2, Store.Doc>, +f: Main.Full, h: {filed(root, ds, f) == True{} : Bool}) -> {filed(root, d <> ds, f) == True{} : Bool}:
  match d:
    case Store.Doc{+path, +id, +size, +text}:
      AL.or_right(Bool.and(Store.in_revisions(root, path), Bool.and(String.eq(id, Main.id_of(f)), spelled(path, text, f))), filed(root, ds, f), h)

def all_weak(+root: String, +d: Store.Doc, +ds: List<&2, Store.Doc>, fs: List<&2, Main.Full>, +h: {all_filed(root, ds, fs) == True{} : Bool}) -> {all_filed(root, d <> ds, fs) == True{} : Bool}:
  match fs:
    case Nil{}:
      {==}
    case +f <> +rest:
      AL.and_intro(filed(root, d <> ds, f), all_filed(root, d <> ds, rest),
        filed_weak(root, d, ds, f, Comp.and_left(filed(root, ds, f), all_filed(root, ds, rest), h)),
        all_weak(root, d, ds, rest, Comp.and_right(filed(root, ds, f), all_filed(root, ds, rest), h)))

# A revision spelled by a document of `revisions/` under its digest is
# filed there.
def filed_head(+root: String, +path: String, +id: String, +size: Nat, +text: String, +rest: List<&2, Store.Doc>, +f: Main.Full, ein: {Store.in_revisions(root, path) == True{} : Bool}, hid: {String.eq(id, Main.id_of(f)) == True{} : Bool}, hs: {spelled(path, text, f) == True{} : Bool}) -> {filed(root, Store.Doc{path, id, size, text} <> rest, f) == True{} : Bool}:
  AL.or_left(Bool.and(Store.in_revisions(root, path), Bool.and(String.eq(id, Main.id_of(f)), spelled(path, text, f))), filed(root, rest, f),
    AL.and_intro(Store.in_revisions(root, path), Bool.and(String.eq(id, Main.id_of(f)), spelled(path, text, f)), ein,
      AL.and_intro(String.eq(id, Main.id_of(f)), spelled(path, text, f), hid, hs)))

def mended_step(+root: String, +path: String, +id: String, +size: Nat, +text: String, +rest: List<&2, Store.Doc>, +n: Nat, +q: String, p: Result<&2, &2, String, Rev.Rev>, +eu: {Rev.unnormal(text) == Some{Rev.Unnormal{n, q}} : Maybe<&2, Rev.Unnormal>}, +ep: {Rev.parse(Rev.mended(text)) == p : Result<&2, &2, String, Rev.Rev>}, +ein: {Store.in_revisions(root, path) == True{} : Bool}, +ih: {all_filed(root, rest, Main.fulls(root, rest)) == True{} : Bool}) -> {all_filed(root, Store.Doc{path, id, size, text} <> rest, Main.push_full(Main.full.unread(id, refusal(path, n, q), p), Main.fulls(root, rest))) == True{} : Bool}:
  match p:
    case Fail{x}:
      all_weak(root, Store.Doc{path, id, size, text}, rest, Main.fulls(root, rest), ih)
    case Done{Rev.Rev{+change, +parents, +supersedes, +author, +when, +revised_by, +revised, +facts, +message}}:
      AL.and_intro(filed(root, Store.Doc{path, id, size, text} <> rest, Main.Full{id, change, parents, supersedes, author, when, revised_by, revised, [Rev.Header{SNil{}, refusal(path, n, q)}], message}), all_filed(root, Store.Doc{path, id, size, text} <> rest, Main.fulls(root, rest)),
        filed_head(root, path, id, size, text, rest, Main.Full{id, change, parents, supersedes, author, when, revised_by, revised, [Rev.Header{SNil{}, refusal(path, n, q)}], message}, ein, S.eq_refl(id), unread_spelled(path, id, text, n, q, change, parents, supersedes, author, when, revised_by, revised, facts, message, eu, ep)),
        all_weak(root, Store.Doc{path, id, size, text}, rest, Main.fulls(root, rest), ih))

def unnormal_step(+root: String, +path: String, +id: String, +size: Nat, +text: String, +rest: List<&2, Store.Doc>, u: Maybe<&2, Rev.Unnormal>, +eu: {Rev.unnormal(text) == u : Maybe<&2, Rev.Unnormal>}, +ein: {Store.in_revisions(root, path) == True{} : Bool}, +ih: {all_filed(root, rest, Main.fulls(root, rest)) == True{} : Bool}) -> {all_filed(root, Store.Doc{path, id, size, text} <> rest, Main.push_full(Main.full.unnormal(id, path, text, u), Main.fulls(root, rest))) == True{} : Bool}:
  match u:
    case None{}:
      all_weak(root, Store.Doc{path, id, size, text}, rest, Main.fulls(root, rest), ih)
    case Some{Rev.Unnormal{+n, +q}}:
      mended_step(root, path, id, size, text, rest, n, q, Rev.parse(Rev.mended(text)), eu, {==}, ein, ih)

# One document read: a revision where it is filed under `revisions/` and
# reads whole, nothing otherwise.
def parsed_step(+root: String, +path: String, +id: String, +size: Nat, +text: String, +rest: List<&2, Store.Doc>, p: Result<&2, &2, String, Rev.Rev>, +ep: {Rev.parse(text) == p : Result<&2, &2, String, Rev.Rev>}, +ein: {Store.in_revisions(root, path) == True{} : Bool}, +ih: {all_filed(root, rest, Main.fulls(root, rest)) == True{} : Bool}) -> {all_filed(root, Store.Doc{path, id, size, text} <> rest, Main.push_full(Main.full.read(id, path, text, p), Main.fulls(root, rest))) == True{} : Bool}:
  match p:
    case Fail{x}:
      unnormal_step(root, path, id, size, text, rest, Rev.unnormal(text), {==}, ein, ih)
    case Done{Rev.Rev{+change, +parents, +supersedes, +author, +when, +revised_by, +revised, +facts, +message}}:
      AL.and_intro(filed(root, Store.Doc{path, id, size, text} <> rest, Main.Full{id, change, parents, supersedes, author, when, revised_by, revised, facts, message}), all_filed(root, Store.Doc{path, id, size, text} <> rest, Main.fulls(root, rest)),
        filed_head(root, path, id, size, text, rest, Main.Full{id, change, parents, supersedes, author, when, revised_by, revised, facts, message}, ein, S.eq_refl(id), head_spelled(path, id, text, change, parents, supersedes, author, when, revised_by, revised, facts, message, ep)),
        all_weak(root, Store.Doc{path, id, size, text}, rest, Main.fulls(root, rest), ih))

def doc_step(+root: String, +path: String, +id: String, +size: Nat, +text: String, +rest: List<&2, Store.Doc>, b: Bool, +eb: {Store.in_revisions(root, path) == b : Bool}, +ih: {all_filed(root, rest, Main.fulls(root, rest)) == True{} : Bool}) -> {all_filed(root, Store.Doc{path, id, size, text} <> rest, Main.push_full(Bool.pick(Maybe<&2, Main.Full>, b, Main.full.read(id, path, text, Rev.parse(text)), None{}), Main.fulls(root, rest))) == True{} : Bool}:
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

# Nothing is lost
# ---------------

def found_push(+path: String, +id: String, +text: String, x: Maybe<&2, Main.Full>, +fs: List<&2, Main.Full>, h: {found(path, id, text, fs) == True{} : Bool}) -> {found(path, id, text, Main.push_full(x, fs)) == True{} : Bool}:
  match x:
    case None{}:
      h
    case Some{+f}:
      AL.or_right(Bool.and(String.eq(Main.id_of(f), id), spelled(path, text, f)), found(path, id, text, fs), h)

def read_push(+root: String, ds: List<&2, Store.Doc>, +x: Maybe<&2, Main.Full>, +fs: List<&2, Main.Full>, +h: {all_read(root, ds, fs) == True{} : Bool}) -> {all_read(root, ds, Main.push_full(x, fs)) == True{} : Bool}:
  match ds:
    case Nil{}:
      {==}
    case Store.Doc{+path, +id, size, +text} <> +rest:
      +miss = Bool.not(Bool.and(Store.in_revisions(root, path), readable(text)))
      AL.and_intro(Bool.or(miss, found(path, id, text, Main.push_full(x, fs))), all_read(root, rest, Main.push_full(x, fs)),
        AL.or_cases({Bool.or(miss, found(path, id, text, Main.push_full(x, fs))) == True{} : Bool}, miss, found(path, id, text, fs), Comp.and_left(Bool.or(miss, found(path, id, text, fs)), all_read(root, rest, fs), h),
          l => AL.or_left(miss, found(path, id, text, Main.push_full(x, fs)), l),
          r => AL.or_right(miss, found(path, id, text, Main.push_full(x, fs)), found_push(path, id, text, x, fs, r))),
        read_push(root, rest, x, fs, Comp.and_right(Bool.or(miss, found(path, id, text, fs)), all_read(root, rest, fs), h)))

def unread_found(+path: String, +id: String, +text: String, +n: Nat, +q: String, pm: Result<&2, &2, String, Rev.Rev>, +eu: {Rev.unnormal(text) == Some{Rev.Unnormal{n, q}} : Maybe<&2, Rev.Unnormal>}, +epm: {Rev.parse(Rev.mended(text)) == pm : Result<&2, &2, String, Rev.Rev>}, +fs: List<&2, Main.Full>) -> {Bool.or(Bool.not(readable.of(Fail{"x"}, Some{Rev.Unnormal{n, q}}, pm)), found(path, id, text, Main.push_full(Main.full.unread(id, refusal(path, n, q), pm), fs))) == True{} : Bool}:
  match pm:
    case Fail{e}:
      {==}
    case Done{Rev.Rev{+change, +parents, +supersedes, +author, +when, +revised_by, +revised, +facts, +message}}:
      AL.or_right(False{}, found(path, id, text, Main.Full{id, change, parents, supersedes, author, when, revised_by, revised, [Rev.Header{SNil{}, refusal(path, n, q)}], message} <> fs),
        AL.or_left(Bool.and(String.eq(id, id), spelled(path, text, Main.Full{id, change, parents, supersedes, author, when, revised_by, revised, [Rev.Header{SNil{}, refusal(path, n, q)}], message})), found(path, id, text, fs),
          AL.and_intro(String.eq(id, id), spelled(path, text, Main.Full{id, change, parents, supersedes, author, when, revised_by, revised, [Rev.Header{SNil{}, refusal(path, n, q)}], message}), S.eq_refl(id), unread_spelled(path, id, text, n, q, change, parents, supersedes, author, when, revised_by, revised, facts, message, eu, epm))))

def unnormal_found(+path: String, +id: String, +text: String, u: Maybe<&2, Rev.Unnormal>, +eu: {Rev.unnormal(text) == u : Maybe<&2, Rev.Unnormal>}, +fs: List<&2, Main.Full>) -> {Bool.or(Bool.not(readable.of(Fail{"x"}, u, Rev.parse(Rev.mended(text)))), found(path, id, text, Main.push_full(Main.full.unnormal(id, path, text, u), fs))) == True{} : Bool}:
  match u:
    case None{}:
      {==}
    case Some{Rev.Unnormal{+n, +q}}:
      unread_found(path, id, text, n, q, Rev.parse(Rev.mended(text)), eu, {==}, fs)

def parse_found(+path: String, +id: String, +text: String, p: Result<&2, &2, String, Rev.Rev>, +ep: {Rev.parse(text) == p : Result<&2, &2, String, Rev.Rev>}, +fs: List<&2, Main.Full>) -> {Bool.or(Bool.not(readable.of(p, Rev.unnormal(text), Rev.parse(Rev.mended(text)))), found(path, id, text, Main.push_full(Main.full.read(id, path, text, p), fs))) == True{} : Bool}:
  match p:
    case Fail{e}:
      unnormal_found(path, id, text, Rev.unnormal(text), {==}, fs)
    case Done{Rev.Rev{+change, +parents, +supersedes, +author, +when, +revised_by, +revised, +facts, +message}}:
      AL.or_right(False{}, found(path, id, text, Main.Full{id, change, parents, supersedes, author, when, revised_by, revised, facts, message} <> fs),
        AL.or_left(Bool.and(String.eq(id, id), spelled(path, text, Main.Full{id, change, parents, supersedes, author, when, revised_by, revised, facts, message})), found(path, id, text, fs),
          AL.and_intro(String.eq(id, id), spelled(path, text, Main.Full{id, change, parents, supersedes, author, when, revised_by, revised, facts, message}), S.eq_refl(id), head_spelled(path, id, text, change, parents, supersedes, author, when, revised_by, revised, facts, message, ep))))

def read_head(+root: String, +path: String, +id: String, +text: String, b: Bool, +eb: {Store.in_revisions(root, path) == b : Bool}, +fs: List<&2, Main.Full>) -> {Bool.or(Bool.not(Bool.and(Store.in_revisions(root, path), readable(text))), found(path, id, text, Main.push_full(Bool.pick(Maybe<&2, Main.Full>, b, Main.full.read(id, path, text, Rev.parse(text)), None{}), fs))) == True{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(Bool, Store.in_revisions(root, path), True{}, eb) : {Bool.or(Bool.not(Bool.and(_, readable(text))), found(path, id, text, Main.push_full(Main.full.read(id, path, text, Rev.parse(text)), fs))) == True{} : Bool}
      parse_found(path, id, text, Rev.parse(text), {==}, fs)
    case False{}:
      %Equal.sym(Bool, Store.in_revisions(root, path), False{}, eb) : {Bool.or(Bool.not(Bool.and(_, readable(text))), found(path, id, text, fs)) == True{} : Bool}
      {==}

# Every document of `revisions/` that reads whole is a revision `fulls`
# reads, under its digest and spelled by it.
def fulls_read(+root: String, ds: List<&2, Store.Doc>) -> {all_read(root, ds, Main.fulls(root, ds)) == True{} : Bool}:
  match ds:
    case Nil{}:
      {==}
    case Store.Doc{+path, +id, +size, +text} <> +rest:
      +x = Bool.pick(Maybe<&2, Main.Full>, Store.in_revisions(root, path), Main.full.read(id, path, text, Rev.parse(text)), None{})
      AL.and_intro(Bool.or(Bool.not(Bool.and(Store.in_revisions(root, path), readable(text))), found(path, id, text, Main.push_full(x, Main.fulls(root, rest)))), all_read(root, rest, Main.push_full(x, Main.fulls(root, rest))),
        read_head(root, path, id, text, Store.in_revisions(root, path), {==}, Main.fulls(root, rest)),
        read_push(root, rest, x, Main.fulls(root, rest), fulls_read(root, rest)))
