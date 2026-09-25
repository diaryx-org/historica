# `merge [<target>...]`: what two lines of work say together, written into
# the folder.
#
# Decision 0012. Nothing conflicted is recorded and nothing is remembered:
# this lays the merge of the heads out in the folder — each file of lines
# as the walk reads it, with the renderer's fences where concurrent work
# met (`conflict.bend`), each file of bytes as the payload the tree kept,
# each link where it points — and prints the `record` line that records
# it, so the pending merge lives in the person's terminal. A file holding
# work nobody recorded is left alone and said to be.
#
# One rule decides what is joined, as the Rust tool's: what is named, and
# every current head that is not.

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
import ./conflict.bend as Conflict
import ./commands.bend as Main
import ./update.bend as Upd

# What is joined
# --------------

# Each head joined, with what a person typed for it: the spelling they gave
# a head they named, so the `record` line says their bookmark back to them,
# and the abbreviated digest of a head they did not.
def typed.has(xs: List<&2, T.Split>, +id: String) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case T.Split{+h, s} <> rest:
      Bool.or(String.eq(h, id), typed.has(rest, id))

def typed.add(+xs: List<&2, T.Split>, +id: String, +s: String) -> List<&2, T.Split>:
  Bool.pick(List<&2, T.Split>, typed.has(xs, id), xs, List.append(&2, T.Split, xs, [T.Split{id, s}]))

def typed.named(+fs: List<&2, Main.Full>, +bs: List<&2, Bm.Bookmark>, ss: List<&2, String>, +acc: List<&2, T.Split>) -> Result<&2, &2, Main.Refused, List<&2, T.Split>>:
  match ss:
    case Nil{}:
      Done{acc}
    case +s <> rest:
      do Result<&2, &2, Main.Refused, List<&2, T.Split>>:
        f : Main.Full <- Main.resolved.r(fs, bs, s)
        typed.named(fs, bs, rest, typed.add(acc, Main.id_of(f), s))

def typed.standing(hs: List<&2, String>, +acc: List<&2, T.Split>) -> List<&2, T.Split>:
  match hs:
    case Nil{}:
      acc
    case +h <> rest:
      typed.standing(rest, typed.add(acc, h, String.take(h, 12n)))

# What a joined head is sorted and found by: its digest.
def typed.key(a: T.Split) -> String:
  match a:
    case T.Split{x, s}:
      x

def typed.le(+a: T.Split, +b: T.Split) -> Bool:
  String.is_le(typed.key(a), typed.key(b))

def typed.enough(+xs: List<&2, T.Split>) -> Result<&2, &2, Main.Refused, List<&2, T.Split>>:
  Bool.pick(Result<&2, &2, Main.Refused, List<&2, T.Split>>, Nat.is_lt(List.length(&2, T.Split, xs), 2n),
    Fail{Main.Refused{1, "merging is joining two lines of work, and this store has one; name the other, or record on both sides first"}},
    Done{List.sort(~T.Split, ~(a => b => String.is_le(typed.key(a), typed.key(b))), xs)})

# What is named, and every head that is not, in digest order: divergence
# is what this command exists for, so naming one head is enough, and naming
# none is enough where divergence is the whole of what there is.
def joined.r(+fs: List<&2, Main.Full>, +bs: List<&2, Bm.Bookmark>, +ss: List<&2, String>) -> Result<&2, &2, Main.Refused, List<&2, T.Split>>:
  do Result<&2, &2, Main.Refused, List<&2, T.Split>>:
    named : List<&2, T.Split> <- typed.named(fs, bs, ss, Nil{})
    typed.enough(typed.standing(Upd.heads.sorted(fs), named))

def typed.ids(xs: List<&2, T.Split>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case T.Split{h, s} <> rest:
      h <> typed.ids(rest)

def typed.spelled(xs: List<&2, T.Split>) -> String:
  match xs:
    case Nil{}:
      SNil{}
    case T.Split{h, s} <> rest:
      " --merge " ++ s ++ typed.spelled(rest)

# Decision 0023: a head can stand on a revision somebody has since
# rewritten, and then what meets below may be that rewrite rather than work
# done twice; said before the fences, where a person meets it.
def rewritten.parents(+id: String, ps: List<&2, String>, +gone: List<&2, String>) -> List<&2, String>:
  match ps:
    case Nil{}:
      Nil{}
    case +p <> rest:
      Rev.keep(Rev.member(gone, p), String.take(id, 8n) ++ " stands on " ++ String.take(p, 8n) ++ ", which something rewrote; what meets below may be that rewrite rather than work done twice", rewritten.parents(id, rest, gone))

def rewritten.go(fs: List<&2, Main.Full>, +gone: List<&2, String>) -> List<&2, String>:
  match fs:
    case Nil{}:
      Nil{}
    case +f <> rest:
      List.append(&2, String, Bool.pick(List<&2, String>, Rev.member(gone, Main.id_of(f)), Nil{}, rewritten.parents(Main.id_of(f), Main.parents_of(f), gone)), rewritten.go(rest, gone))

def rewritten(+fs: List<&2, Main.Full>, +heads: List<&2, String>) -> List<&2, String>:
  rewritten.go(List.sort(~Main.Full, ~(a => b => String.is_le(Main.id_of(a), Main.id_of(b))), Main.among(fs, Main.reached.all(fs, heads))), Rev.superseded(Main.history(fs)))

# A path two files claim
# ----------------------

# Decision 0008 forbids the format inventing a name, so one file keeps the
# path and each other is written beside it under a name whose reason a
# person can read: the marker before the last extension, so the file still
# opens in the editor it did, and no colon, which some filesystems refuse.
def beside.named(+dir: String, +name: String, +marker: String, cut: Maybe<&2, T.Split>) -> String:
  match cut:
    case Some{T.Split{+stem, +ext}}:
      Bool.pick(String, String.is_empty(stem), dir ++ name ++ " " ++ marker, dir ++ stem ++ " " ++ marker ++ "." ++ ext)
    case None{}:
      dir ++ name ++ " " ++ marker

# The last `.` of a name: what comes before it and after.
def last_dot.go(cs: List<&2, Char>, +acc: String, found: Maybe<&2, T.Split>) -> Maybe<&2, T.Split>:
  match cs:
    case Nil{}:
      found
    case +c <> +rest:
      last_dot.go(rest, acc ++ String.from_list([c]), Bool.pick(Maybe<&2, T.Split>, Char.is_eq(c, '.'), Some{T.Split{acc, String.from_list(rest)}}, found))

def last_dot(+name: String) -> Maybe<&2, T.Split>:
  last_dot.go(String.to_list(name), SNil{}, None{})

def beside_name(+path: String, +file: String) -> String:
  +dir = Main.directory_of(path)
  +name = Folder.last_component(path)
  beside.named(Bool.pick(String, String.is_empty(dir), SNil{}, dir ++ "/"), name, "(historica " ++ String.take(file, 8n) ++ ")", last_dot(name))

def beside.files(+path: String, fs: List<&2, String>) -> List<&2, T.Split>:
  match fs:
    case Nil{}:
      Nil{}
    case +f <> rest:
      T.Split{f, beside_name(path, f)} <> beside.files(path, rest)

def beside.of(c: Tree.Contest) -> List<&2, T.Split>:
  match c:
    case Tree.Path{+p, f <> rest}:
      beside.files(p, rest)
    case _:
      Nil{}

def beside(cs: List<&2, Tree.Contest>) -> List<&2, T.Split>:
  match cs:
    case Nil{}:
      Nil{}
    case c <> rest:
      List.append(&2, T.Split, beside.of(c), beside(rest))

def split.get(xs: List<&2, T.Split>, +k: String) -> Maybe<&2, String>:
  match xs:
    case Nil{}:
      None{}
    case T.Split{+a, b} <> rest:
      Bool.pick(Maybe<&2, String>, String.eq(a, k), Some{b}, split.get(rest, k))

# `render::contest_line`, with a path several files claim said too.
def claims.at(fs: List<&2, String>) -> String:
  match fs:
    case Nil{}:
      SNil{}
    case f <> rest:
      "\n  --at " ++ f ++ "=<path>" ++ claims.at(rest)

def contest.said(c: Tree.Contest) -> Maybe<&2, String>:
  match c:
    case Tree.Path{p, +fs}:
      Some{Nat.show(List.length(&2, String, fs)) ++ " files claim " ++ p ++ "; say where each goes with --at:" ++ claims.at(fs)}
    case other:
      Main.contest.line(other)

def contests.said(cs: List<&2, Tree.Contest>) -> List<&2, String>:
  match cs:
    case Nil{}:
      Nil{}
    case c <> rest:
      Main.contest.push(contest.said(c), contests.said(rest))

# What each file comes to
# -----------------------

# One step of laying the merge out: a line to say, a file of lines or a
# payload written — with the mode the tree records — a link pointed, or the
# refusal the Rust tool stops at, after what it already wrote.
type Act is Data:
  Act.Said{line: String}
  Act.Lines{at: String, text: String, mode: Tree.Mode}
  Act.Whole{at: String, from: String, payload: String, mode: Tree.Mode}
  Act.Link{at: String, target: String}
  Act.Stop{msg: String}

# What one file takes, and whether it is one that met.
type Laid is Data:
  Laid{acts: List<&2, Act>, met: Bool}

def UNRECORDED(+at: String) -> String:
  "left " ++ at ++ " alone: it holds work nothing has recorded"

# A link: pointed where the tree says, unless it already points there.
def lay.link(+at: String, h: Upd.Held, want: Maybe<&2, String>) -> Laid:
  match want:
    case None{}:
      Laid{[Act.Said{"left " ++ at ++ " alone: it is a link naming nowhere"}], False{}}
    case Some{+s}:
      Laid{Bool.pick(List<&2, Act>, Upd.lands.link(s, h), Nil{}, [Act.Link{at, s}]), False{}}

def claims.cat(+at: String, cs: List<&2, Tree.Claim>) -> List<&2, Act>:
  match cs:
    case Nil{}:
      Nil{}
    case Tree.Claim{by, w} <> rest:
      Act.Said{"  historica cat " ++ String.take(by, 8n) ++ " " ++ at} <> claims.cat(at, rest)

def payload.claims(cs: List<&2, Tree.Contest>, +file: String) -> List<&2, Tree.Claim>:
  match cs:
    case Nil{}:
      Nil{}
    case Tree.Content{+f, +claims} <> rest:
      Bool.pick(List<&2, Tree.Claim>, String.eq(f, file), claims, payload.claims(rest, file))
    case c <> rest:
      payload.claims(rest, file)

# What stands in the folder may be written over where it is one of the
# versions being joined, or where there is nothing there to read: `held`
# is its digest, or `-`.
def unrecorded(+held: String, +known: List<&2, String>) -> Bool:
  Bool.and(Bool.not(String.eq(held, "-")), Bool.not(Rev.member(known, held)))

# A file of bytes has no lines to fence, so a contested one is said and
# left exactly as it is: the tool cannot tell a resolution from an
# oversight there.
def lay.whole(+at: String, +file: String, +cs: List<&2, Tree.Contest>, +located: Map<&2, String>, +held: String, +heads: List<&2, String>, +m: Tree.Mode, y: Maybe<&2, String>) -> Laid:
  match y:
    case None{}:
      Laid{Act.Said{"left " ++ at ++ " alone: it is contested and holds no lines"} <> claims.cat(at, payload.claims(cs, file)), True{}}
    case Some{+p}:
      +from = Main.stat_of(p, Map.get(String, SNil{}, located, p))
      Laid{Bool.pick(List<&2, Act>, String.is_empty(from), [Act.Stop{"this store does not hold the content " ++ p}],
        Bool.pick(List<&2, Act>, unrecorded(held, p <> heads), [Act.Said{UNRECORDED(at)}], [Act.Whole{at, from, p, m}])), False{}}

# A file of lines: the walk's reading, fenced where what met, unless the
# folder holds text that is neither that, nor the walk's reading unfenced,
# nor what any head leaves — work nobody has recorded. `text` is whether
# what stands is text at all; a file that is not is no one's work to keep.
def lay.lines(+at: String, +held: String, +heads: List<&2, String>, +text: Bool, +m: Tree.Mode, r: Result<&2, &2, String, Conflict.Joined>) -> Laid:
  match r:
    case Fail{e}:
      Laid{[Act.Stop{e}], False{}}
    case Done{+j}:
      +rendered = Conflict.render(j)
      Laid{Bool.pick(List<&2, Act>, Bool.and(text, unrecorded(held, Upd.text_digest(rendered) <> Upd.text_digest(Conflict.plain(j)) <> heads)), [Act.Said{UNRECORDED(at)}], [Act.Lines{at, rendered, m}]), Conflict.met(j)}

# What the folder and the store say about one file's place, gathered
# before anything is decided.
type Place is Data:
  Place{entry: Tree.Entry, at: String, held: String, link: Upd.Held, heads: List<&2, String>, text: Bool, joined: Result<&2, &2, String, Conflict.Joined>}

def lay(+t: Tree.Tree(), +cs: List<&2, Tree.Contest>, +located: Map<&2, String>, p: Place) -> Laid:
  match p:
    case Place{Tree.Entry{f, p2, Tree.Link{}, y, g, m}, +at, held, h, hs, x, r}:
      lay.link(at, h, Maybe.bind(&2, Tree.Target, String, g, x2 => Upd.materialise(t, at, x2)))
    case Place{Tree.Entry{+f, p2, Tree.Whole{}, y, g, +m}, +at, +held, h, +hs, x, r}:
      lay.whole(at, f, cs, located, held, hs, m, y)
    case Place{Tree.Entry{f, p2, Tree.Lines{}, y, g, +m}, +at, +held, h, +hs, +x, r}:
      lay.lines(at, held, hs, x, m, r)

# Every file of the merged tree, in file order: the acts to perform, and
# how many files hold work that met.
type Lay is Data:
  Lay{acts: List<&2, Act>, met: Nat}

def lay.join(a: Laid, b: Lay) -> Lay:
  match a b:
    case Laid{x, m} Lay{y, n}:
      Lay{List.append(&2, Act, x, y), Nat.add(Bool.pick(Nat, m, 1n, 0n), n)}

def lay.all(+t: Tree.Tree(), +cs: List<&2, Tree.Contest>, +located: Map<&2, String>, ps: List<&2, Place>) -> Lay:
  match ps:
    case Nil{}:
      Lay{Nil{}, 0n}
    case p <> rest:
      lay.join(lay(t, cs, located, p), lay.all(t, cs, located, rest))

# Saying it
# ---------

# What follows the lines each file owed: how the paths several files claim
# were settled, how many files hold work that met, and the command that
# records the merge — every head it joined, named as a person typed it, and
# each file written beside a path where this merge wrote it, in full, since
# `--at` names a file against a survey.
def settling(xs: List<&2, T.Split>) -> String:
  match xs:
    case Nil{}:
      SNil{}
    case T.Split{f, p} <> rest:
      " --at \"" ++ f ++ "=" ++ p ++ "\"" ++ settling(rest)

def met.said(+n: Nat, +besides: Bool) -> String:
  Bool.pick(String, Nat.is_gt(n, 0n), Nat.show(n) ++ " file" ++ Bool.pick(String, Nat.is_eq(n, 1n), " holds", "s hold") ++ " work that met; resolve it, delete the lines historica wrote, and record it with:",
    Bool.pick(String, besides, "no lines met; record it with:", "nothing is contested; record it with:"))

def closing(+typed: List<&2, T.Split>, +bs: List<&2, T.Split>, +n: Nat) -> List<&2, String>:
  +besides = Bool.not(List.is_empty(&2, T.Split, bs))
  List.append(&2, String, Bool.pick(List<&2, String>, besides, ["a path two files claim is settled below by where this merge wrote them; type other paths there if you would rather"], Nil{}),
    [met.said(n, besides), "  historica record" ++ typed.spelled(typed) ++ settling(List.sort(~T.Split, ~(a => b => typed.le(a, b)), bs)) ++ " -m <message>"])

# Doing it
# --------

def made(+at: String, +m: Tree.Mode, was: String) -> List<&2, String>:
  Bool.pick(List<&2, String>, Bool.xor(String.eq(was, "1"), Upd.runs(m)), ["made " ++ at ++ " " ++ Tree.mode_show(m)], Nil{})

def moded(+repo: String, +at: String, +m: Tree.Mode) -> IO(List<&2, String>):
  do IO<List<&2, String>>:
    r : Result<&1, &1, U32 & String, String> <- Store.chmodded(Folder.joined(repo, at) ++ "\n" ++ Bool.pick(String, Upd.runs(m), "1", "0"))
    was : String <- Upd.done.io(r)
    return made(at, m, was)

# Each act in turn; what it says is said once they are all done, and a
# refusal stops there, with what was written before it left written. A
# file of lines is written in place, through a link standing at its path,
# as the Rust tool's `fs::write` writes it; a payload lands as a new file.
def perform(+repo: String, acts: List<&2, Act>) -> IO(List<&2, String>):
  match acts:
    case Nil{}:
      IO.pure(List<&2, String>, Nil{})
    case Act.Said{+l} <> rest:
      do IO<List<&2, String>>:
        more : List<&2, String> <- perform(repo, rest)
        return l <> more
    case Act.Stop{msg} <> rest:
      Main.die(List<&2, String>, 1, msg)
    case Act.Link{+at, +target} <> rest:
      do IO<List<&2, String>>:
        r : Result<&1, &1, U32 & String, String> <- Store.linked(Folder.joined(repo, at) ++ "\n" ++ target)
        a : String <- Upd.done.io(r)
        more : List<&2, String> <- perform(repo, rest)
        return ("pointed " ++ at ++ " at " ++ target) <> more
    case Act.Lines{+at, text, +m} <> rest:
      do IO<List<&2, String>>:
        r : Result<&1, &1, U32 & String, String> <- Store.written_through(Folder.joined(repo, at) ++ "\n" ++ text)
        a : String <- Upd.done.io(r)
        set : List<&2, String> <- moded(repo, at, m)
        more : List<&2, String> <- perform(repo, rest)
        return List.append(&2, String, set, more)
    case Act.Whole{+at, from, p, +m} <> rest:
      do IO<List<&2, String>>:
        r : Result<&1, &1, U32 & String, String> <- Store.laid(from ++ "\n" ++ Folder.joined(repo, at) ++ "\n" ++ p)
        a : String <- Upd.done.io(r)
        set : List<&2, String> <- moded(repo, at, m)
        more : List<&2, String> <- perform(repo, rest)
        return List.append(&2, String, set, more)

# Reading what the merge needs
# ----------------------------

def at.of(+bs: List<&2, T.Split>, +e: Tree.Entry) -> String:
  Maybe.default(&2, String, split.get(bs, Tree.entry_file(e)), Tree.entry_path(e))

def ats(+bs: List<&2, T.Split>, es: List<&2, Tree.Entry>) -> List<&2, String>:
  match es:
    case Nil{}:
      Nil{}
    case +e <> rest:
      at.of(bs, e) <> ats(bs, rest)

# What each head leaves one file as, as a digest: the walk of its own
# ancestry for a file of lines, the payload its tree names for one of bytes.
def head.lines(+fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +file: String, hs: List<&2, String>) -> List<&2, String>:
  match hs:
    case Nil{}:
      Nil{}
    case +h <> rest:
      Upd.push(Upd.recorded.lines(Main.walked(fs, ds, h, file)), head.lines(fs, ds, file, rest))

def head.payload(+file: String, r: Result<&2, &2, Main.Refused, Tree.Tree()>) -> Maybe<&2, String>:
  match r:
    case Done{t}:
      Maybe.bind(&2, Tree.Entry, String, Tree.lookup(t, file), e => Tree.entry_payload(e))
    case Fail{e}:
      None{}

def head.wholes(+fs: List<&2, Main.Full>, +file: String, hs: List<&2, String>) -> List<&2, String>:
  match hs:
    case Nil{}:
      Nil{}
    case +h <> rest:
      Upd.push(head.payload(file, Main.tree.r(fs, h)), head.wholes(fs, file, rest))

def is_lines(k: Tree.FileKind) -> Bool:
  match k:
    case Tree.Lines{}:
      True{}
    case _:
      False{}

def heads.of(+fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +heads: List<&2, String>, +e: Tree.Entry) -> List<&2, String>:
  Bool.pick(List<&2, String>, is_lines(Tree.entry_kind(e)), head.lines(fs, ds, Tree.entry_file(e), heads), head.wholes(fs, Tree.entry_file(e), heads))

def joined.of(+fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +heads: List<&2, String>, +e: Tree.Entry) -> Result<&2, &2, String, Conflict.Joined>:
  Bool.pick(Result<&2, &2, String, Conflict.Joined>, is_lines(Tree.entry_kind(e)), Main.joined(fs, ds, heads, Tree.entry_file(e)), Fail{SNil{}})

def places(+fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +heads: List<&2, String>, +bs: List<&2, T.Split>, +dg: Map<&2, String>, +ls: Map<&2, String>, +texts: Map<&2, String>, es: List<&2, Tree.Entry>) -> List<&2, Place>:
  match es:
    case Nil{}:
      Nil{}
    case +e <> rest:
      +at = at.of(bs, e)
      Place{e, at, Main.status.folder_digest(dg, at), Upd.held.of(ls, at, None{}), heads.of(fs, ds, heads, e), Bool.not(String.eq(Main.stat_of(at, Map.get(String, SNil{}, texts, at)), "0")), joined.of(fs, ds, heads, e)} <> places(fs, ds, heads, bs, dg, ls, texts, rest)

# The files whose text decides whether they are left alone: bytes that
# are none of the versions being joined.
def undecided(ps: List<&2, Place>) -> List<&2, String>:
  match ps:
    case Nil{}:
      Nil{}
    case Place{Tree.Entry{f, p, Tree.Lines{}, y, g, m}, +at, +held, h, +hs, x, Done{+j}} <> rest:
      Rev.keep(unrecorded(held, Upd.text_digest(Conflict.render(j)) <> Upd.text_digest(Conflict.plain(j)) <> hs), at, undecided(rest))
    case p <> rest:
      undecided(rest)

def texts(+repo: String, ps: List<&2, String>, m: Map<&2, String>) -> IO(Map<&2, String>):
  match ps:
    case Nil{}:
      IO.pure(Map<&2, String>, m)
    case +p <> rest:
      do IO<Map<&2, String>>:
        bs : List<&2, U32> <- Utf8.read_file(Folder.joined(repo, p))
        texts(repo, rest, Map.set(&2, String, m, p, Bool.pick(String, Folder.is_utf8(bs), "1", "0")))

def payloads(es: List<&2, Tree.Entry>) -> List<&2, String>:
  match es:
    case Nil{}:
      Nil{}
    case Tree.Entry{f, p, Tree.Whole{}, Some{d}, g, m} <> rest:
      d <> payloads(rest)
    case e <> rest:
      payloads(rest)

def links.at(+bs: List<&2, T.Split>, es: List<&2, Tree.Entry>) -> List<&2, String>:
  match es:
    case Nil{}:
      Nil{}
    case Tree.Entry{+f, +p, Tree.Link{}, y, g, m} <> rest:
      Main.directory_of(at.of(bs, Tree.Entry{f, p, Tree.Link{}, y, g, m})) <> links.at(bs, rest)
    case e <> rest:
      links.at(bs, rest)

def lined(es: List<&2, Tree.Entry>) -> List<&2, String>:
  match es:
    case Nil{}:
      Nil{}
    case Tree.Entry{f, p, Tree.Lines{}, y, g, m} <> rest:
      f <> lined(rest)
    case e <> rest:
      lined(rest)

def lay.acts(l: Lay) -> List<&2, Act>:
  match l:
    case Lay{a, n}:
      a

def lay.met(l: Lay) -> Nat:
  match l:
    case Lay{a, n}:
      n

def merge.at(+r: String, +fs: List<&2, Main.Full>, +typed: List<&2, T.Split>) -> IO(Unit):
  +repo = Main.repository(r)
  +heads = typed.ids(typed)
  do IO<Unit>:
    m : Tree.Merged <- Main.refused.io(Tree.Merged, Main.status.tree.r(fs, heads))
    +m2 : Tree.Merged = m
    +t : Tree.Tree() = Tree.merged_tree(m2)
    +cs : List<&2, Tree.Contest> = Tree.merged_contested(m2)
    +bs : List<&2, T.Split> = beside(cs)
    +paths : List<&2, String> = ats(bs, t)
    stats : List<&2, String> <- Store.stats(repo, paths)
    +dg : Map<&2, String> = Main.stats.map(paths, stats, Map.new(&2, String))
    ls : Map<&2, String> <- Upd.listings(repo, Main.sorted_distinct(links.at(bs, t)), Map.new(&2, String))
    +ls2 : Map<&2, String> = ls
    +pay : List<&2, String> = Main.sorted_distinct(payloads(t))
    at : List<&2, String> <- Store.located(r, pay)
    +located : Map<&2, String> = Upd.located.map(r, pay, at, Map.new(&2, String))
    ds : List<&2, Store.Doc> <- Upd.fetched(r, Upd.wanted_all(fs, lined(t)))
    +ds2 : List<&2, Store.Doc> = ds
    +first : List<&2, Place> = places(fs, ds2, heads, bs, dg, ls2, Map.new(&2, String), t)
    tx : Map<&2, String> <- texts(repo, undecided(first), Map.new(&2, String))
    +tx2 : Map<&2, String> = tx
    +laid : Lay = lay.all(t, cs, located, places(fs, ds2, heads, bs, dg, ls2, tx2, t))
    said : List<&2, String> <- perform(repo, lay.acts(laid))
    Main.print_lines(List.concat(&2, String, [rewritten(fs, heads), contests.said(cs), said, closing(typed, bs, lay.met(laid))]))


# `merge [<target>...]`: the store found and opened, and every word a
# target.
def merge(+args: List<&2, String>) -> IO(Unit):
  do IO<Unit>:
    root : String <- Store.root()
    +r : String = root
    rs : List<&2, Store.Doc> <- Store.revisions(r)
    bs : List<&2, Bm.Bookmark> <- Main.bookmarks(r)
    +bs2 : List<&2, Bm.Bookmark> = bs
    +fs : List<&2, Main.Full> = Main.fulls(r, rs)
    typed : List<&2, T.Split> <- Main.refused.io(List<&2, T.Split>, joined.r(fs, bs2, args))
    merge.at(r, fs, typed)
