# `fetch <url> [--join-unrelated] [--fields]`: take what a published copy
# holds and this store lacks (decisions 0048, 0052, 0056, 0057).
#
# A URL cannot be listed, so a publisher writes the listing — `offer`'s
# manifest — beside the copy `export` made, and every path in it resolves
# against the directory the manifest sits in. What is missing is a
# difference against this store, worked out before a byte is asked for; the
# files are asked for in `receive`'s order, content before the revisions
# naming it, and each is hashed against the digest its line gave before it
# is filed under that digest. A path no longer there is the publisher having
# moved on, and the answer is to read the manifest again, three times at
# most. Every one of those decisions is here: the host answers what is at a
# URL, and for a payload writes what it finds into a file named here,
# answering its digest rather than its bytes.

import Base
import ./text.bend as T
import ./revision.bend as Rev
import ./store.bend as Store
import ./tree.bend as Tree
import ./ops.bend as Ops
import ./resolution.bend as Res
import ./standin.bend as Stand
import ./bookmark.bend as Bm
import ./naming.bend as Naming
import ./folder.bend as Folder
import ./sha256.bend as Sha
import ./utf8.bend as Utf8
import ./commands.bend as Main
import ./arrange.bend as Arrange
import ./prune.bend as Prune
import ./receive.bend as Receive
import ./offer.bend as Offer

# The words
# ---------

type FetchCmd is Data:
  FetchCmd{join: Bool, fields: Bool, url: String}

type FWord is Data:
  FWord.Join{}
  FWord.Fields{}
  FWord.Flag{}
  FWord.Plain{}
  FWord.End{}

def fword(+w: String) -> FWord:
  Bool.pick(FWord, String.eq(w, "--join-unrelated"), FWord.Join{},
  Bool.pick(FWord, String.eq(w, "--fields"), FWord.Fields{},
  Bool.pick(FWord, String.starts_with(w, "-"), FWord.Flag{}, FWord.Plain{})))

def fword.of(ws: List<&2, String>) -> FWord:
  match ws:
    case Nil{}:
      FWord.End{}
    case +w <> rest:
      fword(w)

def args.end(+join: Bool, +fields: Bool, url: Maybe<&2, String>) -> Result<&2, &2, Main.Refused, FetchCmd>:
  match url:
    case None{}:
      Fail{Main.Refused{2, "`fetch` wants the URL of a manifest: the `offer.txt` a publisher wrote beside the copy `export` made"}}
    case Some{u}:
      Done{FetchCmd{join, fields, u}}

# The words in order, as the Rust tool reads them: each flag wherever it
# stands, the first other word the URL, and a word starting `-` that is no
# flag, or a second other word, refused where it stands. `k` is what the
# first word is.
def args.go(ws: List<&2, String>, k: FWord, +join: Bool, +fields: Bool, +url: Maybe<&2, String>) -> Result<&2, &2, Main.Refused, FetchCmd>:
  match ws:
    case Nil{}:
      args.end(join, fields, url)
    case +w <> +rest:
      match k:
        case FWord.Join{}:
          args.go(rest, fword.of(rest), True{}, fields, url)
        case FWord.Fields{}:
          args.go(rest, fword.of(rest), join, True{}, url)
        case FWord.Flag{}:
          Fail{Main.Refused{2, "`" ++ w ++ "` is not an argument `fetch` takes"}}
        case FWord.End{}:
          args.end(join, fields, url)
        case FWord.Plain{}:
          match url:
            case None{}:
              args.go(rest, fword.of(rest), join, fields, Some{w})
            case Some{u}:
              Fail{Main.Refused{2, "`fetch` wants one URL, not `" ++ w ++ "`"}}

def args.r(+ws: List<&2, String>) -> Result<&2, &2, Main.Refused, FetchCmd>:
  args.go(ws, fword.of(ws), False{}, False{}, None{})

# What a command `fetch` read says, written back as words: its two flags,
# and the URL as the one other word.
type Said is Data:
  Said{join: Bool, fields: Bool, words: List<&2, String>}

def args.read(r: Result<&2, &2, Main.Refused, FetchCmd>) -> Maybe<&2, Said>:
  match r:
    case Fail{e}:
      None{}
    case Done{FetchCmd{join, fields, url}}:
      Some{Said{join, fields, [url]}}

# The URL
# -------

# The directory a manifest sits in, and the manifest's own name in it.
type Addressed is Data:
  Addressed{root: String, manifest: String}

# The text up to and including the first `://`, and what follows it.
def scheme.go(s: String, +acc: String) -> Maybe<&2, T.Split>:
  match s:
    case SNil{}:
      None{}
    case SCon{+c, +t}:
      Bool.pick(Maybe<&2, T.Split>, String.starts_with(SCon{c, t}, "://"), Some{T.Split{String.reverse(acc) ++ "://", String.drop(t, 2n)}}, scheme.go(t, SCon{c, acc}))

# The first `?` or `#`, anywhere: a query or a fragment has nowhere to go,
# since every other path is built by putting the manifest's directory in
# front of what the manifest says.
def query.of(s: String) -> Maybe<&2, String>:
  match s:
    case SNil{}:
      None{}
    case SCon{+c, t}:
      Bool.pick(Maybe<&2, String>, Bool.or(Char.is_eq(c, '?'), Char.is_eq(c, '#')), Some{SCon{c, SNil{}}}, query.of(t))

# Over a string reversed: everything up to its last `/`, that included, and
# what follows, each put back in order.
def slash.last(r: String, +acc: String) -> Maybe<&2, T.Split>:
  match r:
    case SNil{}:
      None{}
    case SCon{+c, +t}:
      Bool.pick(Maybe<&2, T.Split>, Char.is_eq(c, '/'), Some{T.Split{String.reverse(t) ++ "/", acc}}, slash.last(t, SCon{c, acc}))

def addressed.name(+url: String, +pre: String, s: Maybe<&2, T.Split>) -> Result<&2, &2, Main.Refused, Addressed>:
  match s:
    case None{}:
      Fail{Main.Refused{2, "`" ++ url ++ "` names a host and no manifest; `fetch` wants the URL of the `offer.txt` itself, since every path in it resolves against the directory it sits in"}}
    case Some{T.Split{+dir, +name}}:
      Bool.pick(Result<&2, &2, Main.Refused, Addressed>, String.is_empty(name),
        Fail{Main.Refused{2, "`" ++ url ++ "` names a directory; `fetch` wants the URL of the manifest in it, conventionally `offer.txt`"}},
        Done{Addressed{pre ++ dir, name}})

def addressed.query(+url: String, +pre: String, +rest: String, q: Maybe<&2, String>) -> Result<&2, &2, Main.Refused, Addressed>:
  match q:
    case Some{c}:
      Fail{Main.Refused{2, "`" ++ c ++ "` cannot be part of a manifest's URL: the paths in a manifest resolve against the directory it sits in, so there is nowhere for it to go"}}
    case None{}:
      addressed.name(url, pre, slash.last(String.reverse(rest), SNil{}))

def addressed.of(+url: String, s: Maybe<&2, T.Split>) -> Result<&2, &2, Main.Refused, Addressed>:
  match s:
    case None{}:
      Fail{Main.Refused{2, "`" ++ url ++ "` is not a URL; `fetch` wants one, and a directory on this machine is `receive`'s to read"}}
    case Some{T.Split{+pre, +rest}}:
      addressed.query(url, pre, rest, query.of(url))

# Decision 0052 resolves every path in a manifest against the manifest's
# own directory, so this is the whole of the convention: the URL cut at its
# last `/`, and what follows is one more path in the same space.
def addressed.r(+url: String) -> Result<&2, &2, Main.Refused, Addressed>:
  addressed.of(url, scheme.go(url, SNil{}))

def addressed.root(a: Addressed) -> String:
  match a:
    case Addressed{r, m}:
      r

def addressed.manifest(a: Addressed) -> String:
  match a:
    case Addressed{r, m}:
      m

# One manifest path said as a URL's: every byte that is not unreserved
# escaped, and `/` alone kept, since it is the one character in a path that
# is structure rather than content.
def hex.upper(+n: U32) -> Char:
  Bool.pick(Char, U32.is_lt(n, 10), Chr{U32.add(n, 48)}, Chr{U32.add(n, 55)})

def unreserved(+b: U32) -> Bool:
  Bool.or(Bool.and(U32.is_ge(b, 65), U32.is_le(b, 90)),
  Bool.or(Bool.and(U32.is_ge(b, 97), U32.is_le(b, 122)),
  Bool.or(Bool.and(U32.is_ge(b, 48), U32.is_le(b, 57)),
  Bool.or(U32.is_eq(b, 45), Bool.or(U32.is_eq(b, 46), Bool.or(U32.is_eq(b, 95), Bool.or(U32.is_eq(b, 126), U32.is_eq(b, 47))))))))

def escaped.byte(+b: U32) -> String:
  Bool.pick(String, unreserved(b), SCon{Chr{b}, SNil{}}, SCon{'%', SCon{hex.upper((b >> 4n : U32)), SCon{hex.upper((b .&. 15 : U32)), SNil{}}}})

def escaped.bytes(bs: List<&2, U32>) -> String:
  match bs:
    case Nil{}:
      SNil{}
    case +b <> rest:
      escaped.byte(b) ++ escaped.bytes(rest)

def escaped(+path: String) -> String:
  escaped.bytes(Utf8.encode(path))

# Where one manifest path is asked for.
def url.of(+root: String, +path: String) -> String:
  root ++ escaped(path)

# The manifest
# ------------

type Manifest is Data:
  Manifest{heads: List<&2, String>, entries: List<&2, Offer.Offered>}

def manifest.entries(m: Manifest) -> List<&2, Offer.Offered>:
  match m:
    case Manifest{h, es}:
      es

def OFFER_HEADER() -> String:
  "historica-offer-1"

def unknown.format(+found: String) -> String:
  "this is not a manifest a reader of `historica-offer-1` can use: its first line is `" ++ found ++ "`. a manifest states its spelling so that a stranger can discard it whole rather than half-read it — fetch the published archive instead, which never stopped working"

def malformed(+at: Nat, +because: String) -> String:
  "line " ++ Nat.show(at) ++ " of the manifest is " ++ because

# The lines of a text as the Rust tool's `str::lines` reads them: split at
# each newline, a `\r` before one dropped with it, and nothing after a
# final newline.
def line.cr(+l: String) -> String:
  Bool.pick(String, String.ends_with(l, "\r"), String.take(l, Nat.sub(String.length(l), 1n)), l)

def lines.of(ps: List<&2, String>) -> List<&2, String>:
  match ps:
    case Nil{}:
      Nil{}
    case +p <> rest:
      match rest:
        case Nil{}:
          Bool.pick(List<&2, String>, String.is_empty(p), Nil{}, [p])
        case +q <> more:
          line.cr(p) <> lines.of(q <> more)

def KINDS() -> List<&2, String>:
  ["revision", "operation", "payload", "rule", "reserved", "name"]

# What one line of a manifest is.
type LRead is Data:
  LRead.Head{digest: String}
  LRead.Entry{entry: Offer.Offered}
  LRead.Skip{}
  LRead.Bad{because: String}
  LRead.End{}

type Four is Data:
  Four{kind: String, digest: String, forgets: String, path: String}

# Split three times and no further, so the path keeps whatever spaces it has.
def four.c(+k: String, +d: String, m: Maybe<&2, T.Split>) -> Maybe<&2, Four>:
  match m:
    case None{}:
      None{}
    case Some{T.Split{f, p}}:
      Some{Four{k, d, f, p}}

def four.b(+k: String, m: Maybe<&2, T.Split>) -> Maybe<&2, Four>:
  match m:
    case None{}:
      None{}
    case Some{T.Split{d, rest}}:
      four.c(k, d, T.split_once(rest))

def four.a(m: Maybe<&2, T.Split>) -> Maybe<&2, Four>:
  match m:
    case None{}:
      None{}
    case Some{T.Split{k, rest}}:
      four.b(k, T.split_once(rest))

def four(+l: String) -> Maybe<&2, Four>:
  four.a(T.split_once(l))

def forgets.of(+f: String) -> Maybe<&2, String>:
  Bool.pick(Maybe<&2, String>, String.eq(f, "-"), None{}, Some{f})

# An entry: a kind this reader does not know is a discarded line, checked
# only for its shape; then the digest, then what it forgets.
def line.entry(f: Four) -> LRead:
  match f:
    case Four{+k, +d, +g, +p}:
      Bool.pick(LRead, Rev.member(KINDS(), k),
        Bool.pick(LRead, T.is_digest(d),
          Bool.pick(LRead, Bool.or(String.eq(g, "-"), T.is_digest(g)), LRead.Entry{Offer.Offered{k, d, forgets.of(g), p}}, LRead.Bad{"a forgotten digest that is not a digest"}),
          LRead.Bad{"a digest that is not a digest"}),
        LRead.Skip{})

def line.fields(m: Maybe<&2, Four>) -> LRead:
  match m:
    case None{}:
      LRead.Bad{"a line with fewer than four fields; an entry is `<kind> <digest> <forgets|-> <path>`"}
    case Some{f}:
      line.entry(f)

def line.head(+none_yet: Bool, h: Maybe<&2, String>, +l: String) -> LRead:
  match h:
    case Some{+d}:
      Bool.pick(LRead, none_yet,
        Bool.pick(LRead, T.is_digest(d), LRead.Head{d}, LRead.Bad{"a head that is not a digest"}),
        LRead.Bad{"a `head` line below an entry; the heads come first, above every file"})
    case None{}:
      line.fields(four(l))

def line.at(ls: List<&2, String>, +none_yet: Bool) -> LRead:
  match ls:
    case Nil{}:
      LRead.End{}
    case +l <> rest:
      line.head(none_yet, T.strip_prefix(l, "head "), l)

# Every line after the header, counted as a person counts, the header
# being line one; `k` is what the first of them is.
def body.go(ls: List<&2, String>, k: LRead, +at: Nat, +heads: List<&2, String>, +entries: List<&2, Offer.Offered>) -> Result<&2, &2, String, Manifest>:
  match ls:
    case Nil{}:
      Done{Manifest{List.reverse(&2, String, heads), List.reverse(&2, Offer.Offered, entries)}}
    case l <> +rest:
      match k:
        case LRead.Head{d}:
          body.go(rest, line.at(rest, List.is_empty(&2, Offer.Offered, entries)), 1n+at, d <> heads, entries)
        case LRead.Entry{o}:
          body.go(rest, line.at(rest, False{}), 1n+at, heads, o <> entries)
        case LRead.Skip{}:
          body.go(rest, line.at(rest, List.is_empty(&2, Offer.Offered, entries)), 1n+at, heads, entries)
        case LRead.Bad{b}:
          Fail{malformed(at, b)}
        case LRead.End{}:
          Done{Manifest{List.reverse(&2, String, heads), List.reverse(&2, Offer.Offered, entries)}}

def manifest.lines(ls: List<&2, String>) -> Result<&2, &2, String, Manifest>:
  match ls:
    case Nil{}:
      Fail{unknown.format(SNil{})}
    case +first <> +rest:
      Bool.pick(Result<&2, &2, String, Manifest>, String.eq(first, OFFER_HEADER()), body.go(rest, line.at(rest, True{}), 2n, Nil{}, Nil{}), Fail{unknown.format(first)})

# `Offer::parse`: an unknown kind is a discarded line, an unknown header a
# refused manifest, and anything else that does not hold together refused.
def manifest.parse(+text: String) -> Result<&2, &2, String, Manifest>:
  manifest.lines(lines.of(String.split(text, '\n')))

# What this store holds
# ---------------------

# This store, as a fetch asks about it: its revisions, the digests of its
# documents and payloads, what its forgetting documents forget, the digest
# of every file of `skipped/`, its bookmarks' names, and the files of
# `claims/` it has.
type Here is Data:
  Here{revs: List<&2, Main.Full>, docs: List<&2, String>, pays: List<&2, String>, forgets: List<&2, String>, rules: List<&2, String>, names: List<&2, String>, claims: List<&2, String>}

def text.digest(+text: String) -> String:
  Sha.digest(Utf8.encode(text))

def split.text.digest(s: T.Split) -> String:
  match s:
    case T.Split{p, +t}:
      text.digest(t)

def here.of(+s: Receive.Side) -> Here:
  +st = Receive.stored.of(s)
  Here{Receive.side.fulls(s), Receive.body.ids(Receive.stored.bodies(st)), Receive.payload.ids(Receive.stored.payloads(st)), Receive.body.forgets(Receive.stored.bodies(st)),
    T.map(~T.Split, ~String, ~(x => split.text.digest(x)), Receive.stored.rules(st)),
    T.map(~Bm.Bookmark, ~String, ~(b => Bm.name_of(b)), Receive.side.marks(s)),
    T.map(~T.Split, ~String, ~(c => Receive.split.label(c)), Receive.side.claims(s))}

# The plan
# --------

# Where a manifest's path sits inside the store it names: past the first
# `history/`, at the start or after a `/`.
def after.history(s: String) -> Maybe<&2, String>:
  match s:
    case SNil{}:
      None{}
    case SCon{+c, +t}:
      Bool.pick(Maybe<&2, String>, String.starts_with(SCon{c, t}, "/history/"), Some{String.drop(t, 8n)}, after.history(t))

def filed_under(+path: String) -> Maybe<&2, String>:
  Bool.pick(Maybe<&2, String>, String.starts_with(path, "history/"), Some{String.drop(path, 8n)}, after.history(path))

def named.checked(+n: String) -> Maybe<&2, String>:
  Bool.pick(Maybe<&2, String>, Maybe.is_none(&2, String, Main.name_fault(n)), Some{n}, None{})

def named.txt(m: Maybe<&2, String>) -> Maybe<&2, String>:
  match m:
    case None{}:
      None{}
    case Some{+n}:
      Bool.pick(Maybe<&2, String>, String.ends_with(n, ".txt"), named.checked(String.take(n, Nat.sub(String.length(n), 4n))), None{})

def named.label(m: Maybe<&2, String>) -> Maybe<&2, String>:
  match m:
    case None{}:
      None{}
    case Some{+l}:
      named.txt(T.strip_prefix(l, "names/"))

# The bookmark a manifest path names, if it names one: one bookmark file
# directly under `names/`, whose name the grammar allows (decision 0071).
def named_by(+path: String) -> Maybe<&2, String>:
  named.label(filed_under(path))

def entry.kind(o: Offer.Offered) -> String:
  Offer.offered.kind(o)

def entry.digest(o: Offer.Offered) -> String:
  match o:
    case Offer.Offered{k, d, f, p}:
      d

def entry.path(o: Offer.Offered) -> String:
  Offer.offered.path(o)

def entry.forgets(os: List<&2, Offer.Offered>) -> List<&2, String>:
  match os:
    case Nil{}:
      Nil{}
    case Offer.Offered{k, d, f, p} <> rest:
      Receive.forgets.push(f, entry.forgets(rest))

def of.kind(os: List<&2, Offer.Offered>, +kind: String) -> List<&2, Offer.Offered>:
  match os:
    case Nil{}:
      Nil{}
    case +o <> rest:
      Tree.keep(~Offer.Offered, String.eq(entry.kind(o), kind), o, of.kind(rest, kind))

def digests.of(os: List<&2, Offer.Offered>) -> List<&2, String>:
  T.map(~Offer.Offered, ~String, ~(o => entry.digest(o)), os)

# Of one kind, what this store holds nothing under the digest of and nothing
# forgets.
def fresh(os: List<&2, Offer.Offered>, +held: List<&2, String>, +forgotten: List<&2, String>) -> List<&2, Offer.Offered>:
  match os:
    case Nil{}:
      Nil{}
    case +o <> rest:
      +d = entry.digest(o)
      Tree.keep(~Offer.Offered, Bool.and(Bool.not(Rev.member(held, d)), Bool.not(Rev.member(forgotten, d))), o, fresh(rest, held, forgotten))

# The second copy of anything named twice dropped: a manifest names every
# file at the path it is at, and one set of bytes is filed once.
def once(os: List<&2, Offer.Offered>, +seen: List<&2, String>) -> List<&2, Offer.Offered>:
  match os:
    case Nil{}:
      Nil{}
    case +o <> rest:
      +d = entry.digest(o)
      +had = Rev.member(seen, d)
      Tree.keep(~Offer.Offered, Bool.not(had), o, once(rest, Bool.pick(List<&2, String>, had, seen, d <> seen)))

def wanted(+os: List<&2, Offer.Offered>, +kind: String, +held: List<&2, String>, +forgotten: List<&2, String>) -> List<&2, Offer.Offered>:
  once(fresh(of.kind(os, kind), held, forgotten), Nil{})

# Decision 0062: only the bookmarks this store does not hold. One it holds
# is one it keeps, and a path naming no bookmark is one this reader cannot
# place.
def name.wanted(+held: List<&2, String>, m: Maybe<&2, String>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{+n}:
      Bool.not(Rev.member(held, n))

def name.kept(+held: List<&2, String>, m: Maybe<&2, String>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{+n}:
      Rev.member(held, n)

def names.fresh(os: List<&2, Offer.Offered>, +held: List<&2, String>) -> List<&2, Offer.Offered>:
  match os:
    case Nil{}:
      Nil{}
    case +o <> rest:
      Tree.keep(~Offer.Offered, name.wanted(held, named_by(entry.path(o))), o, names.fresh(rest, held))

def names.kept(os: List<&2, Offer.Offered>, +held: List<&2, String>) -> Nat:
  match os:
    case Nil{}:
      0n
    case +o <> rest:
      +later = names.kept(rest, held)
      Bool.pick(Nat, name.kept(held, named_by(entry.path(o))), 1n+later, later)

# Decision 0056: the path carries the directory, and this store asks its own
# registry about it. `claims/` is the one directory whose files travel and
# union; every other is declined.
def travels(+dir: String) -> Bool:
  String.eq(dir, "claims")

def first.of(ps: List<&2, String>) -> String:
  match ps:
    case Nil{}:
      SNil{}
    case d <> rest:
      d

def first.component(+label: String) -> String:
  first.of(String.split(label, '/'))

def reserved.named(kind: Bool, m: Maybe<&2, String>) -> Maybe<&2, String>:
  match kind:
    case False{}:
      None{}
    case True{}:
      match m:
        case None{}:
          None{}
        case Some{+l}:
          Bool.pick(Maybe<&2, String>, String.is_empty(first.component(l)), None{}, Some{l})

# The label a `reserved` line would be written under, if it names a file
# inside a store, in a directory with a name.
def reserved.label(o: Offer.Offered) -> Maybe<&2, String>:
  match o:
    case Offer.Offered{+k, d, f, +p}:
      reserved.named(String.eq(k, "reserved"), filed_under(p))

def reserved.takes(m: Maybe<&2, String>, +ours: List<&2, String>, +taken: List<&2, String>) -> Maybe<&2, String>:
  match m:
    case None{}:
      None{}
    case Some{+l}:
      Bool.pick(Maybe<&2, String>, Bool.and(travels(first.component(l)), Bool.and(Bool.not(Rev.member(ours, l)), Bool.not(Rev.member(taken, l)))), Some{l}, None{})

def reserved.go(os: List<&2, Offer.Offered>, +ours: List<&2, String>, +taken: List<&2, String>) -> List<&2, Offer.Offered>:
  match os:
    case Nil{}:
      Nil{}
    case +o <> rest:
      +t = reserved.takes(reserved.label(o), ours, taken)
      Tree.keep(~Offer.Offered, Maybe.is_some(&2, String, t), o, reserved.go(rest, ours, Receive.forgets.push(t, taken)))

type Declined is Data:
  Declined{directory: String, files: Nat}

def declined.dir(m: Maybe<&2, String>) -> Maybe<&2, String>:
  match m:
    case None{}:
      None{}
    case Some{+l}:
      +d = first.component(l)
      Bool.pick(Maybe<&2, String>, travels(d), None{}, Some{d})

def declined.dirs(os: List<&2, Offer.Offered>) -> List<&2, String>:
  match os:
    case Nil{}:
      Nil{}
    case +o <> rest:
      Receive.forgets.push(declined.dir(reserved.label(o)), declined.dirs(rest))

# Directories in order, each once with how many times it came.
def declined.runs(ds: List<&2, String>, +at: String, +n: Nat) -> List<&2, Declined>:
  match ds:
    case Nil{}:
      [Declined{at, n}]
    case +d <> rest:
      +same = String.eq(d, at)
      +later = declined.runs(rest, Bool.pick(String, same, at, d), Bool.pick(Nat, same, 1n+n, 1n))
      Bool.pick(List<&2, Declined>, same, later, Declined{at, n} <> later)

def declined.group(ds: List<&2, String>) -> List<&2, Declined>:
  match ds:
    case Nil{}:
      Nil{}
    case +d <> rest:
      declined.runs(rest, d, 1n)

def declined.of(+os: List<&2, Offer.Offered>) -> List<&2, Declined>:
  declined.group(List.sort(~String, ~(a => b => String.is_le(a, b)), declined.dirs(os)))

# Decision 0052: two of decision 0029's three arms, since a manifest carries
# no parent edges for the third — a revision both hold, or one of ours
# naming one of theirs as a parent or as superseded. An empty store, on
# either side, may always be seeded.
def any.in(xs: List<&2, String>, +ys: List<&2, String>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case +x <> rest:
      Bool.or(Rev.member(ys, x), any.in(rest, ys))

def related(+ours: List<&2, Main.Full>, +theirs: List<&2, String>) -> Bool:
  Bool.or(Bool.or(List.is_empty(&2, Main.Full, ours), List.is_empty(&2, String, theirs)),
    Bool.or(any.in(Main.ids(ours), theirs), any.in(Receive.edges(ours), theirs)))

def among.list(xs: List<&2, String>, +ys: List<&2, String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case +x <> rest:
      Rev.keep(Rev.member(ys, x), x, among.list(rest, ys))

type FPlan is Data:
  FPlan{payloads: List<&2, Offer.Offered>, documents: List<&2, Offer.Offered>, revisions: List<&2, Offer.Offered>, rules: List<&2, Offer.Offered>, reserved: List<&2, Offer.Offered>, names: List<&2, Offer.Offered>, kept: Nat, declined: List<&2, Declined>, destroys: List<&2, String>}

def here.revs(h: Here) -> List<&2, Main.Full>:
  match h:
    case Here{r, d, p, f, ru, n, c}:
      r

# `Store::fetch_plan`: what a manifest would add, worked out before a byte
# of it is asked for.
def plan.of(h: Here, +os: List<&2, Offer.Offered>) -> FPlan:
  match h:
    case Here{+revs, +docs, +pays, +forgets, +rules, +names, +claims}:
      +forgotten = List.append(&2, String, forgets, entry.forgets(os))
      FPlan{
        wanted(os, "payload", pays, forgotten),
        wanted(os, "operation", docs, forgotten),
        wanted(os, "revision", Main.ids(revs), Nil{}),
        wanted(os, "rule", rules, Nil{}),
        reserved.go(os, claims, Nil{}),
        once(names.fresh(of.kind(os, "name"), names), Nil{}),
        names.kept(of.kind(os, "name"), names),
        declined.of(os),
        Main.sorted_distinct(among.list(forgotten, List.append(&2, String, docs, pays)))}

def UNRELATED() -> String:
  "this store and that copy share no revision a listing can see; use `--join-unrelated` only if combining two histories is intended. a manifest names digests and no parent edges, so it cannot show that *their* revision stands on one of ours — this refusal is the stricter one a listing can support"

def plan.r(+h: Here, +os: List<&2, Offer.Offered>, +join: Bool) -> Result<&2, &2, Main.Refused, FPlan>:
  Bool.pick(Result<&2, &2, Main.Refused, FPlan>, Bool.or(join, related(here.revs(h), digests.of(of.kind(os, "revision")))), Done{plan.of(h, os)}, Fail{Main.Refused{1, UNRELATED()}})

def plan.payloads(p: FPlan) -> List<&2, Offer.Offered>:
  match p:
    case FPlan{pays, docs, revs, rules, res, names, kept, dec, des}:
      pays

def plan.documents(p: FPlan) -> List<&2, Offer.Offered>:
  match p:
    case FPlan{pays, docs, revs, rules, res, names, kept, dec, des}:
      docs

def plan.revisions(p: FPlan) -> List<&2, Offer.Offered>:
  match p:
    case FPlan{pays, docs, revs, rules, res, names, kept, dec, des}:
      revs

def plan.rules(p: FPlan) -> List<&2, Offer.Offered>:
  match p:
    case FPlan{pays, docs, revs, rules, res, names, kept, dec, des}:
      rules

def plan.reserved(p: FPlan) -> List<&2, Offer.Offered>:
  match p:
    case FPlan{pays, docs, revs, rules, res, names, kept, dec, des}:
      res

def plan.names(p: FPlan) -> List<&2, Offer.Offered>:
  match p:
    case FPlan{pays, docs, revs, rules, res, names, kept, dec, des}:
      names

def plan.destroys(p: FPlan) -> List<&2, String>:
  match p:
    case FPlan{pays, docs, revs, rules, res, names, kept, dec, des}:
      des

# What is asked for, in order
# ---------------------------

# One thing a pass does: pull a payload into the store, get a document of
# text, pull a file of another tool's, or comply with forgetting.
type Step is Data:
  Step.Pay{entry: Offer.Offered}
  Step.Text{entry: Offer.Offered}
  Step.Carry{entry: Offer.Offered}
  Step.Comply{}

def steps.as(os: List<&2, Offer.Offered>, +k: Nat) -> List<&2, Step>:
  match os:
    case Nil{}:
      Nil{}
    case +o <> rest:
      Bool.pick(Step, Nat.is_eq(k, 0n), Step.Pay{o}, Bool.pick(Step, Nat.is_eq(k, 1n), Step.Text{o}, Step.Carry{o})) <> steps.as(rest, k)

# Content first and revisions last, `receive`'s order and `export`'s, so an
# interruption leaves less reachable rather than a revision naming bytes
# that never arrived: payloads, documents, compliance with forgetting,
# revisions, then the rules, another tool's files and the bookmarks no
# revision names. Where there are no revisions, compliance comes last.
def steps.of(p: FPlan) -> List<&2, Step>:
  match p:
    case FPlan{pays, docs, +revs, rules, res, names, kept, dec, +des}:
      +comply = Bool.not(List.is_empty(&2, String, des))
      +early = Bool.and(comply, Bool.not(List.is_empty(&2, Offer.Offered, revs)))
      +late = Bool.and(comply, List.is_empty(&2, Offer.Offered, revs))
      List.concat(&2, Step, [
        steps.as(pays, 0n), steps.as(docs, 1n),
        Bool.pick(List<&2, Step>, early, [Step.Comply{}], Nil{}),
        steps.as(revs, 1n), steps.as(rules, 1n), steps.as(res, 2n), steps.as(names, 1n),
        Bool.pick(List<&2, Step>, late, [Step.Comply{}], Nil{})])

def step.path(s: Step) -> Maybe<&2, String>:
  match s:
    case Step.Pay{o}:
      Some{entry.path(o)}
    case Step.Text{o}:
      Some{entry.path(o)}
    case Step.Carry{o}:
      Some{entry.path(o)}
    case Step.Comply{}:
      None{}

# Every path a pass asks for, in the order it asks.
def asked(ss: List<&2, Step>) -> List<&2, String>:
  match ss:
    case Nil{}:
      Nil{}
    case s <> rest:
      Receive.forgets.push(step.path(s), asked(rest))

# What came, and what to do about it
# ----------------------------------

# What the host answered for one URL.
type Got is Data:
  Got.Text{text: String}
  Got.Bytes{digest: String}
  Got.Status{code: String}
  Got.Pulled{digest: String}
  Got.Failed{message: String}

def got.pulled(m: Maybe<&2, T.Split>, +answer: String) -> Got:
  match m:
    case Some{T.Split{d, n}}:
      Got.Pulled{d}
    case None{}:
      Got.Pulled{answer}

def got.of(r: Result<&1, &1, U32 & String, String>) -> Got:
  match r:
    case Fail{Tuple{code, msg}}:
      Got.Failed{msg}
    case Done{+a}:
      Bool.pick(Got, String.starts_with(a, "text\n"), Got.Text{String.drop(a, 5n)},
      Bool.pick(Got, String.starts_with(a, "bytes "), Got.Bytes{String.drop(a, 6n)},
      Bool.pick(Got, String.starts_with(a, "status "), Got.Status{String.drop(a, 7n)}, got.pulled(T.split_once(a), a))))

# The two ways a server says a file is not there, which decision 0048 makes
# an answer rather than a failure.
def gone(+code: String) -> Bool:
  Bool.or(String.eq(code, "404"), String.eq(code, "410"))

def unreachable(+path: String, +because: String) -> String:
  path ++ " could not be fetched: " ++ because

def TAMPERED(+path: String, +offered: String, +found: String) -> String:
  path ++ " holds " ++ found ++ ", and the manifest offered it as " ++ offered ++ "; nothing that does not hash to what was offered is written, so this store is as it was"

def unusable(+path: String, +because: String) -> String:
  path ++ " arrived intact and cannot be read: " ++ because

# What to do with one answer.
type Land is Data:
  Land.Gone{}
  Land.Refuse{message: String}
  Land.File{at: String, text: String}
  Land.Rule{rule: Maybe<&2, Receive.Ruled>}
  Land.Name{name: String, at: String, text: String}
  Land.Skip{}
  Land.Move{folder: String, from: String, to: String}
  Land.Discard{folder: String, file: String, message: String}

def parsed.ok(r: Result<&2, &2, String, Ops.Doc>) -> Maybe<&2, String>:
  match r:
    case Fail{e}:
      Some{e}
    case Done{d}:
      None{}

def res.ok(r: Result<&2, &2, String, Res.Doc>) -> Maybe<&2, String>:
  match r:
    case Fail{e}:
      Some{e}
    case Done{d}:
      None{}

def rev.ok(r: Result<&2, &2, String, Rev.Rev>) -> Maybe<&2, String>:
  match r:
    case Fail{e}:
      Some{e}
    case Done{d}:
      None{}

def stand.ok(m: Maybe<&2, Stand.Payload>) -> Maybe<&2, String>:
  match m:
    case None{}:
      Some{"not a forgotten payload's two headers, `forgets` and `length`"}
    case Some{p}:
      None{}

# Decision 0032's two grammars and decision 0066's third, told apart by the
# document itself: a forgotten payload's `length` header first.
def op.fault(+text: String) -> Maybe<&2, String>:
  Bool.pick(Maybe<&2, String>, Prune.forgotten.payload(T.lines(text)), stand.ok(Stand.payload.parse(text)),
    Bool.pick(Maybe<&2, String>, Res.is_resolution(text), res.ok(Res.parse(text)), parsed.ok(Ops.parse(text))))

def filed.if(+path: String, fault: Maybe<&2, String>, +at: String, +text: String) -> Land:
  match fault:
    case Some{e}:
      Land.Refuse{unusable(path, e)}
    case None{}:
      Land.File{at, text}

def rule.of(+path: String, +text: String, st: Folder.Stated) -> Land:
  match st:
    case Folder.Stated.Wrong{e}:
      Land.Refuse{unusable(path, e)}
    case Folder.Stated.None{}:
      Land.Skip{}
    case Folder.Stated.One{+sc}:
      Land.Rule{Receive.ruled.of(path, text, Folder.Stated.One{sc})}

def name.usable(+root: String, +n: String, r: Result<&2, &2, Main.Refused, Unit>, st: Bm.Stated) -> Land:
  match r:
    case Fail{Main.Refused{c, m}}:
      Land.Refuse{m}
    case Done{u}:
      Land.Name{n, root ++ "/names/" ++ n ++ ".txt", Bm.write(st)}

def name.of(+root: String, +path: String, +n: String, parsed: Result<&2, &2, String, Bm.Stated>) -> Land:
  match parsed:
    case Fail{e}:
      Land.Refuse{unusable(path, e)}
    case Done{st}:
      name.usable(root, n, Main.name.checked.r(n), st)

def name.land(+root: String, +path: String, +held: List<&2, String>, m: Maybe<&2, String>, +text: String) -> Land:
  match m:
    case None{}:
      Land.Skip{}
    case Some{+n}:
      Bool.pick(Land, Rev.member(held, n), Land.Skip{}, name.of(root, path, n, Bm.parse(text)))

# A document whose bytes are its digest, as its kind has it.
def text.land(+root: String, +held: List<&2, String>, o: Offer.Offered, +text: String) -> Land:
  match o:
    case Offer.Offered{+k, +d, f, +p}:
      Bool.pick(Land, String.eq(k, "operation"), filed.if(p, op.fault(text), root ++ "/operations/" ++ d ++ ".ops.txt", text),
      Bool.pick(Land, String.eq(k, "revision"), filed.if(p, rev.ok(Rev.parse(text)), root ++ "/revisions/" ++ d ++ ".rev.txt", text),
      Bool.pick(Land, String.eq(k, "rule"), rule.of(p, text, Folder.rule_in(text)),
        name.land(root, p, held, named_by(p), text))))

# Bytes that are not text, and are the digest offered: which kind they
# cannot be read as.
def bytes.land(o: Offer.Offered) -> Land:
  match o:
    case Offer.Offered{+k, d, f, +p}:
      Land.Refuse{unusable(p, Bool.pick(String, String.eq(k, "rule"), "a rule file that is not text", Bool.pick(String, String.eq(k, "name"), "a bookmark file that is not text", "a document that is not UTF-8")))}

# Every answer for a document of text: a file here only where the text
# hashes to the digest its line gave, and under that digest.
def got.text(+root: String, +held: List<&2, String>, +o: Offer.Offered, g: Got) -> Land:
  match g:
    case Got.Failed{m}:
      Land.Refuse{unreachable(entry.path(o), m)}
    case Got.Status{+c}:
      Bool.pick(Land, gone(c), Land.Gone{}, Land.Refuse{unreachable(entry.path(o), "the server answered " ++ c)})
    case Got.Bytes{+found}:
      Bool.pick(Land, String.eq(found, entry.digest(o)), bytes.land(o), Land.Refuse{TAMPERED(entry.path(o), entry.digest(o), found)})
    case Got.Text{+t}:
      +found = text.digest(t)
      Bool.pick(Land, String.eq(found, entry.digest(o)), text.land(root, held, o, t), Land.Refuse{TAMPERED(entry.path(o), entry.digest(o), found)})
    case Got.Pulled{d}:
      Land.Refuse{unreachable(entry.path(o), "an answer that is not a document")}

# Where a pulled file is staged, beside where it goes: dot-prefixed, so a
# person who meets one after a crash can see it is not theirs.
def staged(+name: String) -> String:
  "." ++ name ++ ".fetching"

# Every answer for a file pulled into `folder` under `name`: renamed into
# place only where what arrived hashes to the digest its line gave.
def got.pull(+folder: String, +name: String, +o: Offer.Offered, g: Got) -> Land:
  match g:
    case Got.Failed{m}:
      Land.Refuse{unreachable(entry.path(o), m)}
    case Got.Status{+c}:
      Bool.pick(Land, gone(c), Land.Gone{}, Land.Refuse{unreachable(entry.path(o), "the server answered " ++ c)})
    case Got.Pulled{+found}:
      Bool.pick(Land, String.eq(found, entry.digest(o)), Land.Move{folder, staged(name), name}, Land.Discard{folder, staged(name), TAMPERED(entry.path(o), entry.digest(o), found)})
    case Got.Text{t}:
      Land.Refuse{unreachable(entry.path(o), "an answer that is not a file")}
    case Got.Bytes{d}:
      Land.Refuse{unreachable(entry.path(o), "an answer that is not a file")}

# A payload goes into `operations/` under its digest.
def pay.land(+root: String, +o: Offer.Offered, g: Got) -> Land:
  got.pull(root ++ "/operations", entry.digest(o), o, g)

# Another tool's file goes where its label says, add-only.
def carry.land(+root: String, +o: Offer.Offered, g: Got) -> Land:
  +label = Maybe.default(&2, String, reserved.label(o), SNil{})
  got.pull(root ++ "/" ++ Arrange.parent_of(label), Naming.last(label), o, g)

# Carrying it out
# ---------------

# What one fetch did, across every reading of the manifest.
type Tally is Data:
  Tally{revisions: List<&2, String>, documents: Nat, payloads: Nat, rules: Nat, reserved: Nat, names: List<&2, String>, kept: Nat, declined: List<&2, Declined>, destroyed: Nat, refetches: Nat}

# One pass's own: what it has done so far, the rules it has read, the names
# this store now holds, and the path that was gone, if one was.
type State is Data:
  State{tally: Tally, rules: List<&2, Receive.Ruled>, held: List<&2, String>, moved: Maybe<&2, String>}

type Ctx is Data:
  Ctx{fields: Bool, root: String, web: String, manifest: String}

def ctx.fields(c: Ctx) -> Bool:
  match c:
    case Ctx{f, r, w, m}:
      f

def ctx.root(c: Ctx) -> String:
  match c:
    case Ctx{f, r, w, m}:
      r

def ctx.web(c: Ctx) -> String:
  match c:
    case Ctx{f, r, w, m}:
      w

def ctx.manifest(c: Ctx) -> String:
  match c:
    case Ctx{f, r, w, m}:
      m

def tally.document(t: Tally) -> Tally:
  match t:
    case Tally{rs, ds, ps, rus, res, ns, k, dec, des, re}:
      Tally{rs, 1n+ds, ps, rus, res, ns, k, dec, des, re}

def tally.revision(+id: String, t: Tally) -> Tally:
  match t:
    case Tally{rs, ds, ps, rus, res, ns, k, dec, des, re}:
      Tally{List.append(&2, String, rs, [id]), ds, ps, rus, res, ns, k, dec, des, re}

def tally.payload(t: Tally) -> Tally:
  match t:
    case Tally{rs, ds, ps, rus, res, ns, k, dec, des, re}:
      Tally{rs, ds, 1n+ps, rus, res, ns, k, dec, des, re}

def tally.reserved(t: Tally) -> Tally:
  match t:
    case Tally{rs, ds, ps, rus, res, ns, k, dec, des, re}:
      Tally{rs, ds, ps, rus, 1n+res, ns, k, dec, des, re}

def tally.name(+n: String, t: Tally) -> Tally:
  match t:
    case Tally{rs, ds, ps, rus, res, ns, k, dec, des, re}:
      Tally{rs, ds, ps, rus, res, List.append(&2, String, ns, [n]), k, dec, des, re}

def tally.rules(+n: Nat, t: Tally) -> Tally:
  match t:
    case Tally{rs, ds, ps, rus, res, ns, k, dec, des, re}:
      Tally{rs, ds, ps, Nat.add(rus, n), res, ns, k, dec, des, re}

def tally.destroyed(+n: Nat, t: Tally) -> Tally:
  match t:
    case Tally{rs, ds, ps, rus, res, ns, k, dec, des, re}:
      Tally{rs, ds, ps, rus, res, ns, k, dec, Nat.add(des, n), re}

def tally.refetched(t: Tally) -> Tally:
  match t:
    case Tally{rs, ds, ps, rus, res, ns, k, dec, des, re}:
      Tally{rs, ds, ps, rus, res, ns, k, dec, des, 1n+re}

# Stated from the plan rather than accumulated: a description of what the
# manifest holds, which reading it twice does not double.
def tally.planned(p: FPlan, t: Tally) -> Tally:
  match p:
    case FPlan{pays, docs, revs, rules, res, names, +kept, +dec, des}:
      match t:
        case Tally{rs, ds, ps, rus, rs2, ns, k, d0, destroyed, re}:
          Tally{rs, ds, ps, rus, rs2, ns, kept, dec, destroyed, re}

def state.held(s: State) -> List<&2, String>:
  match s:
    case State{t, r, h, m}:
      h

def state.moved(s: State) -> Maybe<&2, String>:
  match s:
    case State{t, r, h, m}:
      m

def io.done(r: Result<&1, &1, U32 & String, String>) -> IO(String):
  Main.name.io(r)

def refused.at(-A: Data, +c: Ctx, +msg: String) -> IO(A):
  Main.stated.io(A, ctx.fields(c), Fail{Main.Refused{1, msg}})

# One answer acted on.
def land.go(+c: Ctx, +o: Offer.Offered, l: Land, +t: Tally, +rules: List<&2, Receive.Ruled>, +held: List<&2, String>, +moved: Maybe<&2, String>) -> IO(State):
  match l:
    case Land.Gone{}:
      IO.pure(State, State{t, rules, held, Some{entry.path(o)}})
    case Land.Refuse{m}:
      refused.at(State, c, m)
    case Land.Skip{}:
      IO.pure(State, State{t, rules, held, moved})
    case Land.Rule{r}:
      IO.pure(State, State{t, Receive.ruled.push(r, rules), held, moved})
    case Land.File{+at, +text}:
      do IO<State>:
        w : Result<&1, &1, U32 & String, String> <- Store.filed(at ++ "\n" ++ text)
        x : String <- io.done(w)
        return State{Bool.pick(Tally, String.eq(entry.kind(o), "revision"), tally.revision(entry.digest(o), t), tally.document(t)), rules, held, moved}
    case Land.Name{+n, +at, +text}:
      do IO<State>:
        w : Result<&1, &1, U32 & String, String> <- Store.written(at ++ "\n" ++ text)
        x : String <- io.done(w)
        return State{tally.name(n, t), rules, n <> held, moved}
    case Land.Move{+folder, +from, +to}:
      do IO<State>:
        w : Result<&1, &1, U32 & String, String> <- Store.moved(folder ++ "\n" ++ from ++ "\n" ++ to)
        +how : String <- io.done(w)
        +landed : Bool = String.eq(how, "moved")
        gone : Result<&1, &1, U32 & String, String> <- Bool.pick(IO(Result<&1, &1, U32 & String, String>), landed, IO.pure(Result<&1, &1, U32 & String, String>, Done{"kept"}), Store.removed(folder ++ "\n" ++ folder ++ "/" ++ from))
        y : String <- io.done(gone)
        return State{Bool.pick(Tally, String.eq(entry.kind(o), "payload"), tally.payload(t), Bool.pick(Tally, landed, tally.reserved(t), t)), rules, held, moved}
    case Land.Discard{+folder, +file, +m}:
      do IO<State>:
        gone : Result<&1, &1, U32 & String, String> <- Store.removed(folder ++ "\n" ++ folder ++ "/" ++ file)
        y : String <- io.done(gone)
        refused.at(State, c, m)

def state.tally(s: State) -> Tally:
  match s:
    case State{t, r, h, m}:
      t

def state.rules(s: State) -> List<&2, Receive.Ruled>:
  match s:
    case State{t, r, h, m}:
      r

def land.io(+c: Ctx, +o: Offer.Offered, l: Land, +st: State) -> IO(State):
  land.go(c, o, l, state.tally(st), state.rules(st), state.held(st), state.moved(st))

# Compliance with forgetting (decision 0014): every original here a
# forgetting document stands in for destroyed, and what that empties.
def comply.io(+c: Ctx, +here: Receive.Side, +des: List<&2, String>, st: State) -> IO(State):
  match st:
    case State{+t, +rules, +held, +moved}:
      +st2 = Receive.stored.of(here)
      +gone = Receive.destroyed(Receive.stored.bodies(st2), Receive.stored.payloads(st2), des)
      do IO<State>:
        Prune.removed(ctx.root(c), gone)
        sw : Result<&1, &1, U32 & String, String> <- Store.swept(ctx.root(c) ++ "/operations")
        return State{tally.destroyed(List.length(&2, String, gone), t), rules, held, moved}

def step.io(+c: Ctx, +here: Receive.Side, +des: List<&2, String>, s: Step, +st: State) -> IO(State):
  match s:
    case Step.Pay{+o}:
      +to = ctx.root(c) ++ "/operations/" ++ staged(entry.digest(o))
      do IO<State>:
        r : Result<&1, &1, U32 & String, String> <- Store.pulled(url.of(ctx.web(c), entry.path(o)) ++ "\n" ++ to)
        land.io(c, o, pay.land(ctx.root(c), o, got.of(r)), st)
    case Step.Carry{+o}:
      +label = Maybe.default(&2, String, reserved.label(o), SNil{})
      +to = ctx.root(c) ++ "/" ++ Arrange.parent_of(label) ++ "/" ++ staged(Naming.last(label))
      do IO<State>:
        r : Result<&1, &1, U32 & String, String> <- Store.pulled(url.of(ctx.web(c), entry.path(o)) ++ "\n" ++ to)
        land.io(c, o, carry.land(ctx.root(c), o, got.of(r)), st)
    case Step.Text{+o}:
      do IO<State>:
        r : Result<&1, &1, U32 & String, String> <- Store.got(url.of(ctx.web(c), entry.path(o)))
        land.io(c, o, got.text(ctx.root(c), state.held(st), o, got.of(r)), st)
    case Step.Comply{}:
      comply.io(c, here, des, st)

# A step after a path was found gone is not taken: the pass stops there.
def step.if(+c: Ctx, +here: Receive.Side, +des: List<&2, String>, s: Step, +st: State) -> IO(State):
  Bool.pick(IO(State), Maybe.is_some(&2, String, state.moved(st)), IO.pure(State, st), step.io(c, here, des, s, st))

def steps.io(+c: Ctx, +here: Receive.Side, +des: List<&2, String>, ss: List<&2, Step>, +st: State) -> IO(State):
  match ss:
    case Nil{}:
      IO.pure(State, st)
    case s <> rest:
      do IO<State>:
        st2 : State <- step.if(c, here, des, s, st)
        steps.io(c, here, des, rest, st2)

# The rules read, unioned as `receive` unions them (decision 0045): a rule
# this store already states is left where it is, and each new one written
# under the label this store derives.
def rules.io(+c: Ctx, +here: Receive.Side, st: State) -> IO(State):
  match st:
    case State{+t, +rules, +held, +moved}:
      +hs = Receive.stored.of(here)
      +lines = Set.from_list(T.map(~Receive.Ruled, ~String, ~(r => Receive.ruled.line(r)), Receive.ruled(Receive.stored.rules(hs))))
      +ws = Receive.rules.written(Receive.rules.lacking(List.reverse(&2, Receive.Ruled, rules), lines), Receive.stored.labels(hs), Nil{}, Nil{})
      do IO<State>:
        Receive.written.rules(ctx.root(c), ws)
        return State{tally.rules(List.length(&2, T.Split, ws), t), Nil{}, held, moved}

def rules.if(+c: Ctx, +here: Receive.Side, +st: State) -> IO(State):
  Bool.pick(IO(State), Maybe.is_some(&2, String, state.moved(st)), IO.pure(State, st), rules.io(c, here, st))

# Reading the manifest
# --------------------

def NO_MANIFEST(+path: String) -> String:
  "there is no manifest at `" ++ path ++ "`; a publisher writes one beside the copy `export` made, conventionally as `offer.txt`"

def manifest.parsed(r: Result<&2, &2, String, Manifest>) -> Result<&2, &2, Main.Refused, Manifest>:
  match r:
    case Fail{m}:
      Fail{Main.Refused{1, m}}
    case Done{m}:
      Done{m}

def manifest.got(+path: String, g: Got) -> Result<&2, &2, Main.Refused, Manifest>:
  match g:
    case Got.Failed{m}:
      Fail{Main.Refused{1, unreachable(path, m)}}
    case Got.Status{+c}:
      Bool.pick(Result<&2, &2, Main.Refused, Manifest>, gone(c), Fail{Main.Refused{1, NO_MANIFEST(path)}}, Fail{Main.Refused{1, unreachable(path, "the server answered " ++ c)}})
    case Got.Bytes{d}:
      Fail{Main.Refused{1, unknown.format("not text at all")}}
    case Got.Text{+t}:
      manifest.parsed(manifest.parse(t))
    case Got.Pulled{d}:
      Fail{Main.Refused{1, unreachable(path, "an answer that is not a document")}}

def manifest.io(+c: Ctx) -> IO(List<&2, Offer.Offered>):
  do IO<List<&2, Offer.Offered>>:
    r : Result<&1, &1, U32 & String, String> <- Store.got(url.of(ctx.web(c), ctx.manifest(c)))
    m : Manifest <- Main.stated.io(Manifest, ctx.fields(c), manifest.got(ctx.manifest(c), got.of(r)))
    return manifest.entries(m)

# The passes
# ----------

# How many times a fetch reads the manifest again before it gives up: a
# publisher must not have to hold still, and one that has moved a path out
# from under three readings in a row is one to say so about.
def REFETCHES() -> Nat:
  3n

def STALE(+path: String) -> String:
  path ++ " was gone every time it was asked for, across " ++ Nat.show(REFETCHES()) ++ " readings of the manifest; the publisher is rewriting the copy faster than it can be fetched, and what arrived is here — running the fetch again finishes it"

# Where a fetch is between passes: a manifest to work from, a path that was
# gone, or finished.
type Run is Data:
  Run.Next{entries: List<&2, Offer.Offered>, tally: Tally, left: Nat}
  Run.Again{path: String, tally: Tally, left: Nat}
  Run.Finished{tally: Tally}

def pass.after(st: State, +left: Nat) -> Run:
  match st:
    case State{t, r, h, m}:
      match m:
        case None{}:
          Run.Finished{t}
        case Some{p}:
          Run.Again{p, t, left}

# One pass: this store read as it now is, the plan worked out against it,
# and every step taken until a path is gone.
def pass.io(+c: Ctx, +join: Bool, +os: List<&2, Offer.Offered>, +t: Tally, +left: Nat) -> IO(Run):
  do IO<Run>:
    here : Receive.Side <- Receive.side.read(ctx.fields(c), ctx.root(c))
    +here2 : Receive.Side = here
    p : FPlan <- Main.stated.io(FPlan, ctx.fields(c), plan.r(here.of(here2), os, join))
    +p2 : FPlan = p
    +start : State = State{tally.planned(p2, t), Nil{}, T.map(~Bm.Bookmark, ~String, ~(b => Bm.name_of(b)), Receive.side.marks(here2)), None{}}
    st : State <- steps.io(c, here2, plan.destroys(p2), steps.of(p2), start)
    st2 : State <- rules.if(c, here2, st)
    return pass.after(st2, left)

def run.io(+c: Ctx, +join: Bool, r: Run) -> IO(Run):
  match r:
    case Run.Finished{t}:
      IO.pure(Run, Run.Finished{t})
    case Run.Next{+os, +t, +left}:
      pass.io(c, join, os, t, left)
    case Run.Again{+p, +t, left}:
      match left:
        case 0n:
          refused.at(Run, c, STALE(p))
        case 1n+l:
          do IO<Run>:
            os : List<&2, Offer.Offered> <- manifest.io(c)
            return Run.Next{os, tally.refetched(t), l}

def runs.io(fuel: Nat, +c: Ctx, +join: Bool, +r: Run) -> IO(Run):
  match fuel:
    case 0n:
      IO.pure(Run, r)
    case 1n+f:
      do IO<Run>:
        r2 : Run <- run.io(c, join, r)
        runs.io(f, c, join, r2)

def run.tally(r: Run) -> Tally:
  match r:
    case Run.Finished{t}:
      t
    case Run.Next{os, t, l}:
      t
    case Run.Again{p, t, l}:
      t

# The report
# ----------

def declined.lines(ds: List<&2, Declined>) -> List<&2, String>:
  match ds:
    case Nil{}:
      Nil{}
    case Declined{+d, +n} <> rest:
      ("declined " ++ Nat.show(n) ++ " files of `" ++ d ++ "/`, which this historica does not carry across a boundary") <> declined.lines(rest)

def count.if(+n: Nat, +line: String) -> List<&2, String>:
  Bool.pick(List<&2, String>, Nat.is_eq(n, 0n), Nil{}, [line])

def said.tally(t: Tally) -> List<&2, String>:
  match t:
    case Tally{+rs, +ds, +ps, +rus, +res, +ns, +k, +dec, +des, +re}:
      +revs = List.length(&2, String, rs)
      +names = List.length(&2, String, ns)
      List.concat(&2, String, [
        ["fetched " ++ Nat.show(revs) ++ " revisions", "fetched " ++ Nat.show(ds) ++ " content documents", "fetched " ++ Nat.show(ps) ++ " payloads"],
        count.if(rus, "fetched " ++ Nat.show(rus) ++ " rules"),
        count.if(res, "fetched " ++ Nat.show(res) ++ " files another tool wrote"),
        count.if(names, "fetched " ++ Nat.show(names) ++ " bookmarks"),
        count.if(k, "kept this copy's own reading of " ++ Nat.show(k) ++ " bookmarks the publisher also states"),
        count.if(des, "destroyed " ++ Nat.show(des) ++ " forgotten originals"),
        declined.lines(dec),
        count.if(re, "read the manifest " ++ Nat.show(1n+re) ++ " times: the copy was being rewritten while it was being read"),
        count.if(revs, "the folder is untouched; `historica update` is its catch-up")])

# Decision 0074's statement: each revision taken, then each bookmark, each
# once and in order, as the Rust tool's ordered set spells them.
def said.fields(t: Tally) -> List<&2, String>:
  match t:
    case Tally{rs, ds, ps, rus, res, ns, k, dec, des, re}:
      Main.WROTE() <> List.append(&2, String,
        T.map(~String, ~String, ~(r => "revision " ++ r), Main.sorted_distinct(rs)),
        T.map(~String, ~String, ~(n => "name " ++ n), Main.sorted_distinct(ns)))

def said.done(fields: Bool, t: Tally) -> List<&2, String>:
  match fields:
    case True{}:
      said.fields(t)
    case False{}:
      said.tally(t)

# The IO
# ------

def BROKEN() -> String:
  "this store does not pass `check`, and a fetch into a store that cannot be trusted would make one fault two; `historica check` says what is wrong"

def CONTRADICTION() -> String:
  "everything the manifest named is here, and this store no longer passes `check`. a fetch verifies every arriving file against the listing and cannot verify that the copy agreed with itself, which is what a `receive` against a local directory does and a fetch cannot; `historica check` says what contradicts what"

def sound.r(+s: Receive.Side, +msg: String) -> Result<&2, &2, Main.Refused, Unit>:
  Bool.pick(Result<&2, &2, Main.Refused, Unit>, Prune.sound(Receive.stored.of(s)), Done{Unit{}}, Fail{Main.Refused{1, msg}})

def TALLY0() -> Tally:
  Tally{Nil{}, 0n, 0n, 0n, 0n, Nil{}, 0n, Nil{}, 0n, 0n}

def fetch.of(c: FetchCmd, a: Addressed) -> IO(Unit):
  match c:
    case FetchCmd{+join, +fields, url}:
      match a:
        case Addressed{+web, +manifest}:
          do IO<Unit>:
            found : Result<&1, &1, U32 & String, String> <- Store.root.found()
            found2 : String <- Main.record.root(fields, found)
            +root : String = found2
            here : Receive.Side <- Receive.side.read(fields, root)
            Main.stated.io(Unit, fields, sound.r(here, BROKEN()))
            +ctx : Ctx = Ctx{fields, root, web, manifest}
            os : List<&2, Offer.Offered> <- manifest.io(ctx)
            done : Run <- runs.io(9n, ctx, join, Run.Next{os, TALLY0(), REFETCHES()})
            after : Receive.Side <- Receive.side.read(fields, root)
            Main.stated.io(Unit, fields, sound.r(after, CONTRADICTION()))
            Arrange.print_lines(said.done(fields, run.tally(done)))

def fetch.url(c: FetchCmd) -> String:
  match c:
    case FetchCmd{j, f, u}:
      u

def fetch(+args: List<&2, String>) -> IO(Unit):
  do IO<Unit>:
    c : FetchCmd <- Main.refused.io(FetchCmd, args.r(args))
    +c2 : FetchCmd = c
    a : Addressed <- Main.refused.io(Addressed, addressed.r(fetch.url(c2)))
    fetch.of(c2, a)
