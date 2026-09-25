# What `offer` publishes of what is private. A manifest is what it would be
# if the store held no private bookmark, and what it would be if it held
# no private rule: neither leaves a line, so neither leaves the file name
# the key exists to keep back.
import Base
import ./offer.bend as Offer
import ./receive.bend as Receive
import ./prune.bend as Prune
import ./arrange.bend as Arrange
import ./bookmark.bend as Bm
import ./folder.bend as Folder
import ./text.bend as T
import ./tree.bend as Tree
import ./commands.bend as Main
import ./string_lemmas.bend as S
import ./prune_lemmas.bend as PruneL
import ./resolution.bend as Res
import ./ops.bend as Ops
import ./standin.bend as Stand
import ./fetch.bend as Fetch
import ./bookmark_lemmas.bend as BmL
import ./spelling_lemmas.bend as Spell
import ./arrange_lemmas.bend as ArrangeL
import ./revision.bend as Rev

# Bookmarks
# ---------

def names_shared(bs: List<&2, Bm.Bookmark>, +ids: List<&2, T.Split>, +prefix: String) -> {Offer.names.offered(bs, ids, prefix) == Offer.names.offered(Offer.shared(bs), ids, prefix) : List<&2, Offer.Offered>}:
  match bs:
    case Nil{}:
      {==}
    case Bm.Bookmark{+n, +t, +p} <> +rest:
      match p:
        case True{}:
          names_shared(rest, ids, prefix)
        case False{}:
          Equal.cong(List<&2, Offer.Offered>, List<&2, Offer.Offered>, x => Offer.offered.found(True{}, Arrange.lookup(ids, "names/" ++ n ++ ".txt"), "names/" ++ n ++ ".txt", "name", prefix, x),
            Offer.names.offered(rest, ids, prefix), Offer.names.offered(Offer.shared(rest), ids, prefix), names_shared(rest, ids, prefix))

# The manifest is the one a store with no private bookmark would have.
def bookmarks(+prefix: String, +s: Prune.Stored, +bs: List<&2, Bm.Bookmark>, +claims: List<&2, T.Split>, +rids: List<&2, T.Split>, +nids: List<&2, T.Split>) -> {Offer.manifest(prefix, s, bs, claims, rids, nids) == Offer.manifest(prefix, s, Offer.shared(bs), claims, rids, nids) : List<&2, String>}:
  Equal.cong(List<&2, Offer.Offered>, List<&2, String>, x => Offer.manifest.of(Offer.manifest.front(prefix, s), Offer.rules.offered(Receive.ruled(Offer.rules.of(s)), rids, prefix), Offer.splits.offered(claims, "reserved", prefix), x),
    Offer.names.offered(bs, nids, prefix), Offer.names.offered(Offer.shared(bs), nids, prefix), names_shared(bs, nids, prefix))

# Rules
# -----

def rule_kept(c: Bool, +path: String, +text: String, +file: String, +line: String, +label: String, +rest: List<&2, T.Split>, +ids: List<&2, T.Split>, +prefix: String, ec: {String.starts_with(line, "private") == c : Bool}, er: {Receive.ruled.of(Receive.skipped_file(path), text, Folder.rule_in(text)) == Some{Receive.Ruled{file, line, label}} : Maybe<&2, Receive.Ruled>}, ih: {Offer.rules.offered(Receive.ruled(rest), ids, prefix) == Offer.rules.offered(Receive.ruled(Offer.shared_files(rest)), ids, prefix) : List<&2, Offer.Offered>}) -> {Offer.offered.found(Bool.not(c), Arrange.lookup(ids, "skipped/" ++ file), "skipped/" ++ file, "rule", prefix, Offer.rules.offered(Receive.ruled(rest), ids, prefix)) == Offer.rules.offered(Receive.ruled(Tree.keep(~T.Split, Bool.not(c), T.Split{path, text}, Offer.shared_files(rest))), ids, prefix) : List<&2, Offer.Offered>}:
  match c:
    case True{}:
      ih
    case False{}:
      %Equal.sym(Maybe<&2, Receive.Ruled>, Receive.ruled.of(Receive.skipped_file(path), text, Folder.rule_in(text)), Some{Receive.Ruled{file, line, label}}, er) : {Offer.offered.found(True{}, Arrange.lookup(ids, "skipped/" ++ file), "skipped/" ++ file, "rule", prefix, Offer.rules.offered(Receive.ruled(rest), ids, prefix)) == Offer.rules.offered(Receive.ruled.push(_, Receive.ruled(Offer.shared_files(rest))), ids, prefix) : List<&2, Offer.Offered>}
      %Equal.sym(Bool, String.starts_with(line, "private"), False{}, ec) : {Offer.offered.found(True{}, Arrange.lookup(ids, "skipped/" ++ file), "skipped/" ++ file, "rule", prefix, Offer.rules.offered(Receive.ruled(rest), ids, prefix)) == Offer.offered.found(Bool.not(_), Arrange.lookup(ids, "skipped/" ++ file), "skipped/" ++ file, "rule", prefix, Offer.rules.offered(Receive.ruled(Offer.shared_files(rest)), ids, prefix)) : List<&2, Offer.Offered>}
      Equal.cong(List<&2, Offer.Offered>, List<&2, Offer.Offered>, x => Offer.offered.found(True{}, Arrange.lookup(ids, "skipped/" ++ file), "skipped/" ++ file, "rule", prefix, x),
        Offer.rules.offered(Receive.ruled(rest), ids, prefix), Offer.rules.offered(Receive.ruled(Offer.shared_files(rest)), ids, prefix), ih)

def rule_step(r: Maybe<&2, Receive.Ruled>, +path: String, +text: String, +rest: List<&2, T.Split>, +ids: List<&2, T.Split>, +prefix: String, er: {Receive.ruled.of(Receive.skipped_file(path), text, Folder.rule_in(text)) == r : Maybe<&2, Receive.Ruled>}, ih: {Offer.rules.offered(Receive.ruled(rest), ids, prefix) == Offer.rules.offered(Receive.ruled(Offer.shared_files(rest)), ids, prefix) : List<&2, Offer.Offered>}) -> {Offer.rules.offered(Receive.ruled.push(r, Receive.ruled(rest)), ids, prefix) == Offer.rules.offered(Receive.ruled(Tree.keep(~T.Split, Bool.not(Offer.rule.private(r)), T.Split{path, text}, Offer.shared_files(rest))), ids, prefix) : List<&2, Offer.Offered>}:
  match r:
    case None{}:
      %Equal.sym(Maybe<&2, Receive.Ruled>, Receive.ruled.of(Receive.skipped_file(path), text, Folder.rule_in(text)), None{}, er) : {Offer.rules.offered(Receive.ruled(rest), ids, prefix) == Offer.rules.offered(Receive.ruled.push(_, Receive.ruled(Offer.shared_files(rest))), ids, prefix) : List<&2, Offer.Offered>}
      ih
    case Some{Receive.Ruled{+file, +line, +label}}:
      rule_kept(String.starts_with(line, "private"), path, text, file, line, label, rest, ids, prefix, {==}, er, ih)

def rules_shared(rs: List<&2, T.Split>, +ids: List<&2, T.Split>, +prefix: String) -> {Offer.rules.offered(Receive.ruled(rs), ids, prefix) == Offer.rules.offered(Receive.ruled(Offer.shared_files(rs)), ids, prefix) : List<&2, Offer.Offered>}:
  match rs:
    case Nil{}:
      {==}
    case T.Split{+path, +text} <> +rest:
      rule_step(Receive.ruled.of(Receive.skipped_file(path), text, Folder.rule_in(text)), path, text, rest, ids, prefix, {==}, rules_shared(rest, ids, prefix))

# The manifest is the one a store with no private rule would have.
def rules(+prefix: String, s: Prune.Stored, +bs: List<&2, Bm.Bookmark>, +claims: List<&2, T.Split>, +rids: List<&2, T.Split>, +nids: List<&2, T.Split>) -> {Offer.manifest(prefix, s, bs, claims, rids, nids) == Offer.manifest(prefix, Offer.shared_rules(s), bs, claims, rids, nids) : List<&2, String>}:
  match s:
    case Prune.Stored{+docs, +revs, +od, +bods, +ps, +names, +rs}:
      Equal.cong(List<&2, Offer.Offered>, List<&2, String>, x => Offer.manifest.of(Offer.manifest.front(prefix, Prune.Stored{docs, revs, od, bods, ps, names, rs}), x, Offer.splits.offered(claims, "reserved", prefix), Offer.names.offered(bs, nids, prefix)),
        Offer.rules.offered(Receive.ruled(rs), rids, prefix), Offer.rules.offered(Receive.ruled(Offer.shared_files(rs)), rids, prefix), rules_shared(rs, rids, prefix))

# Digests
# -------

def and_tt(a: Bool, b: Bool, ea: {a == True{} : Bool}, eb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  match a:
    case True{}:
      eb
    case False{}:
      Empty.absurd({Bool.and(False{}, b) == True{} : Bool}, S.false_true(ea))

def or_r(a: Bool, -b: Bool, e: {b == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      e

def some_inj(+a: String, -b: String, e: {Some{a} == Some{b} : Maybe<&2, String>}) -> {a == b : String}:
  Equal.cong(Maybe<&2, String>, String, m => Maybe.default(&2, String, m, a), Some{a}, Some{b}, e)

# What was listed stays listed with one more file in front.
def from_more(os: List<&2, Offer.Offered>, +x: T.Split, +rest: List<&2, T.Split>, +prefix: String, +h: {Offer.offered.from(os, rest, prefix) == True{} : Bool}) -> {Offer.offered.from(os, x <> rest, prefix) == True{} : Bool}:
  match os:
    case Nil{}:
      {==}
    case Offer.Offered{k, +d, f, +p} <> +more:
      match x:
        case T.Split{+l, +dd}:
          and_tt(Offer.listed(T.Split{l, dd} <> rest, prefix, p, d), Offer.offered.from(more, T.Split{l, dd} <> rest, prefix),
            or_r(Bool.and(String.eq(Offer.addressed(prefix, l), p), String.eq(dd, d)), Offer.listed(rest, prefix, p, d), PruneL.and_l(Offer.listed(rest, prefix, p, d), Offer.offered.from(more, rest, prefix), h)),
            from_more(more, T.Split{l, dd}, rest, prefix, PruneL.and_r(Offer.listed(rest, prefix, p, d), Offer.offered.from(more, rest, prefix), h)))

def self_listed(+l: String, +d: String, +rest: List<&2, T.Split>, +prefix: String) -> {Offer.listed(T.Split{l, d} <> rest, prefix, Offer.addressed(prefix, l), d) == True{} : Bool}:
  %Equal.sym(Bool, String.eq(Offer.addressed(prefix, l), Offer.addressed(prefix, l)), True{}, S.eq_refl(Offer.addressed(prefix, l))) : {Bool.or(Bool.and(_, String.eq(d, d)), Offer.listed(rest, prefix, Offer.addressed(prefix, l), d)) == True{} : Bool}
  %Equal.sym(Bool, String.eq(d, d), True{}, S.eq_refl(d)) : {Bool.or(Bool.and(True{}, _), Offer.listed(rest, prefix, Offer.addressed(prefix, l), d)) == True{} : Bool}
  {==}

def splits_from(ss: List<&2, T.Split>, +kind: String, +prefix: String) -> {Offer.offered.from(Offer.splits.offered(ss, kind, prefix), ss, prefix) == True{} : Bool}:
  match ss:
    case Nil{}:
      {==}
    case T.Split{+p, +d} <> +rest:
      and_tt(Offer.listed(T.Split{p, d} <> rest, prefix, Offer.addressed(prefix, p), d), Offer.offered.from(Offer.splits.offered(rest, kind, prefix), T.Split{p, d} <> rest, prefix),
        self_listed(p, d, rest, prefix),
        from_more(Offer.splits.offered(rest, kind, prefix), T.Split{p, d}, rest, prefix, splits_from(rest, kind, prefix)))

def bodies_from(bs: List<&2, Prune.Body>, +prefix: String) -> {Offer.offered.from(Offer.bodies.offered(bs, prefix), Offer.body.splits(bs), prefix) == True{} : Bool}:
  match bs:
    case Nil{}:
      {==}
    case Prune.Body{+p, +d, ok, f} <> +rest:
      and_tt(Offer.listed(T.Split{p, d} <> Offer.body.splits(rest), prefix, Offer.addressed(prefix, p), d), Offer.offered.from(Offer.bodies.offered(rest, prefix), T.Split{p, d} <> Offer.body.splits(rest), prefix),
        self_listed(p, d, Offer.body.splits(rest), prefix),
        from_more(Offer.bodies.offered(rest, prefix), T.Split{p, d}, Offer.body.splits(rest), prefix, bodies_from(rest, prefix)))

def lookup_step(c: Bool, +k: String, +v: String, +rest: List<&2, T.Split>, +label: String, +d: String, +prefix: String, ec: {String.eq(k, label) == c : Bool}, e: {Bool.pick(Maybe<&2, String>, c, Some{v}, Arrange.lookup(rest, label)) == Some{d} : Maybe<&2, String>}, ih: {Arrange.lookup(rest, label) == Some{d} : Maybe<&2, String>} -> {Offer.listed(rest, prefix, Offer.addressed(prefix, label), d) == True{} : Bool}) -> {Offer.listed(T.Split{k, v} <> rest, prefix, Offer.addressed(prefix, label), d) == True{} : Bool}:
  match c:
    case True{}:
      %S.eq_true(k, label, ec) : {Offer.listed(T.Split{k, v} <> rest, prefix, Offer.addressed(prefix, _), d) == True{} : Bool}
      %some_inj(v, d, e) : {Offer.listed(T.Split{k, v} <> rest, prefix, Offer.addressed(prefix, k), _) == True{} : Bool}
      self_listed(k, v, rest, prefix)
    case False{}:
      or_r(Bool.and(String.eq(Offer.addressed(prefix, k), Offer.addressed(prefix, label)), String.eq(v, d)), Offer.listed(rest, prefix, Offer.addressed(prefix, label), d), ih(e))

def m_none(m: Maybe<&2, String>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      Empty

def none_some(-x: String, e: {None{} == Some{x} : Maybe<&2, String>}) -> Empty:
  %e : {m_none(_) : Type}
  Unit{}

# A file found by its label is listed at that label, with that digest.
def lookup_listed(ids: List<&2, T.Split>, +label: String, +d: String, +prefix: String, e: {Arrange.lookup(ids, label) == Some{d} : Maybe<&2, String>}) -> {Offer.listed(ids, prefix, Offer.addressed(prefix, label), d) == True{} : Bool}:
  match ids:
    case Nil{}:
      Empty.absurd({False{} == True{} : Bool}, none_some(d, e))
    case T.Split{+k, +v} <> +rest:
      lookup_step(String.eq(k, label), k, v, rest, label, d, prefix, {==}, e, x => lookup_listed(rest, label, d, prefix, x))

def found_from(keep: Bool, found: Maybe<&2, String>, +label: String, +kind: String, +prefix: String, +rest: List<&2, Offer.Offered>, +ids: List<&2, T.Split>, ef: {Arrange.lookup(ids, label) == found : Maybe<&2, String>}, ih: {Offer.offered.from(rest, ids, prefix) == True{} : Bool}) -> {Offer.offered.from(Offer.offered.found(keep, found, label, kind, prefix, rest), ids, prefix) == True{} : Bool}:
  match keep:
    case True{}:
      match found:
        case Some{+d}:
          and_tt(Offer.listed(ids, prefix, Offer.addressed(prefix, label), d), Offer.offered.from(rest, ids, prefix), lookup_listed(ids, label, d, prefix, ef), ih)
        case None{}:
          ih
    case False{}:
      ih

def rules_from(rs: List<&2, Receive.Ruled>, +ids: List<&2, T.Split>, +prefix: String) -> {Offer.offered.from(Offer.rules.offered(rs, ids, prefix), ids, prefix) == True{} : Bool}:
  match rs:
    case Nil{}:
      {==}
    case Receive.Ruled{+file, +line, l} <> +rest:
      found_from(Bool.not(String.starts_with(line, "private")), Arrange.lookup(ids, "skipped/" ++ file), "skipped/" ++ file, "rule", prefix, Offer.rules.offered(rest, ids, prefix), ids, {==}, rules_from(rest, ids, prefix))

def names_from(bs: List<&2, Bm.Bookmark>, +ids: List<&2, T.Split>, +prefix: String) -> {Offer.offered.from(Offer.names.offered(bs, ids, prefix), ids, prefix) == True{} : Bool}:
  match bs:
    case Nil{}:
      {==}
    case Bm.Bookmark{+n, t, +p} <> +rest:
      found_from(Bool.not(p), Arrange.lookup(ids, "names/" ++ n ++ ".txt"), "names/" ++ n ++ ".txt", "name", prefix, Offer.names.offered(rest, ids, prefix), ids, {==}, names_from(rest, ids, prefix))

# Every line of a manifest names a file by the digest the store's listing
# gives it.
def digests(+prefix: String, s: Prune.Stored, +marks: List<&2, Bm.Bookmark>, +claims: List<&2, T.Split>, +rids: List<&2, T.Split>, +nids: List<&2, T.Split>) -> {Offer.manifest.from(prefix, s, marks, claims, rids, nids) == True{} : Bool}:
  match s:
    case Prune.Stored{docs, +revs, od, +bs, +ps, names, +rules}:
      and_tt(Offer.offered.from(Offer.splits.offered(ps, "payload", prefix), ps, prefix), Bool.and(Offer.offered.from(Offer.bodies.offered(bs, prefix), Offer.body.splits(bs), prefix), Bool.and(Offer.offered.from(Offer.splits.offered(revs, "revision", prefix), revs, prefix), Bool.and(Offer.offered.from(Offer.rules.offered(Receive.ruled(rules), rids, prefix), rids, prefix), Bool.and(Offer.offered.from(Offer.splits.offered(claims, "reserved", prefix), claims, prefix), Offer.offered.from(Offer.names.offered(marks, nids, prefix), nids, prefix))))),
        splits_from(ps, "payload", prefix),
        and_tt(Offer.offered.from(Offer.bodies.offered(bs, prefix), Offer.body.splits(bs), prefix), Bool.and(Offer.offered.from(Offer.splits.offered(revs, "revision", prefix), revs, prefix), Bool.and(Offer.offered.from(Offer.rules.offered(Receive.ruled(rules), rids, prefix), rids, prefix), Bool.and(Offer.offered.from(Offer.splits.offered(claims, "reserved", prefix), claims, prefix), Offer.offered.from(Offer.names.offered(marks, nids, prefix), nids, prefix)))),
          bodies_from(bs, prefix),
          and_tt(Offer.offered.from(Offer.splits.offered(revs, "revision", prefix), revs, prefix), Bool.and(Offer.offered.from(Offer.rules.offered(Receive.ruled(rules), rids, prefix), rids, prefix), Bool.and(Offer.offered.from(Offer.splits.offered(claims, "reserved", prefix), claims, prefix), Offer.offered.from(Offer.names.offered(marks, nids, prefix), nids, prefix))),
            splits_from(revs, "revision", prefix),
            and_tt(Offer.offered.from(Offer.rules.offered(Receive.ruled(rules), rids, prefix), rids, prefix), Bool.and(Offer.offered.from(Offer.splits.offered(claims, "reserved", prefix), claims, prefix), Offer.offered.from(Offer.names.offered(marks, nids, prefix), nids, prefix)),
              rules_from(Receive.ruled(rules), rids, prefix),
              and_tt(Offer.offered.from(Offer.splits.offered(claims, "reserved", prefix), claims, prefix), Offer.offered.from(Offer.names.offered(marks, nids, prefix), nids, prefix),
                splits_from(claims, "reserved", prefix),
                names_from(marks, nids, prefix))))))

# What a document forgets
# -----------------------

def forgets_of(b: Prune.Body) -> Maybe<&2, String>:
  match b:
    case Prune.Body{p, i, ok, f}:
      f

def two_forgets(r: Bool, +path: String, +id: String, +text: String) -> {Bool.pick(Maybe<&2, String>, r, None{}, Prune.ops.forgets(Ops.parse(text))) == Bool.pick(Maybe<&2, String>, Bool.and(r, True{}), None{}, forgets_of(Prune.body.of.two(path, id, text, r))) : Maybe<&2, String>}:
  match r:
    case True{}:
      {==}
    case False{}:
      {==}

def pick_false(r: Bool, +x: Maybe<&2, String>) -> {x == Bool.pick(Maybe<&2, String>, Bool.and(r, False{}), None{}, x) : Maybe<&2, String>}:
  match r:
    case True{}:
      {==}
    case False{}:
      {==}

def read_forgets(fp: Bool, +path: String, +id: String, +text: String) -> {Bool.pick(Maybe<&2, String>, fp, Stand.payload.forgets(Stand.payload.parse(text)), Bool.pick(Maybe<&2, String>, Res.is_resolution(text), None{}, Prune.ops.forgets(Ops.parse(text)))) == Bool.pick(Maybe<&2, String>, Bool.and(Res.is_resolution(text), Bool.not(fp)), None{}, forgets_of(Prune.body.of(path, id, text, fp))) : Maybe<&2, String>}:
  match fp:
    case True{}:
      pick_false(Res.is_resolution(text), Stand.payload.forgets(Stand.payload.parse(text)))
    case False{}:
      two_forgets(Res.is_resolution(text), path, id, text)

# `offer`'s catalogue lists a document as forgetting what the reading
# `prune`, `receive` and `export` share reads it as forgetting, save a
# resolution that is no stand-in, which it lists as forgetting nothing.
def catalogue(+path: String, +id: String, +text: String) -> {Offer.catalogue.forgets(text) == Bool.pick(Maybe<&2, String>, Bool.and(Res.is_resolution(text), Bool.not(Prune.forgotten.payload(T.lines(text)))), None{}, forgets_of(Prune.body.of(path, id, text, Prune.forgotten.payload(T.lines(text))))) : Maybe<&2, String>}:
  read_forgets(Prune.forgotten.payload(T.lines(text)), path, id, text)

# Reading a line back
# -------------------

def hex_sp.at(+c: Char, b: Bool, eb: {Char.is_eq(c, ' ') == b : Bool}, h: {T.is_hex(c) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, S.false_true(Equal.trans(Bool, False{}, T.is_hex(c), True{}, (%Equal.sym(Char, c, ' ', BmL.chr_eq(c, ' ', eb)) : {False{} == T.is_hex(_) : Bool}
        {==}), h)))

# A string of hex characters has no space in it.
def nosp_hex(s: String, +h: {T.all_chars(~T.is_hex, s) == True{} : Bool}) -> {T.has_char(s, ' ') == False{} : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      ArrangeL.or_ff(Char.is_eq(c, ' '), T.has_char(t, ' '),
        hex_sp.at(c, Char.is_eq(c, ' '), {==}, ArrangeL.and_tl(T.is_hex(c), T.all_chars(~T.is_hex, t), h)),
        nosp_hex(t, ArrangeL.and_tr(T.is_hex(c), T.all_chars(~T.is_hex, t), h)))

# A digest has no space in it.
def nosp_digest(+d: String, h: {T.is_digest(d) == True{} : Bool}) -> {T.has_char(d, ' ') == False{} : Bool}:
  nosp_hex(d, ArrangeL.and_tr(Nat.is_eq(String.length(d), 64n), T.all_chars(~T.is_hex, d), h))

def go_step(b: Bool, +c: Char, +t: String, +r: String, +acc: String, eb: {Char.is_eq(c, ' ') == b : Bool}, +hb: {b == False{} : Bool}, ih: {T.split_once.go(t ++ (" " ++ r), SCon{c, acc}) == Some{T.Split{String.reverse.go(SCon{c, acc}, t), r}} : Maybe<&2, T.Split>}) -> {Bool.pick(Maybe<&2, T.Split>, b, Some{T.Split{String.reverse(acc), t ++ (" " ++ r)}}, T.split_once.go(t ++ (" " ++ r), SCon{c, acc})) == Some{T.Split{String.reverse.go(acc, SCon{c, t}), r}} : Maybe<&2, T.Split>}:
  match b:
    case True{}:
      Empty.absurd({Some{T.Split{String.reverse(acc), t ++ (" " ++ r)}} == Some{T.Split{String.reverse.go(acc, SCon{c, t}), r}} : Maybe<&2, T.Split>}, S.true_false(hb))
    case False{}:
      ih

# The walk that cuts at the first space, over a word with none, a space
# and the rest: the word, and the rest.
def go_word(t: String, +acc: String, +r: String, +h: {T.has_char(t, ' ') == False{} : Bool}) -> {T.split_once.go(t ++ (" " ++ r), acc) == Some{T.Split{String.reverse.go(acc, t), r}} : Maybe<&2, T.Split>}:
  match t:
    case SNil{}:
      {==}
    case SCon{+c, +u}:
      go_step(Char.is_eq(c, ' '), c, u, r, acc, {==}, ArrangeL.or_ff_l(Char.is_eq(c, ' '), T.has_char(u, ' '), h),
        go_word(u, SCon{c, acc}, r, ArrangeL.or_ff_r(Char.is_eq(c, ' '), T.has_char(u, ' '), h)))

# A word with no space, a space and the rest cut at the first space is
# the word and the rest.
def cut_word(+a: String, +r: String, +h: {T.has_char(a, ' ') == False{} : Bool}) -> {T.split_once(a ++ (" " ++ r)) == Some{T.Split{a, r}} : Maybe<&2, T.Split>}:
  Equal.trans(Maybe<&2, T.Split>, T.split_once(a ++ (" " ++ r)), T.split_once.go(a ++ (" " ++ r), SNil{}), Some{T.Split{a, r}}, Spell.split_fast(a ++ (" " ++ r), SNil{}), go_word(a, SNil{}, r, h))

# A kind a reader knows has no space in it and does not start as `head`
# does.
def not_h(k: String) -> Bool:
  match k:
    case SNil{}:
      False{}
    case SCon{c, t}:
      Bool.not(Char.is_eq(c, 'h'))

def kind_ok(+k: String) -> Bool:
  Bool.and(Bool.not(T.has_char(k, ' ')), not_h(k))

def kinds_ok(ks: List<&2, String>) -> Bool:
  match ks:
    case Nil{}:
      True{}
    case +k <> rest:
      Bool.and(kind_ok(k), kinds_ok(rest))

def member_ok.of(c: Bool, +l: String, +rest: List<&2, String>, +k: String, +ec: {String.eq(l, k) == c : Bool}, +ha: {Bool.and(kind_ok(l), kinds_ok(rest)) == True{} : Bool}, hm: {Bool.or(c, Rev.member(rest, k)) == True{} : Bool}, ih: {kinds_ok(rest) == True{} : Bool} -> {Rev.member(rest, k) == True{} : Bool} -> {kind_ok(k) == True{} : Bool}) -> {kind_ok(k) == True{} : Bool}:
  match c:
    case True{}:
      %S.eq_true(l, k, ec) : {kind_ok(_) == True{} : Bool}
      ArrangeL.and_tl(kind_ok(l), kinds_ok(rest), ha)
    case False{}:
      ih(ArrangeL.and_tr(kind_ok(l), kinds_ok(rest), ha), hm)

def member_ok(ks: List<&2, String>, +k: String, +ha: {kinds_ok(ks) == True{} : Bool}, hm: {Rev.member(ks, k) == True{} : Bool}) -> {kind_ok(k) == True{} : Bool}:
  match ks:
    case Nil{}:
      Empty.absurd({kind_ok(k) == True{} : Bool}, S.false_true(hm))
    case +l <> +rest:
      member_ok.of(String.eq(l, k), l, rest, k, {==}, ha, hm, a => b => member_ok(rest, k, a, b))

# Every kind a reader of `historica-offer-1` knows.
def known(+k: String, hm: {Rev.member(Fetch.KINDS(), k) == True{} : Bool}) -> {kind_ok(k) == True{} : Bool}:
  member_ok(Fetch.KINDS(), k, {==}, hm)

def head_pick(b: Bool, +t: String, -y: String, eb: {Bool.not(b) == True{} : Bool}) -> {Bool.pick(Maybe<&2, String>, b, T.strip_prefix(t, y), None{}) == None{} : Maybe<&2, String>}:
  match b:
    case True{}:
      Empty.absurd({T.strip_prefix(t, y) == None{} : Maybe<&2, String>}, S.false_true(eb))
    case False{}:
      {==}

# A line starting with a kind is no head's.
def head_none(k: String, +x: String, h: {not_h(k) == True{} : Bool}) -> {T.strip_prefix(k ++ x, "head ") == None{} : Maybe<&2, String>}:
  match k:
    case SNil{}:
      Empty.absurd({T.strip_prefix(SNil{} ++ x, "head ") == None{} : Maybe<&2, String>}, S.false_true(h))
    case SCon{+c, +t}:
      head_pick(Char.is_eq(c, 'h'), t ++ x, "ead ", h)

# What a line says a file forgets: a digest, or `-` for nothing.
def forgets_ok(g: Maybe<&2, String>) -> Bool:
  match g:
    case None{}:
      True{}
    case Some{x}:
      T.is_digest(x)

def dash_digest(c: Bool, +x: String, ec: {String.eq(x, "-") == c : Bool}, h: {T.is_digest(x) == True{} : Bool}) -> {Bool.pick(Maybe<&2, String>, c, None{}, Some{x}) == Some{x} : Maybe<&2, String>}:
  match c:
    case True{}:
      Empty.absurd({None{} == Some{x} : Maybe<&2, String>}, S.false_true((%S.eq_true(x, "-", ec) : {T.is_digest(_) == True{} : Bool}; h)))
    case False{}:
      {==}

def g_nosp(g: Maybe<&2, String>, h: {forgets_ok(g) == True{} : Bool}) -> {T.has_char(Maybe.default(&2, String, g, "-"), ' ') == False{} : Bool}:
  match g:
    case None{}:
      {==}
    case Some{+x}:
      nosp_digest(x, h)

def g_ok(g: Maybe<&2, String>, h: {forgets_ok(g) == True{} : Bool}) -> {Bool.or(String.eq(Maybe.default(&2, String, g, "-"), "-"), T.is_digest(Maybe.default(&2, String, g, "-"))) == True{} : Bool}:
  match g:
    case None{}:
      {==}
    case Some{+x}:
      PruneL.or_rt(String.eq(x, "-"), T.is_digest(x), h)

def g_back(g: Maybe<&2, String>, h: {forgets_ok(g) == True{} : Bool}) -> {Fetch.forgets.of(Maybe.default(&2, String, g, "-")) == g : Maybe<&2, String>}:
  match g:
    case None{}:
      {==}
    case Some{+x}:
      dash_digest(String.eq(x, "-"), x, {==}, h)

def pick3(a: Bool, b: Bool, c: Bool, -x: Fetch.LRead, -y: Fetch.LRead, -z: Fetch.LRead, -w: Fetch.LRead, ea: {a == True{} : Bool}, eb: {b == True{} : Bool}, ec: {c == True{} : Bool}) -> {Bool.pick(Fetch.LRead, a, Bool.pick(Fetch.LRead, b, Bool.pick(Fetch.LRead, c, x, y), z), w) == x : Fetch.LRead}:
  match a b c:
    case True{} True{} True{}:
      {==}
    case False{} _ _:
      Empty.absurd({Bool.pick(Fetch.LRead, False{}, Bool.pick(Fetch.LRead, b, Bool.pick(Fetch.LRead, c, x, y), z), w) == x : Fetch.LRead}, S.false_true(ea))
    case True{} False{} _:
      Empty.absurd({Bool.pick(Fetch.LRead, True{}, Bool.pick(Fetch.LRead, False{}, Bool.pick(Fetch.LRead, c, x, y), z), w) == x : Fetch.LRead}, S.false_true(eb))
    case True{} True{} False{}:
      Empty.absurd({Bool.pick(Fetch.LRead, True{}, Bool.pick(Fetch.LRead, True{}, Bool.pick(Fetch.LRead, False{}, x, y), z), w) == x : Fetch.LRead}, S.false_true(ec))

# `fetch` reads the line `offer` writes for a file back as that file:
# its kind, its digest, what it forgets and its path, whatever spaces the
# path holds.
def line_back(+k: String, +d: String, +g: Maybe<&2, String>, +p: String, +rest: List<&2, String>, +nh: Bool, +hk: {Rev.member(Fetch.KINDS(), k) == True{} : Bool}, +hd: {T.is_digest(d) == True{} : Bool}, +hg: {forgets_ok(g) == True{} : Bool}) -> {Fetch.line.at(Offer.offered.line(Offer.Offered{k, d, g, p}) <> rest, nh) == Fetch.LRead.Entry{Offer.Offered{k, d, g, p}} : Fetch.LRead}:
  +gd = Maybe.default(&2, String, g, "-")
  +ko = known(k, hk)
  +r2 = gd ++ (" " ++ p)
  +r1 = d ++ (" " ++ r2)
  %Equal.sym(Maybe<&2, String>, T.strip_prefix(k ++ (" " ++ r1), "head "), None{}, head_none(k, " " ++ r1, ArrangeL.and_tr(Bool.not(T.has_char(k, ' ')), not_h(k), ko))) : {Fetch.line.head(nh, _, k ++ (" " ++ r1)) == Fetch.LRead.Entry{Offer.Offered{k, d, g, p}} : Fetch.LRead}
  %Equal.sym(Maybe<&2, T.Split>, T.split_once(k ++ (" " ++ r1)), Some{T.Split{k, r1}}, cut_word(k, r1, ArrangeL.not_tt(T.has_char(k, ' '), ArrangeL.and_tl(Bool.not(T.has_char(k, ' ')), not_h(k), ko)))) : {Fetch.line.fields(Fetch.four.a(_)) == Fetch.LRead.Entry{Offer.Offered{k, d, g, p}} : Fetch.LRead}
  %Equal.sym(Maybe<&2, T.Split>, T.split_once(r1), Some{T.Split{d, r2}}, cut_word(d, r2, nosp_digest(d, hd))) : {Fetch.line.fields(Fetch.four.b(k, _)) == Fetch.LRead.Entry{Offer.Offered{k, d, g, p}} : Fetch.LRead}
  %Equal.sym(Maybe<&2, T.Split>, T.split_once(r2), Some{T.Split{gd, p}}, cut_word(gd, p, g_nosp(g, hg))) : {Fetch.line.fields(Fetch.four.c(k, d, _)) == Fetch.LRead.Entry{Offer.Offered{k, d, g, p}} : Fetch.LRead}
  Equal.trans(Fetch.LRead, Fetch.line.entry(Fetch.Four{k, d, gd, p}), Fetch.LRead.Entry{Offer.Offered{k, d, Fetch.forgets.of(gd), p}}, Fetch.LRead.Entry{Offer.Offered{k, d, g, p}},
    pick3(Rev.member(Fetch.KINDS(), k), T.is_digest(d), Bool.or(String.eq(gd, "-"), T.is_digest(gd)), Fetch.LRead.Entry{Offer.Offered{k, d, Fetch.forgets.of(gd), p}}, Fetch.LRead.Bad{"a forgotten digest that is not a digest"}, Fetch.LRead.Bad{"a digest that is not a digest"}, Fetch.LRead.Skip{}, hk, hd, g_ok(g, hg)),
    Equal.cong(Maybe<&2, String>, Fetch.LRead, x => Fetch.LRead.Entry{Offer.Offered{k, d, x, p}}, Fetch.forgets.of(gd), g, g_back(g, hg)))
