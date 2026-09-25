# What `fetch` files, and what it asks for. A document of text is filed
# only where the text hashes to the digest the manifest's line gave it; a
# payload, or another tool's file, is renamed into place only where the host
# found its bytes hash to that digest, and a payload lands under the very
# digest it was found to have. Every path it asks the host for is one the
# manifest names.
import Base
import ./text.bend as T
import ./revision.bend as Rev
import ./tree.bend as Tree
import ./sha256.bend as Sha
import ./utf8.bend as Utf8
import ./folder.bend as Folder
import ./bookmark.bend as Bm
import ./commands.bend as Main
import ./receive.bend as Receive
import ./offer.bend as Offer
import ./fetch.bend as Fetch
import ./string_lemmas.bend as S
import ./receive_lemmas.bend as ReceiveL
import ./prune_lemmas.bend as PruneL
import ./blamed_lemmas.bend as B
import ./equality_lemmas.bend as Eq

# Landings
# --------

def isf(l: Fetch.Land) -> Bool:
  match l:
    case Fetch.Land.File{a, t}:
      True{}
    case _:
      False{}

def ftext(l: Fetch.Land) -> String:
  match l:
    case Fetch.Land.File{a, t}:
      t
    case _:
      SNil{}

def ism(l: Fetch.Land) -> Bool:
  match l:
    case Fetch.Land.Move{f, a, b}:
      True{}
    case _:
      False{}

def mto(l: Fetch.Land) -> String:
  match l:
    case Fetch.Land.Move{f, a, b}:
      b
    case _:
      SNil{}

# A landing a file is not: one said to be one is not there to say.
def not_file(-l: Fetch.Land, -at: String, -t: String, e: {l == Fetch.Land.File{at, t} : Fetch.Land}, h: {isf(l) == False{} : Bool}) -> Empty:
  S.false_true(Equal.trans(Bool, False{}, isf(l), True{}, Equal.sym(Bool, isf(l), False{}, h), Equal.cong(Fetch.Land, Bool, x => isf(x), l, Fetch.Land.File{at, t}, e)))

def not_move(-l: Fetch.Land, -f: String, -a: String, -b: String, e: {l == Fetch.Land.Move{f, a, b} : Fetch.Land}, h: {ism(l) == False{} : Bool}) -> Empty:
  S.false_true(Equal.trans(Bool, False{}, ism(l), True{}, Equal.sym(Bool, ism(l), False{}, h), Equal.cong(Fetch.Land, Bool, x => ism(x), l, Fetch.Land.Move{f, a, b}, e)))

# Of what a document's kind makes of its text, only a file is a file, and
# it is that text.
def fi(+p: String, fault: Maybe<&2, String>, +at: String, +t: String, h: {isf(Fetch.filed.if(p, fault, at, t)) == True{} : Bool}) -> {ftext(Fetch.filed.if(p, fault, at, t)) == t : String}:
  match fault:
    case Some{e}:
      Empty.absurd({ftext(Fetch.Land.Refuse{Fetch.unusable(p, e)}) == t : String}, S.false_true(h))
    case None{}:
      {==}

def ro(+p: String, +t: String, st: Folder.Stated) -> {isf(Fetch.rule.of(p, t, st)) == False{} : Bool}:
  match st:
    case Folder.Stated.Wrong{e}:
      {==}
    case Folder.Stated.None{}:
      {==}
    case Folder.Stated.One{sc}:
      {==}

def nu(+root: String, +n: String, r: Result<&2, &2, Main.Refused, Unit>, st: Bm.Stated) -> {isf(Fetch.name.usable(root, n, r, st)) == False{} : Bool}:
  match r:
    case Fail{Main.Refused{c, m}}:
      {==}
    case Done{u}:
      {==}

def no(+root: String, +p: String, +n: String, parsed: Result<&2, &2, String, Bm.Stated>) -> {isf(Fetch.name.of(root, p, n, parsed)) == False{} : Bool}:
  match parsed:
    case Fail{e}:
      {==}
    case Done{st}:
      nu(root, n, Main.name.checked.r(n), st)

def nl.c(c: Bool, +root: String, +p: String, +n: String, +t: String) -> {isf(Bool.pick(Fetch.Land, c, Fetch.Land.Skip{}, Fetch.name.of(root, p, n, Bm.parse(t)))) == False{} : Bool}:
  match c:
    case True{}:
      {==}
    case False{}:
      no(root, p, n, Bm.parse(t))

def nl(+root: String, +p: String, +held: List<&2, String>, m: Maybe<&2, String>, +t: String) -> {isf(Fetch.name.land(root, p, held, m, t)) == False{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+n}:
      nl.c(Rev.member(held, n), root, p, n, t)

def tl.c(c3: Bool, +root: String, +held: List<&2, String>, +p: String, +t: String, h: {isf(Bool.pick(Fetch.Land, c3, Fetch.rule.of(p, t, Folder.rule_in(t)), Fetch.name.land(root, p, held, Fetch.named_by(p), t))) == True{} : Bool}) -> {ftext(Bool.pick(Fetch.Land, c3, Fetch.rule.of(p, t, Folder.rule_in(t)), Fetch.name.land(root, p, held, Fetch.named_by(p), t))) == t : String}:
  match c3:
    case True{}:
      Empty.absurd({ftext(Fetch.rule.of(p, t, Folder.rule_in(t))) == t : String}, S.true_false(Equal.trans(Bool, True{}, isf(Fetch.rule.of(p, t, Folder.rule_in(t))), False{}, Equal.sym(Bool, isf(Fetch.rule.of(p, t, Folder.rule_in(t))), True{}, h), ro(p, t, Folder.rule_in(t)))))
    case False{}:
      Empty.absurd({ftext(Fetch.name.land(root, p, held, Fetch.named_by(p), t)) == t : String}, S.true_false(Equal.trans(Bool, True{}, isf(Fetch.name.land(root, p, held, Fetch.named_by(p), t)), False{}, Equal.sym(Bool, isf(Fetch.name.land(root, p, held, Fetch.named_by(p), t)), True{}, h), nl(root, p, held, Fetch.named_by(p), t))))

def tl.b(c2: Bool, c3: Bool, +root: String, +held: List<&2, String>, +d: String, +p: String, +t: String, h: {isf(Bool.pick(Fetch.Land, c2, Fetch.filed.if(p, Fetch.rev.ok(Rev.parse(t)), root ++ "/revisions/" ++ d ++ ".rev.txt", t), Bool.pick(Fetch.Land, c3, Fetch.rule.of(p, t, Folder.rule_in(t)), Fetch.name.land(root, p, held, Fetch.named_by(p), t)))) == True{} : Bool}) -> {ftext(Bool.pick(Fetch.Land, c2, Fetch.filed.if(p, Fetch.rev.ok(Rev.parse(t)), root ++ "/revisions/" ++ d ++ ".rev.txt", t), Bool.pick(Fetch.Land, c3, Fetch.rule.of(p, t, Folder.rule_in(t)), Fetch.name.land(root, p, held, Fetch.named_by(p), t)))) == t : String}:
  match c2:
    case True{}:
      fi(p, Fetch.rev.ok(Rev.parse(t)), root ++ "/revisions/" ++ d ++ ".rev.txt", t, h)
    case False{}:
      tl.c(c3, root, held, p, t, h)

def tl.a(c1: Bool, c2: Bool, c3: Bool, +root: String, +held: List<&2, String>, +d: String, +p: String, +t: String, h: {isf(Bool.pick(Fetch.Land, c1, Fetch.filed.if(p, Fetch.op.fault(t), root ++ "/operations/" ++ d ++ ".ops.txt", t), Bool.pick(Fetch.Land, c2, Fetch.filed.if(p, Fetch.rev.ok(Rev.parse(t)), root ++ "/revisions/" ++ d ++ ".rev.txt", t), Bool.pick(Fetch.Land, c3, Fetch.rule.of(p, t, Folder.rule_in(t)), Fetch.name.land(root, p, held, Fetch.named_by(p), t))))) == True{} : Bool}) -> {ftext(Bool.pick(Fetch.Land, c1, Fetch.filed.if(p, Fetch.op.fault(t), root ++ "/operations/" ++ d ++ ".ops.txt", t), Bool.pick(Fetch.Land, c2, Fetch.filed.if(p, Fetch.rev.ok(Rev.parse(t)), root ++ "/revisions/" ++ d ++ ".rev.txt", t), Bool.pick(Fetch.Land, c3, Fetch.rule.of(p, t, Folder.rule_in(t)), Fetch.name.land(root, p, held, Fetch.named_by(p), t))))) == t : String}:
  match c1:
    case True{}:
      fi(p, Fetch.op.fault(t), root ++ "/operations/" ++ d ++ ".ops.txt", t, h)
    case False{}:
      tl.b(c2, c3, root, held, d, p, t, h)

# Whatever a document's kind, what it files is the text that arrived.
def tl(+root: String, +held: List<&2, String>, o: Offer.Offered, +t: String, h: {isf(Fetch.text.land(root, held, o, t)) == True{} : Bool}) -> {ftext(Fetch.text.land(root, held, o, t)) == t : String}:
  match o:
    case Offer.Offered{+k, +d, f, +p}:
      tl.a(String.eq(k, "operation"), String.eq(k, "revision"), String.eq(k, "rule"), root, held, d, p, t, h)

# The text a file lands with, from a landing that is one.
def file_text(-l: Fetch.Land, -at: String, -t: String, e: {l == Fetch.Land.File{at, t} : Fetch.Land}) -> {ftext(l) == t : String}:
  Equal.cong(Fetch.Land, String, x => ftext(x), l, Fetch.Land.File{at, t}, e)

def file_is(-l: Fetch.Land, -at: String, -t: String, e: {l == Fetch.Land.File{at, t} : Fetch.Land}) -> {isf(l) == True{} : Bool}:
  Equal.cong(Fetch.Land, Bool, x => isf(x), l, Fetch.Land.File{at, t}, e)

def text.hit(c: Bool, +root: String, +held: List<&2, String>, +o: Offer.Offered, +t2: String, -at: String, -t: String, ec: {String.eq(Fetch.text.digest(t2), Fetch.entry.digest(o)) == c : Bool}, +e: {Bool.pick(Fetch.Land, c, Fetch.text.land(root, held, o, t2), Fetch.Land.Refuse{Fetch.TAMPERED(Fetch.entry.path(o), Fetch.entry.digest(o), Fetch.text.digest(t2))}) == Fetch.Land.File{at, t} : Fetch.Land}) -> {Sha.digest(Utf8.encode(t)) == Fetch.entry.digest(o) : String}:
  match c:
    case True{}:
      +same = Equal.trans(String, t, ftext(Fetch.text.land(root, held, o, t2)), t2, Equal.sym(String, ftext(Fetch.text.land(root, held, o, t2)), t, file_text(Fetch.text.land(root, held, o, t2), at, t, e)), tl(root, held, o, t2, file_is(Fetch.text.land(root, held, o, t2), at, t, e)))
      %Equal.sym(String, t, t2, same) : {Sha.digest(Utf8.encode(_)) == Fetch.entry.digest(o) : String}
      S.eq_true(Fetch.text.digest(t2), Fetch.entry.digest(o), ec)
    case False{}:
      Empty.absurd({Sha.digest(Utf8.encode(t)) == Fetch.entry.digest(o) : String}, not_file(Fetch.Land.Refuse{Fetch.TAMPERED(Fetch.entry.path(o), Fetch.entry.digest(o), Fetch.text.digest(t2))}, at, t, e, {==}))

def gone.hit(c: Bool, -m: String, -at: String, -t: String, e: {Bool.pick(Fetch.Land, c, Fetch.Land.Gone{}, Fetch.Land.Refuse{m}) == Fetch.Land.File{at, t} : Fetch.Land}) -> Empty:
  match c:
    case True{}:
      not_file(Fetch.Land.Gone{}, at, t, e, {==})
    case False{}:
      not_file(Fetch.Land.Refuse{m}, at, t, e, {==})

def bytes.hit(c: Bool, o: Offer.Offered, -m: String, -at: String, -t: String, e: {Bool.pick(Fetch.Land, c, Fetch.bytes.land(o), Fetch.Land.Refuse{m}) == Fetch.Land.File{at, t} : Fetch.Land}) -> Empty:
  match c:
    case True{}:
      match o:
        case Offer.Offered{+k, d, f, +p}:
          not_file(Fetch.bytes.land(Offer.Offered{k, d, f, p}), at, t, e, {==})
    case False{}:
      not_file(Fetch.Land.Refuse{m}, at, t, e, {==})

# A document of text is filed only where the text that arrived hashes to
# the digest its line gave: whatever the host answered, a landing that
# files text files text whose digest is the line's.
def filed_is_its_digest(+root: String, +held: List<&2, String>, +o: Offer.Offered, g: Fetch.Got, -at: String, -t: String, e: {Fetch.got.text(root, held, o, g) == Fetch.Land.File{at, t} : Fetch.Land}) -> {Sha.digest(Utf8.encode(t)) == Fetch.entry.digest(o) : String}:
  match g:
    case Fetch.Got.Failed{m}:
      Empty.absurd({Sha.digest(Utf8.encode(t)) == Fetch.entry.digest(o) : String}, not_file(Fetch.Land.Refuse{Fetch.unreachable(Fetch.entry.path(o), m)}, at, t, e, {==}))
    case Fetch.Got.Status{+c}:
      Empty.absurd({Sha.digest(Utf8.encode(t)) == Fetch.entry.digest(o) : String}, gone.hit(Fetch.gone(c), Fetch.unreachable(Fetch.entry.path(o), "the server answered " ++ c), at, t, e))
    case Fetch.Got.Bytes{+found}:
      Empty.absurd({Sha.digest(Utf8.encode(t)) == Fetch.entry.digest(o) : String}, bytes.hit(String.eq(found, Fetch.entry.digest(o)), o, Fetch.TAMPERED(Fetch.entry.path(o), Fetch.entry.digest(o), found), at, t, e))
    case Fetch.Got.Text{+t2}:
      text.hit(String.eq(Fetch.text.digest(t2), Fetch.entry.digest(o)), root, held, o, t2, at, t, {==}, e)
    case Fetch.Got.Pulled{d}:
      Empty.absurd({Sha.digest(Utf8.encode(t)) == Fetch.entry.digest(o) : String}, not_file(Fetch.Land.Refuse{Fetch.unreachable(Fetch.entry.path(o), "an answer that is not a document")}, at, t, e, {==}))

def gone.move(c: Bool, -m: String, -f: String, -a: String, -b: String, e: {Bool.pick(Fetch.Land, c, Fetch.Land.Gone{}, Fetch.Land.Refuse{m}) == Fetch.Land.Move{f, a, b} : Fetch.Land}) -> Empty:
  match c:
    case True{}:
      not_move(Fetch.Land.Gone{}, f, a, b, e, {==})
    case False{}:
      not_move(Fetch.Land.Refuse{m}, f, a, b, e, {==})

def mto_of(-l: Fetch.Land, -f: String, -a: String, -b: String, e: {l == Fetch.Land.Move{f, a, b} : Fetch.Land}) -> {mto(l) == b : String}:
  Equal.cong(Fetch.Land, String, x => mto(x), l, Fetch.Land.Move{f, a, b}, e)

def pull.hit(c: Bool, +folder: String, +name: String, +o: Offer.Offered, +found: String, -f: String, -a: String, -b: String, ec: {String.eq(found, Fetch.entry.digest(o)) == c : Bool}, e: {Bool.pick(Fetch.Land, c, Fetch.Land.Move{folder, Fetch.staged(name), name}, Fetch.Land.Discard{folder, Fetch.staged(name), Fetch.TAMPERED(Fetch.entry.path(o), Fetch.entry.digest(o), found)}) == Fetch.Land.Move{f, a, b} : Fetch.Land}) -> {Fetch.Got.Pulled{found} == Fetch.Got.Pulled{Fetch.entry.digest(o)} : Fetch.Got}:
  match c:
    case True{}:
      Equal.cong(String, Fetch.Got, x => Fetch.Got.Pulled{x}, found, Fetch.entry.digest(o), S.eq_true(found, Fetch.entry.digest(o), ec))
    case False{}:
      Empty.absurd({Fetch.Got.Pulled{found} == Fetch.Got.Pulled{Fetch.entry.digest(o)} : Fetch.Got}, not_move(Fetch.Land.Discard{folder, Fetch.staged(name), Fetch.TAMPERED(Fetch.entry.path(o), Fetch.entry.digest(o), found)}, f, a, b, e, {==}))

# A pulled file is renamed into place only where the host found what
# arrived to hash to the digest its line gave.
def moved_is_its_digest(+folder: String, +name: String, +o: Offer.Offered, g: Fetch.Got, -f: String, -a: String, -b: String, e: {Fetch.got.pull(folder, name, o, g) == Fetch.Land.Move{f, a, b} : Fetch.Land}) -> {g == Fetch.Got.Pulled{Fetch.entry.digest(o)} : Fetch.Got}:
  match g:
    case Fetch.Got.Failed{m}:
      Empty.absurd({Fetch.Got.Failed{m} == Fetch.Got.Pulled{Fetch.entry.digest(o)} : Fetch.Got}, not_move(Fetch.Land.Refuse{Fetch.unreachable(Fetch.entry.path(o), m)}, f, a, b, e, {==}))
    case Fetch.Got.Status{+c}:
      Empty.absurd({Fetch.Got.Status{c} == Fetch.Got.Pulled{Fetch.entry.digest(o)} : Fetch.Got}, gone.move(Fetch.gone(c), Fetch.unreachable(Fetch.entry.path(o), "the server answered " ++ c), f, a, b, e))
    case Fetch.Got.Pulled{+found}:
      pull.hit(String.eq(found, Fetch.entry.digest(o)), folder, name, o, found, f, a, b, {==}, e)
    case Fetch.Got.Text{t}:
      Empty.absurd({Fetch.Got.Text{t} == Fetch.Got.Pulled{Fetch.entry.digest(o)} : Fetch.Got}, not_move(Fetch.Land.Refuse{Fetch.unreachable(Fetch.entry.path(o), "an answer that is not a file")}, f, a, b, e, {==}))
    case Fetch.Got.Bytes{d}:
      Empty.absurd({Fetch.Got.Bytes{d} == Fetch.Got.Pulled{Fetch.entry.digest(o)} : Fetch.Got}, not_move(Fetch.Land.Refuse{Fetch.unreachable(Fetch.entry.path(o), "an answer that is not a file")}, f, a, b, e, {==}))

def pull.to(c: Bool, +folder: String, +name: String, -o: Offer.Offered, +found: String, -f: String, -a: String, -b: String, e: {Bool.pick(Fetch.Land, c, Fetch.Land.Move{folder, Fetch.staged(name), name}, Fetch.Land.Discard{folder, Fetch.staged(name), Fetch.TAMPERED(Fetch.entry.path(o), Fetch.entry.digest(o), found)}) == Fetch.Land.Move{f, a, b} : Fetch.Land}) -> {b == name : String}:
  match c:
    case True{}:
      Equal.sym(String, name, b, mto_of(Fetch.Land.Move{folder, Fetch.staged(name), name}, f, a, b, e))
    case False{}:
      Empty.absurd({b == name : String}, not_move(Fetch.Land.Discard{folder, Fetch.staged(name), Fetch.TAMPERED(Fetch.entry.path(o), Fetch.entry.digest(o), found)}, f, a, b, e, {==}))

# Where a pulled file lands is the name it was pulled for.
def moved_to_name(+folder: String, +name: String, +o: Offer.Offered, g: Fetch.Got, -f: String, -a: String, -b: String, e: {Fetch.got.pull(folder, name, o, g) == Fetch.Land.Move{f, a, b} : Fetch.Land}) -> {b == name : String}:
  match g:
    case Fetch.Got.Failed{m}:
      Empty.absurd({b == name : String}, not_move(Fetch.Land.Refuse{Fetch.unreachable(Fetch.entry.path(o), m)}, f, a, b, e, {==}))
    case Fetch.Got.Status{+c}:
      Empty.absurd({b == name : String}, gone.move(Fetch.gone(c), Fetch.unreachable(Fetch.entry.path(o), "the server answered " ++ c), f, a, b, e))
    case Fetch.Got.Pulled{+found}:
      pull.to(String.eq(found, Fetch.entry.digest(o)), folder, name, o, found, f, a, b, e)
    case Fetch.Got.Text{t}:
      Empty.absurd({b == name : String}, not_move(Fetch.Land.Refuse{Fetch.unreachable(Fetch.entry.path(o), "an answer that is not a file")}, f, a, b, e, {==}))
    case Fetch.Got.Bytes{d}:
      Empty.absurd({b == name : String}, not_move(Fetch.Land.Refuse{Fetch.unreachable(Fetch.entry.path(o), "an answer that is not a file")}, f, a, b, e, {==}))

# A payload lands in `operations/` under the digest the host found its
# bytes to have, which is the digest its line gave.
def payload_lands_under_its_digest(+root: String, +o: Offer.Offered, +g: Fetch.Got, -f: String, -a: String, -b: String, +e: {Fetch.pay.land(root, o, g) == Fetch.Land.Move{f, a, b} : Fetch.Land}) -> {Fetch.Got.Pulled{b} == g : Fetch.Got}:
  %Equal.sym(String, b, Fetch.entry.digest(o), moved_to_name(root ++ "/operations", Fetch.entry.digest(o), o, g, f, a, b, e)) : {Fetch.Got.Pulled{_} == g : Fetch.Got}
  Equal.sym(Fetch.Got, g, Fetch.Got.Pulled{Fetch.entry.digest(o)}, moved_is_its_digest(root ++ "/operations", Fetch.entry.digest(o), o, g, f, a, b, e))

# What it asks for
# ----------------

# A file kept by one of the plan's filters is one whose path was among
# those it was kept from.
def keep_paths(c: Bool, +o: Offer.Offered, -rest: List<&2, Offer.Offered>, +ps: List<&2, String>, ho: {Rev.member(ps, Offer.offered.path(o)) == True{} : Bool}, hr: {Main.all_held(ps, T.map(~Offer.Offered, ~String, ~(o => Offer.offered.path(o)), rest)) == True{} : Bool}) -> {Main.all_held(ps, T.map(~Offer.Offered, ~String, ~(o => Offer.offered.path(o)), Tree.keep(~Offer.Offered, c, o, rest))) == True{} : Bool}:
  match c:
    case True{}:
      B.and_tt(Rev.member(ps, Offer.offered.path(o)), Main.all_held(ps, T.map(~Offer.Offered, ~String, ~(o => Offer.offered.path(o)), rest)), ho, hr)
    case False{}:
      hr

def head_held(+o: Offer.Offered, -rest: List<&2, Offer.Offered>, +ps: List<&2, String>, +h: {Main.all_held(ps, T.map(~Offer.Offered, ~String, ~(o => Offer.offered.path(o)), o <> rest)) == True{} : Bool}) -> {Rev.member(ps, Offer.offered.path(o)) == True{} : Bool}:
  PruneL.and_l(Rev.member(ps, Offer.offered.path(o)), Main.all_held(ps, T.map(~Offer.Offered, ~String, ~(o => Offer.offered.path(o)), rest)), h)

def rest_held(+o: Offer.Offered, -rest: List<&2, Offer.Offered>, +ps: List<&2, String>, +h: {Main.all_held(ps, T.map(~Offer.Offered, ~String, ~(o => Offer.offered.path(o)), o <> rest)) == True{} : Bool}) -> {Main.all_held(ps, T.map(~Offer.Offered, ~String, ~(o => Offer.offered.path(o)), rest)) == True{} : Bool}:
  PruneL.and_r(Rev.member(ps, Offer.offered.path(o)), Main.all_held(ps, T.map(~Offer.Offered, ~String, ~(o => Offer.offered.path(o)), rest)), h)

def kind_held(xs: List<&2, Offer.Offered>, +k: String, +ps: List<&2, String>, +h: {Main.all_held(ps, T.map(~Offer.Offered, ~String, ~(o => Offer.offered.path(o)), xs)) == True{} : Bool}) -> {Main.all_held(ps, T.map(~Offer.Offered, ~String, ~(o => Offer.offered.path(o)), Fetch.of.kind(xs, k))) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +o <> +rest:
      keep_paths(String.eq(Fetch.entry.kind(o), k), o, Fetch.of.kind(rest, k), ps, head_held(o, rest, ps, h), kind_held(rest, k, ps, rest_held(o, rest, ps, h)))

def fresh_held(xs: List<&2, Offer.Offered>, +held: List<&2, String>, +forgotten: List<&2, String>, +ps: List<&2, String>, +h: {Main.all_held(ps, T.map(~Offer.Offered, ~String, ~(o => Offer.offered.path(o)), xs)) == True{} : Bool}) -> {Main.all_held(ps, T.map(~Offer.Offered, ~String, ~(o => Offer.offered.path(o)), Fetch.fresh(xs, held, forgotten))) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +o <> +rest:
      keep_paths(Bool.and(Bool.not(Rev.member(held, Fetch.entry.digest(o))), Bool.not(Rev.member(forgotten, Fetch.entry.digest(o)))), o, Fetch.fresh(rest, held, forgotten), ps, head_held(o, rest, ps, h), fresh_held(rest, held, forgotten, ps, rest_held(o, rest, ps, h)))

def once_held(xs: List<&2, Offer.Offered>, +seen: List<&2, String>, +ps: List<&2, String>, +h: {Main.all_held(ps, T.map(~Offer.Offered, ~String, ~(o => Offer.offered.path(o)), xs)) == True{} : Bool}) -> {Main.all_held(ps, T.map(~Offer.Offered, ~String, ~(o => Offer.offered.path(o)), Fetch.once(xs, seen))) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +o <> +rest:
      keep_paths(Bool.not(Rev.member(seen, Fetch.entry.digest(o))), o, Fetch.once(rest, Bool.pick(List<&2, String>, Rev.member(seen, Fetch.entry.digest(o)), seen, Fetch.entry.digest(o) <> seen)), ps, head_held(o, rest, ps, h), once_held(rest, Bool.pick(List<&2, String>, Rev.member(seen, Fetch.entry.digest(o)), seen, Fetch.entry.digest(o) <> seen), ps, rest_held(o, rest, ps, h)))

def names_held(xs: List<&2, Offer.Offered>, +held: List<&2, String>, +ps: List<&2, String>, +h: {Main.all_held(ps, T.map(~Offer.Offered, ~String, ~(o => Offer.offered.path(o)), xs)) == True{} : Bool}) -> {Main.all_held(ps, T.map(~Offer.Offered, ~String, ~(o => Offer.offered.path(o)), Fetch.names.fresh(xs, held))) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +o <> +rest:
      keep_paths(Fetch.name.wanted(held, Fetch.named_by(Fetch.entry.path(o))), o, Fetch.names.fresh(rest, held), ps, head_held(o, rest, ps, h), names_held(rest, held, ps, rest_held(o, rest, ps, h)))

def reserved_held(xs: List<&2, Offer.Offered>, +ours: List<&2, String>, +taken: List<&2, String>, +ps: List<&2, String>, +h: {Main.all_held(ps, T.map(~Offer.Offered, ~String, ~(o => Offer.offered.path(o)), xs)) == True{} : Bool}) -> {Main.all_held(ps, T.map(~Offer.Offered, ~String, ~(o => Offer.offered.path(o)), Fetch.reserved.go(xs, ours, taken))) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +o <> +rest:
      keep_paths(Maybe.is_some(&2, String, Fetch.reserved.takes(Fetch.reserved.label(o), ours, taken)), o, Fetch.reserved.go(rest, ours, Receive.forgets.push(Fetch.reserved.takes(Fetch.reserved.label(o), ours, taken), taken)), ps, head_held(o, rest, ps, h), reserved_held(rest, ours, Receive.forgets.push(Fetch.reserved.takes(Fetch.reserved.label(o), ours, taken), taken), ps, rest_held(o, rest, ps, h)))

def wanted_held(+os: List<&2, Offer.Offered>, +k: String, +held: List<&2, String>, +forgotten: List<&2, String>, +ps: List<&2, String>, +h: {Main.all_held(ps, T.map(~Offer.Offered, ~String, ~(o => Offer.offered.path(o)), os)) == True{} : Bool}) -> {Main.all_held(ps, T.map(~Offer.Offered, ~String, ~(o => Offer.offered.path(o)), Fetch.wanted(os, k, held, forgotten))) == True{} : Bool}:
  once_held(Fetch.fresh(Fetch.of.kind(os, k), held, forgotten), Nil{}, ps, fresh_held(Fetch.of.kind(os, k), held, forgotten, ps, kind_held(os, k, ps, h)))

# A step asks for its entry's path, whichever kind of step it is.
def step_path(c1: Bool, c2: Bool, -o: Offer.Offered) -> {Fetch.step.path(Bool.pick(Fetch.Step, c1, Fetch.Step.Pay{o}, Bool.pick(Fetch.Step, c2, Fetch.Step.Text{o}, Fetch.Step.Carry{o}))) == Some{Offer.offered.path(o)} : Maybe<&2, String>}:
  match c1:
    case True{}:
      {==}
    case False{}:
      match c2:
        case True{}:
          {==}
        case False{}:
          {==}

def asked_as(xs: List<&2, Offer.Offered>, +k: Nat) -> {Fetch.asked(Fetch.steps.as(xs, k)) == T.map(~Offer.Offered, ~String, ~(o => Offer.offered.path(o)), xs) : List<&2, String>}:
  match xs:
    case Nil{}:
      {==}
    case +o <> +rest:
      %Equal.sym(Maybe<&2, String>, Fetch.step.path(Bool.pick(Fetch.Step, Nat.is_eq(k, 0n), Fetch.Step.Pay{o}, Bool.pick(Fetch.Step, Nat.is_eq(k, 1n), Fetch.Step.Text{o}, Fetch.Step.Carry{o}))), Some{Offer.offered.path(o)}, step_path(Nat.is_eq(k, 0n), Nat.is_eq(k, 1n), o)) : {Receive.forgets.push(_, Fetch.asked(Fetch.steps.as(rest, k))) == T.map(~Offer.Offered, ~String, ~(o => Offer.offered.path(o)), o <> rest) : List<&2, String>}
      Equal.cong(List<&2, String>, List<&2, String>, x => Offer.offered.path(o) <> x, Fetch.asked(Fetch.steps.as(rest, k)), T.map(~Offer.Offered, ~String, ~(o => Offer.offered.path(o)), rest), asked_as(rest, k))

def asked_app.step(m: Maybe<&2, String>, -rest: List<&2, Fetch.Step>, -b: List<&2, Fetch.Step>, ih: {Fetch.asked(List.append(&2, Fetch.Step, rest, b)) == List.append(&2, String, Fetch.asked(rest), Fetch.asked(b)) : List<&2, String>}) -> {Receive.forgets.push(m, Fetch.asked(List.append(&2, Fetch.Step, rest, b))) == List.append(&2, String, Receive.forgets.push(m, Fetch.asked(rest)), Fetch.asked(b)) : List<&2, String>}:
  match m:
    case None{}:
      ih
    case Some{+x}:
      Equal.cong(List<&2, String>, List<&2, String>, y => x <> y, Fetch.asked(List.append(&2, Fetch.Step, rest, b)), List.append(&2, String, Fetch.asked(rest), Fetch.asked(b)), ih)

def asked_app(a: List<&2, Fetch.Step>, +b: List<&2, Fetch.Step>) -> {Fetch.asked(List.append(&2, Fetch.Step, a, b)) == List.append(&2, String, Fetch.asked(a), Fetch.asked(b)) : List<&2, String>}:
  match a:
    case Nil{}:
      {==}
    case s <> +rest:
      asked_app.step(Fetch.step.path(s), rest, b, asked_app(rest, b))

def held_app(a: List<&2, String>, +b: List<&2, String>, +ps: List<&2, String>, +ha: {Main.all_held(ps, a) == True{} : Bool}, hb: {Main.all_held(ps, b) == True{} : Bool}) -> {Main.all_held(ps, List.append(&2, String, a, b)) == True{} : Bool}:
  match a:
    case Nil{}:
      hb
    case +x <> +rest:
      B.and_tt(Rev.member(ps, x), Main.all_held(ps, List.append(&2, String, rest, b)), PruneL.and_l(Rev.member(ps, x), Main.all_held(ps, rest), ha), held_app(rest, b, ps, PruneL.and_r(Rev.member(ps, x), Main.all_held(ps, rest), ha), hb))

def held_steps(+a: List<&2, Fetch.Step>, +b: List<&2, Fetch.Step>, +ps: List<&2, String>, ha: {Main.all_held(ps, Fetch.asked(a)) == True{} : Bool}, hb: {Main.all_held(ps, Fetch.asked(b)) == True{} : Bool}) -> {Main.all_held(ps, Fetch.asked(List.append(&2, Fetch.Step, a, b))) == True{} : Bool}:
  %Equal.sym(List<&2, String>, Fetch.asked(List.append(&2, Fetch.Step, a, b)), List.append(&2, String, Fetch.asked(a), Fetch.asked(b)), asked_app(a, b)) : {Main.all_held(ps, _) == True{} : Bool}
  held_app(Fetch.asked(a), Fetch.asked(b), ps, ha, hb)

def held_as(+xs: List<&2, Offer.Offered>, +k: Nat, +ps: List<&2, String>, h: {Main.all_held(ps, T.map(~Offer.Offered, ~String, ~(o => Offer.offered.path(o)), xs)) == True{} : Bool}) -> {Main.all_held(ps, Fetch.asked(Fetch.steps.as(xs, k))) == True{} : Bool}:
  %Equal.sym(List<&2, String>, Fetch.asked(Fetch.steps.as(xs, k)), T.map(~Offer.Offered, ~String, ~(o => Offer.offered.path(o)), xs), asked_as(xs, k)) : {Main.all_held(ps, _) == True{} : Bool}
  h

def held_comply(c: Bool, +ps: List<&2, String>) -> {Main.all_held(ps, Fetch.asked(Bool.pick(List<&2, Fetch.Step>, c, [Fetch.Step.Comply{}], Nil{}))) == True{} : Bool}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

def held_plan(p: Fetch.FPlan, +ps: List<&2, String>, h1: {Main.all_held(ps, T.map(~Offer.Offered, ~String, ~(o => Offer.offered.path(o)), Fetch.plan.payloads(p))) == True{} : Bool}, h2: {Main.all_held(ps, T.map(~Offer.Offered, ~String, ~(o => Offer.offered.path(o)), Fetch.plan.documents(p))) == True{} : Bool}, h3: {Main.all_held(ps, T.map(~Offer.Offered, ~String, ~(o => Offer.offered.path(o)), Fetch.plan.revisions(p))) == True{} : Bool}, h4: {Main.all_held(ps, T.map(~Offer.Offered, ~String, ~(o => Offer.offered.path(o)), Fetch.plan.rules(p))) == True{} : Bool}, h5: {Main.all_held(ps, T.map(~Offer.Offered, ~String, ~(o => Offer.offered.path(o)), Fetch.plan.reserved(p))) == True{} : Bool}, h6: {Main.all_held(ps, T.map(~Offer.Offered, ~String, ~(o => Offer.offered.path(o)), Fetch.plan.names(p))) == True{} : Bool}) -> {Main.all_held(ps, Fetch.asked(Fetch.steps.of(p))) == True{} : Bool}:
  match p:
    case Fetch.FPlan{+pays, +docs, +revs, +rules, +res, +names, kept, dec, +des}:
      +comply = Bool.not(List.is_empty(&2, String, des))
      +early = Bool.and(comply, Bool.not(List.is_empty(&2, Offer.Offered, revs)))
      +late = Bool.and(comply, List.is_empty(&2, Offer.Offered, revs))
      held_steps(Fetch.steps.as(pays, 0n), List.concat(&2, Fetch.Step, [Fetch.steps.as(docs, 1n), Bool.pick(List<&2, Fetch.Step>, early, [Fetch.Step.Comply{}], Nil{}), Fetch.steps.as(revs, 1n), Fetch.steps.as(rules, 1n), Fetch.steps.as(res, 2n), Fetch.steps.as(names, 1n), Bool.pick(List<&2, Fetch.Step>, late, [Fetch.Step.Comply{}], Nil{})]), ps, held_as(pays, 0n, ps, h1),
      held_steps(Fetch.steps.as(docs, 1n), List.concat(&2, Fetch.Step, [Bool.pick(List<&2, Fetch.Step>, early, [Fetch.Step.Comply{}], Nil{}), Fetch.steps.as(revs, 1n), Fetch.steps.as(rules, 1n), Fetch.steps.as(res, 2n), Fetch.steps.as(names, 1n), Bool.pick(List<&2, Fetch.Step>, late, [Fetch.Step.Comply{}], Nil{})]), ps, held_as(docs, 1n, ps, h2),
      held_steps(Bool.pick(List<&2, Fetch.Step>, early, [Fetch.Step.Comply{}], Nil{}), List.concat(&2, Fetch.Step, [Fetch.steps.as(revs, 1n), Fetch.steps.as(rules, 1n), Fetch.steps.as(res, 2n), Fetch.steps.as(names, 1n), Bool.pick(List<&2, Fetch.Step>, late, [Fetch.Step.Comply{}], Nil{})]), ps, held_comply(early, ps),
      held_steps(Fetch.steps.as(revs, 1n), List.concat(&2, Fetch.Step, [Fetch.steps.as(rules, 1n), Fetch.steps.as(res, 2n), Fetch.steps.as(names, 1n), Bool.pick(List<&2, Fetch.Step>, late, [Fetch.Step.Comply{}], Nil{})]), ps, held_as(revs, 1n, ps, h3),
      held_steps(Fetch.steps.as(rules, 1n), List.concat(&2, Fetch.Step, [Fetch.steps.as(res, 2n), Fetch.steps.as(names, 1n), Bool.pick(List<&2, Fetch.Step>, late, [Fetch.Step.Comply{}], Nil{})]), ps, held_as(rules, 1n, ps, h4),
      held_steps(Fetch.steps.as(res, 2n), List.concat(&2, Fetch.Step, [Fetch.steps.as(names, 1n), Bool.pick(List<&2, Fetch.Step>, late, [Fetch.Step.Comply{}], Nil{})]), ps, held_as(res, 2n, ps, h5),
      held_steps(Fetch.steps.as(names, 1n), List.concat(&2, Fetch.Step, [Bool.pick(List<&2, Fetch.Step>, late, [Fetch.Step.Comply{}], Nil{})]), ps, held_as(names, 1n, ps, h6),
      held_steps(Bool.pick(List<&2, Fetch.Step>, late, [Fetch.Step.Comply{}], Nil{}), Nil{}, ps, held_comply(late, ps), {==}))))))))

# Every path a fetch asks the host for, in any pass, is one the manifest
# names.
def asks_what_is_named(h: Fetch.Here, +os: List<&2, Offer.Offered>) -> {Main.all_held(T.map(~Offer.Offered, ~String, ~(o => Offer.offered.path(o)), os), Fetch.asked(Fetch.steps.of(Fetch.plan.of(h, os)))) == True{} : Bool}:
  match h:
    case Fetch.Here{+revs, +docs, +pays, +forgets, +rules, +names, +claims}:
      +ps = T.map(~Offer.Offered, ~String, ~(o => Offer.offered.path(o)), os)
      +all = ReceiveL.held_refl(ps)
      +forgotten = List.append(&2, String, forgets, Fetch.entry.forgets(os))
      held_plan(Fetch.plan.of(Fetch.Here{revs, docs, pays, forgets, rules, names, claims}, os), ps,
        wanted_held(os, "payload", pays, forgotten, ps, all),
        wanted_held(os, "operation", docs, forgotten, ps, all),
        wanted_held(os, "revision", Main.ids(revs), Nil{}, ps, all),
        wanted_held(os, "rule", rules, Nil{}, ps, all),
        reserved_held(os, claims, Nil{}, ps, all),
        once_held(Fetch.names.fresh(Fetch.of.kind(os, "name"), names), Nil{}, ps, names_held(Fetch.of.kind(os, "name"), names, ps, kind_held(os, "name", ps, all))))

# Where it asks
# -------------

def app_nil(s: String) -> {String.append(s, SNil{}) == s : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+h, t}:
      Equal.cong(String, String, x => SCon{h, x}, String.append(t, SNil{}), t, app_nil(t))

def rev_go(s: String, +acc: String) -> {String.reverse.go(s, acc) == String.append(String.reverse(s), acc) : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      Equal.trans(String, String.reverse.go(t, SCon{h, acc}), String.append(String.reverse(t), SCon{h, acc}), String.append(String.reverse.go(t, SCon{h, SNil{}}), acc),
        rev_go(t, SCon{h, acc}),
        Equal.sym(String, String.append(String.reverse.go(t, SCon{h, SNil{}}), acc), String.append(String.reverse(t), SCon{h, acc}),
          Equal.trans(String, String.append(String.reverse.go(t, SCon{h, SNil{}}), acc), String.append(String.append(String.reverse(t), SCon{h, SNil{}}), acc), String.append(String.reverse(t), SCon{h, acc}),
            Equal.cong(String, String, x => String.append(x, acc), String.reverse.go(t, SCon{h, SNil{}}), String.append(String.reverse(t), SCon{h, SNil{}}), rev_go(t, SCon{h, SNil{}})),
            B.app_assoc(String.reverse(t), SCon{h, SNil{}}, acc))))

def rev_app1(x: String, +h: Char) -> {String.reverse(String.append(x, SCon{h, SNil{}})) == SCon{h, String.reverse(x)} : String}:
  match x:
    case SNil{}:
      {==}
    case SCon{+c, +y}:
      Equal.trans(String, String.reverse.go(String.append(y, SCon{h, SNil{}}), SCon{c, SNil{}}), String.append(String.reverse(String.append(y, SCon{h, SNil{}})), SCon{c, SNil{}}), SCon{h, String.reverse.go(y, SCon{c, SNil{}})},
        rev_go(String.append(y, SCon{h, SNil{}}), SCon{c, SNil{}}),
        Equal.trans(String, String.append(String.reverse(String.append(y, SCon{h, SNil{}})), SCon{c, SNil{}}), SCon{h, String.append(String.reverse(y), SCon{c, SNil{}})}, SCon{h, String.reverse.go(y, SCon{c, SNil{}})},
          Equal.cong(String, String, z => String.append(z, SCon{c, SNil{}}), String.reverse(String.append(y, SCon{h, SNil{}})), SCon{h, String.reverse(y)}, rev_app1(y, h)),
          Equal.sym(String, SCon{h, String.reverse.go(y, SCon{c, SNil{}})}, SCon{h, String.append(String.reverse(y), SCon{c, SNil{}})},
            Equal.cong(String, String, z => SCon{h, z}, String.reverse.go(y, SCon{c, SNil{}}), String.append(String.reverse(y), SCon{c, SNil{}}), rev_go(y, SCon{c, SNil{}})))))

def rev_rev(s: String) -> {String.reverse(String.reverse(s)) == s : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      Equal.trans(String, String.reverse(String.reverse.go(t, SCon{h, SNil{}})), String.reverse(String.append(String.reverse(t), SCon{h, SNil{}})), SCon{h, t},
        Equal.cong(String, String, x => String.reverse(x), String.reverse.go(t, SCon{h, SNil{}}), String.append(String.reverse(t), SCon{h, SNil{}}), rev_go(t, SCon{h, SNil{}})),
        Equal.trans(String, String.reverse(String.append(String.reverse(t), SCon{h, SNil{}})), SCon{h, String.reverse(String.reverse(t))}, SCon{h, t},
          rev_app1(String.reverse(t), h),
          Equal.cong(String, String, x => SCon{h, x}, String.reverse(String.reverse(t)), t, rev_rev(t))))

def drop0(s: String) -> {s == String.drop(s, 0n) : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{h, t}:
      {==}

def sw.step(b: Bool, +x: Char, +xt: String, +y: Char, +yt: String, eb: {Char.is_eq(x, y) == b : Bool}, h: {String.starts_with.if(xt, yt, b) == True{} : Bool}, ih: {String.starts_with(xt, yt) == True{} : Bool} -> {xt == String.append(yt, String.drop(xt, String.length(yt))) : String}) -> {SCon{x, xt} == SCon{y, String.append(yt, String.drop(xt, String.length(yt)))} : String}:
  match b:
    case False{}:
      Empty.absurd({SCon{x, xt} == SCon{y, String.append(yt, String.drop(xt, String.length(yt)))} : String}, S.false_true(h))
    case True{}:
      %Eq.char_eq(x, y, eb) : {SCon{x, xt} == SCon{_, String.append(yt, String.drop(xt, String.length(yt)))} : String}
      Equal.cong(String, String, z => SCon{x, z}, xt, String.append(yt, String.drop(xt, String.length(yt))), ih(h))

def sw.s(s: String, +y: Char, +yt: String, h: {String.starts_with(s, SCon{y, yt}) == True{} : Bool}, ih: @xt: String -> {String.starts_with(xt, yt) == True{} : Bool} -> {xt == String.append(yt, String.drop(xt, String.length(yt))) : String}) -> {s == String.append(SCon{y, yt}, String.drop(s, String.length(SCon{y, yt}))) : String}:
  match s:
    case SNil{}:
      Empty.absurd({SNil{} == String.append(SCon{y, yt}, String.drop(SNil{}, String.length(SCon{y, yt}))) : String}, S.false_true(h))
    case SCon{+x, +xt}:
      sw.step(Char.is_eq(x, y), x, xt, y, yt, {==}, h, ih(xt))

# A string that starts with a prefix is that prefix and the rest of it.
def sw(p: String, +s: String, h: {String.starts_with(s, p) == True{} : Bool}) -> {s == String.append(p, String.drop(s, String.length(p))) : String}:
  match p:
    case SNil{}:
      drop0(s)
    case SCon{+y, +yt}:
      sw.s(s, y, yt, h, xt => hx => sw(yt, xt, hx))

def sp.a(m: Maybe<&2, T.Split>) -> String:
  match m:
    case Some{T.Split{a, b}}:
      a
    case None{}:
      SNil{}

def sp.b(m: Maybe<&2, T.Split>) -> String:
  match m:
    case Some{T.Split{a, b}}:
      b
    case None{}:
      SNil{}

def sp.is(m: Maybe<&2, T.Split>) -> Bool:
  match m:
    case Some{x}:
      True{}
    case None{}:
      False{}

def none_split(-p: String, -r: String, e: {None{} == Some{T.Split{p, r}} : Maybe<&2, T.Split>}) -> Empty:
  S.false_true(Equal.cong(Maybe<&2, T.Split>, Bool, x => sp.is(x), None{}, Some{T.Split{p, r}}, e))

# The pair a found split is, read off an equation saying which it is.
def split_eq(-a: String, -b: String, -p: String, -r: String, +e: {Some{T.Split{a, b}} == Some{T.Split{p, r}} : Maybe<&2, T.Split>}) -> {String.append(a, b) == String.append(p, r) : String}:
  %Equal.cong(Maybe<&2, T.Split>, String, x => sp.a(x), Some{T.Split{a, b}}, Some{T.Split{p, r}}, e) : {String.append(a, b) == String.append(_, r) : String}
  %Equal.cong(Maybe<&2, T.Split>, String, x => sp.b(x), Some{T.Split{a, b}}, Some{T.Split{p, r}}, e) : {String.append(a, b) == String.append(a, _) : String}
  {==}

def sc.step(b: Bool, +c: Char, +t: String, +acc: String, -p: String, -r: String, eb: {String.starts_with(SCon{c, t}, "://") == b : Bool}, e: {Bool.pick(Maybe<&2, T.Split>, b, Some{T.Split{String.append(String.reverse(acc), "://"), String.drop(t, 2n)}}, Fetch.scheme.go(t, SCon{c, acc})) == Some{T.Split{p, r}} : Maybe<&2, T.Split>}, ih: {Fetch.scheme.go(t, SCon{c, acc}) == Some{T.Split{p, r}} : Maybe<&2, T.Split>} -> {String.append(p, r) == String.append(String.reverse(SCon{c, acc}), t) : String}) -> {String.append(p, r) == String.append(String.reverse(acc), SCon{c, t}) : String}:
  match b:
    case True{}:
      +whole = sw("://", SCon{c, t}, eb)
      Equal.trans(String, String.append(p, r), String.append(String.append(String.reverse(acc), "://"), String.drop(t, 2n)), String.append(String.reverse(acc), SCon{c, t}),
        Equal.sym(String, String.append(String.append(String.reverse(acc), "://"), String.drop(t, 2n)), String.append(p, r), split_eq(String.append(String.reverse(acc), "://"), String.drop(t, 2n), p, r, e)),
        Equal.trans(String, String.append(String.append(String.reverse(acc), "://"), String.drop(t, 2n)), String.append(String.reverse(acc), String.append("://", String.drop(t, 2n))), String.append(String.reverse(acc), SCon{c, t}),
          B.app_assoc(String.reverse(acc), "://", String.drop(t, 2n)),
          Equal.cong(String, String, x => String.append(String.reverse(acc), x), String.append("://", String.drop(t, 2n)), SCon{c, t}, Equal.sym(String, SCon{c, t}, String.append("://", String.drop(t, 2n)), whole))))
    case False{}:
      Equal.trans(String, String.append(p, r), String.append(String.reverse(SCon{c, acc}), t), String.append(String.reverse(acc), SCon{c, t}),
        ih(e),
        Equal.trans(String, String.append(String.reverse.go(acc, SCon{c, SNil{}}), t), String.append(String.append(String.reverse(acc), SCon{c, SNil{}}), t), String.append(String.reverse(acc), SCon{c, t}),
          Equal.cong(String, String, x => String.append(x, t), String.reverse.go(acc, SCon{c, SNil{}}), String.append(String.reverse(acc), SCon{c, SNil{}}), rev_go(acc, SCon{c, SNil{}})),
          B.app_assoc(String.reverse(acc), SCon{c, SNil{}}, t)))

# What precedes a URL's first `://`, and what follows it, are the URL.
def scheme_ok(s: String, +acc: String, -p: String, -r: String, e: {Fetch.scheme.go(s, acc) == Some{T.Split{p, r}} : Maybe<&2, T.Split>}) -> {String.append(p, r) == String.append(String.reverse(acc), s) : String}:
  match s:
    case SNil{}:
      Empty.absurd({String.append(p, r) == String.append(String.reverse(acc), SNil{}) : String}, none_split(p, r, e))
    case SCon{+c, +t}:
      sc.step(String.starts_with(SCon{c, t}, "://"), c, t, acc, p, r, {==}, e, x => scheme_ok(t, SCon{c, acc}, p, r, x))

def sl.step(b: Bool, +c: Char, +t: String, +acc: String, -d: String, -n: String, eb: {Char.is_eq(c, '/') == b : Bool}, e: {Bool.pick(Maybe<&2, T.Split>, b, Some{T.Split{String.append(String.reverse(t), "/"), acc}}, Fetch.slash.last(t, SCon{c, acc})) == Some{T.Split{d, n}} : Maybe<&2, T.Split>}, ih: {Fetch.slash.last(t, SCon{c, acc}) == Some{T.Split{d, n}} : Maybe<&2, T.Split>} -> {String.append(d, n) == String.append(String.reverse(t), SCon{c, acc}) : String}) -> {String.append(d, n) == String.append(String.reverse(SCon{c, t}), acc) : String}:
  match b:
    case True{}:
      %Equal.sym(Char, c, '/', Eq.char_eq(c, '/', eb)) : {String.append(d, n) == String.append(String.reverse(SCon{_, t}), acc) : String}
      Equal.trans(String, String.append(d, n), String.append(String.append(String.reverse(t), "/"), acc), String.append(String.reverse.go(t, "/"), acc),
        Equal.sym(String, String.append(String.append(String.reverse(t), "/"), acc), String.append(d, n), split_eq(String.append(String.reverse(t), "/"), acc, d, n, e)),
        Equal.sym(String, String.append(String.reverse.go(t, "/"), acc), String.append(String.append(String.reverse(t), "/"), acc),
          Equal.cong(String, String, x => String.append(x, acc), String.reverse.go(t, "/"), String.append(String.reverse(t), "/"), rev_go(t, "/"))))
    case False{}:
      Equal.trans(String, String.append(d, n), String.append(String.reverse(t), SCon{c, acc}), String.append(String.reverse.go(t, SCon{c, SNil{}}), acc),
        ih(e),
        Equal.sym(String, String.append(String.reverse.go(t, SCon{c, SNil{}}), acc), String.append(String.reverse(t), SCon{c, acc}),
          Equal.trans(String, String.append(String.reverse.go(t, SCon{c, SNil{}}), acc), String.append(String.append(String.reverse(t), SCon{c, SNil{}}), acc), String.append(String.reverse(t), SCon{c, acc}),
            Equal.cong(String, String, x => String.append(x, acc), String.reverse.go(t, SCon{c, SNil{}}), String.append(String.reverse(t), SCon{c, SNil{}}), rev_go(t, SCon{c, SNil{}})),
            B.app_assoc(String.reverse(t), SCon{c, SNil{}}, acc))))

# Over a string reversed, what precedes its last `/` and what follows put
# back together are the string, with what was already held on the end.
def slash_ok(r: String, +acc: String, -d: String, -n: String, e: {Fetch.slash.last(r, acc) == Some{T.Split{d, n}} : Maybe<&2, T.Split>}) -> {String.append(d, n) == String.append(String.reverse(r), acc) : String}:
  match r:
    case SNil{}:
      Empty.absurd({String.append(d, n) == String.append(String.reverse(SNil{}), acc) : String}, none_split(d, n, e))
    case SCon{+c, +t}:
      sl.step(Char.is_eq(c, '/'), c, t, acc, d, n, {==}, e, x => slash_ok(t, SCon{c, acc}, d, n, x))

def sn.step(b: Bool, +c: Char, +t: String, +acc: String, -d: String, -n: String, eb: {Char.is_eq(c, '/') == b : Bool}, e: {Bool.pick(Maybe<&2, T.Split>, b, Some{T.Split{String.append(String.reverse(t), "/"), acc}}, Fetch.slash.last(t, SCon{c, acc})) == Some{T.Split{d, n}} : Maybe<&2, T.Split>}, ha: {List.all(~&2, ~Char, ~(c => Bool.not(Char.is_eq(c, '/'))), String.to_list(acc)) == True{} : Bool}, ih: {Fetch.slash.last(t, SCon{c, acc}) == Some{T.Split{d, n}} : Maybe<&2, T.Split>} -> {List.all(~&2, ~Char, ~(c => Bool.not(Char.is_eq(c, '/'))), String.to_list(SCon{c, acc})) == True{} : Bool} -> {List.all(~&2, ~Char, ~(c => Bool.not(Char.is_eq(c, '/'))), String.to_list(n)) == True{} : Bool}) -> {List.all(~&2, ~Char, ~(c => Bool.not(Char.is_eq(c, '/'))), String.to_list(n)) == True{} : Bool}:
  match b:
    case True{}:
      %Equal.cong(Maybe<&2, T.Split>, String, x => sp.b(x), Some{T.Split{String.append(String.reverse(t), "/"), acc}}, Some{T.Split{d, n}}, e) : {List.all(~&2, ~Char, ~(c => Bool.not(Char.is_eq(c, '/'))), String.to_list(_)) == True{} : Bool}
      ha
    case False{}:
      ih(e, %Equal.sym(Bool, Char.is_eq(c, '/'), False{}, eb) : {Bool.and(Bool.not(_), List.all(~&2, ~Char, ~(c => Bool.not(Char.is_eq(c, '/'))), String.to_list(acc))) == True{} : Bool}
        ha)

# And nothing that followed the last `/` is one.
def slash_ns(r: String, +acc: String, -d: String, -n: String, e: {Fetch.slash.last(r, acc) == Some{T.Split{d, n}} : Maybe<&2, T.Split>}, ha: {List.all(~&2, ~Char, ~(c => Bool.not(Char.is_eq(c, '/'))), String.to_list(acc)) == True{} : Bool}) -> {List.all(~&2, ~Char, ~(c => Bool.not(Char.is_eq(c, '/'))), String.to_list(n)) == True{} : Bool}:
  match r:
    case SNil{}:
      Empty.absurd({List.all(~&2, ~Char, ~(c => Bool.not(Char.is_eq(c, '/'))), String.to_list(n)) == True{} : Bool}, none_split(d, n, e))
    case SCon{+c, +t}:
      sn.step(Char.is_eq(c, '/'), c, t, acc, d, n, {==}, e, ha, x => h2 => slash_ns(t, SCon{c, acc}, d, n, x, h2))

# Every string starts with the empty one.
def sw_nil(s: String) -> {String.starts_with(s, SNil{}) == True{} : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{h, t}:
      {==}

def swa.step(bb: Bool, +x: Char, +xt: String, +b: String, +y: Char, +yt: String, eb: {Char.is_eq(x, y) == bb : Bool}, h: {String.starts_with.if(xt, yt, bb) == True{} : Bool}, ih: {String.starts_with(xt, yt) == True{} : Bool} -> {String.starts_with(String.append(xt, b), yt) == True{} : Bool}) -> {String.starts_with(SCon{x, String.append(xt, b)}, SCon{y, yt}) == True{} : Bool}:
  match bb:
    case False{}:
      Empty.absurd({String.starts_with(SCon{x, String.append(xt, b)}, SCon{y, yt}) == True{} : Bool}, S.false_true(h))
    case True{}:
      %Equal.sym(Bool, Char.is_eq(x, y), True{}, eb) : {String.starts_with.if(String.append(xt, b), yt, _) == True{} : Bool}
      ih(h)

def swa.s(a: String, +b: String, +y: Char, +yt: String, h: {String.starts_with(a, SCon{y, yt}) == True{} : Bool}, ih: @xt: String -> {String.starts_with(xt, yt) == True{} : Bool} -> {String.starts_with(String.append(xt, b), yt) == True{} : Bool}) -> {String.starts_with(String.append(a, b), SCon{y, yt}) == True{} : Bool}:
  match a:
    case SNil{}:
      Empty.absurd({String.starts_with(String.append(SNil{}, b), SCon{y, yt}) == True{} : Bool}, S.false_true(h))
    case SCon{+x, +xt}:
      swa.step(Char.is_eq(x, y), x, xt, b, y, yt, {==}, h, ih(xt))

# What starts with a prefix still does with anything after it.
def sw_app(c: String, +a: String, +b: String, h: {String.starts_with(a, c) == True{} : Bool}) -> {String.starts_with(String.append(a, b), c) == True{} : Bool}:
  match c:
    case SNil{}:
      sw_nil(String.append(a, b))
    case SCon{+y, +yt}:
      swa.s(a, b, y, yt, h, xt => hx => sw_app(yt, xt, b, hx))

# Two strings put together, reversed, are each reversed the other way round.
def rev_app(a: String, +b: String) -> {String.reverse(String.append(a, b)) == String.append(String.reverse(b), String.reverse(a)) : String}:
  match a:
    case SNil{}:
      Equal.sym(String, String.append(String.reverse(b), SNil{}), String.reverse(b), app_nil(String.reverse(b)))
    case SCon{+h, +t}:
      Equal.trans(String, String.reverse.go(String.append(t, b), SCon{h, SNil{}}), String.append(String.reverse(String.append(t, b)), SCon{h, SNil{}}), String.append(String.reverse(b), String.reverse.go(t, SCon{h, SNil{}})),
        rev_go(String.append(t, b), SCon{h, SNil{}}),
        Equal.trans(String, String.append(String.reverse(String.append(t, b)), SCon{h, SNil{}}), String.append(String.append(String.reverse(b), String.reverse(t)), SCon{h, SNil{}}), String.append(String.reverse(b), String.reverse.go(t, SCon{h, SNil{}})),
          Equal.cong(String, String, x => String.append(x, SCon{h, SNil{}}), String.reverse(String.append(t, b)), String.append(String.reverse(b), String.reverse(t)), rev_app(t, b)),
          Equal.trans(String, String.append(String.append(String.reverse(b), String.reverse(t)), SCon{h, SNil{}}), String.append(String.reverse(b), String.append(String.reverse(t), SCon{h, SNil{}})), String.append(String.reverse(b), String.reverse.go(t, SCon{h, SNil{}})),
            B.app_assoc(String.reverse(b), String.reverse(t), SCon{h, SNil{}}),
            Equal.cong(String, String, x => String.append(String.reverse(b), x), String.append(String.reverse(t), SCon{h, SNil{}}), String.reverse.go(t, SCon{h, SNil{}}), Equal.sym(String, String.reverse.go(t, SCon{h, SNil{}}), String.append(String.reverse(t), SCon{h, SNil{}}), rev_go(t, SCon{h, SNil{}}))))))

# Whatever ends with `/` still does with anything in front of it.
def ends_app(+p: String, +d: String, h: {String.ends_with(d, "/") == True{} : Bool}) -> {String.ends_with(String.append(p, d), "/") == True{} : Bool}:
  %Equal.sym(String, String.reverse(String.append(p, d)), String.append(String.reverse(d), String.reverse(p)), rev_app(p, d)) : {String.starts_with(_, "/") == True{} : Bool}
  sw_app("/", String.reverse(d), String.reverse(p), h)

def se.step(b: Bool, +c: Char, +t: String, +acc: String, -d: String, -n: String, eb: {Char.is_eq(c, '/') == b : Bool}, e: {Bool.pick(Maybe<&2, T.Split>, b, Some{T.Split{String.append(String.reverse(t), "/"), acc}}, Fetch.slash.last(t, SCon{c, acc})) == Some{T.Split{d, n}} : Maybe<&2, T.Split>}, ih: {Fetch.slash.last(t, SCon{c, acc}) == Some{T.Split{d, n}} : Maybe<&2, T.Split>} -> {String.ends_with(d, "/") == True{} : Bool}) -> {String.ends_with(d, "/") == True{} : Bool}:
  match b:
    case True{}:
      %Equal.cong(Maybe<&2, T.Split>, String, x => sp.a(x), Some{T.Split{String.append(String.reverse(t), "/"), acc}}, Some{T.Split{d, n}}, e) : {String.ends_with(_, "/") == True{} : Bool}
      %Equal.sym(String, String.reverse(String.append(String.reverse(t), "/")), SCon{'/', String.reverse(String.reverse(t))}, rev_app1(String.reverse(t), '/')) : {String.starts_with(_, "/") == True{} : Bool}
      sw_nil(String.reverse(String.reverse(t)))
    case False{}:
      ih(e)

# Over a string reversed, what precedes its last `/` ends with it.
def slash_end(r: String, +acc: String, -d: String, -n: String, e: {Fetch.slash.last(r, acc) == Some{T.Split{d, n}} : Maybe<&2, T.Split>}) -> {String.ends_with(d, "/") == True{} : Bool}:
  match r:
    case SNil{}:
      Empty.absurd({String.ends_with(d, "/") == True{} : Bool}, none_split(d, n, e))
    case SCon{+c, +t}:
      se.step(Char.is_eq(c, '/'), c, t, acc, d, n, {==}, e, x => slash_end(t, SCon{c, acc}, d, n, x))

# The whole of the URL, put back together from where it was cut.
def url_whole(+url: String, +pre: String, +rest: String, +dir: String, +name: String, es: {Fetch.scheme.go(url, SNil{}) == Some{T.Split{pre, rest}} : Maybe<&2, T.Split>}, esl: {Fetch.slash.last(String.reverse(rest), SNil{}) == Some{T.Split{dir, name}} : Maybe<&2, T.Split>}) -> {String.append(String.append(pre, dir), name) == url : String}:
  Equal.trans(String, String.append(String.append(pre, dir), name), String.append(pre, String.append(dir, name)), url,
    B.app_assoc(pre, dir, name),
    Equal.trans(String, String.append(pre, String.append(dir, name)), String.append(pre, rest), url,
      Equal.cong(String, String, x => String.append(pre, x), String.append(dir, name), rest,
        Equal.trans(String, String.append(dir, name), String.append(String.reverse(String.reverse(rest)), SNil{}), rest,
          slash_ok(String.reverse(rest), SNil{}, dir, name, esl),
          Equal.trans(String, String.append(String.reverse(String.reverse(rest)), SNil{}), String.reverse(String.reverse(rest)), rest, app_nil(String.reverse(String.reverse(rest))), rev_rev(rest)))),
      scheme_ok(url, SNil{}, pre, rest, es)))

def ad.empty(b: Bool, +url: String, +pre: String, +rest: String, +dir: String, +name: String, -r: String, -m: String, eb: {String.is_empty(name) == b : Bool}, es: {Fetch.scheme.go(url, SNil{}) == Some{T.Split{pre, rest}} : Maybe<&2, T.Split>}, +esl: {Fetch.slash.last(String.reverse(rest), SNil{}) == Some{T.Split{dir, name}} : Maybe<&2, T.Split>}, +e: {Bool.pick(Result<&2, &2, Main.Refused, Fetch.Addressed>, b, Fail{Main.Refused{2, "`" ++ url ++ "` names a directory; `fetch` wants the URL of the manifest in it, conventionally `offer.txt`"}}, Done{Fetch.Addressed{String.append(pre, dir), name}}) == Done{Fetch.Addressed{r, m}} : Result<&2, &2, Main.Refused, Fetch.Addressed>}) -> {Bool.and(String.eq(String.append(r, m), url), Bool.and(String.ends_with(r, "/"), Bool.and(Bool.not(String.is_empty(m)), List.all(~&2, ~Char, ~(c => Bool.not(Char.is_eq(c, '/'))), String.to_list(m))))) == True{} : Bool}:
  match b:
    case True{}:
      Empty.absurd({Bool.and(String.eq(String.append(r, m), url), Bool.and(String.ends_with(r, "/"), Bool.and(Bool.not(String.is_empty(m)), List.all(~&2, ~Char, ~(c => Bool.not(Char.is_eq(c, '/'))), String.to_list(m))))) == True{} : Bool}, B.fail_done(Fetch.Addressed, Main.Refused{2, "`" ++ url ++ "` names a directory; `fetch` wants the URL of the manifest in it, conventionally `offer.txt`"}, Fetch.Addressed{r, m}, e))
    case False{}:
      +same = B.done_eq(Fetch.Addressed, Fetch.Addressed{String.append(pre, dir), name}, Fetch.Addressed{r, m}, e)
      %Equal.cong(Fetch.Addressed, String, x => Fetch.addressed.root(x), Fetch.Addressed{String.append(pre, dir), name}, Fetch.Addressed{r, m}, same) : {Bool.and(String.eq(String.append(_, m), url), Bool.and(String.ends_with(_, "/"), Bool.and(Bool.not(String.is_empty(m)), List.all(~&2, ~Char, ~(c => Bool.not(Char.is_eq(c, '/'))), String.to_list(m))))) == True{} : Bool}
      %Equal.cong(Fetch.Addressed, String, x => Fetch.addressed.manifest(x), Fetch.Addressed{String.append(pre, dir), name}, Fetch.Addressed{r, m}, same) : {Bool.and(String.eq(String.append(String.append(pre, dir), _), url), Bool.and(String.ends_with(String.append(pre, dir), "/"), Bool.and(Bool.not(String.is_empty(_)), List.all(~&2, ~Char, ~(c => Bool.not(Char.is_eq(c, '/'))), String.to_list(_))))) == True{} : Bool}
      %Equal.sym(String, String.append(String.append(pre, dir), name), url, url_whole(url, pre, rest, dir, name, es, esl)) : {Bool.and(String.eq(_, url), Bool.and(String.ends_with(String.append(pre, dir), "/"), Bool.and(Bool.not(String.is_empty(name)), List.all(~&2, ~Char, ~(c => Bool.not(Char.is_eq(c, '/'))), String.to_list(name))))) == True{} : Bool}
      %Equal.sym(Bool, String.eq(url, url), True{}, S.eq_refl(url)) : {Bool.and(_, Bool.and(String.ends_with(String.append(pre, dir), "/"), Bool.and(Bool.not(String.is_empty(name)), List.all(~&2, ~Char, ~(c => Bool.not(Char.is_eq(c, '/'))), String.to_list(name))))) == True{} : Bool}
      %Equal.sym(Bool, String.ends_with(String.append(pre, dir), "/"), True{}, ends_app(pre, dir, slash_end(String.reverse(rest), SNil{}, dir, name, esl))) : {Bool.and(True{}, Bool.and(_, Bool.and(Bool.not(String.is_empty(name)), List.all(~&2, ~Char, ~(c => Bool.not(Char.is_eq(c, '/'))), String.to_list(name))))) == True{} : Bool}
      %Equal.sym(Bool, String.is_empty(name), False{}, eb) : {Bool.and(True{}, Bool.and(True{}, Bool.and(Bool.not(_), List.all(~&2, ~Char, ~(c => Bool.not(Char.is_eq(c, '/'))), String.to_list(name))))) == True{} : Bool}
      %Equal.sym(Bool, List.all(~&2, ~Char, ~(c => Bool.not(Char.is_eq(c, '/'))), String.to_list(name)), True{}, slash_ns(String.reverse(rest), SNil{}, dir, name, esl, {==})) : {Bool.and(True{}, Bool.and(True{}, Bool.and(True{}, _))) == True{} : Bool}
      {==}

def ad.name(sl: Maybe<&2, T.Split>, +url: String, +pre: String, +rest: String, -r: String, -m: String, es: {Fetch.scheme.go(url, SNil{}) == Some{T.Split{pre, rest}} : Maybe<&2, T.Split>}, esl: {Fetch.slash.last(String.reverse(rest), SNil{}) == sl : Maybe<&2, T.Split>}, e: {Fetch.addressed.name(url, pre, sl) == Done{Fetch.Addressed{r, m}} : Result<&2, &2, Main.Refused, Fetch.Addressed>}) -> {Bool.and(String.eq(String.append(r, m), url), Bool.and(String.ends_with(r, "/"), Bool.and(Bool.not(String.is_empty(m)), List.all(~&2, ~Char, ~(c => Bool.not(Char.is_eq(c, '/'))), String.to_list(m))))) == True{} : Bool}:
  match sl:
    case None{}:
      Empty.absurd({Bool.and(String.eq(String.append(r, m), url), Bool.and(String.ends_with(r, "/"), Bool.and(Bool.not(String.is_empty(m)), List.all(~&2, ~Char, ~(c => Bool.not(Char.is_eq(c, '/'))), String.to_list(m))))) == True{} : Bool}, B.fail_done(Fetch.Addressed, Main.Refused{2, "`" ++ url ++ "` names a host and no manifest; `fetch` wants the URL of the `offer.txt` itself, since every path in it resolves against the directory it sits in"}, Fetch.Addressed{r, m}, e))
    case Some{T.Split{+dir, +name}}:
      ad.empty(String.is_empty(name), url, pre, rest, dir, name, r, m, {==}, es, esl, e)

def ad.query(q: Maybe<&2, String>, +url: String, +pre: String, +rest: String, -r: String, -m: String, es: {Fetch.scheme.go(url, SNil{}) == Some{T.Split{pre, rest}} : Maybe<&2, T.Split>}, e: {Fetch.addressed.query(url, pre, rest, q) == Done{Fetch.Addressed{r, m}} : Result<&2, &2, Main.Refused, Fetch.Addressed>}) -> {Bool.and(String.eq(String.append(r, m), url), Bool.and(String.ends_with(r, "/"), Bool.and(Bool.not(String.is_empty(m)), List.all(~&2, ~Char, ~(c => Bool.not(Char.is_eq(c, '/'))), String.to_list(m))))) == True{} : Bool}:
  match q:
    case Some{c}:
      Empty.absurd({Bool.and(String.eq(String.append(r, m), url), Bool.and(String.ends_with(r, "/"), Bool.and(Bool.not(String.is_empty(m)), List.all(~&2, ~Char, ~(c => Bool.not(Char.is_eq(c, '/'))), String.to_list(m))))) == True{} : Bool}, B.fail_done(Fetch.Addressed, Main.Refused{2, "`" ++ c ++ "` cannot be part of a manifest's URL: the paths in a manifest resolve against the directory it sits in, so there is nowhere for it to go"}, Fetch.Addressed{r, m}, e))
    case None{}:
      ad.name(Fetch.slash.last(String.reverse(rest), SNil{}), url, pre, rest, r, m, es, {==}, e)

def ad.of(sm: Maybe<&2, T.Split>, +url: String, -r: String, -m: String, es: {Fetch.scheme.go(url, SNil{}) == sm : Maybe<&2, T.Split>}, e: {Fetch.addressed.of(url, sm) == Done{Fetch.Addressed{r, m}} : Result<&2, &2, Main.Refused, Fetch.Addressed>}) -> {Bool.and(String.eq(String.append(r, m), url), Bool.and(String.ends_with(r, "/"), Bool.and(Bool.not(String.is_empty(m)), List.all(~&2, ~Char, ~(c => Bool.not(Char.is_eq(c, '/'))), String.to_list(m))))) == True{} : Bool}:
  match sm:
    case None{}:
      Empty.absurd({Bool.and(String.eq(String.append(r, m), url), Bool.and(String.ends_with(r, "/"), Bool.and(Bool.not(String.is_empty(m)), List.all(~&2, ~Char, ~(c => Bool.not(Char.is_eq(c, '/'))), String.to_list(m))))) == True{} : Bool}, B.fail_done(Fetch.Addressed, Main.Refused{2, "`" ++ url ++ "` is not a URL; `fetch` wants one, and a directory on this machine is `receive`'s to read"}, Fetch.Addressed{r, m}, e))
    case Some{T.Split{+pre, +rest}}:
      ad.query(Fetch.query.of(url), url, pre, rest, r, m, es, e)

# A URL `fetch` accepts is cut into the directory a manifest sits in and the
# manifest's own name: the two are the URL, the directory ends with `/`,
# the name is not empty, and no `/` is in it — so the directory is
# everything up to the URL's last `/`, that included.
def addressed_ok(+url: String, -r: String, -m: String, e: {Fetch.addressed.r(url) == Done{Fetch.Addressed{r, m}} : Result<&2, &2, Main.Refused, Fetch.Addressed>}) -> {Bool.and(String.eq(String.append(r, m), url), Bool.and(String.ends_with(r, "/"), Bool.and(Bool.not(String.is_empty(m)), List.all(~&2, ~Char, ~(c => Bool.not(Char.is_eq(c, '/'))), String.to_list(m))))) == True{} : Bool}:
  ad.of(Fetch.scheme.go(url, SNil{}), url, r, m, {==}, e)

# A bookmark once a pass
# ----------------------

# Whether a landing writes a bookmark.
def writes_a_bookmark(l: Fetch.Land) -> Bool:
  match l:
    case Fetch.Land.Name{n, a, t}:
      True{}
    case _:
      False{}

def wb_filed(+p: String, fault: Maybe<&2, String>, +at: String, +t: String) -> {writes_a_bookmark(Fetch.filed.if(p, fault, at, t)) == False{} : Bool}:
  match fault:
    case Some{e}:
      {==}
    case None{}:
      {==}

def wb_rule(+p: String, +t: String, st: Folder.Stated) -> {writes_a_bookmark(Fetch.rule.of(p, t, st)) == False{} : Bool}:
  match st:
    case Folder.Stated.Wrong{e}:
      {==}
    case Folder.Stated.None{}:
      {==}
    case Folder.Stated.One{sc}:
      {==}

def wb_bytes(o: Offer.Offered) -> {writes_a_bookmark(Fetch.bytes.land(o)) == False{} : Bool}:
  match o:
    case Offer.Offered{+k, d, f, +p}:
      {==}

def mem_head(+x: String, +rest: List<&2, String>) -> {Rev.member(x <> rest, x) == True{} : Bool}:
  %Equal.sym(Bool, String.eq(x, x), True{}, S.eq_refl(x)) : {Bool.or(_, Rev.member(rest, x)) == True{} : Bool}
  {==}

# A line naming a bookmark the pass holds lands as nothing.
def wb_name(+root: String, +p: String, +n: String, +held: List<&2, String>, +t: String) -> {writes_a_bookmark(Fetch.name.land(root, p, n <> held, Some{n}, t)) == False{} : Bool}:
  %Equal.sym(Bool, Rev.member(n <> held, n), True{}, mem_head(n, held)) : {writes_a_bookmark(Bool.pick(Fetch.Land, _, Fetch.Land.Skip{}, Fetch.name.of(root, p, n, Bm.parse(t)))) == False{} : Bool}
  {==}

def wb_text.c(c3: Bool, +root: String, +n: String, +held: List<&2, String>, +p: String, +t: String) -> {writes_a_bookmark(Bool.pick(Fetch.Land, c3, Fetch.rule.of(p, t, Folder.rule_in(t)), Fetch.name.land(root, p, n <> held, Some{n}, t))) == False{} : Bool}:
  match c3:
    case True{}:
      wb_rule(p, t, Folder.rule_in(t))
    case False{}:
      wb_name(root, p, n, held, t)

def wb_text.b(c2: Bool, c3: Bool, +root: String, +n: String, +held: List<&2, String>, +d: String, +p: String, +t: String) -> {writes_a_bookmark(Bool.pick(Fetch.Land, c2, Fetch.filed.if(p, Fetch.rev.ok(Rev.parse(t)), root ++ "/revisions/" ++ d ++ ".rev.txt", t), Bool.pick(Fetch.Land, c3, Fetch.rule.of(p, t, Folder.rule_in(t)), Fetch.name.land(root, p, n <> held, Some{n}, t)))) == False{} : Bool}:
  match c2:
    case True{}:
      wb_filed(p, Fetch.rev.ok(Rev.parse(t)), root ++ "/revisions/" ++ d ++ ".rev.txt", t)
    case False{}:
      wb_text.c(c3, root, n, held, p, t)

def wb_text.a(c1: Bool, c2: Bool, c3: Bool, +root: String, +n: String, +held: List<&2, String>, +d: String, +p: String, +t: String) -> {writes_a_bookmark(Bool.pick(Fetch.Land, c1, Fetch.filed.if(p, Fetch.op.fault(t), root ++ "/operations/" ++ d ++ ".ops.txt", t), Bool.pick(Fetch.Land, c2, Fetch.filed.if(p, Fetch.rev.ok(Rev.parse(t)), root ++ "/revisions/" ++ d ++ ".rev.txt", t), Bool.pick(Fetch.Land, c3, Fetch.rule.of(p, t, Folder.rule_in(t)), Fetch.name.land(root, p, n <> held, Some{n}, t))))) == False{} : Bool}:
  match c1:
    case True{}:
      wb_filed(p, Fetch.op.fault(t), root ++ "/operations/" ++ d ++ ".ops.txt", t)
    case False{}:
      wb_text.b(c2, c3, root, n, held, d, p, t)

# Whatever its kind, a document whose path names a bookmark the pass holds
# writes no bookmark.
def wb_text(+root: String, +n: String, +held: List<&2, String>, o: Offer.Offered, +t: String, h: {Fetch.named_by(Offer.offered.path(o)) == Some{n} : Maybe<&2, String>}) -> {writes_a_bookmark(Fetch.text.land(root, n <> held, o, t)) == False{} : Bool}:
  match o:
    case Offer.Offered{+k, +d, f, +p}:
      %Equal.sym(Maybe<&2, String>, Fetch.named_by(p), Some{n}, h) : {writes_a_bookmark(Bool.pick(Fetch.Land, String.eq(k, "operation"), Fetch.filed.if(p, Fetch.op.fault(t), root ++ "/operations/" ++ d ++ ".ops.txt", t), Bool.pick(Fetch.Land, String.eq(k, "revision"), Fetch.filed.if(p, Fetch.rev.ok(Rev.parse(t)), root ++ "/revisions/" ++ d ++ ".rev.txt", t), Bool.pick(Fetch.Land, String.eq(k, "rule"), Fetch.rule.of(p, t, Folder.rule_in(t)), Fetch.name.land(root, p, n <> held, _, t))))) == False{} : Bool}
      wb_text.a(String.eq(k, "operation"), String.eq(k, "revision"), String.eq(k, "rule"), root, n, held, d, p, t)

def wb_pick(c: Bool, -a: Fetch.Land, -b: Fetch.Land, ha: {writes_a_bookmark(a) == False{} : Bool}, hb: {writes_a_bookmark(b) == False{} : Bool}) -> {writes_a_bookmark(Bool.pick(Fetch.Land, c, a, b)) == False{} : Bool}:
  match c:
    case True{}:
      ha
    case False{}:
      hb

# In one pass, a bookmark is written once: once a pass has written `n`,
# whatever the host answers for a later line naming `n`, no bookmark is
# written for it.
def once_a_pass(+o: Offer.Offered, +n: String, +at: String, +text: String, +t: Fetch.Tally, +rules: List<&2, Receive.Ruled>, +held: List<&2, String>, +moved: Maybe<&2, String>, +landed: Bool, +root: String, +o2: Offer.Offered, g: Fetch.Got, +h: {Fetch.named_by(Offer.offered.path(o2)) == Some{n} : Maybe<&2, String>}) -> {writes_a_bookmark(Fetch.got.text(root, Fetch.state.held(Fetch.land.after(o, Fetch.Land.Name{n, at, text}, t, rules, held, moved, landed)), o2, g)) == False{} : Bool}:
  match g:
    case Fetch.Got.Failed{m}:
      {==}
    case Fetch.Got.Status{+c}:
      wb_pick(Fetch.gone(c), Fetch.Land.Gone{}, Fetch.Land.Refuse{Fetch.unreachable(Fetch.entry.path(o2), "the server answered " ++ c)}, {==}, {==})
    case Fetch.Got.Bytes{+found}:
      wb_pick(String.eq(found, Fetch.entry.digest(o2)), Fetch.bytes.land(o2), Fetch.Land.Refuse{Fetch.TAMPERED(Fetch.entry.path(o2), Fetch.entry.digest(o2), found)}, wb_bytes(o2), {==})
    case Fetch.Got.Text{+t2}:
      wb_pick(String.eq(Fetch.text.digest(t2), Fetch.entry.digest(o2)), Fetch.text.land(root, n <> held, o2, t2), Fetch.Land.Refuse{Fetch.TAMPERED(Fetch.entry.path(o2), Fetch.entry.digest(o2), Fetch.text.digest(t2))}, wb_text(root, n, held, o2, t2, h), {==})
    case Fetch.Got.Pulled{d}:
      {==}
