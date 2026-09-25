# Every revision `fulls` reads is one a document of `revisions/` spells,
# and every document there that reads as a revision is read. A document
# the parser accepts is the revision `Rev.write` writes back byte for byte
# (`LAWS.revision_write_parse`); one it refuses only for a path not in
# normal form C is read with its causal headers and, in place of its
# facts, the refusal every reader of the whole of it meets, at the line
# the header naming that path is on; and mending such a document touches
# nothing but its `add` and `move` headers.
import Base
import ./revision.bend as Rev
import ./store.bend as Store
import ./commands.bend as Main
import ./string_lemmas.bend as S
import ./anchor_lemmas.bend as AL
import ./revision_lemmas.bend as RevL
import ./composition_lemmas.bend as Comp
import ./text.bend as T
import ./nfc.bend as Nfc
import ./spelling_lemmas.bend as Sp
import ./blamed_lemmas.bend as B
import ./decimal_lemmas.bend as Dec

# The line a path not in normal form C is refused at
# --------------------------------------------------

# A line naming a path not in normal form C: an `add` or `move` header
# ending in a space and that path.
def names.unnormal(+l: String, +q: String) -> Bool:
  Bool.and(Bool.or(String.starts_with(l, "add "), String.starts_with(l, "move ")), Bool.and(String.ends_with(l, " " ++ q), Bool.not(Nfc.is_nfc(q))))

# Line `n` of the lines `ls`, the first of which is line `k`, names `q`
# so, and no line before it is blank: it is among the headers.
def line.at(ls: List<&2, String>, +k: Nat, +n: Nat, +q: String) -> Bool:
  match ls:
    case Nil{}:
      False{}
    case +l <> rest:
      Bool.pick(Bool, Nat.is_eq(k, n), names.unnormal(l, q), Bool.and(Bool.not(String.is_empty(l)), line.at(rest, 1n+k, n, q)))

def u_line(m: Maybe<&2, Rev.Unnormal>) -> Nat:
  match m:
    case None{}:
      0n
    case Some{Rev.Unnormal{n, p}}:
      n

def u_path(m: Maybe<&2, Rev.Unnormal>) -> String:
  match m:
    case None{}:
      SNil{}
    case Some{Rev.Unnormal{n, p}}:
      p

def u_disc(m: Maybe<&2, Rev.Unnormal>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      Empty

def none_some(-x: Rev.Unnormal, e: {None{} == Some{x} : Maybe<&2, Rev.Unnormal>}) -> Empty:
  %e : {u_disc(_) : Type}
  Unit{}

def s_disc(m: Maybe<&2, String>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      Empty

def none_some_s(-x: String, e: {None{} == Some{x} : Maybe<&2, String>}) -> Empty:
  %e : {s_disc(_) : Type}
  Unit{}

def ends_named(+key: String, +file: String, +q: String) -> {String.ends_with(key ++ (file ++ (" " ++ q)), " " ++ q) == True{} : Bool}:
  B.ends_pre(key, file ++ (" " ++ q), " " ++ q, B.ends_pre(file, " " ++ q, " " ++ q, B.ends_refl(" " ++ q)))

def value_nfc(b: Bool, +l: String, +key: String, +file: String, +path: String, +k: Nat, +n: Nat, +q: String, +eb: {Nfc.is_nfc(path) == b : Bool}, +el: {l == key ++ (file ++ (" " ++ path)) : String}, +hk: {Bool.or(String.starts_with(l, "add "), String.starts_with(l, "move ")) == True{} : Bool}, +e: {Bool.pick(Maybe<&2, Rev.Unnormal>, b, None{}, Some{Rev.Unnormal{k, path}}) == Some{Rev.Unnormal{n, q}} : Maybe<&2, Rev.Unnormal>}) -> {Bool.and(Nat.is_eq(k, n), names.unnormal(l, q)) == True{} : Bool}:
  match b:
    case True{}:
      Empty.absurd({Bool.and(Nat.is_eq(k, n), names.unnormal(l, q)) == True{} : Bool}, none_some(Rev.Unnormal{n, q}, e))
    case False{}:
      +ekn = Equal.cong(Maybe<&2, Rev.Unnormal>, Nat, u_line, Some{Rev.Unnormal{k, path}}, Some{Rev.Unnormal{n, q}}, e)
      +epq = Equal.cong(Maybe<&2, Rev.Unnormal>, String, u_path, Some{Rev.Unnormal{k, path}}, Some{Rev.Unnormal{n, q}}, e)
      AL.and_intro(Nat.is_eq(k, n), names.unnormal(l, q),
        (%ekn : {Nat.is_eq(k, _) == True{} : Bool}; Comp.eq_refl(k)),
        AL.and_intro(Bool.or(String.starts_with(l, "add "), String.starts_with(l, "move ")), Bool.and(String.ends_with(l, " " ++ q), Bool.not(Nfc.is_nfc(q))), hk,
          AL.and_intro(String.ends_with(l, " " ++ q), Bool.not(Nfc.is_nfc(q)),
            (%epq : {String.ends_with(l, " " ++ _) == True{} : Bool};
             %Equal.sym(String, l, key ++ (file ++ (" " ++ path)), el) : {String.ends_with(_, " " ++ path) == True{} : Bool};
             ends_named(key, file, path)),
            (%epq : {Bool.not(Nfc.is_nfc(_)) == True{} : Bool};
             %Equal.sym(Bool, Nfc.is_nfc(path), False{}, eb) : {Bool.not(_) == True{} : Bool};
             {==}))))

def value_path(+l: String, +key: String, +r: String, +k: Nat, +n: Nat, +q: String, cut: Maybe<&2, T.Split>, +ec: {T.split_once(r) == cut : Maybe<&2, T.Split>}, +el: {l == key ++ r : String}, +hk: {Bool.or(String.starts_with(l, "add "), String.starts_with(l, "move ")) == True{} : Bool}, e: {Bool.pick(Maybe<&2, Rev.Unnormal>, Nfc.is_nfc(Rev.unnormal.path(cut)), None{}, Some{Rev.Unnormal{k, Rev.unnormal.path(cut)}}) == Some{Rev.Unnormal{n, q}} : Maybe<&2, Rev.Unnormal>}) -> {Bool.and(Nat.is_eq(k, n), names.unnormal(l, q)) == True{} : Bool}:
  match cut:
    case None{}:
      Empty.absurd({Bool.and(Nat.is_eq(k, n), names.unnormal(l, q)) == True{} : Bool}, none_some(Rev.Unnormal{n, q}, e))
    case Some{T.Split{+file, +path}}:
      +er = Sp.split_top(r, file, path, ec)
      value_nfc(Nfc.is_nfc(path), l, key, file, path, k, n, q, {==}, Equal.trans(String, l, key ++ r, key ++ (file ++ (" " ++ path)), el, Equal.cong(String, String, x => key ++ x, r, file ++ (" " ++ path), er)), hk, e)

def keyed_move(+l: String, +k: Nat, +n: Nat, +q: String, +r: String, em: {T.strip_prefix(l, "move ") == Some{r} : Maybe<&2, String>}, e: {Rev.unnormal.value(k, Some{r}) == Some{Rev.Unnormal{n, q}} : Maybe<&2, Rev.Unnormal>}) -> {Bool.and(Nat.is_eq(k, n), names.unnormal(l, q)) == True{} : Bool}:
  +el = Sp.strip_eq(l, "move ", r, em)
  +hs : {String.starts_with(l, "move ") == True{} : Bool} = (%Equal.sym(String, l, "move " ++ r, el) : {String.starts_with(_, "move ") == True{} : Bool}; B.sw_ext("move ", "move ", r, B.sw_refl("move ")))
  value_path(l, "move ", r, k, n, q, T.split_once(r), {==}, el, AL.or_right(String.starts_with(l, "add "), String.starts_with(l, "move "), hs), e)

def keyed_add(a: Maybe<&2, String>, +l: String, +k: Nat, +n: Nat, +q: String, +r: String, +ea: {T.strip_prefix(l, "add ") == a : Maybe<&2, String>}, ekv: {Maybe.or(&2, String, a, T.strip_prefix(l, "move ")) == Some{r} : Maybe<&2, String>}, e: {Rev.unnormal.value(k, Some{r}) == Some{Rev.Unnormal{n, q}} : Maybe<&2, Rev.Unnormal>}) -> {Bool.and(Nat.is_eq(k, n), names.unnormal(l, q)) == True{} : Bool}:
  match a:
    case None{}:
      keyed_move(l, k, n, q, r, ekv, e)
    case Some{+r1}:
      +er = Equal.cong(Maybe<&2, String>, String, m => Maybe.default(&2, String, m, SNil{}), Some{r1}, Some{r}, ekv)
      +el = Equal.trans(String, l, "add " ++ r1, "add " ++ r, Sp.strip_eq(l, "add ", r1, ea), Equal.cong(String, String, x => "add " ++ x, r1, r, er))
      +hs : {String.starts_with(l, "add ") == True{} : Bool} = (%Equal.sym(String, l, "add " ++ r, el) : {String.starts_with(_, "add ") == True{} : Bool}; B.sw_ext("add ", "add ", r, B.sw_refl("add ")))
      value_path(l, "add ", r, k, n, q, T.split_once(r), {==}, el, AL.or_left(String.starts_with(l, "add "), String.starts_with(l, "move "), hs), e)

def keyed_ok(+l: String, +k: Nat, +n: Nat, +q: String, kv: Maybe<&2, String>, ekv: {Rev.unnormal.keyed(l) == kv : Maybe<&2, String>}, e: {Rev.unnormal.value(k, kv) == Some{Rev.Unnormal{n, q}} : Maybe<&2, Rev.Unnormal>}) -> {Bool.and(Nat.is_eq(k, n), names.unnormal(l, q)) == True{} : Bool}:
  match kv:
    case None{}:
      Empty.absurd({Bool.and(Nat.is_eq(k, n), names.unnormal(l, q)) == True{} : Bool}, none_some(Rev.Unnormal{n, q}, e))
    case Some{+r}:
      keyed_add(T.strip_prefix(l, "add "), l, k, n, q, r, {==}, ekv, e)

def go_or(+l: String, +rest: List<&2, String>, +k: Nat, +n: Nat, +q: String, v: Maybe<&2, Rev.Unnormal>, ev: {Rev.unnormal.value(k, Rev.unnormal.keyed(l)) == v : Maybe<&2, Rev.Unnormal>}, h: {Maybe.or(&2, Rev.Unnormal, v, Rev.unnormal.go(rest, 1n+k)) == Some{Rev.Unnormal{n, q}} : Maybe<&2, Rev.Unnormal>}, +hne: {String.is_empty(l) == False{} : Bool}, ih: {Rev.unnormal.go(rest, 1n+k) == Some{Rev.Unnormal{n, q}} : Maybe<&2, Rev.Unnormal>} -> {Bool.and(Nat.is_le(1n+k, n), line.at(rest, 1n+k, n, q)) == True{} : Bool}) -> {Bool.and(Nat.is_le(k, n), Bool.pick(Bool, Nat.is_eq(k, n), names.unnormal(l, q), Bool.and(Bool.not(String.is_empty(l)), line.at(rest, 1n+k, n, q)))) == True{} : Bool}:
  match v:
    case None{}:
      +r = ih(h)
      +le1 = Comp.and_left(Nat.is_le(1n+k, n), line.at(rest, 1n+k, n, q), r)
      +ne = Comp.lt_not_eq(k, n, Dec.lt_of_le_succ(k, n, le1))
      %Equal.sym(Bool, Nat.is_eq(k, n), False{}, ne) : {Bool.and(Nat.is_le(k, n), Bool.pick(Bool, _, names.unnormal(l, q), Bool.and(Bool.not(String.is_empty(l)), line.at(rest, 1n+k, n, q)))) == True{} : Bool}
      %Equal.sym(Bool, String.is_empty(l), False{}, hne) : {Bool.and(Nat.is_le(k, n), Bool.and(Bool.not(_), line.at(rest, 1n+k, n, q))) == True{} : Bool}
      AL.and_intro(Nat.is_le(k, n), line.at(rest, 1n+k, n, q), Comp.le_pred(k, n, le1), Comp.and_right(Nat.is_le(1n+k, n), line.at(rest, 1n+k, n, q), r))
    case Some{+x}:
      +g = keyed_ok(l, k, n, q, Rev.unnormal.keyed(l), {==}, Equal.trans(Maybe<&2, Rev.Unnormal>, Rev.unnormal.value(k, Rev.unnormal.keyed(l)), Some{x}, Some{Rev.Unnormal{n, q}}, ev, h))
      +eq = Comp.and_left(Nat.is_eq(k, n), names.unnormal(l, q), g)
      +ekn = Comp.eq_of_is_eq(k, n, eq)
      %Equal.sym(Bool, Nat.is_eq(k, n), True{}, eq) : {Bool.and(Nat.is_le(k, n), Bool.pick(Bool, _, names.unnormal(l, q), Bool.and(Bool.not(String.is_empty(l)), line.at(rest, 1n+k, n, q)))) == True{} : Bool}
      AL.and_intro(Nat.is_le(k, n), names.unnormal(l, q), (%ekn : {Nat.is_le(k, _) == True{} : Bool}; Comp.le_refl(k)), Comp.and_right(Nat.is_eq(k, n), names.unnormal(l, q), g))

# The line `unnormal` names, counting from `k`, is at or after `k`, and
# names the path so.
def go_at(ls: List<&2, String>, +k: Nat, +n: Nat, +q: String, h: {Rev.unnormal.go(ls, k) == Some{Rev.Unnormal{n, q}} : Maybe<&2, Rev.Unnormal>}) -> {Bool.and(Nat.is_le(k, n), line.at(ls, k, n, q)) == True{} : Bool}:
  match ls:
    case Nil{}:
      Empty.absurd({Bool.and(Nat.is_le(k, n), False{}) == True{} : Bool}, none_some(Rev.Unnormal{n, q}, h))
    case SNil{} <> rest:
      Empty.absurd({Bool.and(Nat.is_le(k, n), line.at(SNil{} <> rest, k, n, q)) == True{} : Bool}, none_some(Rev.Unnormal{n, q}, h))
    case SCon{+c, +t} <> +rest:
      go_or(SCon{c, t}, rest, k, n, q, Rev.unnormal.value(k, Rev.unnormal.keyed(SCon{c, t})), {==}, h, {==}, x => go_at(rest, 1n+k, n, q, x))

# Where `unnormal` finds a path not in normal form C, the line it names —
# the format line counted as the first — is a header naming that path.
def unnormal_at(s: String, +n: Nat, +q: String, h: {Rev.unnormal(s) == Some{Rev.Unnormal{n, q}} : Maybe<&2, Rev.Unnormal>}) -> {line.at(String.split(s, '\n'), 1n, n, q) == True{} : Bool}:
  Comp.and_right(Nat.is_le(1n, n), line.at(String.split(s, '\n'), 1n, n, q), go_at(String.split(s, '\n'), 1n, n, q, h))

# What mending changes
# --------------------

# Two lists of lines the same, line for line.
def same(xs: List<&2, String>, ys: List<&2, String>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case +x <> xr +y <> yr:
      Bool.and(String.eq(y, x), same(xr, yr))
    case _ _:
      False{}

# A line mended: an `add` header stays one, a `move` header stays one, and
# any other line is left as it is.
def mended.line.ok(+x: String, +y: String) -> Bool:
  Bool.pick(Bool, String.starts_with(x, "add "), String.starts_with(y, "add "), Bool.pick(Bool, String.starts_with(x, "move "), String.starts_with(y, "move "), String.eq(y, x)))

# The lines `ys` agree with the document's lines `xs`: as many, each
# header mended as above, and from the blank line that ends the headers
# on, every line the document's own.
def mended.agrees(xs: List<&2, String>, ys: List<&2, String>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case +x <> +xr +y <> +yr:
      Bool.pick(Bool, String.is_empty(x), Bool.and(String.eq(y, x), same(xr, yr)), Bool.and(mended.line.ok(x, y), mended.agrees(xr, yr)))
    case _ _:
      False{}

def same_refl(xs: List<&2, String>) -> {same(xs, xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      AL.and_intro(String.eq(x, x), same(rest, rest), S.eq_refl(x), same_refl(rest))

def value_keyed(+key: String, cut: Maybe<&2, T.Split>) -> {String.starts_with(Rev.mended.value(key, cut), key) == True{} : Bool}:
  match cut:
    case None{}:
      B.sw_refl(key)
    case Some{T.Split{+file, +path}}:
      B.sw_ext(key, key, file ++ " " ++ Nfc.nfc(path), B.sw_refl(key))

def line_ok.of(a: Bool, m: Bool, +l: String, +va: String, +vm: String, +ha: {String.starts_with(va, "add ") == True{} : Bool}, +hm: {String.starts_with(vm, "move ") == True{} : Bool}) -> {Bool.pick(Bool, a, String.starts_with(Bool.pick(String, a, va, Bool.pick(String, m, vm, l)), "add "), Bool.pick(Bool, m, String.starts_with(Bool.pick(String, a, va, Bool.pick(String, m, vm, l)), "move "), String.eq(Bool.pick(String, a, va, Bool.pick(String, m, vm, l)), l))) == True{} : Bool}:
  match a m:
    case True{} _:
      ha
    case False{} True{}:
      hm
    case False{} False{}:
      S.eq_refl(l)

def line_ok(+l: String) -> {mended.line.ok(l, Rev.mended.line(l)) == True{} : Bool}:
  line_ok.of(String.starts_with(l, "add "), String.starts_with(l, "move "), l, Rev.mended.value("add ", T.split_once(String.drop(l, 4n))), Rev.mended.value("move ", T.split_once(String.drop(l, 5n))), value_keyed("add ", T.split_once(String.drop(l, 4n))), value_keyed("move ", T.split_once(String.drop(l, 5n))))

# The lines `mended` joins agree with the document's.
def mended_agrees(ls: List<&2, String>) -> {mended.agrees(ls, Rev.mended.go(ls)) == True{} : Bool}:
  match ls:
    case Nil{}:
      {==}
    case SNil{} <> +rest:
      AL.and_intro(String.eq(SNil{}, SNil{}), same(rest, rest), {==}, same_refl(rest))
    case SCon{+c, +t} <> +rest:
      AL.and_intro(mended.line.ok(SCon{c, t}, Rev.mended.line(SCon{c, t})), mended.agrees(rest, Rev.mended.go(rest)), line_ok(SCon{c, t}), mended_agrees(rest))

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
# writes the revision back as the document, byte for byte; or the parser
# refuses the document, `Rev.unnormal` finds a path not in normal form C
# at some line, the revision's facts are the refusal naming that path and
# line, and the revision with the facts of the document `Rev.mended` makes
# put back writes that mended document.
def spelled(+path: String, +text: String, +f: Main.Full) -> Bool:
  Bool.or(String.eq(Rev.write(Main.full.rev(f)), text), Bool.and(Result.is_fail(&2, &2, String, Rev.Rev, Rev.parse(text)), mended.of(path, text, f, Rev.unnormal(text))))

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
  AL.or_left(String.eq(Rev.write(Rev.Rev{change, parents, supersedes, author, when, revised_by, revised, facts, message}), text), Bool.and(Result.is_fail(&2, &2, String, Rev.Rev, Rev.parse(text)), mended.of(path, text, Main.Full{id, change, parents, supersedes, author, when, revised_by, revised, facts, message}, Rev.unnormal(text))),
    (%sw : {String.eq(_, text) == True{} : Bool}; S.eq_refl(text)))

# What is refused only for a path not in normal form C is spelled as the
# refusal, over what the mended document says.
def unread_spelled(+path: String, +id: String, +text: String, +n: Nat, +q: String, +change: String, +parents: List<&2, String>, +supersedes: List<&2, String>, +author: String, +when: String, +revised_by: Maybe<&2, String>, +revised: Maybe<&2, String>, +facts: List<&2, Rev.Header>, +message: String, +eu: {Rev.unnormal(text) == Some{Rev.Unnormal{n, q}} : Maybe<&2, Rev.Unnormal>}, +hf: {Result.is_fail(&2, &2, String, Rev.Rev, Rev.parse(text)) == True{} : Bool}, +ep: {Rev.parse(Rev.mended(text)) == Done{Rev.Rev{change, parents, supersedes, author, when, revised_by, revised, facts, message}} : Result<&2, &2, String, Rev.Rev>}) -> {spelled(path, text, Main.Full{id, change, parents, supersedes, author, when, revised_by, revised, [Rev.Header{SNil{}, refusal(path, n, q)}], message}) == True{} : Bool}:
  AL.or_right(String.eq(Rev.write(Main.full.rev(Main.Full{id, change, parents, supersedes, author, when, revised_by, revised, [Rev.Header{SNil{}, refusal(path, n, q)}], message})), text), Bool.and(Result.is_fail(&2, &2, String, Rev.Rev, Rev.parse(text)), mended.of(path, text, Main.Full{id, change, parents, supersedes, author, when, revised_by, revised, [Rev.Header{SNil{}, refusal(path, n, q)}], message}, Rev.unnormal(text))),
    AL.and_intro(Result.is_fail(&2, &2, String, Rev.Rev, Rev.parse(text)), mended.of(path, text, Main.Full{id, change, parents, supersedes, author, when, revised_by, revised, [Rev.Header{SNil{}, refusal(path, n, q)}], message}, Rev.unnormal(text)), hf, (%Equal.sym(Maybe<&2, Rev.Unnormal>, Rev.unnormal(text), Some{Rev.Unnormal{n, q}}, eu) : {mended.of(path, text, Main.Full{id, change, parents, supersedes, author, when, revised_by, revised, [Rev.Header{SNil{}, refusal(path, n, q)}], message}, _) == True{} : Bool};
     %Equal.sym(Result<&2, &2, String, Rev.Rev>, Rev.parse(Rev.mended(text)), Done{Rev.Rev{change, parents, supersedes, author, when, revised_by, revised, facts, message}}, ep) : {mended.parsed(text, refusal(path, n, q), Main.Full{id, change, parents, supersedes, author, when, revised_by, revised, [Rev.Header{SNil{}, refusal(path, n, q)}], message}, _) == True{} : Bool};
     %Equal.sym(String, Rev.write(Rev.Rev{change, parents, supersedes, author, when, revised_by, revised, facts, message}), Rev.mended(text), RevL.write_parse(Rev.mended(text), Rev.Rev{change, parents, supersedes, author, when, revised_by, revised, facts, message}, ep)) : {Bool.and(String.eq(_, Rev.mended(text)), unread.is([Rev.Header{SNil{}, refusal(path, n, q)}], refusal(path, n, q))) == True{} : Bool};
     AL.and_intro(String.eq(Rev.mended(text), Rev.mended(text)), String.eq(refusal(path, n, q), refusal(path, n, q)), S.eq_refl(Rev.mended(text)), S.eq_refl(refusal(path, n, q))))))

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

def mended_step(+root: String, +path: String, +id: String, +size: Nat, +text: String, +rest: List<&2, Store.Doc>, +n: Nat, +q: String, p: Result<&2, &2, String, Rev.Rev>, +eu: {Rev.unnormal(text) == Some{Rev.Unnormal{n, q}} : Maybe<&2, Rev.Unnormal>}, +ep: {Rev.parse(Rev.mended(text)) == p : Result<&2, &2, String, Rev.Rev>}, +hf: {Result.is_fail(&2, &2, String, Rev.Rev, Rev.parse(text)) == True{} : Bool}, +ein: {Store.in_revisions(root, path) == True{} : Bool}, +ih: {all_filed(root, rest, Main.fulls(root, rest)) == True{} : Bool}) -> {all_filed(root, Store.Doc{path, id, size, text} <> rest, Main.push_full(Main.full.unread(id, refusal(path, n, q), p), Main.fulls(root, rest))) == True{} : Bool}:
  match p:
    case Fail{x}:
      all_weak(root, Store.Doc{path, id, size, text}, rest, Main.fulls(root, rest), ih)
    case Done{Rev.Rev{+change, +parents, +supersedes, +author, +when, +revised_by, +revised, +facts, +message}}:
      AL.and_intro(filed(root, Store.Doc{path, id, size, text} <> rest, Main.Full{id, change, parents, supersedes, author, when, revised_by, revised, [Rev.Header{SNil{}, refusal(path, n, q)}], message}), all_filed(root, Store.Doc{path, id, size, text} <> rest, Main.fulls(root, rest)),
        filed_head(root, path, id, size, text, rest, Main.Full{id, change, parents, supersedes, author, when, revised_by, revised, [Rev.Header{SNil{}, refusal(path, n, q)}], message}, ein, S.eq_refl(id), unread_spelled(path, id, text, n, q, change, parents, supersedes, author, when, revised_by, revised, facts, message, eu, hf, ep)),
        all_weak(root, Store.Doc{path, id, size, text}, rest, Main.fulls(root, rest), ih))

def unnormal_step(+root: String, +path: String, +id: String, +size: Nat, +text: String, +rest: List<&2, Store.Doc>, u: Maybe<&2, Rev.Unnormal>, +eu: {Rev.unnormal(text) == u : Maybe<&2, Rev.Unnormal>}, +hf: {Result.is_fail(&2, &2, String, Rev.Rev, Rev.parse(text)) == True{} : Bool}, +ein: {Store.in_revisions(root, path) == True{} : Bool}, +ih: {all_filed(root, rest, Main.fulls(root, rest)) == True{} : Bool}) -> {all_filed(root, Store.Doc{path, id, size, text} <> rest, Main.push_full(Main.full.unnormal(id, path, text, u), Main.fulls(root, rest))) == True{} : Bool}:
  match u:
    case None{}:
      all_weak(root, Store.Doc{path, id, size, text}, rest, Main.fulls(root, rest), ih)
    case Some{Rev.Unnormal{+n, +q}}:
      mended_step(root, path, id, size, text, rest, n, q, Rev.parse(Rev.mended(text)), eu, {==}, hf, ein, ih)

# One document read: a revision where it is filed under `revisions/` and
# reads whole, nothing otherwise.
def parsed_step(+root: String, +path: String, +id: String, +size: Nat, +text: String, +rest: List<&2, Store.Doc>, p: Result<&2, &2, String, Rev.Rev>, +ep: {Rev.parse(text) == p : Result<&2, &2, String, Rev.Rev>}, +ein: {Store.in_revisions(root, path) == True{} : Bool}, +ih: {all_filed(root, rest, Main.fulls(root, rest)) == True{} : Bool}) -> {all_filed(root, Store.Doc{path, id, size, text} <> rest, Main.push_full(Main.full.read(id, path, text, p), Main.fulls(root, rest))) == True{} : Bool}:
  match p:
    case Fail{x}:
      unnormal_step(root, path, id, size, text, rest, Rev.unnormal(text), {==}, (%Equal.sym(Result<&2, &2, String, Rev.Rev>, Rev.parse(text), Fail{x}, ep) : {Result.is_fail(&2, &2, String, Rev.Rev, _) == True{} : Bool}; {==}), ein, ih)
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

def unread_found(+path: String, +id: String, +text: String, +n: Nat, +q: String, pm: Result<&2, &2, String, Rev.Rev>, +eu: {Rev.unnormal(text) == Some{Rev.Unnormal{n, q}} : Maybe<&2, Rev.Unnormal>}, +epm: {Rev.parse(Rev.mended(text)) == pm : Result<&2, &2, String, Rev.Rev>}, +hf: {Result.is_fail(&2, &2, String, Rev.Rev, Rev.parse(text)) == True{} : Bool}, +fs: List<&2, Main.Full>) -> {Bool.or(Bool.not(readable.of(Fail{"x"}, Some{Rev.Unnormal{n, q}}, pm)), found(path, id, text, Main.push_full(Main.full.unread(id, refusal(path, n, q), pm), fs))) == True{} : Bool}:
  match pm:
    case Fail{e}:
      {==}
    case Done{Rev.Rev{+change, +parents, +supersedes, +author, +when, +revised_by, +revised, +facts, +message}}:
      AL.or_right(False{}, found(path, id, text, Main.Full{id, change, parents, supersedes, author, when, revised_by, revised, [Rev.Header{SNil{}, refusal(path, n, q)}], message} <> fs),
        AL.or_left(Bool.and(String.eq(id, id), spelled(path, text, Main.Full{id, change, parents, supersedes, author, when, revised_by, revised, [Rev.Header{SNil{}, refusal(path, n, q)}], message})), found(path, id, text, fs),
          AL.and_intro(String.eq(id, id), spelled(path, text, Main.Full{id, change, parents, supersedes, author, when, revised_by, revised, [Rev.Header{SNil{}, refusal(path, n, q)}], message}), S.eq_refl(id), unread_spelled(path, id, text, n, q, change, parents, supersedes, author, when, revised_by, revised, facts, message, eu, hf, epm))))

def unnormal_found(+path: String, +id: String, +text: String, u: Maybe<&2, Rev.Unnormal>, +eu: {Rev.unnormal(text) == u : Maybe<&2, Rev.Unnormal>}, +hf: {Result.is_fail(&2, &2, String, Rev.Rev, Rev.parse(text)) == True{} : Bool}, +fs: List<&2, Main.Full>) -> {Bool.or(Bool.not(readable.of(Fail{"x"}, u, Rev.parse(Rev.mended(text)))), found(path, id, text, Main.push_full(Main.full.unnormal(id, path, text, u), fs))) == True{} : Bool}:
  match u:
    case None{}:
      {==}
    case Some{Rev.Unnormal{+n, +q}}:
      unread_found(path, id, text, n, q, Rev.parse(Rev.mended(text)), eu, {==}, hf, fs)

def parse_found(+path: String, +id: String, +text: String, p: Result<&2, &2, String, Rev.Rev>, +ep: {Rev.parse(text) == p : Result<&2, &2, String, Rev.Rev>}, +fs: List<&2, Main.Full>) -> {Bool.or(Bool.not(readable.of(p, Rev.unnormal(text), Rev.parse(Rev.mended(text)))), found(path, id, text, Main.push_full(Main.full.read(id, path, text, p), fs))) == True{} : Bool}:
  match p:
    case Fail{e}:
      unnormal_found(path, id, text, Rev.unnormal(text), {==}, (%Equal.sym(Result<&2, &2, String, Rev.Rev>, Rev.parse(text), Fail{e}, ep) : {Result.is_fail(&2, &2, String, Rev.Rev, _) == True{} : Bool}; {==}), fs)
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
