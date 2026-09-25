# What the host answers, read back. A host effect answers in lines, and
# the port reads the lines; this writes them as the host writes them — the
# adapter's code in `ffi/src/lib.rs` — and holds each reader to reading back
# exactly what was written. `Store.at` answers a line for each digest asked,
# in order, then a line for each document said to forget one of them.
import Base
import ./store.bend as Store
import ./text.bend as T
import ./revision.bend as Rev
import ./string_lemmas.bend as S
import ./bookmark_lemmas.bend as BmL
import ./composition_lemmas.bend as Comp
import ./anchor_lemmas.bend as AL

# Lines
# -----

# Every string of `xs` has no newline in it.
def all_nonl(xs: List<&2, String>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case x <> rest:
      Bool.and(BmL.nonl(x), all_nonl(rest))

# A string with no newline in it is one line.
def split_one(s: String, +h: {BmL.nonl(s) == True{} : Bool}) -> {String.split(s, '\n') == [s] : List<&2, String>}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      Equal.trans(List<&2, String>, String.split.fin(c, String.split(t, '\n'), Char.is_eq(c, '\n')), String.split.fin(c, String.split(t, '\n'), False{}), [SCon{c, t}],
        Equal.cong(Bool, List<&2, String>, b => String.split.fin(c, String.split(t, '\n'), b), Char.is_eq(c, '\n'), False{}, AL.not_of_true(Char.is_eq(c, '\n'), Comp.and_left(Bool.not(Char.is_eq(c, '\n')), BmL.nonl(t), h))),
        Equal.cong(List<&2, String>, List<&2, String>, l => String.split.push(c, l), String.split(t, '\n'), [t], split_one(t, Comp.and_right(Bool.not(Char.is_eq(c, '\n')), BmL.nonl(t), h))))

def split_join.go(xs: List<&2, String>, +h: String, +hh: {BmL.nonl(h) == True{} : Bool}, +hx: {all_nonl(xs) == True{} : Bool}) -> {String.split(String.join.go(xs, h, "\n"), '\n') == h <> xs : List<&2, String>}:
  match xs:
    case Nil{}:
      split_one(h, hh)
    case +x <> +rest:
      Equal.trans(List<&2, String>, String.split(h ++ SCon{'\n', String.join.go(rest, x, "\n")}, '\n'), h <> String.split(String.join.go(rest, x, "\n"), '\n'), h <> x <> rest,
        BmL.split_nl(h, String.join.go(rest, x, "\n"), hh),
        Equal.cong(List<&2, String>, List<&2, String>, l => h <> l, String.split(String.join.go(rest, x, "\n"), '\n'), x <> rest,
          split_join.go(rest, x, Comp.and_left(BmL.nonl(x), all_nonl(rest), hx), Comp.and_right(BmL.nonl(x), all_nonl(rest), hx))))

# Lines of one line each, joined with newlines, split at them: the lines.
def split_join(+x: String, +rest: List<&2, String>, +hx: {all_nonl(x <> rest) == True{} : Bool}) -> {String.split(String.join(x <> rest, "\n"), '\n') == x <> rest : List<&2, String>}:
  split_join.go(rest, x, Comp.and_left(BmL.nonl(x), all_nonl(rest), hx), Comp.and_right(BmL.nonl(x), all_nonl(rest), hx))

def nonl_app(a: String, -b: String, +ha: {BmL.nonl(a) == True{} : Bool}, hb: {BmL.nonl(b) == True{} : Bool}) -> {BmL.nonl(a ++ b) == True{} : Bool}:
  BmL.nonl_app(a, b, ha, hb)

def all_nonl_app(xs: List<&2, String>, -ys: List<&2, String>, +hx: {all_nonl(xs) == True{} : Bool}, hy: {all_nonl(ys) == True{} : Bool}) -> {all_nonl(List.append(&2, String, xs, ys)) == True{} : Bool}:
  match xs:
    case Nil{}:
      hy
    case +x <> +rest:
      AL.and_intro(BmL.nonl(x), all_nonl(List.append(&2, String, rest, ys)), Comp.and_left(BmL.nonl(x), all_nonl(rest), hx), all_nonl_app(rest, ys, Comp.and_right(BmL.nonl(x), all_nonl(rest), hx), hy))

# Strings
# -------

def take_zero(s: String) -> {String.take(s, 0n) == SNil{} : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{c, t}:
      {==}

def drop_zero(s: String) -> {String.drop(s, 0n) == s : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{c, t}:
      {==}

# As many characters as `a` holds, of `a` and what follows it, are `a`.
def take_past(a: String, +b: String) -> {String.take(a ++ b, String.length(a)) == a : String}:
  match a:
    case SNil{}:
      take_zero(b)
    case SCon{+c, t}:
      Equal.cong(String, String, x => SCon{c, x}, String.take(t ++ b, String.length(t)), t, take_past(t, b))

# One more than that dropped, past a separator, leaves what follows it.
def drop_past(a: String, +c: Char, +p: String) -> {String.drop(a ++ SCon{c, p}, 1n+String.length(a)) == p : String}:
  match a:
    case SNil{}:
      drop_zero(p)
    case SCon{x, t}:
      drop_past(t, c, p)

def member_is(xs: List<&2, String>, +x: String) -> {Store.member(xs, x) == Rev.member(xs, x) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +y <> rest:
      Equal.cong(Bool, Bool, m => Bool.or(String.eq(y, x), m), Store.member(rest, x), Rev.member(rest, x), member_is(rest, x))

# What the host answers `Store.at`
# --------------------------------

# Where the bytes with a digest are, as the host knows it: a path relative
# to the store, or nothing.
def at.line(a: Maybe<&2, String>) -> String:
  match a:
    case None{}:
      "-"
    case Some{p}:
      p

def at.lines(as: List<&2, Maybe<&2, String>>) -> List<&2, String>:
  match as:
    case Nil{}:
      Nil{}
    case a <> rest:
      at.line(a) <> at.lines(rest)

# A document the host's catalogue says forgets a digest: `<digest> <path>`.
def forgets.line(f: T.Split) -> String:
  match f:
    case T.Split{d, p}:
      d ++ " " ++ p

def forgets.lines(fs: List<&2, T.Split>) -> List<&2, String>:
  match fs:
    case Nil{}:
      Nil{}
    case f <> rest:
      forgets.line(f) <> forgets.lines(rest)

# The answer in the `forgets` form: the lines joined, as `lines.join("\n")`.
def at.answer(as: List<&2, Maybe<&2, String>>, fs: List<&2, T.Split>) -> String:
  String.join(List.append(&2, String, at.lines(as), forgets.lines(fs)), "\n")

# A path the host gives for a document: not empty, not `-`, and one line.
def path_ok(+p: String) -> Bool:
  Bool.and(Bool.not(String.is_empty(p)), Bool.and(Bool.not(String.eq(p, "-")), BmL.nonl(p)))

def answers_ok(as: List<&2, Maybe<&2, String>>) -> Bool:
  match as:
    case Nil{}:
      True{}
    case None{} <> rest:
      answers_ok(rest)
    case Some{+p} <> rest:
      Bool.and(path_ok(p), answers_ok(rest))

# A digest is sixty-four characters and one line.
def forgets_ok(fs: List<&2, T.Split>) -> Bool:
  match fs:
    case Nil{}:
      True{}
    case T.Split{+d, +p} <> rest:
      Bool.and(Bool.and(Nat.is_eq(String.length(d), 64n), BmL.nonl(d)), Bool.and(path_ok(p), forgets_ok(rest)))

# An answer for each digest asked, every path one the host gives.
def answer_ok(ds: List<&2, String>, +as: List<&2, Maybe<&2, String>>, +fs: List<&2, T.Split>) -> Bool:
  Bool.and(Nat.is_eq(List.length(&2, String, ds), List.length(&2, Maybe<&2, String>, as)), Bool.and(answers_ok(as), forgets_ok(fs)))

# What it asks to be read: each path given, with the store's root before it.
def found(+root: String, as: List<&2, Maybe<&2, String>>) -> List<&2, String>:
  match as:
    case Nil{}:
      Nil{}
    case None{} <> rest:
      found(root, rest)
    case Some{p} <> rest:
      (root ++ "/" ++ p) <> found(root, rest)

# The digests the store holds: those given a path, in the order asked.
def held(ds: List<&2, String>, as: List<&2, Maybe<&2, String>>) -> List<&2, String>:
  match ds as:
    case d <> dr Some{p} <> ar:
      d <> held(dr, ar)
    case d <> dr None{} <> ar:
      held(dr, ar)
    case _ _:
      Nil{}

# And those it holds nothing for.
def gone(ds: List<&2, String>, as: List<&2, Maybe<&2, String>>) -> List<&2, String>:
  match ds as:
    case d <> dr None{} <> ar:
      d <> gone(dr, ar)
    case d <> dr Some{p} <> ar:
      gone(dr, ar)
    case _ _:
      Nil{}

# The documents said to forget a digest among `hs`, in the host's order.
def near(+root: String, +hs: List<&2, String>, fs: List<&2, T.Split>) -> List<&2, String>:
  match fs:
    case Nil{}:
      Nil{}
    case T.Split{+d, p} <> rest:
      List.filter.put(String, root ++ "/" ++ p, near(root, hs, rest), Rev.member(hs, d))

# Reading the answer back
# -----------------------

# The first answer for each digest asked is the host's line for it, and
# what follows those lines is the rest.
def answered_app(ds: List<&2, String>, as: List<&2, Maybe<&2, String>>, -ys: List<&2, String>, h: {Nat.is_eq(List.length(&2, String, ds), List.length(&2, Maybe<&2, String>, as)) == True{} : Bool}) -> {Store.answered(ds, List.append(&2, String, at.lines(as), ys)) == at.lines(as) : List<&2, String>}:
  match ds as:
    case Nil{} Nil{}:
      {==}
    case Nil{} a <> ar:
      Empty.absurd({Store.answered(Nil{}, List.append(&2, String, at.lines(a <> ar), ys)) == at.lines(a <> ar) : List<&2, String>}, S.false_true(h))
    case d <> dr Nil{}:
      Empty.absurd({Store.answered(d <> dr, List.append(&2, String, at.lines(Nil{}), ys)) == at.lines(Nil{}) : List<&2, String>}, S.false_true(h))
    case d <> dr +a <> ar:
      Equal.cong(List<&2, String>, List<&2, String>, l => at.line(a) <> l, Store.answered(dr, List.append(&2, String, at.lines(ar), ys)), at.lines(ar), answered_app(dr, ar, ys, h))

def besides_app(ds: List<&2, String>, as: List<&2, Maybe<&2, String>>, +ys: List<&2, String>, h: {Nat.is_eq(List.length(&2, String, ds), List.length(&2, Maybe<&2, String>, as)) == True{} : Bool}) -> {Store.besides(ds, List.append(&2, String, at.lines(as), ys)) == ys : List<&2, String>}:
  match ds as:
    case Nil{} Nil{}:
      {==}
    case Nil{} a <> ar:
      Empty.absurd({Store.besides(Nil{}, List.append(&2, String, at.lines(a <> ar), ys)) == ys : List<&2, String>}, S.false_true(h))
    case d <> dr Nil{}:
      Empty.absurd({Store.besides(d <> dr, List.append(&2, String, at.lines(Nil{}), ys)) == ys : List<&2, String>}, S.false_true(h))
    case d <> dr a <> ar:
      besides_app(dr, ar, ys, h)

def path_ne(+p: String, h: {path_ok(p) == True{} : Bool}) -> {String.is_empty(p) == False{} : Bool}:
  AL.not_of_true(String.is_empty(p), Comp.and_left(Bool.not(String.is_empty(p)), Bool.and(Bool.not(String.eq(p, "-")), BmL.nonl(p)), h))

def path_dash(+p: String, h: {path_ok(p) == True{} : Bool}) -> {String.eq(p, "-") == False{} : Bool}:
  AL.not_of_true(String.eq(p, "-"), Comp.and_left(Bool.not(String.eq(p, "-")), BmL.nonl(p), Comp.and_right(Bool.not(String.is_empty(p)), Bool.and(Bool.not(String.eq(p, "-")), BmL.nonl(p)), h)))

def path_nonl(+p: String, h: {path_ok(p) == True{} : Bool}) -> {BmL.nonl(p) == True{} : Bool}:
  Comp.and_right(Bool.not(String.eq(p, "-")), BmL.nonl(p), Comp.and_right(Bool.not(String.is_empty(p)), Bool.and(Bool.not(String.eq(p, "-")), BmL.nonl(p)), h))

# Each path given is read, under the root; `-` is nothing to read.
def found_paths(+root: String, as: List<&2, Maybe<&2, String>>, +h: {answers_ok(as) == True{} : Bool}) -> {Store.at.paths(root, at.lines(as)) == found(root, as) : List<&2, String>}:
  match as:
    case Nil{}:
      {==}
    case None{} <> +rest:
      found_paths(root, rest, h)
    case Some{+p} <> +rest:
      +hp = Comp.and_left(path_ok(p), answers_ok(rest), h)
      %Equal.sym(Bool, String.eq(p, "-"), False{}, path_dash(p, hp)) : {Bool.pick(List<&2, String>, Bool.or(_, String.is_empty(p)), Store.at.paths(root, at.lines(rest)), (root ++ "/" ++ p) <> Store.at.paths(root, at.lines(rest))) == (root ++ "/" ++ p) <> found(root, rest) : List<&2, String>}
      %Equal.sym(Bool, String.is_empty(p), False{}, path_ne(p, hp)) : {Bool.pick(List<&2, String>, Bool.or(False{}, _), Store.at.paths(root, at.lines(rest)), (root ++ "/" ++ p) <> Store.at.paths(root, at.lines(rest))) == (root ++ "/" ++ p) <> found(root, rest) : List<&2, String>}
      Equal.cong(List<&2, String>, List<&2, String>, l => (root ++ "/" ++ p) <> l, Store.at.paths(root, at.lines(rest)), found(root, rest), found_paths(root, rest, Comp.and_right(path_ok(p), answers_ok(rest), h)))

# A digest given a path is one the store holds, in the order asked.
def held_of(ds: List<&2, String>, as: List<&2, Maybe<&2, String>>, +h: {answers_ok(as) == True{} : Bool}) -> {Store.held.of(ds, at.lines(as)) == held(ds, as) : List<&2, String>}:
  match ds as:
    case Nil{} _:
      {==}
    case d <> dr Nil{}:
      {==}
    case d <> dr None{} <> ar:
      held_of(dr, ar, h)
    case +d <> dr Some{+p} <> ar:
      %Equal.sym(Bool, String.eq(p, "-"), False{}, path_dash(p, Comp.and_left(path_ok(p), answers_ok(ar), h))) : {List.filter.put(String, d, Store.held.of(dr, at.lines(ar)), Bool.not(_)) == d <> held(dr, ar) : List<&2, String>}
      Equal.cong(List<&2, String>, List<&2, String>, l => d <> l, Store.held.of(dr, at.lines(ar)), held(dr, ar), held_of(dr, ar, Comp.and_right(path_ok(p), answers_ok(ar), h)))

# A digest answered `-` is one it holds nothing for, in the order asked.
def gone_of(ds: List<&2, String>, as: List<&2, Maybe<&2, String>>, +h: {answers_ok(as) == True{} : Bool}) -> {Store.missing(ds, at.lines(as)) == gone(ds, as) : List<&2, String>}:
  match ds as:
    case Nil{} _:
      {==}
    case d <> dr Nil{}:
      {==}
    case +d <> dr None{} <> ar:
      Equal.cong(List<&2, String>, List<&2, String>, l => d <> l, Store.missing(dr, at.lines(ar)), gone(dr, ar), gone_of(dr, ar, h))
    case d <> dr Some{+p} <> ar:
      %Equal.sym(Bool, String.eq(p, "-"), False{}, path_dash(p, Comp.and_left(path_ok(p), answers_ok(ar), h))) : {List.filter.put(String, d, Store.missing(dr, at.lines(ar)), _) == gone(dr, ar) : List<&2, String>}
      gone_of(dr, ar, Comp.and_right(path_ok(p), answers_ok(ar), h))

# A document said to forget a digest is read where the digest is one the
# store holds: its line is the digest, a space, and its path.
def under_put(+root: String, m: Bool, +p: String, +b: List<&2, String>, -n: List<&2, String>, ne: {String.is_empty(p) == False{} : Bool}, ih: {Store.under(root, b) == n : List<&2, String>}) -> {Store.under(root, List.filter.put(String, p, b, m)) == List.filter.put(String, root ++ "/" ++ p, n, m) : List<&2, String>}:
  match m p:
    case False{} _:
      ih
    case True{} SNil{}:
      Empty.absurd({Store.under(root, SNil{} <> b) == (root ++ "/" ++ SNil{}) <> n : List<&2, String>}, S.true_false(ne))
    case True{} SCon{+c, +t}:
      Equal.cong(List<&2, String>, List<&2, String>, l => (root ++ "/" ++ SCon{c, t}) <> l, Store.under(root, b), n, ih)

def digest_of(+d: String, +p: String, len: {String.length(d) == 64n : Nat}) -> {String.take(d ++ " " ++ p, 64n) == d : String}:
  %len : {String.take(d ++ " " ++ p, _) == d : String}
  take_past(d, " " ++ p)

def path_of(+d: String, +p: String, len: {String.length(d) == 64n : Nat}) -> {String.drop(d ++ " " ++ p, 65n) == p : String}:
  %len : {String.drop(d ++ " " ++ p, 1n+_) == p : String}
  drop_past(d, ' ', p)

def beside_line(+hs: List<&2, String>, +d: String, +p: String, +ls: List<&2, String>, +len: {String.length(d) == 64n : Nat}) -> {Store.beside.paths(hs, (d ++ " " ++ p) <> ls) == List.filter.put(String, p, Store.beside.paths(hs, ls), Rev.member(hs, d)) : List<&2, String>}:
  +te = digest_of(d, p, len)
  +de = path_of(d, p, len)
  %Equal.sym(String, String.take(d ++ " " ++ p, 64n), d, te) : {List.filter.put(String, String.drop(d ++ " " ++ p, 65n), Store.beside.paths(hs, ls), Store.member(hs, _)) == List.filter.put(String, p, Store.beside.paths(hs, ls), Rev.member(hs, d)) : List<&2, String>}
  %Equal.sym(String, String.drop(d ++ " " ++ p, 65n), p, de) : {List.filter.put(String, _, Store.beside.paths(hs, ls), Store.member(hs, d)) == List.filter.put(String, p, Store.beside.paths(hs, ls), Rev.member(hs, d)) : List<&2, String>}
  %Equal.sym(Bool, Store.member(hs, d), Rev.member(hs, d), member_is(hs, d)) : {List.filter.put(String, p, Store.beside.paths(hs, ls), _) == List.filter.put(String, p, Store.beside.paths(hs, ls), Rev.member(hs, d)) : List<&2, String>}
  {==}

def near_of(+root: String, +hs: List<&2, String>, fs: List<&2, T.Split>, +h: {forgets_ok(fs) == True{} : Bool}) -> {Store.under(root, Store.beside.paths(hs, forgets.lines(fs))) == near(root, hs, fs) : List<&2, String>}:
  match fs:
    case Nil{}:
      {==}
    case T.Split{+d, +p} <> +rest:
      +hd = Comp.and_left(Bool.and(Nat.is_eq(String.length(d), 64n), BmL.nonl(d)), Bool.and(path_ok(p), forgets_ok(rest)), h)
      +hr = Comp.and_right(Bool.and(Nat.is_eq(String.length(d), 64n), BmL.nonl(d)), Bool.and(path_ok(p), forgets_ok(rest)), h)
      +len = Comp.eq_of_is_eq(String.length(d), 64n, Comp.and_left(Nat.is_eq(String.length(d), 64n), BmL.nonl(d), hd))
      %Equal.sym(List<&2, String>, Store.beside.paths(hs, (d ++ " " ++ p) <> forgets.lines(rest)), List.filter.put(String, p, Store.beside.paths(hs, forgets.lines(rest)), Rev.member(hs, d)), beside_line(hs, d, p, forgets.lines(rest), len)) : {Store.under(root, _) == near(root, hs, T.Split{d, p} <> rest) : List<&2, String>}
      under_put(root, Rev.member(hs, d), p, Store.beside.paths(hs, forgets.lines(rest)), near(root, hs, rest), path_ne(p, Comp.and_left(path_ok(p), forgets_ok(rest), hr)), near_of(root, hs, rest, Comp.and_right(path_ok(p), forgets_ok(rest), hr)))

def lines_nonl(as: List<&2, Maybe<&2, String>>, +h: {answers_ok(as) == True{} : Bool}) -> {all_nonl(at.lines(as)) == True{} : Bool}:
  match as:
    case Nil{}:
      {==}
    case None{} <> +rest:
      lines_nonl(rest, h)
    case Some{+p} <> +rest:
      AL.and_intro(BmL.nonl(p), all_nonl(at.lines(rest)), path_nonl(p, Comp.and_left(path_ok(p), answers_ok(rest), h)), lines_nonl(rest, Comp.and_right(path_ok(p), answers_ok(rest), h)))

def forgets_nonl(fs: List<&2, T.Split>, +h: {forgets_ok(fs) == True{} : Bool}) -> {all_nonl(forgets.lines(fs)) == True{} : Bool}:
  match fs:
    case Nil{}:
      {==}
    case T.Split{+d, +p} <> +rest:
      +hd = Comp.and_left(Bool.and(Nat.is_eq(String.length(d), 64n), BmL.nonl(d)), Bool.and(path_ok(p), forgets_ok(rest)), h)
      +hr = Comp.and_right(Bool.and(Nat.is_eq(String.length(d), 64n), BmL.nonl(d)), Bool.and(path_ok(p), forgets_ok(rest)), h)
      AL.and_intro(BmL.nonl(d ++ " " ++ p), all_nonl(forgets.lines(rest)),
        nonl_app(d, " " ++ p, Comp.and_right(Nat.is_eq(String.length(d), 64n), BmL.nonl(d), hd), path_nonl(p, Comp.and_left(path_ok(p), forgets_ok(rest), hr))),
        forgets_nonl(rest, Comp.and_right(path_ok(p), forgets_ok(rest), hr)))

# With the answer split back into its lines, what `fetch` asks to be read
# is what the host answered.
def asked_of(+root: String, +ds: List<&2, String>, +as: List<&2, Maybe<&2, String>>, +fs: List<&2, T.Split>, +h: {answer_ok(ds, as, fs) == True{} : Bool}, e: {List.append(&2, String, at.lines(as), forgets.lines(fs)) == String.split(at.answer(as, fs), '\n') : List<&2, String>}) -> {Store.asked(root, ds, at.answer(as, fs)) == Store.Asked{found(root, as), held(ds, as), near(root, held(ds, as), fs), gone(ds, as)} : Store.Asked}:
  +hl = Comp.and_left(Nat.is_eq(List.length(&2, String, ds), List.length(&2, Maybe<&2, String>, as)), Bool.and(answers_ok(as), forgets_ok(fs)), h)
  +ho = Comp.and_right(Nat.is_eq(List.length(&2, String, ds), List.length(&2, Maybe<&2, String>, as)), Bool.and(answers_ok(as), forgets_ok(fs)), h)
  +ha = Comp.and_left(answers_ok(as), forgets_ok(fs), ho)
  +hf = Comp.and_right(answers_ok(as), forgets_ok(fs), ho)
  %e : {Store.Asked{Store.at.paths(root, Store.answered(ds, _)), Store.held.of(ds, Store.answered(ds, _)), Store.under(root, Store.beside.paths(Store.held.of(ds, Store.answered(ds, _)), Store.besides(ds, _))), Store.missing(ds, Store.answered(ds, _))} == Store.Asked{found(root, as), held(ds, as), near(root, held(ds, as), fs), gone(ds, as)} : Store.Asked}
  %Equal.sym(List<&2, String>, Store.answered(ds, List.append(&2, String, at.lines(as), forgets.lines(fs))), at.lines(as), answered_app(ds, as, forgets.lines(fs), hl)) : {Store.Asked{Store.at.paths(root, _), Store.held.of(ds, _), Store.under(root, Store.beside.paths(Store.held.of(ds, _), Store.besides(ds, List.append(&2, String, at.lines(as), forgets.lines(fs))))), Store.missing(ds, _)} == Store.Asked{found(root, as), held(ds, as), near(root, held(ds, as), fs), gone(ds, as)} : Store.Asked}
  %Equal.sym(List<&2, String>, Store.besides(ds, List.append(&2, String, at.lines(as), forgets.lines(fs))), forgets.lines(fs), besides_app(ds, as, forgets.lines(fs), hl)) : {Store.Asked{Store.at.paths(root, at.lines(as)), Store.held.of(ds, at.lines(as)), Store.under(root, Store.beside.paths(Store.held.of(ds, at.lines(as)), _)), Store.missing(ds, at.lines(as))} == Store.Asked{found(root, as), held(ds, as), near(root, held(ds, as), fs), gone(ds, as)} : Store.Asked}
  %Equal.sym(List<&2, String>, Store.at.paths(root, at.lines(as)), found(root, as), found_paths(root, as, ha)) : {Store.Asked{_, Store.held.of(ds, at.lines(as)), Store.under(root, Store.beside.paths(Store.held.of(ds, at.lines(as)), forgets.lines(fs))), Store.missing(ds, at.lines(as))} == Store.Asked{found(root, as), held(ds, as), near(root, held(ds, as), fs), gone(ds, as)} : Store.Asked}
  %Equal.sym(List<&2, String>, Store.held.of(ds, at.lines(as)), held(ds, as), held_of(ds, as, ha)) : {Store.Asked{found(root, as), _, Store.under(root, Store.beside.paths(_, forgets.lines(fs))), Store.missing(ds, at.lines(as))} == Store.Asked{found(root, as), held(ds, as), near(root, held(ds, as), fs), gone(ds, as)} : Store.Asked}
  %Equal.sym(List<&2, String>, Store.missing(ds, at.lines(as)), gone(ds, as), gone_of(ds, as, ha)) : {Store.Asked{found(root, as), held(ds, as), Store.under(root, Store.beside.paths(held(ds, as), forgets.lines(fs))), _} == Store.Asked{found(root, as), held(ds, as), near(root, held(ds, as), fs), gone(ds, as)} : Store.Asked}
  %Equal.sym(List<&2, String>, Store.under(root, Store.beside.paths(held(ds, as), forgets.lines(fs))), near(root, held(ds, as), fs), near_of(root, held(ds, as), fs, hf)) : {Store.Asked{found(root, as), held(ds, as), _, gone(ds, as)} == Store.Asked{found(root, as), held(ds, as), near(root, held(ds, as), fs), gone(ds, as)} : Store.Asked}
  {==}

def nothing_asked(+root: String, ds: List<&2, String>, +h: {answer_ok(ds, Nil{}, Nil{}) == True{} : Bool}) -> {Store.asked(root, ds, at.answer(Nil{}, Nil{})) == Store.Asked{found(root, Nil{}), held(ds, Nil{}), near(root, held(ds, Nil{}), Nil{}), gone(ds, Nil{})} : Store.Asked}:
  match ds:
    case Nil{}:
      {==}
    case d <> dr:
      Empty.absurd({Store.asked(root, d <> dr, at.answer(Nil{}, Nil{})) == Store.Asked{found(root, Nil{}), held(d <> dr, Nil{}), near(root, held(d <> dr, Nil{}), Nil{}), gone(d <> dr, Nil{})} : Store.Asked}, S.false_true(Comp.and_left(Nat.is_eq(List.length(&2, String, d <> dr), 0n), Bool.and(True{}, True{}), h)))

# `fetch_reads_the_hosts_answer`.
def fetch_reads(as: List<&2, Maybe<&2, String>>, fs: List<&2, T.Split>, +root: String, +ds: List<&2, String>, +h: {answer_ok(ds, as, fs) == True{} : Bool}) -> {Store.asked(root, ds, at.answer(as, fs)) == Store.Asked{found(root, as), held(ds, as), near(root, held(ds, as), fs), gone(ds, as)} : Store.Asked}:
  match as fs:
    case +a <> +ar +fs2:
      +ho = Comp.and_right(Nat.is_eq(List.length(&2, String, ds), List.length(&2, Maybe<&2, String>, a <> ar)), Bool.and(answers_ok(a <> ar), forgets_ok(fs2)), h)
      asked_of(root, ds, a <> ar, fs2, h, Equal.sym(List<&2, String>, String.split(at.answer(a <> ar, fs2), '\n'), List.append(&2, String, at.lines(a <> ar), forgets.lines(fs2)),
        split_join(at.line(a), List.append(&2, String, at.lines(ar), forgets.lines(fs2)), all_nonl_app(at.lines(a <> ar), forgets.lines(fs2), lines_nonl(a <> ar, Comp.and_left(answers_ok(a <> ar), forgets_ok(fs2), ho)), forgets_nonl(fs2, Comp.and_right(answers_ok(a <> ar), forgets_ok(fs2), ho))))))
    case Nil{} +f <> +fr:
      +ho = Comp.and_right(Nat.is_eq(List.length(&2, String, ds), 0n), Bool.and(True{}, forgets_ok(f <> fr)), h)
      asked_of(root, ds, Nil{}, f <> fr, h, Equal.sym(List<&2, String>, String.split(at.answer(Nil{}, f <> fr), '\n'), forgets.lines(f <> fr),
        split_join(forgets.line(f), forgets.lines(fr), forgets_nonl(f <> fr, ho))))
    case Nil{} Nil{}:
      nothing_asked(root, ds, h)

# What `Store.unsettled` reads
# ----------------------------

# The digests the documents are said to forget, in the host's order.
def forgotten(fs: List<&2, T.Split>) -> List<&2, String>:
  match fs:
    case Nil{}:
      Nil{}
    case T.Split{d, p} <> rest:
      d <> forgotten(rest)

# Every string of `xs` holds something.
def all_full(xs: List<&2, String>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case x <> rest:
      Bool.and(Bool.not(String.is_empty(x)), all_full(rest))

# A listing with no empty line keeps every line.
def kept_full(xs: List<&2, String>, +h: {all_full(xs) == True{} : Bool}) -> {Store.kept(xs) == xs : List<&2, String>}:
  match xs:
    case Nil{}:
      {==}
    case SNil{} <> rest:
      Empty.absurd({Store.kept(SNil{} <> rest) == SNil{} <> rest : List<&2, String>}, S.false_true(Comp.and_left(False{}, all_full(rest), h)))
    case SCon{+c, +t} <> +rest:
      Equal.cong(List<&2, String>, List<&2, String>, l => SCon{c, t} <> l, Store.kept(rest), rest, kept_full(rest, Comp.and_right(True{}, all_full(rest), h)))

def full_app(xs: List<&2, String>, -ys: List<&2, String>, +hx: {all_full(xs) == True{} : Bool}, hy: {all_full(ys) == True{} : Bool}) -> {all_full(List.append(&2, String, xs, ys)) == True{} : Bool}:
  match xs:
    case Nil{}:
      hy
    case +x <> +rest:
      AL.and_intro(Bool.not(String.is_empty(x)), all_full(List.append(&2, String, rest, ys)), Comp.and_left(Bool.not(String.is_empty(x)), all_full(rest), hx), full_app(rest, ys, Comp.and_right(Bool.not(String.is_empty(x)), all_full(rest), hx), hy))

def lines_full(as: List<&2, Maybe<&2, String>>, +h: {answers_ok(as) == True{} : Bool}) -> {all_full(at.lines(as)) == True{} : Bool}:
  match as:
    case Nil{}:
      {==}
    case None{} <> +rest:
      lines_full(rest, h)
    case Some{+p} <> +rest:
      AL.and_intro(Bool.not(String.is_empty(p)), all_full(at.lines(rest)), AL.not_true(String.is_empty(p), path_ne(p, Comp.and_left(path_ok(p), answers_ok(rest), h))), lines_full(rest, Comp.and_right(path_ok(p), answers_ok(rest), h)))

def app_full(a: String, -b: String) -> {String.is_empty(a ++ SCon{' ', b}) == False{} : Bool}:
  match a:
    case SNil{}:
      {==}
    case SCon{c, t}:
      {==}

def forgets_full(fs: List<&2, T.Split>) -> {all_full(forgets.lines(fs)) == True{} : Bool}:
  match fs:
    case Nil{}:
      {==}
    case T.Split{+d, +p} <> +rest:
      AL.and_intro(Bool.not(String.is_empty(d ++ " " ++ p)), all_full(forgets.lines(rest)), AL.not_true(String.is_empty(d ++ " " ++ p), app_full(d, p)), forgets_full(rest))

# Each forgetting line names the digest it is said to forget.
def forgotten_of(fs: List<&2, T.Split>, +h: {forgets_ok(fs) == True{} : Bool}) -> {Store.forgotten.of(forgets.lines(fs)) == forgotten(fs) : List<&2, String>}:
  match fs:
    case Nil{}:
      {==}
    case T.Split{+d, +p} <> +rest:
      +hd = Comp.and_left(Bool.and(Nat.is_eq(String.length(d), 64n), BmL.nonl(d)), Bool.and(path_ok(p), forgets_ok(rest)), h)
      +hr = Comp.and_right(Bool.and(Nat.is_eq(String.length(d), 64n), BmL.nonl(d)), Bool.and(path_ok(p), forgets_ok(rest)), h)
      %Equal.sym(String, String.take(d ++ " " ++ p, 64n), d, digest_of(d, p, Comp.eq_of_is_eq(String.length(d), 64n, Comp.and_left(Nat.is_eq(String.length(d), 64n), BmL.nonl(d), hd)))) : {_ <> Store.forgotten.of(forgets.lines(rest)) == d <> forgotten(rest) : List<&2, String>}
      Equal.cong(List<&2, String>, List<&2, String>, l => d <> l, Store.forgotten.of(forgets.lines(rest)), forgotten(rest), forgotten_of(rest, Comp.and_right(path_ok(p), forgets_ok(rest), hr)))

# A digest answered `-` is unsettled, one given a path is not, and then
# each digest a document is said to forget is.
def unsettled_of(ds: List<&2, String>, as: List<&2, Maybe<&2, String>>, +fs: List<&2, T.Split>, +hl: {Nat.is_eq(List.length(&2, String, ds), List.length(&2, Maybe<&2, String>, as)) == True{} : Bool}, +ha: {answers_ok(as) == True{} : Bool}, +hf: {forgets_ok(fs) == True{} : Bool}) -> {Store.unsettled.of(ds, List.append(&2, String, at.lines(as), forgets.lines(fs))) == List.append(&2, String, gone(ds, as), forgotten(fs)) : List<&2, String>}:
  match ds as:
    case Nil{} Nil{}:
      forgotten_of(fs, hf)
    case Nil{} a <> ar:
      Empty.absurd({Store.unsettled.of(Nil{}, List.append(&2, String, at.lines(a <> ar), forgets.lines(fs))) == List.append(&2, String, gone(Nil{}, a <> ar), forgotten(fs)) : List<&2, String>}, S.false_true(hl))
    case d <> dr Nil{}:
      Empty.absurd({Store.unsettled.of(d <> dr, List.append(&2, String, at.lines(Nil{}), forgets.lines(fs))) == List.append(&2, String, gone(d <> dr, Nil{}), forgotten(fs)) : List<&2, String>}, S.false_true(hl))
    case +d <> dr None{} <> ar:
      Equal.cong(List<&2, String>, List<&2, String>, l => d <> l, Store.unsettled.of(dr, List.append(&2, String, at.lines(ar), forgets.lines(fs))), List.append(&2, String, gone(dr, ar), forgotten(fs)), unsettled_of(dr, ar, fs, hl, ha, hf))
    case d <> dr Some{+p} <> ar:
      %Equal.sym(Bool, String.eq(p, "-"), False{}, path_dash(p, Comp.and_left(path_ok(p), answers_ok(ar), ha))) : {List.filter.put(String, d, Store.unsettled.of(dr, List.append(&2, String, at.lines(ar), forgets.lines(fs))), _) == List.append(&2, String, gone(dr, ar), forgotten(fs)) : List<&2, String>}
      unsettled_of(dr, ar, fs, hl, Comp.and_right(path_ok(p), answers_ok(ar), ha), hf)

def unsettled_lines(+ds: List<&2, String>, +as: List<&2, Maybe<&2, String>>, +fs: List<&2, T.Split>, +h: {answer_ok(ds, as, fs) == True{} : Bool}, e: {List.append(&2, String, at.lines(as), forgets.lines(fs)) == String.split(at.answer(as, fs), '\n') : List<&2, String>}) -> {Store.unsettled.read(ds, at.answer(as, fs)) == List.append(&2, String, gone(ds, as), forgotten(fs)) : List<&2, String>}:
  +hl = Comp.and_left(Nat.is_eq(List.length(&2, String, ds), List.length(&2, Maybe<&2, String>, as)), Bool.and(answers_ok(as), forgets_ok(fs)), h)
  +ho = Comp.and_right(Nat.is_eq(List.length(&2, String, ds), List.length(&2, Maybe<&2, String>, as)), Bool.and(answers_ok(as), forgets_ok(fs)), h)
  +ha = Comp.and_left(answers_ok(as), forgets_ok(fs), ho)
  +hf = Comp.and_right(answers_ok(as), forgets_ok(fs), ho)
  %e : {Store.unsettled.of(ds, Store.kept(_)) == List.append(&2, String, gone(ds, as), forgotten(fs)) : List<&2, String>}
  %Equal.sym(List<&2, String>, Store.kept(List.append(&2, String, at.lines(as), forgets.lines(fs))), List.append(&2, String, at.lines(as), forgets.lines(fs)), kept_full(List.append(&2, String, at.lines(as), forgets.lines(fs)), full_app(at.lines(as), forgets.lines(fs), lines_full(as, ha), forgets_full(fs)))) : {Store.unsettled.of(ds, _) == List.append(&2, String, gone(ds, as), forgotten(fs)) : List<&2, String>}
  unsettled_of(ds, as, fs, hl, ha, hf)

def nothing_unsettled(ds: List<&2, String>, +h: {answer_ok(ds, Nil{}, Nil{}) == True{} : Bool}) -> {Store.unsettled.read(ds, at.answer(Nil{}, Nil{})) == List.append(&2, String, gone(ds, Nil{}), forgotten(Nil{})) : List<&2, String>}:
  match ds:
    case Nil{}:
      {==}
    case d <> dr:
      Empty.absurd({Store.unsettled.read(d <> dr, at.answer(Nil{}, Nil{})) == List.append(&2, String, gone(d <> dr, Nil{}), forgotten(Nil{})) : List<&2, String>}, S.false_true(Comp.and_left(Nat.is_eq(List.length(&2, String, d <> dr), 0n), Bool.and(True{}, True{}), h)))

# `unsettled_reads_the_hosts_answer`.
def unsettled_reads(as: List<&2, Maybe<&2, String>>, fs: List<&2, T.Split>, +ds: List<&2, String>, +h: {answer_ok(ds, as, fs) == True{} : Bool}) -> {Store.unsettled.read(ds, at.answer(as, fs)) == List.append(&2, String, gone(ds, as), forgotten(fs)) : List<&2, String>}:
  match as fs:
    case +a <> +ar +fs2:
      +ho = Comp.and_right(Nat.is_eq(List.length(&2, String, ds), List.length(&2, Maybe<&2, String>, a <> ar)), Bool.and(answers_ok(a <> ar), forgets_ok(fs2)), h)
      unsettled_lines(ds, a <> ar, fs2, h, Equal.sym(List<&2, String>, String.split(at.answer(a <> ar, fs2), '\n'), List.append(&2, String, at.lines(a <> ar), forgets.lines(fs2)),
        split_join(at.line(a), List.append(&2, String, at.lines(ar), forgets.lines(fs2)), all_nonl_app(at.lines(a <> ar), forgets.lines(fs2), lines_nonl(a <> ar, Comp.and_left(answers_ok(a <> ar), forgets_ok(fs2), ho)), forgets_nonl(fs2, Comp.and_right(answers_ok(a <> ar), forgets_ok(fs2), ho))))))
    case Nil{} +f <> +fr:
      +ho = Comp.and_right(Nat.is_eq(List.length(&2, String, ds), 0n), Bool.and(True{}, forgets_ok(f <> fr)), h)
      unsettled_lines(ds, Nil{}, f <> fr, h, Equal.sym(List<&2, String>, String.split(at.answer(Nil{}, f <> fr), '\n'), forgets.lines(f <> fr),
        split_join(forgets.line(f), forgets.lines(fr), forgets_nonl(f <> fr, ho))))
    case Nil{} Nil{}:
      nothing_unsettled(ds, h)

# What `Store.run` is asked
# -------------------------

def char_refl(c: Char) -> {Char.is_eq(c, c) == True{} : Bool}:
  match c:
    case Chr{U32{w}}:
      (%Equal.sym(Cmp, Word.cmp(32n, w, w), EQ{}, S.word_refl(32n, w)) : {Cmp.is_eq(_) == True{} : Bool}
        {==})

# A string that does not hold the character `c`.
def nosep(s: String, +c: Char) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{x, t}:
      Bool.and(Bool.not(Char.is_eq(x, c)), nosep(t, c))

def all_nosep(xs: List<&2, String>, +c: Char) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case x <> rest:
      Bool.and(nosep(x, c), all_nosep(rest, c))

# A string without `c`, then `c`: the string, then the rest split.
def split_sep(s: String, -r: String, +c: Char, +h: {nosep(s, c) == True{} : Bool}) -> {String.split(s ++ SCon{c, r}, c) == s <> String.split(r, c) : List<&2, String>}:
  match s:
    case SNil{}:
      %Equal.sym(Bool, Char.is_eq(c, c), True{}, char_refl(c)) : {String.split.fin(c, String.split(r, c), _) == SNil{} <> String.split(r, c) : List<&2, String>}
      {==}
    case SCon{+x, +t}:
      Equal.trans(List<&2, String>, String.split.fin(x, String.split(t ++ SCon{c, r}, c), Char.is_eq(x, c)), String.split.fin(x, String.split(t ++ SCon{c, r}, c), False{}), SCon{x, t} <> String.split(r, c),
        Equal.cong(Bool, List<&2, String>, b => String.split.fin(x, String.split(t ++ SCon{c, r}, c), b), Char.is_eq(x, c), False{}, AL.not_of_true(Char.is_eq(x, c), Comp.and_left(Bool.not(Char.is_eq(x, c)), nosep(t, c), h))),
        Equal.cong(List<&2, String>, List<&2, String>, l => String.split.push(x, l), String.split(t ++ SCon{c, r}, c), t <> String.split(r, c), split_sep(t, r, c, Comp.and_right(Bool.not(Char.is_eq(x, c)), nosep(t, c), h))))

# A string without `c` is one piece.
def split_whole(s: String, +c: Char, +h: {nosep(s, c) == True{} : Bool}) -> {String.split(s, c) == [s] : List<&2, String>}:
  match s:
    case SNil{}:
      {==}
    case SCon{+x, +t}:
      Equal.trans(List<&2, String>, String.split.fin(x, String.split(t, c), Char.is_eq(x, c)), String.split.fin(x, String.split(t, c), False{}), [SCon{x, t}],
        Equal.cong(Bool, List<&2, String>, b => String.split.fin(x, String.split(t, c), b), Char.is_eq(x, c), False{}, AL.not_of_true(Char.is_eq(x, c), Comp.and_left(Bool.not(Char.is_eq(x, c)), nosep(t, c), h))),
        Equal.cong(List<&2, String>, List<&2, String>, l => String.split.push(x, l), String.split(t, c), [t], split_whole(t, c, Comp.and_right(Bool.not(Char.is_eq(x, c)), nosep(t, c), h))))

def app_nil(s: String) -> {s ++ SNil{} == s : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+x, t}:
      Equal.cong(String, String, r => SCon{x, r}, t ++ SNil{}, t, app_nil(t))

# A word, then each argument after a NUL, split at NUL: the word and each
# argument.
def split_args(args: List<&2, String>, +w: String, +hw: {nosep(w, '\u{0}') == True{} : Bool}, +ha: {all_nosep(args, '\u{0}') == True{} : Bool}) -> {String.split(w ++ Store.run.args(args), '\u{0}') == w <> args : List<&2, String>}:
  match args:
    case Nil{}:
      %Equal.sym(String, w ++ SNil{}, w, app_nil(w)) : {String.split(_, '\u{0}') == [w] : List<&2, String>}
      split_whole(w, '\u{0}', hw)
    case +a <> +rest:
      Equal.trans(List<&2, String>, String.split(w ++ SCon{'\u{0}', a ++ Store.run.args(rest)}, '\u{0}'), w <> String.split(a ++ Store.run.args(rest), '\u{0}'), w <> a <> rest,
        split_sep(w, a ++ Store.run.args(rest), '\u{0}', hw),
        Equal.cong(List<&2, String>, List<&2, String>, l => w <> l, String.split(a ++ Store.run.args(rest), '\u{0}'), a <> rest, split_args(rest, a, Comp.and_left(nosep(a, '\u{0}'), all_nosep(rest, '\u{0}'), ha), Comp.and_right(nosep(a, '\u{0}'), all_nosep(rest, '\u{0}'), ha))))

# `run_asks_for_what_it_names`: the directory, the program and each
# argument, none of which holds a NUL, read back by splitting at NUL.
def run_asks(+dir: String, +program: String, +args: List<&2, String>, +h: {all_nosep(dir <> program <> args, '\u{0}') == True{} : Bool}) -> {String.split(Store.run.query(dir, program, args), '\u{0}') == dir <> program <> args : List<&2, String>}:
  +hd = Comp.and_left(nosep(dir, '\u{0}'), all_nosep(program <> args, '\u{0}'), h)
  +hr = Comp.and_right(nosep(dir, '\u{0}'), all_nosep(program <> args, '\u{0}'), h)
  Equal.trans(List<&2, String>, String.split(dir ++ SCon{'\u{0}', program ++ Store.run.args(args)}, '\u{0}'), dir <> String.split(program ++ Store.run.args(args), '\u{0}'), dir <> program <> args,
    split_sep(dir, program ++ Store.run.args(args), '\u{0}', hd),
    Equal.cong(List<&2, String>, List<&2, String>, l => dir <> l, String.split(program ++ Store.run.args(args), '\u{0}'), program <> args, split_args(args, program, Comp.and_left(nosep(program, '\u{0}'), all_nosep(args, '\u{0}'), hr), Comp.and_right(nosep(program, '\u{0}'), all_nosep(args, '\u{0}'), hr))))
