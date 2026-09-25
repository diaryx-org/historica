# What the walk yields and what a read opens. The walk yields each path
# once, in path order. The name a directory's listing spells a path with,
# read back from the lines the host writes for it, is the last entry name
# whose normal form is the path, and the path itself where there is none.
import Base
import ./folder.bend as F
import ./nfc.bend as N
import ./text.bend as T
import ./nfc_lemmas.bend as NfcL
import ./finding_lemmas.bend as FindL
import ./listed_lemmas.bend as ListedL
import ./sort_lemmas.bend as SortL

# The names a listing's entries have, in order: every entry's but a name
# that is not UTF-8, which nothing can spell a path with, and never a
# link's target.
def names(es: List<&2, NfcL.Listed>) -> List<&2, String>:
  match es:
    case Nil{}:
      Nil{}
    case NfcL.Listed.Dir{n} <> rest:
      n <> names(rest)
    case NfcL.Listed.File{r, z, n} <> rest:
      n <> names(rest)
    case NfcL.Listed.Link{n, t} <> rest:
      n <> names(rest)
    case NfcL.Listed.Unreadable{n} <> rest:
      n <> names(rest)
    case NfcL.Listed.Other{n} <> rest:
      n <> names(rest)
    case NfcL.Listed.Unspelled{x} <> rest:
      names(rest)

# The last of `ns` whose normal form is `want`, if any is.
def last_spelling(ns: List<&2, String>, +want: String) -> Maybe<&2, String>:
  match ns:
    case Nil{}:
      None{}
    case +n <> rest:
      Maybe.or(&2, String, last_spelling(rest, want), Bool.pick(Maybe<&2, String>, String.eq(N.nfc(n), want), Some{n}, None{}))

# The host writes a file's runs and size with no space in them.
def sized(es: List<&2, NfcL.Listed>) -> Bool:
  match es:
    case Nil{}:
      True{}
    case NfcL.Listed.File{r, z, n} <> rest:
      Bool.and(Bool.and(Bool.not(T.has_char(r, ' ')), Bool.not(T.has_char(z, ' '))), sized(rest))
    case e <> rest:
      sized(rest)

# A name taken over what was taken before it, or what was, is the later
# match, or the earlier.
def or_pick(l: Maybe<&2, String>, b: Bool, +n: String, +got: Maybe<&2, String>) -> {Maybe.or(&2, String, l, Bool.pick(Maybe<&2, String>, b, Some{n}, got)) == Maybe.or(&2, String, Maybe.or(&2, String, l, Bool.pick(Maybe<&2, String>, b, Some{n}, None{})), got) : Maybe<&2, String>}:
  match l b:
    case Some{x} _:
      {==}
    case None{} True{}:
      {==}
    case None{} False{}:
      {==}

# A file's line names the file: its name is what follows its runs and its
# size.
def file_name(+r: String, +z: String, +n: String, hr: {T.has_char(r, ' ') == False{} : Bool}, hz: {T.has_char(z, ' ') == False{} : Bool}) -> {F.entry.name("f " ++ r ++ " " ++ z ++ " " ++ n) == n : String}:
  +x : String = r ++ " " ++ z ++ " " ++ n
  %Equal.sym(Bool, String.starts_with(x, SNil{}), True{}, NfcL.sw_empty(x)) : {Bool.pick(String, _, F.entry.file(T.split_once(String.drop(x, 0n))), String.drop(x, 0n)) == n : String}
  %Equal.sym(String, String.drop(x, 0n), x, NfcL.drop_zero(x)) : {F.entry.file(T.split_once(_)) == n : String}
  %Equal.sym(Maybe<&2, T.Split>, T.split_once(r ++ " " ++ z ++ " " ++ n), Some{T.Split{r, z ++ " " ++ n}}, FindL.split_once_at(r, z ++ " " ++ n, hr)) : {F.entry.file(_) == n : String}
  %Equal.sym(Maybe<&2, T.Split>, T.split_once(z ++ " " ++ n), Some{T.Split{z, n}}, FindL.split_once_at(z, n, hz)) : {F.entry.sized(_) == n : String}
  {==}

# Reading the lines back from any name taken so far: the last entry name
# the lines spell `want` with, or what was taken before.
def read_back(es: List<&2, NfcL.Listed>, +want: String, +got: Maybe<&2, String>, +h: {sized(es) == True{} : Bool}) -> {F.spelling.go(NfcL.listed.lines(es), want, got, False{}) == Maybe.or(&2, String, last_spelling(names(es), want), got) : Maybe<&2, String>}:
  match es:
    case Nil{}:
      {==}
    case NfcL.Listed.Dir{+n} <> +rest:
      %Equal.sym(String, String.drop(n, 0n), n, NfcL.drop_zero(n)) : {F.spelling.go(NfcL.listed.lines(rest), want, Bool.pick(Maybe<&2, String>, String.eq(N.nfc(_), want), Some{_}, got), False{}) == Maybe.or(&2, String, last_spelling(names(NfcL.Listed.Dir{n} <> rest), want), got) : Maybe<&2, String>}
      Equal.trans(Maybe<&2, String>, F.spelling.go(NfcL.listed.lines(rest), want, Bool.pick(Maybe<&2, String>, String.eq(N.nfc(n), want), Some{n}, got), False{}), Maybe.or(&2, String, last_spelling(names(rest), want), Bool.pick(Maybe<&2, String>, String.eq(N.nfc(n), want), Some{n}, got)), Maybe.or(&2, String, last_spelling(names(NfcL.Listed.Dir{n} <> rest), want), got),
        read_back(rest, want, Bool.pick(Maybe<&2, String>, String.eq(N.nfc(n), want), Some{n}, got), h),
        or_pick(last_spelling(names(rest), want), String.eq(N.nfc(n), want), n, got))
    case NfcL.Listed.File{+r, +z, +n} <> +rest:
      +hf = NfcL.and_l(Bool.and(Bool.not(T.has_char(r, ' ')), Bool.not(T.has_char(z, ' '))), sized(rest), h)
      +hr = FindL.not_has(r, ' ', NfcL.and_l(Bool.not(T.has_char(r, ' ')), Bool.not(T.has_char(z, ' ')), hf))
      +hz = FindL.not_has(z, ' ', NfcL.and_r(Bool.not(T.has_char(r, ' ')), Bool.not(T.has_char(z, ' ')), hf))
      %Equal.sym(String, F.entry.name("f " ++ r ++ " " ++ z ++ " " ++ n), n, file_name(r, z, n, hr, hz)) : {F.spelling.go(NfcL.listed.lines(rest), want, Bool.pick(Maybe<&2, String>, Bool.and(True{}, String.eq(N.nfc(_), want)), Some{_}, got), False{}) == Maybe.or(&2, String, last_spelling(names(NfcL.Listed.File{r, z, n} <> rest), want), got) : Maybe<&2, String>}
      Equal.trans(Maybe<&2, String>, F.spelling.go(NfcL.listed.lines(rest), want, Bool.pick(Maybe<&2, String>, String.eq(N.nfc(n), want), Some{n}, got), False{}), Maybe.or(&2, String, last_spelling(names(rest), want), Bool.pick(Maybe<&2, String>, String.eq(N.nfc(n), want), Some{n}, got)), Maybe.or(&2, String, last_spelling(names(NfcL.Listed.File{r, z, n} <> rest), want), got),
        read_back(rest, want, Bool.pick(Maybe<&2, String>, String.eq(N.nfc(n), want), Some{n}, got), NfcL.and_r(Bool.and(Bool.not(T.has_char(r, ' ')), Bool.not(T.has_char(z, ' '))), sized(rest), h)),
        or_pick(last_spelling(names(rest), want), String.eq(N.nfc(n), want), n, got))
    case NfcL.Listed.Link{+n, t} <> +rest:
      %Equal.sym(Bool, String.starts_with(n, SNil{}), True{}, NfcL.sw_empty(n)) : {F.spelling.go(t <> NfcL.listed.lines(rest), want, Bool.pick(Maybe<&2, String>, String.eq(N.nfc(String.drop(n, 0n)), want), Some{String.drop(n, 0n)}, got), _) == Maybe.or(&2, String, last_spelling(names(NfcL.Listed.Link{n, t} <> rest), want), got) : Maybe<&2, String>}
      %Equal.sym(String, String.drop(n, 0n), n, NfcL.drop_zero(n)) : {F.spelling.go(NfcL.listed.lines(rest), want, Bool.pick(Maybe<&2, String>, String.eq(N.nfc(_), want), Some{_}, got), False{}) == Maybe.or(&2, String, last_spelling(names(NfcL.Listed.Link{n, t} <> rest), want), got) : Maybe<&2, String>}
      Equal.trans(Maybe<&2, String>, F.spelling.go(NfcL.listed.lines(rest), want, Bool.pick(Maybe<&2, String>, String.eq(N.nfc(n), want), Some{n}, got), False{}), Maybe.or(&2, String, last_spelling(names(rest), want), Bool.pick(Maybe<&2, String>, String.eq(N.nfc(n), want), Some{n}, got)), Maybe.or(&2, String, last_spelling(names(NfcL.Listed.Link{n, t} <> rest), want), got),
        read_back(rest, want, Bool.pick(Maybe<&2, String>, String.eq(N.nfc(n), want), Some{n}, got), h),
        or_pick(last_spelling(names(rest), want), String.eq(N.nfc(n), want), n, got))
    case NfcL.Listed.Unreadable{+n} <> +rest:
      %Equal.sym(String, String.drop(n, 0n), n, NfcL.drop_zero(n)) : {F.spelling.go(NfcL.listed.lines(rest), want, Bool.pick(Maybe<&2, String>, String.eq(N.nfc(_), want), Some{_}, got), False{}) == Maybe.or(&2, String, last_spelling(names(NfcL.Listed.Unreadable{n} <> rest), want), got) : Maybe<&2, String>}
      Equal.trans(Maybe<&2, String>, F.spelling.go(NfcL.listed.lines(rest), want, Bool.pick(Maybe<&2, String>, String.eq(N.nfc(n), want), Some{n}, got), False{}), Maybe.or(&2, String, last_spelling(names(rest), want), Bool.pick(Maybe<&2, String>, String.eq(N.nfc(n), want), Some{n}, got)), Maybe.or(&2, String, last_spelling(names(NfcL.Listed.Unreadable{n} <> rest), want), got),
        read_back(rest, want, Bool.pick(Maybe<&2, String>, String.eq(N.nfc(n), want), Some{n}, got), h),
        or_pick(last_spelling(names(rest), want), String.eq(N.nfc(n), want), n, got))
    case NfcL.Listed.Other{+n} <> +rest:
      %Equal.sym(String, String.drop(n, 0n), n, NfcL.drop_zero(n)) : {F.spelling.go(NfcL.listed.lines(rest), want, Bool.pick(Maybe<&2, String>, String.eq(N.nfc(_), want), Some{_}, got), False{}) == Maybe.or(&2, String, last_spelling(names(NfcL.Listed.Other{n} <> rest), want), got) : Maybe<&2, String>}
      Equal.trans(Maybe<&2, String>, F.spelling.go(NfcL.listed.lines(rest), want, Bool.pick(Maybe<&2, String>, String.eq(N.nfc(n), want), Some{n}, got), False{}), Maybe.or(&2, String, last_spelling(names(rest), want), Bool.pick(Maybe<&2, String>, String.eq(N.nfc(n), want), Some{n}, got)), Maybe.or(&2, String, last_spelling(names(NfcL.Listed.Other{n} <> rest), want), got),
        read_back(rest, want, Bool.pick(Maybe<&2, String>, String.eq(N.nfc(n), want), Some{n}, got), h),
        or_pick(last_spelling(names(rest), want), String.eq(N.nfc(n), want), n, got))
    case NfcL.Listed.Unspelled{+x} <> +rest:
      %Equal.sym(Bool, String.starts_with(x, SNil{}), True{}, NfcL.sw_empty(x)) : {F.spelling.go(NfcL.listed.lines(rest), want, Bool.pick(Maybe<&2, String>, Bool.and(Bool.not(_), String.eq(N.nfc(String.drop(x, 0n)), want)), Some{String.drop(x, 0n)}, got), False{}) == Maybe.or(&2, String, last_spelling(names(rest), want), got) : Maybe<&2, String>}
      read_back(rest, want, got, h)

def or_none(m: Maybe<&2, String>, +want: String) -> {Maybe.default(&2, String, Maybe.or(&2, String, m, None{}), want) == Maybe.default(&2, String, m, want) : String}:
  match m:
    case None{}:
      {==}
    case Some{x}:
      {==}

# The name a read opens: the last entry name whose normal form is the
# path, and the path itself where the listing has none.
def spelled_there(+es: List<&2, NfcL.Listed>, +want: String, +h: {sized(es) == True{} : Bool}) -> {F.spelling(NfcL.listed.lines(es), want) == Maybe.default(&2, String, last_spelling(names(es), want), want) : String}:
  %Equal.sym(Maybe<&2, String>, F.spelling.go(NfcL.listed.lines(es), want, None{}, False{}), Maybe.or(&2, String, last_spelling(names(es), want), None{}), read_back(es, want, None{}, h)) : {Maybe.default(&2, String, _, want) == Maybe.default(&2, String, last_spelling(names(es), want), want) : String}
  or_none(last_spelling(names(es), want), want)

# The walk
# --------

# Strictly rising: each file's path at or after the one before it and not
# the same, so no path twice and every path in order.
def rising.go(fs: List<&2, F.Found>, +last: String) -> Bool:
  match fs:
    case Nil{}:
      True{}
    case +f <> rest:
      Bool.and(Bool.and(String.is_le(last, F.found.path(f)), Bool.not(String.eq(F.found.path(f), last))), rising.go(rest, F.found.path(f)))

def rising(fs: List<&2, F.Found>) -> Bool:
  match fs:
    case Nil{}:
      True{}
    case +f <> rest:
      rising.go(rest, F.found.path(f))

# In order, and no two in a row at one path, is strictly rising.
def rising_of(xs: List<&2, F.Found>, +k: String, +hs: {SortL.sorted.from(~F.Found, ~(f => F.found.path(f)), xs, k) == True{} : Bool}, +ha: {F.apart.go(xs, k) == True{} : Bool}) -> {rising.go(xs, k) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +f <> +rest:
      +p = F.found.path(f)
      NfcL.and_i(Bool.and(String.is_le(k, p), Bool.not(String.eq(p, k))), rising.go(rest, p),
        NfcL.and_i(String.is_le(k, p), Bool.not(String.eq(p, k)),
          NfcL.and_l(String.is_le(k, p), SortL.sorted.from(~F.Found, ~(f => F.found.path(f)), rest, p), hs),
          NfcL.and_l(Bool.not(String.eq(p, k)), F.apart.go(rest, p), ha)),
        rising_of(rest, p, NfcL.and_r(String.is_le(k, p), SortL.sorted.from(~F.Found, ~(f => F.found.path(f)), rest, p), hs), NfcL.and_r(Bool.not(String.eq(p, k)), F.apart.go(rest, p), ha)))

def rising_top(ys: List<&2, F.Found>, +hs: {SortL.sorted(~F.Found, ~(f => F.found.path(f)), ys) == True{} : Bool}, +ha: {F.apart(ys) == True{} : Bool}) -> {rising(ys) == True{} : Bool}:
  match ys:
    case Nil{}:
      {==}
    case +f <> +rest:
      rising_of(rest, F.found.path(f), NfcL.and_r(String.is_le(SNil{}, F.found.path(f)), SortL.sorted.from(~F.Found, ~(f => F.found.path(f)), rest, F.found.path(f)), hs), ha)

# What the walk yields rises strictly by path: it is sorted, and keeping
# one file for a path leaves no two in a row at it.
def walk_rising(+fs: List<&2, F.Found>, +rs: List<&2, T.Split>) -> {rising(F.walked.found(F.walk.finish(F.Walked{fs, rs}))) == True{} : Bool}:
  rising_top(F.walked.found(F.walk.finish(F.Walked{fs, rs})), ListedL.finish_sorted(fs, rs), NfcL.walk_apart(List.sort(~F.Found, ~(a => b => String.is_le(F.found.path(a), F.found.path(b))), fs)))
