# What opening a store reads of a revision it accepts: the reading decision
# 0061 keeps a revision in the graph by when the whole reading refuses it.
# A document of a first line, `key value` header lines, a blank line and a
# message reads back as those headers and that message.
import Base
import ./revision.bend as Rev
import ./text.bend as T
import ./bookmark_lemmas.bend as BmL
import ./identity_lemmas.bend as IdentityL
import ./spelling_lemmas.bend as Spell
import ./composition_lemmas.bend as Comp
import ./anchor_lemmas.bend as AL

# The document
# ------------

# A header line: the key, a space, and the value.
def header.line(h: T.Split) -> String:
  match h:
    case T.Split{+k, +v}:
      k ++ SCon{' ', v}

def header.lines(hs: List<&2, T.Split>) -> List<&2, String>:
  match hs:
    case Nil{}:
      Nil{}
    case +h <> rest:
      header.line(h) <> header.lines(rest)

# A document as the opening reading takes it: a first line, a line for
# each header, a blank line, and the message.
def doc(+first: String, +hs: List<&2, T.Split>, +m: String) -> String:
  IdentityL.text(first <> List.append(&2, String, header.lines(hs), [SNil{}])) ++ m

# A string with no newline in it.
def one_line(+s: String) -> Bool:
  BmL.nonl(s)

# Headers a document can hold as lines: no key holds a space or a newline,
# and no value a newline.
def plain(hs: List<&2, T.Split>) -> Bool:
  match hs:
    case Nil{}:
      True{}
    case T.Split{+k, +v} <> rest:
      Bool.and(Bool.not(T.has_char(k, ' ')), Bool.and(BmL.nonl(k), Bool.and(BmL.nonl(v), plain(rest))))

# The value of the first header under a key.
def first(hs: List<&2, T.Split>, +key: String) -> Maybe<&2, String>:
  match hs:
    case Nil{}:
      None{}
    case T.Split{+k, +v} <> rest:
      Bool.pick(Maybe<&2, String>, String.eq(k, key), Some{v}, first(rest, key))

# The values of every header under a key, in order.
def every(hs: List<&2, T.Split>, +key: String) -> List<&2, String>:
  match hs:
    case Nil{}:
      Nil{}
    case T.Split{+k, +v} <> rest:
      +more = every(rest, key)
      Bool.pick(List<&2, String>, String.eq(k, key), v <> more, more)

# The revision those headers and that message state: its change, author
# and time the first `change`, `author` and `when` say, its parents and
# what it supersedes every `parent` and `supersedes` in order, and no
# facts.
def stated(+hs: List<&2, T.Split>, +m: String) -> Rev.Rev:
  Rev.Rev{Maybe.default(&2, String, first(hs, "change"), SNil{}), every(hs, "parent"), every(hs, "supersedes"),
    Maybe.default(&2, String, first(hs, "author"), SNil{}), Maybe.default(&2, String, first(hs, "when"), SNil{}),
    first(hs, "revised-by"), first(hs, "revised"), Nil{}, m}

# From the text to its lines
# --------------------------

def marked(ls: List<&2, String>) -> List<&2, T.Line>:
  match ls:
    case Nil{}:
      Nil{}
    case +l <> rest:
      T.Line{l, True{}} <> marked(rest)

def all_nonl(ls: List<&2, String>) -> Bool:
  match ls:
    case Nil{}:
      True{}
    case +l <> rest:
      Bool.and(BmL.nonl(l), all_nonl(rest))

def str_assoc(a: String, -b: String, -c: String) -> {(a ++ b) ++ c == a ++ (b ++ c) : String}:
  match a:
    case SNil{}:
      {==}
    case SCon{+h, t}:
      Equal.cong(String, String, x => SCon{h, x}, (t ++ b) ++ c, t ++ (b ++ c), str_assoc(t, b, c))

# Lines with no newline in them, each ended by one, and then more: those
# lines, then the pieces of the rest.
def split_text(ls: List<&2, String>, +m: String, +h: {all_nonl(ls) == True{} : Bool}) -> {String.split(IdentityL.text(ls) ++ m, '\n') == List.append(&2, String, ls, String.split(m, '\n')) : List<&2, String>}:
  match ls:
    case Nil{}:
      {==}
    case +l <> rest:
      %Equal.sym(String, (l ++ SCon{'\n', IdentityL.text(rest)}) ++ m, l ++ SCon{'\n', IdentityL.text(rest) ++ m}, str_assoc(l, SCon{'\n', IdentityL.text(rest)}, m)) : {String.split(_, '\n') == l <> List.append(&2, String, rest, String.split(m, '\n')) : List<&2, String>}
      %Equal.sym(List<&2, String>, String.split(l ++ SCon{'\n', IdentityL.text(rest) ++ m}, '\n'), l <> String.split(IdentityL.text(rest) ++ m, '\n'), BmL.split_nl(l, IdentityL.text(rest) ++ m, Comp.and_left(BmL.nonl(l), all_nonl(rest), h))) : {_ == l <> List.append(&2, String, rest, String.split(m, '\n')) : List<&2, String>}
      Equal.cong(List<&2, String>, List<&2, String>, x => l <> x, String.split(IdentityL.text(rest) ++ m, '\n'), List.append(&2, String, rest, String.split(m, '\n')), split_text(rest, m, Comp.and_right(BmL.nonl(l), all_nonl(rest), h)))

def go_nil(+l: String, parts: List<&2, String>, ne: {Spell.nonempty(String, parts) == True{} : Bool}) -> {T.lines.go(l <> parts) == T.Line{l, True{}} <> T.lines.go(parts) : List<&2, T.Line>}:
  match parts:
    case Nil{}:
      Empty.absurd({T.lines.go([l]) == [T.Line{l, True{}}] : List<&2, T.Line>}, Comp.false_true(ne))
    case p <> ps:
      {==}

def go_app_cons(rest: List<&2, String>, +l: String, +parts: List<&2, String>, +ne: {Spell.nonempty(String, parts) == True{} : Bool}, ih: {T.lines.go(List.append(&2, String, rest, parts)) == List.append(&2, T.Line, marked(rest), T.lines.go(parts)) : List<&2, T.Line>}) -> {T.lines.go(l <> List.append(&2, String, rest, parts)) == T.Line{l, True{}} <> List.append(&2, T.Line, marked(rest), T.lines.go(parts)) : List<&2, T.Line>}:
  match rest:
    case Nil{}:
      go_nil(l, parts, ne)
    case +r <> rs:
      Equal.cong(List<&2, T.Line>, List<&2, T.Line>, x => T.Line{l, True{}} <> x, T.lines.go(r <> List.append(&2, String, rs, parts)), List.append(&2, T.Line, marked(r <> rs), T.lines.go(parts)), ih)

def go_app(ls: List<&2, String>, +parts: List<&2, String>, +ne: {Spell.nonempty(String, parts) == True{} : Bool}) -> {T.lines.go(List.append(&2, String, ls, parts)) == List.append(&2, T.Line, marked(ls), T.lines.go(parts)) : List<&2, T.Line>}:
  match ls:
    case Nil{}:
      {==}
    case +l <> +rest:
      go_app_cons(rest, l, parts, ne, go_app(rest, parts, ne))

# The lines of a text of lines, then more, are those lines, each ended by
# a newline, then the lines of the rest.
def lines_text(+ls: List<&2, String>, +m: String, +h: {all_nonl(ls) == True{} : Bool}) -> {T.lines(IdentityL.text(ls) ++ m) == List.append(&2, T.Line, marked(ls), T.lines(m)) : List<&2, T.Line>}:
  %Equal.sym(List<&2, String>, String.split(IdentityL.text(ls) ++ m, '\n'), List.append(&2, String, ls, String.split(m, '\n')), split_text(ls, m, h)) : {T.lines.go(_) == List.append(&2, T.Line, marked(ls), T.lines(m)) : List<&2, T.Line>}
  go_app(ls, String.split(m, '\n'), Spell.split_nonempty(m, '\n'))

# The headers and the message read
# --------------------------------

def headers(hs: List<&2, T.Split>) -> List<&2, Rev.Header>:
  match hs:
    case Nil{}:
      Nil{}
    case T.Split{+k, +v} <> rest:
      Rev.Header{k, v} <> headers(rest)

def plain_key(+k: String, +v: String, -rest: List<&2, T.Split>, h: {plain(T.Split{k, v} <> rest) == True{} : Bool}) -> {T.has_char(k, ' ') == False{} : Bool}:
  AL.not_of_true(T.has_char(k, ' '), Comp.and_left(Bool.not(T.has_char(k, ' ')), Bool.and(BmL.nonl(k), Bool.and(BmL.nonl(v), plain(rest))), h))

def plain_rest(+k: String, +v: String, -rest: List<&2, T.Split>, h: {plain(T.Split{k, v} <> rest) == True{} : Bool}) -> {plain(rest) == True{} : Bool}:
  Comp.and_right(BmL.nonl(v), plain(rest), Comp.and_right(BmL.nonl(k), Bool.and(BmL.nonl(v), plain(rest)), Comp.and_right(Bool.not(T.has_char(k, ' ')), Bool.and(BmL.nonl(k), Bool.and(BmL.nonl(v), plain(rest))), h)))

# Every header line is read back as its key and value, and the blank line
# ends them.
def headers_read(hs: List<&2, T.Split>, +r: List<&2, T.Line>, +h: {plain(hs) == True{} : Bool}) -> {Rev.opening.headers(List.append(&2, T.Line, marked(List.append(&2, String, header.lines(hs), [SNil{}])), r)) == headers(hs) : List<&2, Rev.Header>}:
  match hs:
    case Nil{}:
      {==}
    case T.Split{+k, +v} <> +rest:
      +X = List.append(&2, T.Line, marked(List.append(&2, String, header.lines(rest), [SNil{}])), r)
      %Equal.sym(Bool, String.is_empty(k ++ SCon{' ', v}), False{}, IdentityL.filled(k, ' ', v)) : {Bool.pick(List<&2, Rev.Header>, _, Nil{}, List.append(&2, Rev.Header, Rev.opening.pair(T.split_once(k ++ SCon{' ', v})), Rev.opening.headers(X))) == Rev.Header{k, v} <> headers(rest) : List<&2, Rev.Header>}
      %Equal.sym(Maybe<&2, T.Split>, T.split_once(k ++ SCon{' ', v}), Some{T.Split{k, v}}, IdentityL.split_kv(k, v, plain_key(k, v, rest, h))) : {List.append(&2, Rev.Header, Rev.opening.pair(_), Rev.opening.headers(X)) == Rev.Header{k, v} <> headers(rest) : List<&2, Rev.Header>}
      Equal.cong(List<&2, Rev.Header>, List<&2, Rev.Header>, x => Rev.Header{k, v} <> x, Rev.opening.headers(X), headers(rest), headers_read(rest, r, plain_rest(k, v, rest, h)))

def unlines_same(ls: List<&2, T.Line>) -> {Rev.unlines(ls) == Spell.unlines(ls) : String}:
  match ls:
    case Nil{}:
      {==}
    case T.Line{+t, +n} <> rest:
      Equal.cong(String, String, y => t ++ (Bool.pick(String, n, "\n", SNil{}) ++ y), Rev.unlines(rest), Spell.unlines(rest), unlines_same(rest))

# The message is everything after the blank line, as written.
def message_read(hs: List<&2, T.Split>, +m: String) -> {Rev.opening.message(List.append(&2, T.Line, marked(List.append(&2, String, header.lines(hs), [SNil{}])), T.lines(m))) == m : String}:
  match hs:
    case Nil{}:
      Equal.trans(String, Rev.unlines(T.lines(m)), Spell.unlines(T.lines(m)), m, unlines_same(T.lines(m)), Spell.unlines_lines(m))
    case T.Split{+k, +v} <> +rest:
      %Equal.sym(Bool, String.is_empty(k ++ SCon{' ', v}), False{}, IdentityL.filled(k, ' ', v)) : {Bool.pick(String, _, Rev.unlines(List.append(&2, T.Line, marked(List.append(&2, String, header.lines(rest), [SNil{}])), T.lines(m))), Rev.opening.message(List.append(&2, T.Line, marked(List.append(&2, String, header.lines(rest), [SNil{}])), T.lines(m)))) == m : String}
      message_read(rest, m)

def value_first(hs: List<&2, T.Split>, +key: String) -> {Rev.value_of(headers(hs), key) == first(hs, key) : Maybe<&2, String>}:
  match hs:
    case Nil{}:
      {==}
    case T.Split{+k, +v} <> rest:
      Equal.cong(Maybe<&2, String>, Maybe<&2, String>, x => Bool.pick(Maybe<&2, String>, String.eq(k, key), Some{v}, x), Rev.value_of(headers(rest), key), first(rest, key), value_first(rest, key))

def keep_pick(b: Bool, -v: String, -xs: List<&2, String>) -> {Rev.keep(b, v, xs) == Bool.pick(List<&2, String>, b, v <> xs, xs) : List<&2, String>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def values_every(hs: List<&2, T.Split>, +key: String) -> {Rev.values_of(headers(hs), key) == every(hs, key) : List<&2, String>}:
  match hs:
    case Nil{}:
      {==}
    case T.Split{+k, +v} <> rest:
      %Equal.sym(List<&2, String>, Rev.values_of(headers(rest), key), every(rest, key), values_every(rest, key)) : {Rev.keep(String.eq(k, key), v, _) == Bool.pick(List<&2, String>, String.eq(k, key), v <> every(rest, key), every(rest, key)) : List<&2, String>}
      keep_pick(String.eq(k, key), v, every(rest, key))

# The revision `opening.rev` assembles from a header list and a message.
def assembled(+hl: List<&2, Rev.Header>, +m: String) -> Rev.Rev:
  Rev.Rev{Maybe.default(&2, String, Rev.value_of(hl, "change"), SNil{}), Rev.values_of(hl, "parent"), Rev.values_of(hl, "supersedes"),
    Maybe.default(&2, String, Rev.value_of(hl, "author"), SNil{}), Maybe.default(&2, String, Rev.value_of(hl, "when"), SNil{}),
    Rev.value_of(hl, "revised-by"), Rev.value_of(hl, "revised"), Nil{}, m}

def assembled_stated(+hs: List<&2, T.Split>, +m: String) -> {assembled(headers(hs), m) == stated(hs, m) : Rev.Rev}:
  %Equal.sym(Maybe<&2, String>, Rev.value_of(headers(hs), "change"), first(hs, "change"), value_first(hs, "change")) : {Rev.Rev{Maybe.default(&2, String, _, SNil{}), Rev.values_of(headers(hs), "parent"), Rev.values_of(headers(hs), "supersedes"), Maybe.default(&2, String, Rev.value_of(headers(hs), "author"), SNil{}), Maybe.default(&2, String, Rev.value_of(headers(hs), "when"), SNil{}), Rev.value_of(headers(hs), "revised-by"), Rev.value_of(headers(hs), "revised"), Nil{}, m} == stated(hs, m) : Rev.Rev}
  %Equal.sym(List<&2, String>, Rev.values_of(headers(hs), "parent"), every(hs, "parent"), values_every(hs, "parent")) : {Rev.Rev{Maybe.default(&2, String, first(hs, "change"), SNil{}), _, Rev.values_of(headers(hs), "supersedes"), Maybe.default(&2, String, Rev.value_of(headers(hs), "author"), SNil{}), Maybe.default(&2, String, Rev.value_of(headers(hs), "when"), SNil{}), Rev.value_of(headers(hs), "revised-by"), Rev.value_of(headers(hs), "revised"), Nil{}, m} == stated(hs, m) : Rev.Rev}
  %Equal.sym(List<&2, String>, Rev.values_of(headers(hs), "supersedes"), every(hs, "supersedes"), values_every(hs, "supersedes")) : {Rev.Rev{Maybe.default(&2, String, first(hs, "change"), SNil{}), every(hs, "parent"), _, Maybe.default(&2, String, Rev.value_of(headers(hs), "author"), SNil{}), Maybe.default(&2, String, Rev.value_of(headers(hs), "when"), SNil{}), Rev.value_of(headers(hs), "revised-by"), Rev.value_of(headers(hs), "revised"), Nil{}, m} == stated(hs, m) : Rev.Rev}
  %Equal.sym(Maybe<&2, String>, Rev.value_of(headers(hs), "author"), first(hs, "author"), value_first(hs, "author")) : {Rev.Rev{Maybe.default(&2, String, first(hs, "change"), SNil{}), every(hs, "parent"), every(hs, "supersedes"), Maybe.default(&2, String, _, SNil{}), Maybe.default(&2, String, Rev.value_of(headers(hs), "when"), SNil{}), Rev.value_of(headers(hs), "revised-by"), Rev.value_of(headers(hs), "revised"), Nil{}, m} == stated(hs, m) : Rev.Rev}
  %Equal.sym(Maybe<&2, String>, Rev.value_of(headers(hs), "when"), first(hs, "when"), value_first(hs, "when")) : {Rev.Rev{Maybe.default(&2, String, first(hs, "change"), SNil{}), every(hs, "parent"), every(hs, "supersedes"), Maybe.default(&2, String, first(hs, "author"), SNil{}), Maybe.default(&2, String, _, SNil{}), Rev.value_of(headers(hs), "revised-by"), Rev.value_of(headers(hs), "revised"), Nil{}, m} == stated(hs, m) : Rev.Rev}
  %Equal.sym(Maybe<&2, String>, Rev.value_of(headers(hs), "revised-by"), first(hs, "revised-by"), value_first(hs, "revised-by")) : {Rev.Rev{Maybe.default(&2, String, first(hs, "change"), SNil{}), every(hs, "parent"), every(hs, "supersedes"), Maybe.default(&2, String, first(hs, "author"), SNil{}), Maybe.default(&2, String, first(hs, "when"), SNil{}), _, Rev.value_of(headers(hs), "revised"), Nil{}, m} == stated(hs, m) : Rev.Rev}
  %Equal.sym(Maybe<&2, String>, Rev.value_of(headers(hs), "revised"), first(hs, "revised"), value_first(hs, "revised")) : {Rev.Rev{Maybe.default(&2, String, first(hs, "change"), SNil{}), every(hs, "parent"), every(hs, "supersedes"), Maybe.default(&2, String, first(hs, "author"), SNil{}), Maybe.default(&2, String, first(hs, "when"), SNil{}), first(hs, "revised-by"), _, Nil{}, m} == stated(hs, m) : Rev.Rev}
  {==}

def plain_lines(hs: List<&2, T.Split>, +h: {plain(hs) == True{} : Bool}) -> {all_nonl(List.append(&2, String, header.lines(hs), [SNil{}])) == True{} : Bool}:
  match hs:
    case Nil{}:
      {==}
    case T.Split{+k, +v} <> +rest:
      +h1 = Comp.and_right(Bool.not(T.has_char(k, ' ')), Bool.and(BmL.nonl(k), Bool.and(BmL.nonl(v), plain(rest))), h)
      +hk = Comp.and_left(BmL.nonl(k), Bool.and(BmL.nonl(v), plain(rest)), h1)
      +hv = Comp.and_left(BmL.nonl(v), plain(rest), Comp.and_right(BmL.nonl(k), Bool.and(BmL.nonl(v), plain(rest)), h1))
      AL.and_intro(BmL.nonl(k ++ SCon{' ', v}), all_nonl(List.append(&2, String, header.lines(rest), [SNil{}])), BmL.nonl_app(k, SCon{' ', v}, hk, hv), plain_lines(rest, plain_rest(k, v, rest, h)))

# What opening reads of such a document is the revision its headers and
# message state.
def opens_as_stated(+first: String, +hs: List<&2, T.Split>, +m: String, +hf: {one_line(first) == True{} : Bool}, +hp: {plain(hs) == True{} : Bool}) -> {Rev.opening.rev(Rev.opening.tail(T.lines(doc(first, hs, m)))) == stated(hs, m) : Rev.Rev}:
  +ls = List.append(&2, T.Line, marked(List.append(&2, String, header.lines(hs), [SNil{}])), T.lines(m))
  %Equal.sym(List<&2, T.Line>, T.lines(doc(first, hs, m)), List.append(&2, T.Line, marked(first <> List.append(&2, String, header.lines(hs), [SNil{}])), T.lines(m)), lines_text(first <> List.append(&2, String, header.lines(hs), [SNil{}]), m, AL.and_intro(BmL.nonl(first), all_nonl(List.append(&2, String, header.lines(hs), [SNil{}])), hf, plain_lines(hs, hp)))) : {Rev.opening.rev(Rev.opening.tail(_)) == stated(hs, m) : Rev.Rev}
  Equal.trans(Rev.Rev, Rev.opening.rev(ls), assembled(headers(hs), m), stated(hs, m),
    Equal.trans(Rev.Rev, Rev.opening.rev(ls), assembled(Rev.opening.headers(ls), m), assembled(headers(hs), m),
      Equal.cong(String, Rev.Rev, x => assembled(Rev.opening.headers(ls), x), Rev.opening.message(ls), m, message_read(hs, m)),
      Equal.cong(List<&2, Rev.Header>, Rev.Rev, x => assembled(x, m), Rev.opening.headers(ls), headers(hs), headers_read(hs, T.lines(m), hp))),
    assembled_stated(hs, m))

# And where opening accepts it, that is what it reads.
def opened(+first: String, +hs: List<&2, T.Split>, +m: String, +hf: {one_line(first) == True{} : Bool}, +hp: {plain(hs) == True{} : Bool}, +e: {Rev.refusal.opening(doc(first, hs, m)) == None{} : Maybe<&2, String>}) -> {Rev.opening.read(doc(first, hs, m)) == Some{stated(hs, m)} : Maybe<&2, Rev.Rev>}:
  %Equal.sym(Maybe<&2, String>, Rev.refusal.opening(doc(first, hs, m)), None{}, e) : {Bool.pick(Maybe<&2, Rev.Rev>, Maybe.is_some(&2, String, _), None{}, Some{Rev.opening.rev(Rev.opening.tail(T.lines(doc(first, hs, m))))}) == Some{stated(hs, m)} : Maybe<&2, Rev.Rev>}
  Equal.cong(Rev.Rev, Maybe<&2, Rev.Rev>, x => Some{x}, Rev.opening.rev(Rev.opening.tail(T.lines(doc(first, hs, m)))), stated(hs, m), opens_as_stated(first, hs, m, hf, hp))
