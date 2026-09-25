# `fetch` reads back the manifest `offer` writes. `offer` prints the lines
# `Offer.rendered` makes of a copy's heads and files — the header, a `head`
# line for each head, a line for each file — each with a newline after it;
# `fetch`, handed that text by the host as the document at the manifest's
# URL, reads every head and every file back as it was written: the kind,
# the digest, what it forgets, and the path, spaces and all.
import Base
import ./text.bend as T
import ./revision.bend as Rev
import ./offer.bend as Offer
import ./fetch.bend as Fetch
import ./string_lemmas.bend as S
import ./bookmark_lemmas.bend as BmL
import ./composition_lemmas.bend as Comp
import ./anchor_lemmas.bend as AL
import ./spelling_lemmas.bend as SpL
import ./fetching_lemmas.bend as FetchingL
import ./commands.bend as Main

# What the laws say
# -----------------

# What `print_lines` writes of a list of lines: each line, and a newline
# after it.
def printed(ls: List<&2, String>) -> String:
  match ls:
    case Nil{}:
      SNil{}
    case l <> rest:
      l ++ SCon{'\n', printed(rest)}

# What a file forgets, as a line can say it: nothing, or a digest.
def forgets_ok(f: Maybe<&2, String>) -> Bool:
  match f:
    case None{}:
      True{}
    case Some{+g}:
      T.is_digest(g)

# A file `offer` names and a reader of `historica-offer-1` takes: one of the
# six kinds, a digest, what it forgets as a digest or nothing, and a path
# with no newline in it that does not end with a carriage return.
def writable(o: Offer.Offered) -> Bool:
  match o:
    case Offer.Offered{+k, +d, f, +p}:
      Bool.and(Rev.member(["revision", "operation", "payload", "rule", "reserved", "name"], k),
        Bool.and(T.is_digest(d),
          Bool.and(forgets_ok(f),
            Bool.and(BmL.nonl(p), Bool.not(String.ends_with(p, "\r"))))))

# Choices
# -------

def pick_t(-A: Data, c: Bool, -x: A, -y: A, e: {c == True{} : Bool}) -> {Bool.pick(A, c, x, y) == x : A}:
  match c:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({Bool.pick(A, False{}, x, y) == x : A}, S.false_true(e))

# A list reversed twice, the second time onto nothing, is the first
# reversal's accumulator reversed onto the list.
def lrev_go(-A: Data, xs: List<&2, A>, +acc: List<&2, A>) -> {List.reverse.go(&2, A, List.reverse.go(&2, A, xs, acc), Nil{}) == List.reverse.go(&2, A, acc, xs) : List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> t:
      lrev_go(A, t, x <> acc)

def lrev(-A: Data, +xs: List<&2, A>) -> {List.reverse(&2, A, List.reverse.go(&2, A, xs, Nil{})) == xs : List<&2, A>}:
  lrev_go(A, xs, Nil{})

# Characters
# ----------

# A string with no space in it.
def nosp(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{c, t}:
      Bool.and(Bool.not(Char.is_eq(c, ' ')), nosp(t))

# A hex digit is none of the characters that are not one.
def hex_not.at(+c: Char, +q: Char, b: Bool, eb: {Char.is_eq(c, q) == b : Bool}, hq: {T.is_hex(q) == False{} : Bool}, h: {T.is_hex(c) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, S.false_true(Equal.trans(Bool, False{}, T.is_hex(c), True{},
        (%Equal.sym(Char, c, q, BmL.chr_eq(c, q, eb)) : {False{} == T.is_hex(_) : Bool}
          Equal.sym(Bool, T.is_hex(q), False{}, hq)), h)))

def hex_not(+c: Char, +q: Char, hq: {T.is_hex(q) == False{} : Bool}, h: {T.is_hex(c) == True{} : Bool}) -> {Char.is_eq(c, q) == False{} : Bool}:
  hex_not.at(c, q, Char.is_eq(c, q), {==}, hq, h)

def hexes(+d: String, h: {T.is_digest(d) == True{} : Bool}) -> {T.all_chars(~T.is_hex, d) == True{} : Bool}:
  Comp.and_right(Nat.is_eq(String.length(d), 64n), T.all_chars(~T.is_hex, d), h)

def nosp_hex(s: String, +h: {T.all_chars(~T.is_hex, s) == True{} : Bool}) -> {nosp(s) == True{} : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      AL.and_intro(Bool.not(Char.is_eq(c, ' ')), nosp(t),
        AL.not_true(Char.is_eq(c, ' '), hex_not(c, ' ', {==}, Comp.and_left(T.is_hex(c), T.all_chars(~T.is_hex, t), h))),
        nosp_hex(t, Comp.and_right(T.is_hex(c), T.all_chars(~T.is_hex, t), h)))

# Cutting at a space
# ------------------

# A word with no space in it, a space, and the rest: `split_once` cuts at
# that space.
def split_go_sp(s: String, +r: String, +acc: String, +h: {nosp(s) == True{} : Bool}) -> {T.split_once.go(s ++ SCon{' ', r}, acc) == Some{T.Split{String.reverse(String.reverse.go(s, acc)), r}} : Maybe<&2, T.Split>}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %Equal.sym(Bool, Char.is_eq(c, ' '), False{}, AL.not_of_true(Char.is_eq(c, ' '), Comp.and_left(Bool.not(Char.is_eq(c, ' ')), nosp(t), h))) : {Bool.pick(Maybe<&2, T.Split>, _, Some{T.Split{String.reverse(acc), t ++ SCon{' ', r}}}, T.split_once.go(t ++ SCon{' ', r}, SCon{c, acc})) == Some{T.Split{String.reverse(String.reverse.go(t, SCon{c, acc})), r}} : Maybe<&2, T.Split>}
      split_go_sp(t, r, SCon{c, acc}, Comp.and_right(Bool.not(Char.is_eq(c, ' ')), nosp(t), h))

def split_sp(+s: String, +r: String, +h: {nosp(s) == True{} : Bool}) -> {T.split_once(s ++ SCon{' ', r}) == Some{T.Split{s, r}} : Maybe<&2, T.Split>}:
  %Equal.sym(Maybe<&2, T.Split>, T.split_once.fast(s ++ SCon{' ', r}, SNil{}, T.space_first(s ++ SCon{' ', r})), T.split_once.go(s ++ SCon{' ', r}, SNil{}), SpL.split_fast(s ++ SCon{' ', r}, SNil{})) : {_ == Some{T.Split{s, r}} : Maybe<&2, T.Split>}
  %FetchingL.rev_rev(s) : {T.split_once.go(s ++ SCon{' ', r}, SNil{}) == Some{T.Split{_, r}} : Maybe<&2, T.Split>}
  split_go_sp(s, r, SNil{}, h)

# An entry split three times: the kind, the digest, what it forgets, and
# the path, whatever spaces the path holds.
def four_line(+k: String, +d: String, +f: String, +p: String, +hk: {nosp(k) == True{} : Bool}, +hd: {nosp(d) == True{} : Bool}, +hf: {nosp(f) == True{} : Bool}) -> {Fetch.four(k ++ (" " ++ (d ++ (" " ++ (f ++ (" " ++ p)))))) == Some{Fetch.Four{k, d, f, p}} : Maybe<&2, Fetch.Four>}:
  %Equal.sym(Maybe<&2, T.Split>, T.split_once(k ++ SCon{' ', d ++ (" " ++ (f ++ (" " ++ p)))}), Some{T.Split{k, d ++ (" " ++ (f ++ (" " ++ p)))}}, split_sp(k, d ++ (" " ++ (f ++ (" " ++ p))), hk)) : {Fetch.four.a(_) == Some{Fetch.Four{k, d, f, p}} : Maybe<&2, Fetch.Four>}
  %Equal.sym(Maybe<&2, T.Split>, T.split_once(d ++ SCon{' ', f ++ (" " ++ p)}), Some{T.Split{d, f ++ (" " ++ p)}}, split_sp(d, f ++ (" " ++ p), hd)) : {Fetch.four.b(k, _) == Some{Fetch.Four{k, d, f, p}} : Maybe<&2, Fetch.Four>}
  %Equal.sym(Maybe<&2, T.Split>, T.split_once(f ++ SCon{' ', p}), Some{T.Split{f, p}}, split_sp(f, p, hf)) : {Fetch.four.c(k, d, _) == Some{Fetch.Four{k, d, f, p}} : Maybe<&2, Fetch.Four>}
  {==}

# The six kinds
# -------------

def kind_split(-R: Type, +k: String, hk: {Rev.member(["revision", "operation", "payload", "rule", "reserved", "name"], k) == True{} : Bool}, r1: {"revision" == k : String} -> R, r2: {"operation" == k : String} -> R, r3: {"payload" == k : String} -> R, r4: {"rule" == k : String} -> R, r5: {"reserved" == k : String} -> R, r6: {"name" == k : String} -> R) -> R:
  AL.or_cases(R, String.eq("revision", k), Rev.member(["operation", "payload", "rule", "reserved", "name"], k), hk, e => r1(S.eq_true("revision", k, e)),
    e2 => AL.or_cases(R, String.eq("operation", k), Rev.member(["payload", "rule", "reserved", "name"], k), e2, e => r2(S.eq_true("operation", k, e)),
      e3 => AL.or_cases(R, String.eq("payload", k), Rev.member(["rule", "reserved", "name"], k), e3, e => r3(S.eq_true("payload", k, e)),
        e4 => AL.or_cases(R, String.eq("rule", k), Rev.member(["reserved", "name"], k), e4, e => r4(S.eq_true("rule", k, e)),
          e5 => AL.or_cases(R, String.eq("reserved", k), Rev.member(["name"], k), e5, e => r5(S.eq_true("reserved", k, e)),
            e6 => AL.or_cases(R, String.eq("name", k), Rev.member(Nil{}, k), e6, e => r6(S.eq_true("name", k, e)),
              no => Empty.absurd(R, S.false_true(no))))))))

def kind_nosp(+k: String, hk: {Rev.member(["revision", "operation", "payload", "rule", "reserved", "name"], k) == True{} : Bool}) -> {nosp(k) == True{} : Bool}:
  kind_split({nosp(k) == True{} : Bool}, k, hk,
    e => (%e : {nosp(_) == True{} : Bool}
      {==}),
    e => (%e : {nosp(_) == True{} : Bool}
      {==}),
    e => (%e : {nosp(_) == True{} : Bool}
      {==}),
    e => (%e : {nosp(_) == True{} : Bool}
      {==}),
    e => (%e : {nosp(_) == True{} : Bool}
      {==}),
    e => (%e : {nosp(_) == True{} : Bool}
      {==}))

def kind_nonl(+k: String, hk: {Rev.member(["revision", "operation", "payload", "rule", "reserved", "name"], k) == True{} : Bool}) -> {BmL.nonl(k) == True{} : Bool}:
  kind_split({BmL.nonl(k) == True{} : Bool}, k, hk,
    e => (%e : {BmL.nonl(_) == True{} : Bool}
      {==}),
    e => (%e : {BmL.nonl(_) == True{} : Bool}
      {==}),
    e => (%e : {BmL.nonl(_) == True{} : Bool}
      {==}),
    e => (%e : {BmL.nonl(_) == True{} : Bool}
      {==}),
    e => (%e : {BmL.nonl(_) == True{} : Bool}
      {==}),
    e => (%e : {BmL.nonl(_) == True{} : Bool}
      {==}))

# No kind begins `head `, so no entry is read as a head.
def kind_head(+k: String, +x: String, hk: {Rev.member(["revision", "operation", "payload", "rule", "reserved", "name"], k) == True{} : Bool}) -> {T.strip_prefix(k ++ x, "head ") == None{} : Maybe<&2, String>}:
  kind_split({T.strip_prefix(k ++ x, "head ") == None{} : Maybe<&2, String>}, k, hk,
    e => (%e : {T.strip_prefix(_ ++ x, "head ") == None{} : Maybe<&2, String>}
      {==}),
    e => (%e : {T.strip_prefix(_ ++ x, "head ") == None{} : Maybe<&2, String>}
      {==}),
    e => (%e : {T.strip_prefix(_ ++ x, "head ") == None{} : Maybe<&2, String>}
      {==}),
    e => (%e : {T.strip_prefix(_ ++ x, "head ") == None{} : Maybe<&2, String>}
      {==}),
    e => (%e : {T.strip_prefix(_ ++ x, "head ") == None{} : Maybe<&2, String>}
      {==}),
    e => (%e : {T.strip_prefix(_ ++ x, "head ") == None{} : Maybe<&2, String>}
      {==}))

# What a file forgets
# -------------------

def not_dash.at(+g: String, b: Bool, eb: {String.eq(g, "-") == b : Bool}, hg: {T.is_digest(g) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, S.false_true(Equal.trans(Bool, False{}, T.is_digest(g), True{},
        (%Equal.sym(String, g, "-", S.eq_true(g, "-", eb)) : {False{} == T.is_digest(_) : Bool}
          {==}), hg)))

# A digest is not `-`.
def not_dash(+g: String, hg: {T.is_digest(g) == True{} : Bool}) -> {String.eq(g, "-") == False{} : Bool}:
  not_dash.at(g, String.eq(g, "-"), {==}, hg)

def fnosp(f: Maybe<&2, String>, hf: {forgets_ok(f) == True{} : Bool}) -> {nosp(Maybe.default(&2, String, f, "-")) == True{} : Bool}:
  match f:
    case None{}:
      {==}
    case Some{+g}:
      nosp_hex(g, hexes(g, hf))

def fnonl(f: Maybe<&2, String>, hf: {forgets_ok(f) == True{} : Bool}) -> {BmL.nonl(Maybe.default(&2, String, f, "-")) == True{} : Bool}:
  match f:
    case None{}:
      {==}
    case Some{+g}:
      BmL.nonl_hex(g, hexes(g, hf))

def forgets_line(f: Maybe<&2, String>, +hf: {forgets_ok(f) == True{} : Bool}) -> {Bool.or(String.eq(Maybe.default(&2, String, f, "-"), "-"), T.is_digest(Maybe.default(&2, String, f, "-"))) == True{} : Bool}:
  match f:
    case None{}:
      {==}
    case Some{+g}:
      %Equal.sym(Bool, String.eq(g, "-"), False{}, not_dash(g, hf)) : {Bool.or(_, T.is_digest(g)) == True{} : Bool}
      hf

# What a line says a file forgets is what it was written to forget.
def forgets_back(f: Maybe<&2, String>, +hf: {forgets_ok(f) == True{} : Bool}) -> {Fetch.forgets.of(Maybe.default(&2, String, f, "-")) == f : Maybe<&2, String>}:
  match f:
    case None{}:
      {==}
    case Some{+g}:
      %Equal.sym(Bool, String.eq(g, "-"), False{}, not_dash(g, hf)) : {Bool.pick(Maybe<&2, String>, _, None{}, Some{g}) == Some{g} : Maybe<&2, String>}
      {==}

# Reading one line
# ----------------

def strip_nil(s: String) -> {T.strip_prefix(s, SNil{}) == Some{s} : Maybe<&2, String>}:
  match s:
    case SNil{}:
      {==}
    case SCon{c, t}:
      {==}

# A `head` line is read as its head.
def head_read(+d: String, -rest: List<&2, String>, hd: {T.is_digest(d) == True{} : Bool}) -> {Fetch.line.at(("head " ++ d) <> rest, True{}) == Fetch.LRead.Head{d} : Fetch.LRead}:
  %Equal.sym(Maybe<&2, String>, T.strip_prefix(d, SNil{}), Some{d}, strip_nil(d)) : {Fetch.line.head(True{}, _, "head " ++ d) == Fetch.LRead.Head{d} : Fetch.LRead}
  pick_t(Fetch.LRead, T.is_digest(d), Fetch.LRead.Head{d}, Fetch.LRead.Bad{"a head that is not a digest"}, hd)

# A file's line is read as that file.
def entry_read.go(+k: String, +d: String, +f: Maybe<&2, String>, +p: String, -rest: List<&2, String>, b: Bool, +hk: {Rev.member(["revision", "operation", "payload", "rule", "reserved", "name"], k) == True{} : Bool}, +hd: {T.is_digest(d) == True{} : Bool}, +hf: {forgets_ok(f) == True{} : Bool}) -> {Fetch.line.at(Offer.offered.line(Offer.Offered{k, d, f, p}) <> rest, b) == Fetch.LRead.Entry{Offer.Offered{k, d, f, p}} : Fetch.LRead}:
  %Equal.sym(Maybe<&2, String>, T.strip_prefix(k ++ (" " ++ (d ++ (" " ++ (Maybe.default(&2, String, f, "-") ++ (" " ++ p))))), "head "), None{}, kind_head(k, " " ++ (d ++ (" " ++ (Maybe.default(&2, String, f, "-") ++ (" " ++ p)))), hk)) : {Fetch.line.head(b, _, k ++ (" " ++ (d ++ (" " ++ (Maybe.default(&2, String, f, "-") ++ (" " ++ p)))))) == Fetch.LRead.Entry{Offer.Offered{k, d, f, p}} : Fetch.LRead}
  %Equal.sym(Maybe<&2, Fetch.Four>, Fetch.four(k ++ (" " ++ (d ++ (" " ++ (Maybe.default(&2, String, f, "-") ++ (" " ++ p)))))), Some{Fetch.Four{k, d, Maybe.default(&2, String, f, "-"), p}}, four_line(k, d, Maybe.default(&2, String, f, "-"), p, kind_nosp(k, hk), nosp_hex(d, hexes(d, hd)), fnosp(f, hf))) : {Fetch.line.fields(_) == Fetch.LRead.Entry{Offer.Offered{k, d, f, p}} : Fetch.LRead}
  Equal.trans(Fetch.LRead,
    Bool.pick(Fetch.LRead, Rev.member(Fetch.KINDS(), k), Bool.pick(Fetch.LRead, T.is_digest(d), Bool.pick(Fetch.LRead, Bool.or(String.eq(Maybe.default(&2, String, f, "-"), "-"), T.is_digest(Maybe.default(&2, String, f, "-"))), Fetch.LRead.Entry{Offer.Offered{k, d, Fetch.forgets.of(Maybe.default(&2, String, f, "-")), p}}, Fetch.LRead.Bad{"a forgotten digest that is not a digest"}), Fetch.LRead.Bad{"a digest that is not a digest"}), Fetch.LRead.Skip{}),
    Fetch.LRead.Entry{Offer.Offered{k, d, Fetch.forgets.of(Maybe.default(&2, String, f, "-")), p}},
    Fetch.LRead.Entry{Offer.Offered{k, d, f, p}},
    Equal.trans(Fetch.LRead,
      Bool.pick(Fetch.LRead, Rev.member(Fetch.KINDS(), k), Bool.pick(Fetch.LRead, T.is_digest(d), Bool.pick(Fetch.LRead, Bool.or(String.eq(Maybe.default(&2, String, f, "-"), "-"), T.is_digest(Maybe.default(&2, String, f, "-"))), Fetch.LRead.Entry{Offer.Offered{k, d, Fetch.forgets.of(Maybe.default(&2, String, f, "-")), p}}, Fetch.LRead.Bad{"a forgotten digest that is not a digest"}), Fetch.LRead.Bad{"a digest that is not a digest"}), Fetch.LRead.Skip{}),
      Bool.pick(Fetch.LRead, T.is_digest(d), Bool.pick(Fetch.LRead, Bool.or(String.eq(Maybe.default(&2, String, f, "-"), "-"), T.is_digest(Maybe.default(&2, String, f, "-"))), Fetch.LRead.Entry{Offer.Offered{k, d, Fetch.forgets.of(Maybe.default(&2, String, f, "-")), p}}, Fetch.LRead.Bad{"a forgotten digest that is not a digest"}), Fetch.LRead.Bad{"a digest that is not a digest"}),
      Fetch.LRead.Entry{Offer.Offered{k, d, Fetch.forgets.of(Maybe.default(&2, String, f, "-")), p}},
      pick_t(Fetch.LRead, Rev.member(Fetch.KINDS(), k), Bool.pick(Fetch.LRead, T.is_digest(d), Bool.pick(Fetch.LRead, Bool.or(String.eq(Maybe.default(&2, String, f, "-"), "-"), T.is_digest(Maybe.default(&2, String, f, "-"))), Fetch.LRead.Entry{Offer.Offered{k, d, Fetch.forgets.of(Maybe.default(&2, String, f, "-")), p}}, Fetch.LRead.Bad{"a forgotten digest that is not a digest"}), Fetch.LRead.Bad{"a digest that is not a digest"}), Fetch.LRead.Skip{}, hk),
      Equal.trans(Fetch.LRead,
        Bool.pick(Fetch.LRead, T.is_digest(d), Bool.pick(Fetch.LRead, Bool.or(String.eq(Maybe.default(&2, String, f, "-"), "-"), T.is_digest(Maybe.default(&2, String, f, "-"))), Fetch.LRead.Entry{Offer.Offered{k, d, Fetch.forgets.of(Maybe.default(&2, String, f, "-")), p}}, Fetch.LRead.Bad{"a forgotten digest that is not a digest"}), Fetch.LRead.Bad{"a digest that is not a digest"}),
        Bool.pick(Fetch.LRead, Bool.or(String.eq(Maybe.default(&2, String, f, "-"), "-"), T.is_digest(Maybe.default(&2, String, f, "-"))), Fetch.LRead.Entry{Offer.Offered{k, d, Fetch.forgets.of(Maybe.default(&2, String, f, "-")), p}}, Fetch.LRead.Bad{"a forgotten digest that is not a digest"}),
        Fetch.LRead.Entry{Offer.Offered{k, d, Fetch.forgets.of(Maybe.default(&2, String, f, "-")), p}},
        pick_t(Fetch.LRead, T.is_digest(d), Bool.pick(Fetch.LRead, Bool.or(String.eq(Maybe.default(&2, String, f, "-"), "-"), T.is_digest(Maybe.default(&2, String, f, "-"))), Fetch.LRead.Entry{Offer.Offered{k, d, Fetch.forgets.of(Maybe.default(&2, String, f, "-")), p}}, Fetch.LRead.Bad{"a forgotten digest that is not a digest"}), Fetch.LRead.Bad{"a digest that is not a digest"}, hd),
        pick_t(Fetch.LRead, Bool.or(String.eq(Maybe.default(&2, String, f, "-"), "-"), T.is_digest(Maybe.default(&2, String, f, "-"))), Fetch.LRead.Entry{Offer.Offered{k, d, Fetch.forgets.of(Maybe.default(&2, String, f, "-")), p}}, Fetch.LRead.Bad{"a forgotten digest that is not a digest"}, forgets_line(f, hf)))),
    Equal.cong(Maybe<&2, String>, Fetch.LRead, x => Fetch.LRead.Entry{Offer.Offered{k, d, x, p}}, Fetch.forgets.of(Maybe.default(&2, String, f, "-")), f, forgets_back(f, hf)))

# The parts of a file `offer` names.
def wr_kind(+k: String, +d: String, f: Maybe<&2, String>, +p: String, h: {writable(Offer.Offered{k, d, f, p}) == True{} : Bool}) -> {Rev.member(["revision", "operation", "payload", "rule", "reserved", "name"], k) == True{} : Bool}:
  Comp.and_left(Rev.member(["revision", "operation", "payload", "rule", "reserved", "name"], k), Bool.and(T.is_digest(d), Bool.and(forgets_ok(f), Bool.and(BmL.nonl(p), Bool.not(String.ends_with(p, "\r"))))), h)

def wr_more(+k: String, +d: String, f: Maybe<&2, String>, +p: String, h: {writable(Offer.Offered{k, d, f, p}) == True{} : Bool}) -> {Bool.and(T.is_digest(d), Bool.and(forgets_ok(f), Bool.and(BmL.nonl(p), Bool.not(String.ends_with(p, "\r"))))) == True{} : Bool}:
  Comp.and_right(Rev.member(["revision", "operation", "payload", "rule", "reserved", "name"], k), Bool.and(T.is_digest(d), Bool.and(forgets_ok(f), Bool.and(BmL.nonl(p), Bool.not(String.ends_with(p, "\r"))))), h)

def wr_digest(+k: String, +d: String, +f: Maybe<&2, String>, +p: String, h: {writable(Offer.Offered{k, d, f, p}) == True{} : Bool}) -> {T.is_digest(d) == True{} : Bool}:
  Comp.and_left(T.is_digest(d), Bool.and(forgets_ok(f), Bool.and(BmL.nonl(p), Bool.not(String.ends_with(p, "\r")))), wr_more(k, d, f, p, h))

def wr_rest(+k: String, +d: String, +f: Maybe<&2, String>, +p: String, h: {writable(Offer.Offered{k, d, f, p}) == True{} : Bool}) -> {Bool.and(forgets_ok(f), Bool.and(BmL.nonl(p), Bool.not(String.ends_with(p, "\r")))) == True{} : Bool}:
  Comp.and_right(T.is_digest(d), Bool.and(forgets_ok(f), Bool.and(BmL.nonl(p), Bool.not(String.ends_with(p, "\r")))), wr_more(k, d, f, p, h))

def wr_forgets(+k: String, +d: String, +f: Maybe<&2, String>, +p: String, h: {writable(Offer.Offered{k, d, f, p}) == True{} : Bool}) -> {forgets_ok(f) == True{} : Bool}:
  Comp.and_left(forgets_ok(f), Bool.and(BmL.nonl(p), Bool.not(String.ends_with(p, "\r"))), wr_rest(k, d, f, p, h))

def wr_path(+k: String, +d: String, +f: Maybe<&2, String>, +p: String, h: {writable(Offer.Offered{k, d, f, p}) == True{} : Bool}) -> {Bool.and(BmL.nonl(p), Bool.not(String.ends_with(p, "\r"))) == True{} : Bool}:
  Comp.and_right(forgets_ok(f), Bool.and(BmL.nonl(p), Bool.not(String.ends_with(p, "\r"))), wr_rest(k, d, f, p, h))

def entry_read(o: Offer.Offered, -rest: List<&2, String>, b: Bool, +h: {writable(o) == True{} : Bool}) -> {Fetch.line.at(Offer.offered.line(o) <> rest, b) == Fetch.LRead.Entry{o} : Fetch.LRead}:
  match o:
    case Offer.Offered{+k, +d, +f, +p}:
      entry_read.go(k, d, f, p, rest, b, wr_kind(k, d, f, p, h), wr_digest(k, d, f, p, h), wr_forgets(k, d, f, p, h))

# The lines
# ---------

# Whether a string's last character is a carriage return, `c` being the
# one before `t`.
def cr.go(t: String, c: Char) -> Bool:
  match t:
    case SNil{}:
      Char.is_eq(c, '\r')
    case SCon{d, u}:
      cr.go(u, d)

def swif_nil(+acc: String, b: Bool) -> {String.starts_with.if(acc, SNil{}, b) == b : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      FetchingL.sw_nil(acc)

def ew_go(t: String, +c: Char, +acc: String) -> {String.starts_with(String.reverse.go(t, SCon{c, acc}), "\r") == cr.go(t, c) : Bool}:
  match t:
    case SNil{}:
      swif_nil(acc, Char.is_eq(c, '\r'))
    case SCon{+d, u}:
      ew_go(u, d, SCon{c, acc})

def ew_cons(+c: Char, +t: String) -> {String.ends_with(SCon{c, t}, "\r") == cr.go(t, c) : Bool}:
  ew_go(t, c, SNil{})

def cr_app(y: String, +x: Char, +c: Char, +s: String) -> {cr.go(y ++ SCon{c, s}, x) == cr.go(s, c) : Bool}:
  match y:
    case SNil{}:
      {==}
    case SCon{+z, w}:
      cr_app(w, z, c, s)

def ew_sp(a: String, +r: String) -> {String.ends_with(a ++ SCon{' ', r}, "\r") == cr.go(r, ' ') : Bool}:
  match a:
    case SNil{}:
      ew_cons(' ', r)
    case SCon{+x, +y}:
      Equal.trans(Bool, String.ends_with(SCon{x, y ++ SCon{' ', r}}, "\r"), cr.go(y ++ SCon{' ', r}, x), cr.go(r, ' '), ew_cons(x, y ++ SCon{' ', r}), cr_app(y, x, ' ', r))

def cr_end(p: String, h: {String.ends_with(p, "\r") == False{} : Bool}) -> {cr.go(p, ' ') == False{} : Bool}:
  match p:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      Equal.trans(Bool, cr.go(t, c), String.ends_with(SCon{c, t}, "\r"), False{}, Equal.sym(Bool, String.ends_with(SCon{c, t}, "\r"), cr.go(t, c), ew_cons(c, t)), h)

def cr_hex(t: String, +c: Char, hc: {Char.is_eq(c, '\r') == False{} : Bool}, +ht: {T.all_chars(~T.is_hex, t) == True{} : Bool}) -> {cr.go(t, c) == False{} : Bool}:
  match t:
    case SNil{}:
      hc
    case SCon{+d, +u}:
      cr_hex(u, d, hex_not(d, '\r', {==}, Comp.and_left(T.is_hex(d), T.all_chars(~T.is_hex, u), ht)), Comp.and_right(T.is_hex(d), T.all_chars(~T.is_hex, u), ht))

# A line with no newline in it and no carriage return at its end.
def line_ok(+l: String) -> Bool:
  Bool.and(BmL.nonl(l), Bool.not(String.ends_with(l, "\r")))

def clean(ls: List<&2, String>) -> Bool:
  match ls:
    case Nil{}:
      True{}
    case l <> rest:
      Bool.and(line_ok(l), clean(rest))

def head_ok(+d: String, +hd: {T.is_digest(d) == True{} : Bool}) -> {line_ok("head " ++ d) == True{} : Bool}:
  AL.and_intro(BmL.nonl("head " ++ d), Bool.not(String.ends_with("head " ++ d, "\r")),
    BmL.nonl_app("head ", d, {==}, BmL.nonl_hex(d, hexes(d, hd))),
    AL.not_true(String.ends_with("head " ++ d, "\r"), Equal.trans(Bool, String.ends_with("head " ++ d, "\r"), cr.go(d, ' '), False{}, ew_cons('h', "ead " ++ d), cr_hex(d, ' ', {==}, hexes(d, hd)))))

def entry_ok.go(+k: String, +d: String, +f: Maybe<&2, String>, +p: String, +hk: {Rev.member(["revision", "operation", "payload", "rule", "reserved", "name"], k) == True{} : Bool}, +hd: {T.is_digest(d) == True{} : Bool}, +hf: {forgets_ok(f) == True{} : Bool}, +hp: {Bool.and(BmL.nonl(p), Bool.not(String.ends_with(p, "\r"))) == True{} : Bool}) -> {line_ok(Offer.offered.line(Offer.Offered{k, d, f, p})) == True{} : Bool}:
  AL.and_intro(BmL.nonl(k ++ (" " ++ (d ++ (" " ++ (Maybe.default(&2, String, f, "-") ++ (" " ++ p)))))), Bool.not(String.ends_with(k ++ (" " ++ (d ++ (" " ++ (Maybe.default(&2, String, f, "-") ++ (" " ++ p))))), "\r")),
    BmL.nonl_app(k, " " ++ (d ++ (" " ++ (Maybe.default(&2, String, f, "-") ++ (" " ++ p)))), kind_nonl(k, hk),
      BmL.nonl_app(d, " " ++ (Maybe.default(&2, String, f, "-") ++ (" " ++ p)), BmL.nonl_hex(d, hexes(d, hd)),
        BmL.nonl_app(Maybe.default(&2, String, f, "-"), " " ++ p, fnonl(f, hf), Comp.and_left(BmL.nonl(p), Bool.not(String.ends_with(p, "\r")), hp)))),
    AL.not_true(String.ends_with(k ++ (" " ++ (d ++ (" " ++ (Maybe.default(&2, String, f, "-") ++ (" " ++ p))))), "\r"),
      Equal.trans(Bool, String.ends_with(k ++ SCon{' ', d ++ (" " ++ (Maybe.default(&2, String, f, "-") ++ (" " ++ p)))}, "\r"), cr.go(d ++ SCon{' ', Maybe.default(&2, String, f, "-") ++ (" " ++ p)}, ' '), False{},
        ew_sp(k, d ++ (" " ++ (Maybe.default(&2, String, f, "-") ++ (" " ++ p)))),
        Equal.trans(Bool, cr.go(d ++ SCon{' ', Maybe.default(&2, String, f, "-") ++ (" " ++ p)}, ' '), cr.go(Maybe.default(&2, String, f, "-") ++ SCon{' ', p}, ' '), False{},
          cr_app(d, ' ', ' ', Maybe.default(&2, String, f, "-") ++ (" " ++ p)),
          Equal.trans(Bool, cr.go(Maybe.default(&2, String, f, "-") ++ SCon{' ', p}, ' '), cr.go(p, ' '), False{},
            cr_app(Maybe.default(&2, String, f, "-"), ' ', ' ', p),
            cr_end(p, AL.not_of_true(String.ends_with(p, "\r"), Comp.and_right(BmL.nonl(p), Bool.not(String.ends_with(p, "\r")), hp))))))))

def entry_ok(o: Offer.Offered, +h: {writable(o) == True{} : Bool}) -> {line_ok(Offer.offered.line(o)) == True{} : Bool}:
  match o:
    case Offer.Offered{+k, +d, +f, +p}:
      entry_ok.go(k, d, f, p, wr_kind(k, d, f, p, h), wr_digest(k, d, f, p, h), wr_forgets(k, d, f, p, h), wr_path(k, d, f, p, h))

def clean_app(a: List<&2, String>, -b: List<&2, String>, +ha: {clean(a) == True{} : Bool}, hb: {clean(b) == True{} : Bool}) -> {clean(List.append(&2, String, a, b)) == True{} : Bool}:
  match a:
    case Nil{}:
      hb
    case +l <> rest:
      AL.and_intro(line_ok(l), clean(List.append(&2, String, rest, b)), Comp.and_left(line_ok(l), clean(rest), ha), clean_app(rest, b, Comp.and_right(line_ok(l), clean(rest), ha), hb))

def clean_heads(hs: List<&2, String>, +h: {List.all(~&2, ~String, ~(d => T.is_digest(d)), hs) == True{} : Bool}) -> {clean(Offer.heads.said(hs)) == True{} : Bool}:
  match hs:
    case Nil{}:
      {==}
    case +d <> rest:
      AL.and_intro(line_ok("head " ++ d), clean(Offer.heads.said(rest)), head_ok(d, Comp.and_left(T.is_digest(d), List.all(~&2, ~String, ~(d => T.is_digest(d)), rest), h)), clean_heads(rest, Comp.and_right(T.is_digest(d), List.all(~&2, ~String, ~(d => T.is_digest(d)), rest), h)))

def clean_entries(os: List<&2, Offer.Offered>, +h: {List.all(~&2, ~Offer.Offered, ~(o => writable(o)), os) == True{} : Bool}) -> {clean(T.map(~Offer.Offered, ~String, ~(o => Offer.offered.line(o)), os)) == True{} : Bool}:
  match os:
    case Nil{}:
      {==}
    case +o <> rest:
      AL.and_intro(line_ok(Offer.offered.line(o)), clean(T.map(~Offer.Offered, ~String, ~(o => Offer.offered.line(o)), rest)), entry_ok(o, Comp.and_left(writable(o), List.all(~&2, ~Offer.Offered, ~(o => writable(o)), rest), h)), clean_entries(rest, Comp.and_right(writable(o), List.all(~&2, ~Offer.Offered, ~(o => writable(o)), rest), h)))

def clean_rendered(+hs: List<&2, String>, +os: List<&2, Offer.Offered>, +hh: {List.all(~&2, ~String, ~(d => T.is_digest(d)), hs) == True{} : Bool}, +ho: {List.all(~&2, ~Offer.Offered, ~(o => writable(o)), os) == True{} : Bool}) -> {clean(Offer.rendered(hs, os)) == True{} : Bool}:
  clean_app(Offer.heads.said(hs), T.map(~Offer.Offered, ~String, ~(o => Offer.offered.line(o)), os), clean_heads(hs, hh), clean_entries(os, ho))

# Printed lines, split at each newline, are the lines and an empty last.
def split_printed(ls: List<&2, String>, +h: {clean(ls) == True{} : Bool}) -> {String.split(printed(ls), '\n') == List.append(&2, String, ls, [SNil{}]) : List<&2, String>}:
  match ls:
    case Nil{}:
      {==}
    case +l <> +rest:
      Equal.trans(List<&2, String>, String.split(l ++ SCon{'\n', printed(rest)}, '\n'), l <> String.split(printed(rest), '\n'), l <> List.append(&2, String, rest, [SNil{}]),
        BmL.split_nl(l, printed(rest), Comp.and_left(BmL.nonl(l), Bool.not(String.ends_with(l, "\r")), Comp.and_left(line_ok(l), clean(rest), h))),
        Equal.cong(List<&2, String>, List<&2, String>, x => l <> x, String.split(printed(rest), '\n'), List.append(&2, String, rest, [SNil{}]), split_printed(rest, Comp.and_right(line_ok(l), clean(rest), h))))

def cr_keep(+l: String, h: {String.ends_with(l, "\r") == False{} : Bool}) -> {Fetch.line.cr(l) == l : String}:
  %Equal.sym(Bool, String.ends_with(l, "\r"), False{}, h) : {Bool.pick(String, _, String.take(l, Nat.sub(String.length(l), 1n)), l) == l : String}
  {==}

def ok_cr(+l: String, h: {line_ok(l) == True{} : Bool}) -> {Fetch.line.cr(l) == l : String}:
  cr_keep(l, AL.not_of_true(String.ends_with(l, "\r"), Comp.and_right(BmL.nonl(l), Bool.not(String.ends_with(l, "\r")), h)))

def lines_app(rest: List<&2, String>, +l: String, +h: {clean(l <> rest) == True{} : Bool}) -> {Fetch.lines.of(l <> List.append(&2, String, rest, [SNil{}])) == l <> rest : List<&2, String>}:
  match rest:
    case Nil{}:
      Equal.cong(String, List<&2, String>, x => [x], Fetch.line.cr(l), l, ok_cr(l, Comp.and_left(line_ok(l), True{}, h)))
    case +r <> +more:
      Equal.trans(List<&2, String>, Fetch.line.cr(l) <> Fetch.lines.of(r <> List.append(&2, String, more, [SNil{}])), l <> Fetch.lines.of(r <> List.append(&2, String, more, [SNil{}])), l <> (r <> more),
        Equal.cong(String, List<&2, String>, x => x <> Fetch.lines.of(r <> List.append(&2, String, more, [SNil{}])), Fetch.line.cr(l), l, ok_cr(l, Comp.and_left(line_ok(l), clean(r <> more), h))),
        Equal.cong(List<&2, String>, List<&2, String>, x => l <> x, Fetch.lines.of(r <> List.append(&2, String, more, [SNil{}])), r <> more, lines_app(more, r, Comp.and_right(line_ok(l), clean(r <> more), h))))

def lines_app0(ls: List<&2, String>, +h: {clean(ls) == True{} : Bool}) -> {Fetch.lines.of(List.append(&2, String, ls, [SNil{}])) == ls : List<&2, String>}:
  match ls:
    case Nil{}:
      {==}
    case +l <> rest:
      lines_app(rest, l, h)

# Printed lines, read back as the Rust tool's `str::lines` reads them, are
# the lines.
def lines_back(+ls: List<&2, String>, +h: {clean(ls) == True{} : Bool}) -> {Fetch.lines.of(String.split(printed(ls), '\n')) == ls : List<&2, String>}:
  %Equal.sym(List<&2, String>, String.split(printed(ls), '\n'), List.append(&2, String, ls, [SNil{}]), split_printed(ls, h)) : {Fetch.lines.of(_) == ls : List<&2, String>}
  lines_app0(ls, h)

# Reading the manifest
# --------------------

# Every file's line, from the first file on, is read as that file: the
# manifest is the heads read so far and the files as they were written.
def entries_go(os: List<&2, Offer.Offered>, b: Bool, +at: Nat, +hs: List<&2, String>, +es: List<&2, Offer.Offered>, +h: {List.all(~&2, ~Offer.Offered, ~(o => writable(o)), os) == True{} : Bool}) -> {Fetch.body.go(T.map(~Offer.Offered, ~String, ~(o => Offer.offered.line(o)), os), Fetch.line.at(T.map(~Offer.Offered, ~String, ~(o => Offer.offered.line(o)), os), b), at, hs, es) == Done{Fetch.Manifest{List.reverse(&2, String, hs), List.reverse(&2, Offer.Offered, List.reverse.go(&2, Offer.Offered, os, es))}} : Result<&2, &2, String, Fetch.Manifest>}:
  match os:
    case Nil{}:
      {==}
    case +o <> +rest:
      %Equal.sym(Fetch.LRead, Fetch.line.at(Offer.offered.line(o) <> T.map(~Offer.Offered, ~String, ~(o => Offer.offered.line(o)), rest), b), Fetch.LRead.Entry{o}, entry_read(o, T.map(~Offer.Offered, ~String, ~(o => Offer.offered.line(o)), rest), b, Comp.and_left(writable(o), List.all(~&2, ~Offer.Offered, ~(o => writable(o)), rest), h))) : {Fetch.body.go(Offer.offered.line(o) <> T.map(~Offer.Offered, ~String, ~(o => Offer.offered.line(o)), rest), _, at, hs, es) == Done{Fetch.Manifest{List.reverse(&2, String, hs), List.reverse(&2, Offer.Offered, List.reverse.go(&2, Offer.Offered, rest, o <> es))}} : Result<&2, &2, String, Fetch.Manifest>}
      entries_go(rest, False{}, 1n+at, hs, o <> es, Comp.and_right(writable(o), List.all(~&2, ~Offer.Offered, ~(o => writable(o)), rest), h))

# The `head` lines, then the files: every head read, in order, and then
# every file.
def heads_go(ds: List<&2, String>, +os: List<&2, Offer.Offered>, +at: Nat, +hs: List<&2, String>, +hh: {List.all(~&2, ~String, ~(d => T.is_digest(d)), ds) == True{} : Bool}, +ho: {List.all(~&2, ~Offer.Offered, ~(o => writable(o)), os) == True{} : Bool}) -> {Fetch.body.go(List.append(&2, String, Offer.heads.said(ds), T.map(~Offer.Offered, ~String, ~(o => Offer.offered.line(o)), os)), Fetch.line.at(List.append(&2, String, Offer.heads.said(ds), T.map(~Offer.Offered, ~String, ~(o => Offer.offered.line(o)), os)), True{}), at, hs, Nil{}) == Done{Fetch.Manifest{List.reverse(&2, String, List.reverse.go(&2, String, ds, hs)), os}} : Result<&2, &2, String, Fetch.Manifest>}:
  match ds:
    case Nil{}:
      %lrev(Offer.Offered, os) : {Fetch.body.go(T.map(~Offer.Offered, ~String, ~(o => Offer.offered.line(o)), os), Fetch.line.at(T.map(~Offer.Offered, ~String, ~(o => Offer.offered.line(o)), os), True{}), at, hs, Nil{}) == Done{Fetch.Manifest{List.reverse(&2, String, hs), _}} : Result<&2, &2, String, Fetch.Manifest>}
      entries_go(os, True{}, at, hs, Nil{}, ho)
    case +d <> +rest:
      %Equal.sym(Fetch.LRead, Fetch.line.at(("head " ++ d) <> List.append(&2, String, Offer.heads.said(rest), T.map(~Offer.Offered, ~String, ~(o => Offer.offered.line(o)), os)), True{}), Fetch.LRead.Head{d}, head_read(d, List.append(&2, String, Offer.heads.said(rest), T.map(~Offer.Offered, ~String, ~(o => Offer.offered.line(o)), os)), Comp.and_left(T.is_digest(d), List.all(~&2, ~String, ~(d => T.is_digest(d)), rest), hh))) : {Fetch.body.go(("head " ++ d) <> List.append(&2, String, Offer.heads.said(rest), T.map(~Offer.Offered, ~String, ~(o => Offer.offered.line(o)), os)), _, at, hs, Nil{}) == Done{Fetch.Manifest{List.reverse(&2, String, List.reverse.go(&2, String, rest, d <> hs)), os}} : Result<&2, &2, String, Fetch.Manifest>}
      heads_go(rest, os, 1n+at, d <> hs, Comp.and_right(T.is_digest(d), List.all(~&2, ~String, ~(d => T.is_digest(d)), rest), hh), ho)

# The text `offer` prints parses as the heads and files it was printed
# from.
def parse_back(+hs: List<&2, String>, +os: List<&2, Offer.Offered>, +hh: {List.all(~&2, ~String, ~(d => T.is_digest(d)), hs) == True{} : Bool}, +ho: {List.all(~&2, ~Offer.Offered, ~(o => writable(o)), os) == True{} : Bool}) -> {Fetch.manifest.parse(printed(Offer.rendered(hs, os))) == Done{Fetch.Manifest{hs, os}} : Result<&2, &2, String, Fetch.Manifest>}:
  %Equal.sym(List<&2, String>, Fetch.lines.of(String.split(printed(Offer.rendered(hs, os)), '\n')), Offer.rendered(hs, os), lines_back(Offer.rendered(hs, os), clean_rendered(hs, os, hh, ho))) : {Fetch.manifest.lines(_) == Done{Fetch.Manifest{hs, os}} : Result<&2, &2, String, Fetch.Manifest>}
  %lrev(String, hs) : {Fetch.manifest.lines(Offer.rendered(hs, os)) == Done{Fetch.Manifest{_, os}} : Result<&2, &2, String, Fetch.Manifest>}
  heads_go(hs, os, 2n, Nil{}, hh, ho)

# The host's answer for a document of text is read as that text.
def got_text(+x: String) -> {Fetch.got.of(Done{"text\n" ++ x}) == Fetch.Got.Text{x} : Fetch.Got}:
  Equal.trans(Fetch.Got,
    Bool.pick(Fetch.Got, String.starts_with(x, SNil{}), Fetch.Got.Text{String.drop(x, 0n)}, Bool.pick(Fetch.Got, String.starts_with("text\n" ++ x, "bytes "), Fetch.Got.Bytes{String.drop("text\n" ++ x, 6n)}, Bool.pick(Fetch.Got, String.starts_with("text\n" ++ x, "status "), Fetch.Got.Status{String.drop("text\n" ++ x, 7n)}, Fetch.got.pulled(T.split_once("text\n" ++ x), "text\n" ++ x)))),
    Fetch.Got.Text{String.drop(x, 0n)},
    Fetch.Got.Text{x},
    pick_t(Fetch.Got, String.starts_with(x, SNil{}), Fetch.Got.Text{String.drop(x, 0n)}, Bool.pick(Fetch.Got, String.starts_with("text\n" ++ x, "bytes "), Fetch.Got.Bytes{String.drop("text\n" ++ x, 6n)}, Bool.pick(Fetch.Got, String.starts_with("text\n" ++ x, "status "), Fetch.Got.Status{String.drop("text\n" ++ x, 7n)}, Fetch.got.pulled(T.split_once("text\n" ++ x), "text\n" ++ x))), FetchingL.sw_nil(x)),
    Equal.cong(String, Fetch.Got, y => Fetch.Got.Text{y}, String.drop(x, 0n), x, Equal.sym(String, x, String.drop(x, 0n), FetchingL.drop0(x))))

# What `offer` prints, answered by the host as the document at the
# manifest's URL, `fetch` reads as the heads and files it was printed from.
def reads_back(+url: String, +hs: List<&2, String>, +os: List<&2, Offer.Offered>, +hh: {List.all(~&2, ~String, ~(d => T.is_digest(d)), hs) == True{} : Bool}, +ho: {List.all(~&2, ~Offer.Offered, ~(o => writable(o)), os) == True{} : Bool}) -> {Fetch.manifest.got(url, Fetch.got.of(Done{"text\n" ++ printed(Offer.rendered(hs, os))})) == Done{Fetch.Manifest{hs, os}} : Result<&2, &2, Main.Refused, Fetch.Manifest>}:
  %Equal.sym(Fetch.Got, Fetch.got.of(Done{"text\n" ++ printed(Offer.rendered(hs, os))}), Fetch.Got.Text{printed(Offer.rendered(hs, os))}, got_text(printed(Offer.rendered(hs, os)))) : {Fetch.manifest.got(url, _) == Done{Fetch.Manifest{hs, os}} : Result<&2, &2, Main.Refused, Fetch.Manifest>}
  %Equal.sym(Result<&2, &2, String, Fetch.Manifest>, Fetch.manifest.parse(printed(Offer.rendered(hs, os))), Done{Fetch.Manifest{hs, os}}, parse_back(hs, os, hh, ho)) : {Fetch.manifest.parsed(_) == Done{Fetch.Manifest{hs, os}} : Result<&2, &2, Main.Refused, Fetch.Manifest>}
  {==}
