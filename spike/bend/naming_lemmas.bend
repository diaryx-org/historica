# What a store calls the files a record writes. A revision's stem is its
# month, a `/`, and a name holding nothing a filesystem reserves: the date,
# and a summary of the message whose separators, reserved characters and
# control characters all became spaces before a word of it was kept —
# splitting on a space, keeping pieces, joining with a space, trimming and
# cutting all keep only characters that were there. A summary is sixty
# characters at most and gives up a dot or a space at either end. And each
# file of content is filed under its path, or a digest, with every control
# character scrubbed.
import Base
import ./naming.bend as N
import ./folder.bend as Folder
import ./text.bend as T
import ./anchor_lemmas.bend as AL
import ./composition_lemmas.bend as Comp
import ./abbrev_lemmas.bend as Abbrev
import ./string_lemmas.bend as S
import ./sort_lemmas.bend as SortL

# Every character passing a test
# ------------------------------

def every_app(~p: Char -> Bool, a: String, +b: String, +ha: {N.every(~p, a) == True{} : Bool}, hb: {N.every(~p, b) == True{} : Bool}) -> {N.every(~p, a ++ b) == True{} : Bool}:
  match a:
    case SNil{}:
      hb
    case SCon{+c, +rest}:
      AL.and_intro(p(c), N.every(~p, rest ++ b), Comp.and_left(p(c), N.every(~p, rest), ha), every_app(~p, rest, b, Comp.and_right(p(c), N.every(~p, rest), ha), hb))

def every_take(~p: Char -> Bool, s: String, n: Nat, +h: {N.every(~p, s) == True{} : Bool}) -> {N.every(~p, String.take(s, n)) == True{} : Bool}:
  match s n:
    case SNil{} _:
      {==}
    case SCon{+c, +rest} 0n:
      {==}
    case SCon{+c, +rest} 1n+m:
      AL.and_intro(p(c), N.every(~p, String.take(rest, m)), Comp.and_left(p(c), N.every(~p, rest), h), every_take(~p, rest, m, Comp.and_right(p(c), N.every(~p, rest), h)))

def every_rev_go(~p: Char -> Bool, s: String, +acc: String, +h: {N.every(~p, s) == True{} : Bool}, +ha: {N.every(~p, acc) == True{} : Bool}) -> {N.every(~p, String.reverse.go(s, acc)) == True{} : Bool}:
  match s:
    case SNil{}:
      ha
    case SCon{+c, +rest}:
      every_rev_go(~p, rest, SCon{c, acc}, Comp.and_right(p(c), N.every(~p, rest), h), AL.and_intro(p(c), N.every(~p, acc), Comp.and_left(p(c), N.every(~p, rest), h), ha))

def every_rev(~p: Char -> Bool, +s: String, +h: {N.every(~p, s) == True{} : Bool}) -> {N.every(~p, String.reverse(s)) == True{} : Bool}:
  every_rev_go(~p, s, SNil{}, h, {==})

# Every piece of a list.
def all_every(~p: Char -> Bool, xs: List<&2, String>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case x <> rest:
      Bool.and(N.every(~p, x), all_every(~p, rest))

def push_ok(~p: Char -> Bool, +c: Char, ps: List<&2, String>, +hc: {p(c) == True{} : Bool}, +h: {all_every(~p, ps) == True{} : Bool}) -> {all_every(~p, String.split.push(c, ps)) == True{} : Bool}:
  match ps:
    case Nil{}:
      AL.and_intro(N.every(~p, SCon{c, SNil{}}), True{}, AL.and_intro(p(c), True{}, hc, {==}), {==})
    case +x <> +rest:
      AL.and_intro(N.every(~p, SCon{c, x}), all_every(~p, rest),
        AL.and_intro(p(c), N.every(~p, x), hc, Comp.and_left(N.every(~p, x), all_every(~p, rest), h)),
        Comp.and_right(N.every(~p, x), all_every(~p, rest), h))

def fin_ok(~p: Char -> Bool, +c: Char, +ps: List<&2, String>, cut: Bool, +hc: {p(c) == True{} : Bool}, +h: {all_every(~p, ps) == True{} : Bool}) -> {all_every(~p, String.split.fin(c, ps, cut)) == True{} : Bool}:
  match cut:
    case False{}:
      push_ok(~p, c, ps, hc, h)
    case True{}:
      h

def every_split(~p: Char -> Bool, s: String, +sep: Char, +h: {N.every(~p, s) == True{} : Bool}) -> {all_every(~p, String.split(s, sep)) == True{} : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +rest}:
      fin_ok(~p, c, String.split(rest, sep), Char.is_eq(c, sep), Comp.and_left(p(c), N.every(~p, rest), h), every_split(~p, rest, sep, Comp.and_right(p(c), N.every(~p, rest), h)))

def every_join_go(~p: Char -> Bool, xs: List<&2, String>, +h: String, +sep: String, +hh: {N.every(~p, h) == True{} : Bool}, +hs: {N.every(~p, sep) == True{} : Bool}, +hx: {all_every(~p, xs) == True{} : Bool}) -> {N.every(~p, String.join.go(xs, h, sep)) == True{} : Bool}:
  match xs:
    case Nil{}:
      hh
    case +x <> +rest:
      every_app(~p, h, String.append(sep, String.join.go(rest, x, sep)), hh,
        every_app(~p, sep, String.join.go(rest, x, sep), hs,
          every_join_go(~p, rest, x, sep, Comp.and_left(N.every(~p, x), all_every(~p, rest), hx), hs, Comp.and_right(N.every(~p, x), all_every(~p, rest), hx))))

def every_join(~p: Char -> Bool, xs: List<&2, String>, +sep: String, +hs: {N.every(~p, sep) == True{} : Bool}, +hx: {all_every(~p, xs) == True{} : Bool}) -> {N.every(~p, String.join(xs, sep)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      every_join_go(~p, rest, x, sep, Comp.and_left(N.every(~p, x), all_every(~p, rest), hx), hs, Comp.and_right(N.every(~p, x), all_every(~p, rest), hx))

def nonempty_pick(~p: Char -> Bool, c: Bool, +x: String, +later: List<&2, String>, +hx: {N.every(~p, x) == True{} : Bool}, +hl: {all_every(~p, later) == True{} : Bool}) -> {all_every(~p, Bool.pick(List<&2, String>, c, later, x <> later)) == True{} : Bool}:
  match c:
    case True{}:
      hl
    case False{}:
      AL.and_intro(N.every(~p, x), all_every(~p, later), hx, hl)

def every_nonempty(~p: Char -> Bool, xs: List<&2, String>, +h: {all_every(~p, xs) == True{} : Bool}) -> {all_every(~p, N.nonempty(xs)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      nonempty_pick(~p, String.is_empty(x), x, N.nonempty(rest), Comp.and_left(N.every(~p, x), all_every(~p, rest), h), every_nonempty(~p, rest, Comp.and_right(N.every(~p, x), all_every(~p, rest), h)))

# What trimming leaves is a suffix, so it keeps only characters that were
# there.
def spare_pick(~p: Char -> Bool, b: Bool, +c: Char, -rest: String, -later: String, +h: {N.every(~p, SCon{c, rest}) == True{} : Bool}, hl: {N.every(~p, later) == True{} : Bool}) -> {N.every(~p, Bool.pick(String, b, later, SCon{c, rest})) == True{} : Bool}:
  match b:
    case True{}:
      hl
    case False{}:
      h

def every_drop_spare(~p: Char -> Bool, s: String, +h: {N.every(~p, s) == True{} : Bool}) -> {N.every(~p, N.drop_spare(s)) == True{} : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +rest}:
      spare_pick(~p, N.spare(c), c, rest, N.drop_spare(rest), h, every_drop_spare(~p, rest, Comp.and_right(p(c), N.every(~p, rest), h)))

def every_drop_space(~p: Char -> Bool, s: String, +h: {N.every(~p, s) == True{} : Bool}) -> {N.every(~p, N.drop_space(s)) == True{} : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +rest}:
      spare_pick(~p, N.is_space(c), c, rest, N.drop_space(rest), h, every_drop_space(~p, rest, Comp.and_right(p(c), N.every(~p, rest), h)))

def every_trim_spare(~p: Char -> Bool, +s: String, +h: {N.every(~p, s) == True{} : Bool}) -> {N.every(~p, N.trim_spare(s)) == True{} : Bool}:
  every_rev(~p, N.drop_spare(String.reverse(N.drop_spare(s))), every_drop_spare(~p, String.reverse(N.drop_spare(s)), every_rev(~p, N.drop_spare(s), every_drop_spare(~p, s, h))))

def every_trim_end_spare(~p: Char -> Bool, +s: String, +h: {N.every(~p, s) == True{} : Bool}) -> {N.every(~p, N.trim_end_spare(s)) == True{} : Bool}:
  every_rev(~p, N.drop_spare(String.reverse(s)), every_drop_spare(~p, String.reverse(s), every_rev(~p, s, h)))

def every_trim_end_space(~p: Char -> Bool, +s: String, +h: {N.every(~p, s) == True{} : Bool}) -> {N.every(~p, String.reverse(N.drop_space(String.reverse(s)))) == True{} : Bool}:
  every_rev(~p, N.drop_space(String.reverse(s)), every_drop_space(~p, String.reverse(s), every_rev(~p, s, h)))

# Cutting at a word keeps a prefix, read back from the reversed cut.
def every_m(~p: Char -> Bool, m: Maybe<&2, String>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{w}:
      N.every(~p, w)

def last_space_pick(~p: Char -> Bool, b: Bool, +rest: String, -later: Maybe<&2, String>, +h: {N.every(~p, rest) == True{} : Bool}, hl: {every_m(~p, later) == True{} : Bool}) -> {every_m(~p, Bool.pick(Maybe<&2, String>, b, Some{String.reverse(rest)}, later)) == True{} : Bool}:
  match b:
    case True{}:
      every_rev(~p, rest, h)
    case False{}:
      hl

def every_last_space(~p: Char -> Bool, s: String, +h: {N.every(~p, s) == True{} : Bool}) -> {every_m(~p, N.before_last_space(s)) == True{} : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +rest}:
      last_space_pick(~p, Char.is_eq(c, ' '), rest, N.before_last_space(rest), Comp.and_right(p(c), N.every(~p, rest), h), every_last_space(~p, rest, Comp.and_right(p(c), N.every(~p, rest), h)))

def cut_pick(~p: Char -> Bool, b: Bool, +cut: String, +w: String, +hc: {N.every(~p, cut) == True{} : Bool}, +hw: {N.every(~p, w) == True{} : Bool}) -> {N.every(~p, Bool.pick(String, b, String.reverse(N.drop_space(String.reverse(cut))), w)) == True{} : Bool}:
  match b:
    case True{}:
      every_trim_end_space(~p, cut, hc)
    case False{}:
      hw

def every_cut(~p: Char -> Bool, +cut: String, words: Maybe<&2, String>, +hc: {N.every(~p, cut) == True{} : Bool}, hw: {every_m(~p, words) == True{} : Bool}) -> {N.every(~p, N.clip.cut(cut, words)) == True{} : Bool}:
  match words:
    case Some{+w}:
      cut_pick(~p, String.is_empty(w), cut, w, hc, hw)
    case None{}:
      every_trim_end_space(~p, cut, hc)

def clip_pick(~p: Char -> Bool, b: Bool, +s: String, +limit: Nat, +h: {N.every(~p, s) == True{} : Bool}) -> {N.every(~p, Bool.pick(String, b, s, N.clip.cut(String.take(s, limit), N.before_last_space(String.reverse(String.take(s, limit)))))) == True{} : Bool}:
  match b:
    case True{}:
      h
    case False{}:
      every_cut(~p, String.take(s, limit), N.before_last_space(String.reverse(String.take(s, limit))), every_take(~p, s, limit, h),
        every_last_space(~p, String.reverse(String.take(s, limit)), every_rev(~p, String.take(s, limit), every_take(~p, s, limit, h))))

def every_clip(~p: Char -> Bool, +s: String, +limit: Nat, +h: {N.every(~p, s) == True{} : Bool}) -> {N.every(~p, N.clip(s, limit)) == True{} : Bool}:
  clip_pick(~p, Nat.is_le(String.length(s), limit), s, limit, h)

# The summary
# -----------

# Whatever the message, its separators, reserved and control characters
# and its spaces all became spaces.
def spaced_pick(b: Bool, +c: Char, e: {Bool.or(N.reserved(c), N.is_space(c)) == b : Bool}) -> {Bool.not(N.reserved(Bool.pick(Char, b, ' ', c))) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      AL.not_true(N.reserved(c), AL.or_false_l(N.reserved(c), N.is_space(c), e))

def plain_spaced(s: String) -> {N.plain(N.spaced(s)) == True{} : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +rest}:
      AL.and_intro(Bool.not(N.reserved(Bool.pick(Char, Bool.or(N.reserved(c), N.is_space(c)), ' ', c))), N.plain(N.spaced(rest)),
        spaced_pick(Bool.or(N.reserved(c), N.is_space(c)), c, {==}), plain_spaced(rest))

def plain_collapsed(+s: String) -> {N.plain(N.collapsed(s)) == True{} : Bool}:
  every_join(~(c => Bool.not(N.reserved(c))), N.nonempty(String.split(N.spaced(s), ' ')), " ", {==},
    every_nonempty(~(c => Bool.not(N.reserved(c))), String.split(N.spaced(s), ' '),
      every_split(~(c => Bool.not(N.reserved(c))), N.spaced(s), ' ', plain_spaced(s))))

def summary_pick(b: Bool, +change: String, +trimmed: String, +hc: {N.plain(change) == True{} : Bool}, +ht: {N.plain(trimmed) == True{} : Bool}) -> {N.plain(Bool.pick(String, b, String.take(change, N.CHANGE_CHARS()), trimmed)) == True{} : Bool}:
  match b:
    case True{}:
      every_take(~(c => Bool.not(N.reserved(c))), change, N.CHANGE_CHARS(), hc)
    case False{}:
      ht

def plain_summary(+message: String, +change: String, +hc: {N.plain(change) == True{} : Bool}) -> {N.plain(N.summary(message, change)) == True{} : Bool}:
  summary_pick(String.is_empty(N.trim_end_spare(N.clip(N.trim_spare(N.collapsed(N.first_line(message))), N.SUMMARY_CHARS()))), change, N.trim_end_spare(N.clip(N.trim_spare(N.collapsed(N.first_line(message))), N.SUMMARY_CHARS())), hc,
    every_trim_end_spare(~(c => Bool.not(N.reserved(c))), N.clip(N.trim_spare(N.collapsed(N.first_line(message))), N.SUMMARY_CHARS()),
      every_clip(~(c => Bool.not(N.reserved(c))), N.trim_spare(N.collapsed(N.first_line(message))), N.SUMMARY_CHARS(),
        every_trim_spare(~(c => Bool.not(N.reserved(c))), N.collapsed(N.first_line(message)), plain_collapsed(N.first_line(message))))))

# The stem
# --------

def str_assoc(a: String, -b: String, -c: String) -> {(a ++ b) ++ c == a ++ (b ++ c) : String}:
  match a:
    case SNil{}:
      {==}
    case SCon{+x, +rest}:
      %str_assoc(rest, b, c) : {SCon{x, (rest ++ b) ++ c} == SCon{x, _} : String}
      {==}

def month_app(month: String, +y: String, +h: {N.plain(y) == True{} : Bool}) -> {N.in_month(month, month ++ "/" ++ y) == True{} : Bool}:
  match month:
    case SNil{}:
      h
    case SCon{+m, ms}:
      %Equal.sym(Bool, Char.is_eq(m, m), True{}, Abbrev.char_refl(m)) : {Bool.and(_, N.in_month(ms, ms ++ "/" ++ y)) == True{} : Bool}
      month_app(ms, y, h)

def month_more(+month: String, +y: String, +s: String, +h: {N.plain(y ++ s) == True{} : Bool}) -> {N.in_month(month, (month ++ "/" ++ y) ++ s) == True{} : Bool}:
  %Equal.sym(String, (month ++ "/" ++ y) ++ s, month ++ ("/" ++ y) ++ s, str_assoc(month, "/" ++ y, s)) : {N.in_month(month, _) == True{} : Bool}
  month_app(month, y ++ s, h)

def plain_space(+a: String, +b: String, +ha: {N.plain(a) == True{} : Bool}, +hb: {N.plain(b) == True{} : Bool}) -> {N.plain(a ++ " " ++ b) == True{} : Bool}:
  every_app(~(c => Bool.not(N.reserved(c))), a, " " ++ b, ha, hb)

def stem_pick(shares: Bool, same: Bool, +month: String, +y: String, +c8: String, +d12: String, +hy: {N.plain(y) == True{} : Bool}, +hc: {N.plain(c8) == True{} : Bool}, +hd: {N.plain(d12) == True{} : Bool}) -> {N.in_month(month, Bool.pick(String, shares, Bool.pick(String, same, (month ++ "/" ++ y) ++ " " ++ c8 ++ " " ++ d12, (month ++ "/" ++ y) ++ " " ++ c8), month ++ "/" ++ y)) == True{} : Bool}:
  match shares:
    case False{}:
      month_app(month, y, hy)
    case True{}:
      match same:
        case True{}:
          month_more(month, y, " " ++ c8 ++ " " ++ d12, plain_space(y, c8 ++ " " ++ d12, hy, plain_space(c8, d12, hc, hd)))
        case False{}:
          month_more(month, y, " " ++ c8, plain_space(y, c8, hy, hc))

def stem_ok(+when: String, +message: String, +change: String, +id: String, +ns: List<&2, N.Named>, +hw: {N.plain(String.take(when, 10n)) == True{} : Bool}, +hc: {N.plain(change) == True{} : Bool}, +hi: {N.plain(id) == True{} : Bool}) -> {N.in_month(String.take(when, 7n), N.stem(when, message, change, id, ns)) == True{} : Bool}:
  stem_pick(N.sharing_base(ns, N.compose(when, message, change)), N.sharing_change(ns, N.compose(when, message, change), change), String.take(when, 7n), String.take(when, 10n) ++ " " ++ N.summary(message, change), String.take(change, N.CHANGE_CHARS()), String.take(id, N.DIGEST_CHARS()),
    plain_space(String.take(when, 10n), N.summary(message, change), hw, plain_summary(message, change, hc)),
    every_take(~(c => Bool.not(N.reserved(c))), change, N.CHANGE_CHARS(), hc),
    every_take(~(c => Bool.not(N.reserved(c))), id, N.DIGEST_CHARS(), hi))

# Filing content
# --------------

def ok_char(c: Char) -> Bool:
  Bool.not(Folder.is_control(c))

def scrub_pick(b: Bool, +c: Char, e: {Folder.is_control(c) == b : Bool}) -> {Bool.not(Folder.is_control(Bool.pick(Char, b, ' ', c))) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      AL.not_true(Folder.is_control(c), e)

def scrubbed_ok(s: String) -> {N.controlless(N.scrubbed(s)) == True{} : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +rest}:
      AL.and_intro(Bool.not(Folder.is_control(Bool.pick(Char, Folder.is_control(c), ' ', c))), N.controlless(N.scrubbed(rest)),
        scrub_pick(Folder.is_control(c), c, {==}), scrubbed_ok(rest))

# The last component, and everything before it.
def all_every_rev_go(~p: Char -> Bool, xs: List<&2, String>, +acc: List<&2, String>, +hx: {all_every(~p, xs) == True{} : Bool}, +ha: {all_every(~p, acc) == True{} : Bool}) -> {all_every(~p, List.reverse.go(&2, String, xs, acc)) == True{} : Bool}:
  match xs:
    case Nil{}:
      ha
    case +x <> +rest:
      all_every_rev_go(~p, rest, x <> acc, Comp.and_right(N.every(~p, x), all_every(~p, rest), hx), AL.and_intro(N.every(~p, x), all_every(~p, acc), Comp.and_left(N.every(~p, x), all_every(~p, rest), hx), ha))

def all_every_rev(~p: Char -> Bool, +xs: List<&2, String>, +hx: {all_every(~p, xs) == True{} : Bool}) -> {all_every(~p, List.reverse(&2, String, xs)) == True{} : Bool}:
  all_every_rev_go(~p, xs, Nil{}, hx, {==})

def every_first(~p: Char -> Bool, xs: List<&2, String>, +h: {all_every(~p, xs) == True{} : Bool}) -> {N.every(~p, Maybe.default(&2, String, List.get(&2, String, xs, 0n), SNil{})) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      Comp.and_left(N.every(~p, x), all_every(~p, rest), h)

def every_last(~p: Char -> Bool, +s: String, +h: {N.every(~p, s) == True{} : Bool}) -> {N.every(~p, N.last(s)) == True{} : Bool}:
  every_first(~p, List.reverse(&2, String, String.split(s, '/')), all_every_rev(~p, String.split(s, '/'), every_split(~p, s, '/', h)))

def head_pick(~p: Char -> Bool, b: Bool, +hs: {N.every(~p, "/") == True{} : Bool}) -> {N.every(~p, Bool.pick(String, b, SNil{}, "/")) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      hs

def every_head_of(~p: Char -> Bool, parts: List<&2, String>, +hs: {N.every(~p, "/") == True{} : Bool}, +h: {all_every(~p, parts) == True{} : Bool}) -> {N.every(~p, N.head.of(parts)) == True{} : Bool}:
  match parts:
    case Nil{}:
      {==}
    case +x <> +rest:
      every_app(~p, String.join(List.reverse(&2, String, rest), "/"), Bool.pick(String, List.is_empty(&2, String, rest), SNil{}, "/"),
        every_join(~p, List.reverse(&2, String, rest), "/", hs, all_every_rev(~p, rest, Comp.and_right(N.every(~p, x), all_every(~p, rest), h))),
        head_pick(~p, List.is_empty(&2, String, rest), hs))

def every_head(~p: Char -> Bool, +s: String, +hs: {N.every(~p, "/") == True{} : Bool}, +h: {N.every(~p, s) == True{} : Bool}) -> {N.every(~p, N.head(s)) == True{} : Bool}:
  every_head_of(~p, List.reverse(&2, String, String.split(s, '/')), hs, all_every_rev(~p, String.split(s, '/'), every_split(~p, s, '/', h)))

def unsuffixed_pick(~p: Char -> Bool, b: Bool, +s: String, +n: Nat, +h: {N.every(~p, s) == True{} : Bool}) -> {N.every(~p, Bool.pick(String, b, String.take(s, n), s)) == True{} : Bool}:
  match b:
    case True{}:
      every_take(~p, s, n, h)
    case False{}:
      h

def every_unsuffixed(~p: Char -> Bool, +s: String, +h: {N.every(~p, s) == True{} : Bool}) -> {N.every(~p, N.unsuffixed(s)) == True{} : Bool}:
  unsuffixed_pick(~p, String.ends_with(s, N.OPS()), s, Nat.sub(String.length(s), String.length(N.OPS())), h)

# A name made distinct keeps its path's characters, a space and the
# digest's.
def suffixed_pick(b: Bool, +name: String, +held: String, +hn: {N.controlless(name) == True{} : Bool}, +hh: {N.controlless(held) == True{} : Bool}) -> {N.controlless(Bool.pick(String, b, N.head(name) ++ N.unsuffixed(N.last(name)) ++ " " ++ String.take(held, N.DIGEST_CHARS()) ++ N.OPS(), N.head(name) ++ N.last(name) ++ " " ++ String.take(held, N.DIGEST_CHARS()))) == True{} : Bool}:
  match b:
    case True{}:
      every_app(~ok_char, N.head(name), N.unsuffixed(N.last(name)) ++ " " ++ String.take(held, N.DIGEST_CHARS()) ++ N.OPS(), every_head(~ok_char, name, {==}, hn),
        every_app(~ok_char, N.unsuffixed(N.last(name)), " " ++ String.take(held, N.DIGEST_CHARS()) ++ N.OPS(), every_unsuffixed(~ok_char, N.last(name), every_last(~ok_char, name, hn)),
          every_app(~ok_char, " ", String.take(held, N.DIGEST_CHARS()) ++ N.OPS(), {==},
            every_app(~ok_char, String.take(held, N.DIGEST_CHARS()), N.OPS(), every_take(~ok_char, held, N.DIGEST_CHARS(), hh), {==}))))
    case False{}:
      every_app(~ok_char, N.head(name), N.last(name) ++ " " ++ String.take(held, N.DIGEST_CHARS()), every_head(~ok_char, name, {==}, hn),
        every_app(~ok_char, N.last(name), " " ++ String.take(held, N.DIGEST_CHARS()), every_last(~ok_char, name, hn),
          every_app(~ok_char, " ", String.take(held, N.DIGEST_CHARS()), {==}, every_take(~ok_char, held, N.DIGEST_CHARS(), hh))))

def suffixed_ok(+name: String, +held: String, document: Bool, +hn: {N.controlless(name) == True{} : Bool}, +hh: {N.controlless(held) == True{} : Bool}) -> {N.controlless(N.suffixed(name, held, document)) == True{} : Bool}:
  suffixed_pick(document, name, held, hn, hh)

# The name each filing wants, and the one it is settled on.
def wanted_ok(w: N.Wanted) -> Bool:
  match w:
    case N.Wanted{held, name, document}:
      Bool.and(N.controlless(held), N.controlless(name))

def payload_pick(b: Bool, +p: String, +held: String, +hp: {N.controlless(p) == True{} : Bool}, +hh: {N.controlless(held) == True{} : Bool}) -> {N.controlless(Bool.pick(String, b, N.suffixed(p, held, False{}), p)) == True{} : Bool}:
  match b:
    case True{}:
      suffixed_ok(p, held, False{}, hp, hh)
    case False{}:
      hp

def wanted_pick(b: Bool, +p: String, +held: String, +hp: {N.controlless(p) == True{} : Bool}, +hh: {N.controlless(held) == True{} : Bool}) -> {N.controlless(Bool.pick(String, b, p ++ N.OPS(), Bool.pick(String, Bool.or(String.ends_with(N.last(p), N.OPS()), N.platform_name(N.last(p))), N.suffixed(p, held, False{}), p))) == True{} : Bool}:
  match b:
    case True{}:
      every_app(~ok_char, p, N.OPS(), hp, {==})
    case False{}:
      payload_pick(Bool.or(String.ends_with(N.last(p), N.OPS()), N.platform_name(N.last(p))), p, held, hp, hh)

def wanted_of_ok(+held: String, +path: String, +document: Bool, +hh: {N.controlless(held) == True{} : Bool}) -> {wanted_ok(N.wanted.of(held, path, document)) == True{} : Bool}:
  AL.and_intro(N.controlless(held), N.controlless(Bool.pick(String, document, N.scrubbed(path) ++ N.OPS(), Bool.pick(String, Bool.or(String.ends_with(N.last(N.scrubbed(path)), N.OPS()), N.platform_name(N.last(N.scrubbed(path)))), N.suffixed(N.scrubbed(path), held, False{}), N.scrubbed(path)))),
    hh, wanted_pick(document, N.scrubbed(path), held, scrubbed_ok(path), hh))

def wanted_all(fs: List<&2, N.Filing>, +h: {N.helds_controlless(fs) == True{} : Bool}) -> {SortL.all_ok(~N.Wanted, ~wanted_ok, T.map(~N.Filing, ~N.Wanted, ~(f => N.wanted(f)), fs)) == True{} : Bool}:
  match fs:
    case Nil{}:
      {==}
    case N.Filing{+held, +path, +document} <> +rest:
      AL.and_intro(wanted_ok(N.wanted.of(held, path, document)), SortL.all_ok(~N.Wanted, ~wanted_ok, T.map(~N.Filing, ~N.Wanted, ~(f => N.wanted(f)), rest)),
        wanted_of_ok(held, path, document, Comp.and_left(N.controlless(held), N.helds_controlless(rest), h)),
        wanted_all(rest, Comp.and_right(N.controlless(held), N.helds_controlless(rest), h)))

def split_ok(s: T.Split) -> Bool:
  match s:
    case T.Split{h, n}:
      N.controlless(n)

def taken_pick(b: Bool, +name: String, +held: String, +document: Bool, +hn: {N.controlless(name) == True{} : Bool}, +hh: {N.controlless(held) == True{} : Bool}) -> {N.controlless(Bool.pick(String, b, N.suffixed(name, held, document), name)) == True{} : Bool}:
  match b:
    case True{}:
      suffixed_ok(name, held, document, hn, hh)
    case False{}:
      hn

def ops_pick(document: Bool) -> {N.controlless(Bool.pick(String, document, N.OPS(), SNil{})) == True{} : Bool}:
  match document:
    case True{}:
      {==}
    case False{}:
      {==}

def dir_pick(b: Bool, +name: String, +held: String, +document: Bool, +names: List<&2, String>, +hn: {N.controlless(name) == True{} : Bool}, +hh: {N.controlless(held) == True{} : Bool}) -> {N.controlless(Bool.pick(String, b, held ++ Bool.pick(String, document, N.OPS(), SNil{}), Bool.pick(String, Nat.is_gt(N.count(names, name), 1n), N.suffixed(name, held, document), name))) == True{} : Bool}:
  match b:
    case True{}:
      every_app(~ok_char, held, Bool.pick(String, document, N.OPS(), SNil{}), hh, ops_pick(document))
    case False{}:
      taken_pick(Nat.is_gt(N.count(names, name), 1n), name, held, document, hn, hh)

def settled_ok(+dirs: List<&2, String>, +names: List<&2, String>, w: N.Wanted, +h: {wanted_ok(w) == True{} : Bool}) -> {split_ok(N.settled(dirs, names, w)) == True{} : Bool}:
  match w:
    case N.Wanted{+held, +name, +document}:
      dir_pick(N.member(dirs, name), name, held, document, names, Comp.and_right(N.controlless(held), N.controlless(name), h), Comp.and_left(N.controlless(held), N.controlless(name), h))

def settled_all_ok(+dirs: List<&2, String>, +names: List<&2, String>, ws: List<&2, N.Wanted>, +h: {SortL.all_ok(~N.Wanted, ~wanted_ok, ws) == True{} : Bool}) -> {SortL.all_ok(~T.Split, ~split_ok, N.settled_all(dirs, names, ws)) == True{} : Bool}:
  match ws:
    case Nil{}:
      {==}
    case +w <> +rest:
      AL.and_intro(split_ok(N.settled(dirs, names, w)), SortL.all_ok(~T.Split, ~split_ok, N.settled_all(dirs, names, rest)),
        settled_ok(dirs, names, w, Comp.and_left(wanted_ok(w), SortL.all_ok(~N.Wanted, ~wanted_ok, rest), h)),
        settled_all_ok(dirs, names, rest, Comp.and_right(wanted_ok(w), SortL.all_ok(~N.Wanted, ~wanted_ok, rest), h)))

def filed_ok(+fs: List<&2, N.Filing>, +h: {N.helds_controlless(fs) == True{} : Bool}) -> {SortL.all_ok(~T.Split, ~split_ok, N.filed(fs)) == True{} : Bool}:
  settled_all_ok(
    List.concat(&2, String, T.map(~String, ~List<&2, String>, ~(n => N.prefixes(n)), T.map(~N.Wanted, ~String, ~(w => N.wanted.name(w)), List.sort(~N.Wanted, ~(a => b => String.is_le(N.wanted.key(a), N.wanted.key(b))), T.map(~N.Filing, ~N.Wanted, ~(f => N.wanted(f)), fs))))),
    T.map(~N.Wanted, ~String, ~(w => N.wanted.name(w)), List.sort(~N.Wanted, ~(a => b => String.is_le(N.wanted.key(a), N.wanted.key(b))), T.map(~N.Filing, ~N.Wanted, ~(f => N.wanted(f)), fs))),
    List.sort(~N.Wanted, ~(a => b => String.is_le(N.wanted.key(a), N.wanted.key(b))), T.map(~N.Filing, ~N.Wanted, ~(f => N.wanted(f)), fs)),
    SortL.all_sort(~N.Wanted, ~(a => b => String.is_le(N.wanted.key(a), N.wanted.key(b))), ~wanted_ok, T.map(~N.Filing, ~N.Wanted, ~(f => N.wanted(f)), fs), wanted_all(fs, h)))

# And the name a digest is looked up under is one of those, or the digest.
def as_pick(b: Bool, +n: String, +later: String, +hn: {N.controlless(n) == True{} : Bool}, +hl: {N.controlless(later) == True{} : Bool}) -> {N.controlless(Bool.pick(String, b, n, later)) == True{} : Bool}:
  match b:
    case True{}:
      hn
    case False{}:
      hl

def filed_as_ok(xs: List<&2, T.Split>, +held: String, +hx: {SortL.all_ok(~T.Split, ~split_ok, xs) == True{} : Bool}, +hh: {N.controlless(held) == True{} : Bool}) -> {N.controlless(N.filed_as(xs, held)) == True{} : Bool}:
  match xs:
    case Nil{}:
      hh
    case T.Split{+h, +n} <> +rest:
      as_pick(Bool.and(String.eq(h, held), String.eq(N.filed_as(rest, held), held)), n, N.filed_as(rest, held),
        Comp.and_left(N.controlless(n), SortL.all_ok(~T.Split, ~split_ok, rest), hx),
        filed_as_ok(rest, held, Comp.and_right(N.controlless(n), SortL.all_ok(~T.Split, ~split_ok, rest), hx), hh))

# The latest timestamp
# --------------------

def mdisc(m: Maybe<&2, String>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      Empty

def none_some(-x: String, e: {None{} == Some{x} : Maybe<&2, String>}) -> Empty:
  %e : {mdisc(_) : Type}
  Unit{}

def some_inj(-x: String, -y: String, e: {Some{x} == Some{y} : Maybe<&2, String>}) -> {x == y : String}:
  Equal.cong(Maybe<&2, String>, String, m => Maybe.default(&2, String, m, x), Some{x}, Some{y}, e)

def ge_zero(n: Nat) -> {Nat.is_ge(n, 0n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

def ge_false_le(a: Nat, b: Nat, e: {Nat.is_ge(a, b) == False{} : Bool}) -> {Nat.is_le(a, b) == True{} : Bool}:
  match a b:
    case 0n 0n:
      Empty.absurd({Nat.is_le(0n, 0n) == True{} : Bool}, S.true_false(e))
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      Empty.absurd({Nat.is_le(1n+p, 0n) == True{} : Bool}, S.true_false(e))
    case 1n+p 1n+q:
      ge_false_le(p, q, e)

def le_refl(n: Nat) -> {Nat.is_le(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      le_refl(p)

# What holds of `newest`'s answer as it walks, with `best` the answer so
# far: it is one it was handed or the best, no later one was handed, and
# the best is no later.
def best_is(best: Maybe<&2, String>, +r: String) -> Bool:
  match best:
    case None{}:
      False{}
    case Some{b}:
      String.eq(b, r)

def best_le(best: Maybe<&2, String>, +r: String) -> Bool:
  match best:
    case None{}:
      True{}
    case Some{b}:
      Nat.is_le(N.instant(b), N.instant(r))

def inv(+ws: List<&2, String>, +best: Maybe<&2, String>, +r: String) -> Bool:
  Bool.and(Bool.or(N.member(ws, r), best_is(best, r)), Bool.and(N.no_later(ws, r), best_le(best, r)))

def found_or(+e: Bool, +m: Bool, +b: Bool, h: {Bool.or(m, b) == True{} : Bool}) -> {Bool.or(Bool.or(e, m), b) == True{} : Bool}:
  AL.or_cases({Bool.or(Bool.or(e, m), b) == True{} : Bool}, m, b, h,
    hm => AL.or_left(Bool.or(e, m), b, AL.or_right(e, m, hm)),
    hb => AL.or_right(Bool.or(e, m), b, hb))

def found_here(+e: Bool, +m: Bool, +b: Bool, h: {Bool.or(m, e) == True{} : Bool}) -> {Bool.or(Bool.or(e, m), b) == True{} : Bool}:
  AL.or_cases({Bool.or(Bool.or(e, m), b) == True{} : Bool}, m, e, h,
    hm => AL.or_left(Bool.or(e, m), b, AL.or_right(e, m, hm)),
    he => AL.or_left(Bool.or(e, m), b, AL.or_left(e, m, he)))

# Where the timestamp in hand is at least the best, it becomes the best,
# and the old best is no later than the answer.
def taken_best(best: Maybe<&2, String>, +w: String, +r: String, +ec: {Nat.is_ge(N.instant(w), Maybe.default(&2, Nat, Maybe.map(&2, String, Nat, b => N.instant(b), best), 0n)) == True{} : Bool}, +hw: {Nat.is_le(N.instant(w), N.instant(r)) == True{} : Bool}) -> {best_le(best, r) == True{} : Bool}:
  match best:
    case None{}:
      {==}
    case Some{+b}:
      SortL.nat_le_trans(N.instant(b), N.instant(w), N.instant(r), Abbrev.ge_le(N.instant(w), N.instant(b), ec), hw)

# Where it is earlier than the best, it is no later than the answer either.
def passed_best(best: Maybe<&2, String>, +w: String, +r: String, +ec: {Nat.is_ge(N.instant(w), Maybe.default(&2, Nat, Maybe.map(&2, String, Nat, b => N.instant(b), best), 0n)) == False{} : Bool}, +hb: {best_le(best, r) == True{} : Bool}) -> {Nat.is_le(N.instant(w), N.instant(r)) == True{} : Bool}:
  match best:
    case None{}:
      Empty.absurd({Nat.is_le(N.instant(w), N.instant(r)) == True{} : Bool}, S.true_false(Equal.trans(Bool, True{}, Nat.is_ge(N.instant(w), 0n), False{}, Equal.sym(Bool, Nat.is_ge(N.instant(w), 0n), True{}, ge_zero(N.instant(w))), ec)))
    case Some{+b}:
      SortL.nat_le_trans(N.instant(w), N.instant(b), N.instant(r), ge_false_le(N.instant(w), N.instant(b), ec), hb)

def newest_step(c: Bool, +w: String, +rest: List<&2, String>, +best: Maybe<&2, String>, +r: String, +ec: {Nat.is_ge(N.instant(w), Maybe.default(&2, Nat, Maybe.map(&2, String, Nat, b => N.instant(b), best), 0n)) == c : Bool}, +ih: {inv(rest, Bool.pick(Maybe<&2, String>, c, Some{w}, best), r) == True{} : Bool}) -> {inv(w <> rest, best, r) == True{} : Bool}:
  match c:
    case True{}:
      AL.and_intro(Bool.or(N.member(w <> rest, r), best_is(best, r)), Bool.and(N.no_later(w <> rest, r), best_le(best, r)),
        found_here(String.eq(w, r), N.member(rest, r), best_is(best, r), Comp.and_left(Bool.or(N.member(rest, r), String.eq(w, r)), Bool.and(N.no_later(rest, r), Nat.is_le(N.instant(w), N.instant(r))), ih)),
        AL.and_intro(N.no_later(w <> rest, r), best_le(best, r),
          AL.and_intro(Nat.is_le(N.instant(w), N.instant(r)), N.no_later(rest, r),
            Comp.and_right(N.no_later(rest, r), Nat.is_le(N.instant(w), N.instant(r)), Comp.and_right(Bool.or(N.member(rest, r), String.eq(w, r)), Bool.and(N.no_later(rest, r), Nat.is_le(N.instant(w), N.instant(r))), ih)),
            Comp.and_left(N.no_later(rest, r), Nat.is_le(N.instant(w), N.instant(r)), Comp.and_right(Bool.or(N.member(rest, r), String.eq(w, r)), Bool.and(N.no_later(rest, r), Nat.is_le(N.instant(w), N.instant(r))), ih))),
          taken_best(best, w, r, ec, Comp.and_right(N.no_later(rest, r), Nat.is_le(N.instant(w), N.instant(r)), Comp.and_right(Bool.or(N.member(rest, r), String.eq(w, r)), Bool.and(N.no_later(rest, r), Nat.is_le(N.instant(w), N.instant(r))), ih)))))
    case False{}:
      AL.and_intro(Bool.or(N.member(w <> rest, r), best_is(best, r)), Bool.and(N.no_later(w <> rest, r), best_le(best, r)),
        found_or(String.eq(w, r), N.member(rest, r), best_is(best, r), Comp.and_left(Bool.or(N.member(rest, r), best_is(best, r)), Bool.and(N.no_later(rest, r), best_le(best, r)), ih)),
        AL.and_intro(N.no_later(w <> rest, r), best_le(best, r),
          AL.and_intro(Nat.is_le(N.instant(w), N.instant(r)), N.no_later(rest, r),
            passed_best(best, w, r, ec, Comp.and_right(N.no_later(rest, r), best_le(best, r), Comp.and_right(Bool.or(N.member(rest, r), best_is(best, r)), Bool.and(N.no_later(rest, r), best_le(best, r)), ih))),
            Comp.and_left(N.no_later(rest, r), best_le(best, r), Comp.and_right(Bool.or(N.member(rest, r), best_is(best, r)), Bool.and(N.no_later(rest, r), best_le(best, r)), ih))),
          Comp.and_right(N.no_later(rest, r), best_le(best, r), Comp.and_right(Bool.or(N.member(rest, r), best_is(best, r)), Bool.and(N.no_later(rest, r), best_le(best, r)), ih))))

def newest_end(best: Maybe<&2, String>, +r: String, e: {best == Some{r} : Maybe<&2, String>}) -> {inv(Nil{}, best, r) == True{} : Bool}:
  match best:
    case None{}:
      Empty.absurd({inv(Nil{}, None{}, r) == True{} : Bool}, none_some(r, e))
    case Some{+b}:
      %some_inj(b, r, e) : {Bool.and(Bool.or(False{}, String.eq(b, _)), Bool.and(True{}, Nat.is_le(N.instant(b), N.instant(_)))) == True{} : Bool}
      %Equal.sym(Bool, String.eq(b, b), True{}, S.eq_refl(b)) : {Bool.and(_, Nat.is_le(N.instant(b), N.instant(b))) == True{} : Bool}
      le_refl(N.instant(b))

def newest_inv(ws: List<&2, String>, +best: Maybe<&2, String>, +r: String, e: {N.newest(ws, best) == Some{r} : Maybe<&2, String>}) -> {inv(ws, best, r) == True{} : Bool}:
  match ws:
    case Nil{}:
      newest_end(best, r, e)
    case +w <> +rest:
      newest_step(Nat.is_ge(N.instant(w), Maybe.default(&2, Nat, Maybe.map(&2, String, Nat, b => N.instant(b), best), 0n)), w, rest, best, r, {==},
        newest_inv(rest, Bool.pick(Maybe<&2, String>, Nat.is_ge(N.instant(w), Maybe.default(&2, Nat, Maybe.map(&2, String, Nat, b => N.instant(b), best), 0n)), Some{w}, best), r, e))

def or_false_id(b: Bool) -> {Bool.or(b, False{}) == b : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def and_true_id(b: Bool) -> {Bool.and(b, True{}) == b : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def latest_ok(+ws: List<&2, String>, +r: String, e: {N.newest(ws, None{}) == Some{r} : Maybe<&2, String>}) -> {N.latest(ws, r) == True{} : Bool}:
  %or_false_id(N.member(ws, r)) : {Bool.and(_, N.no_later(ws, r)) == True{} : Bool}
  %and_true_id(N.no_later(ws, r)) : {Bool.and(Bool.or(N.member(ws, r), False{}), _) == True{} : Bool}
  newest_inv(ws, None{}, r, e)

# A blank message
# ---------------

def rev_nonempty(s: String, -c: Char, -acc: String) -> {String.is_empty(String.reverse.go(s, SCon{c, acc})) == False{} : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{h, t}:
      rev_nonempty(t, h, SCon{c, acc})

def empty_rev(s: String) -> {String.is_empty(String.reverse(s)) == String.is_empty(s) : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{h, t}:
      rev_nonempty(t, h, SNil{})

def and_swap(x: Bool, y: Bool, -z: Bool) -> {Bool.and(y, Bool.and(x, z)) == Bool.and(Bool.and(x, y), z) : Bool}:
  match x y:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def every_rev_go_eq(~p: Char -> Bool, s: String, +acc: String) -> {N.every(~p, String.reverse.go(s, acc)) == Bool.and(N.every(~p, s), N.every(~p, acc)) : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +rest}:
      Equal.trans(Bool, N.every(~p, String.reverse.go(rest, SCon{c, acc})), Bool.and(N.every(~p, rest), Bool.and(p(c), N.every(~p, acc))), Bool.and(Bool.and(p(c), N.every(~p, rest)), N.every(~p, acc)),
        every_rev_go_eq(~p, rest, SCon{c, acc}), and_swap(p(c), N.every(~p, rest), N.every(~p, acc)))

def every_rev_eq(~p: Char -> Bool, +s: String) -> {N.every(~p, String.reverse(s)) == N.every(~p, s) : Bool}:
  Equal.trans(Bool, N.every(~p, String.reverse(s)), Bool.and(N.every(~p, s), True{}), N.every(~p, s), every_rev_go_eq(~p, s, SNil{}), and_true_id(N.every(~p, s)))

def drop_pick(b: Bool, -c: Char, -rest: String, -later: String, -all: Bool, ih: {String.is_empty(later) == all : Bool}) -> {String.is_empty(Bool.pick(String, b, later, SCon{c, rest})) == Bool.and(b, all) : Bool}:
  match b:
    case True{}:
      ih
    case False{}:
      {==}

# Leading space is dropped all the way exactly where there is nothing else.
def empty_drop(s: String) -> {String.is_empty(N.drop_space(s)) == N.every(~N.is_space, s) : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +rest}:
      drop_pick(N.is_space(c), c, rest, N.drop_space(rest), N.every(~N.is_space, rest), empty_drop(rest))

def every_pick(b: Bool, +c: Char, +rest: String, -later: String, ih: {N.every(~N.is_space, later) == N.every(~N.is_space, rest) : Bool}, e: {N.is_space(c) == b : Bool}) -> {N.every(~N.is_space, Bool.pick(String, b, later, SCon{c, rest})) == Bool.and(N.is_space(c), N.every(~N.is_space, rest)) : Bool}:
  match b:
    case True{}:
      %Equal.sym(Bool, N.is_space(c), True{}, e) : {N.every(~N.is_space, later) == Bool.and(_, N.every(~N.is_space, rest)) : Bool}
      ih
    case False{}:
      {==}

def every_drop(s: String) -> {N.every(~N.is_space, N.drop_space(s)) == N.every(~N.is_space, s) : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +rest}:
      every_pick(N.is_space(c), c, rest, N.drop_space(rest), every_drop(rest), {==})

def blank(+s: String) -> {String.is_empty(N.trim_space(s)) == N.every(~N.is_space, s) : Bool}:
  Equal.trans(Bool, String.is_empty(N.trim_space(s)), String.is_empty(N.drop_space(String.reverse(N.drop_space(s)))), N.every(~N.is_space, s),
    empty_rev(N.drop_space(String.reverse(N.drop_space(s)))),
    Equal.trans(Bool, String.is_empty(N.drop_space(String.reverse(N.drop_space(s)))), N.every(~N.is_space, String.reverse(N.drop_space(s))), N.every(~N.is_space, s),
      empty_drop(String.reverse(N.drop_space(s))),
      Equal.trans(Bool, N.every(~N.is_space, String.reverse(N.drop_space(s))), N.every(~N.is_space, N.drop_space(s)), N.every(~N.is_space, s),
        every_rev_eq(~N.is_space, N.drop_space(s)), every_drop(s))))
