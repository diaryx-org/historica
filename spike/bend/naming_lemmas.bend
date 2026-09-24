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
