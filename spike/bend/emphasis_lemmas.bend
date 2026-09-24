# Emphasis changes no character. A changed line is cut into words, the
# words are compared with `similar`'s Myers, and the runs that differ are
# drawn in inverse video; whatever the comparison found, the runs of each
# side, read in order, are that side's line.
import Base
import ./commands.bend as Main
import ./similar.bend as Sim
import ./unicode.bend as Uni
import ./composition_lemmas.bend as Comp
import ./equality_lemmas.bend as Eq

# Strings
# -------

def app_assoc(a: String, -b: String, -c: String) -> {(a ++ b) ++ c == a ++ (b ++ c) : String}:
  match a:
    case SNil{}:
      {==}
    case SCon{h, t}:
      Equal.cong(String, String, x => SCon{h, x}, (t ++ b) ++ c, t ++ (b ++ c), app_assoc(t, b, c))

def rev_go_app(s: String, acc: String, -b: String) -> {String.reverse.go(s, acc ++ b) == String.reverse.go(s, acc) ++ b : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{h, t}:
      rev_go_app(t, SCon{h, acc}, b)

def rev_cons(c: Char, run: String) -> {String.reverse(SCon{c, run}) == String.reverse(run) ++ SCon{c, SNil{}} : String}:
  rev_go_app(run, SNil{}, SCon{c, SNil{}})

# Lists of words
# --------------

def lrev_go_app(xs: List<&2, String>, acc: List<&2, String>, -b: List<&2, String>) -> {List.reverse.go(&2, String, xs, List.append(&2, String, acc, b)) == List.append(&2, String, List.reverse.go(&2, String, xs, acc), b) : List<&2, String>}:
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      lrev_go_app(t, h <> acc, b)

def lrev_snoc(x: String, acc: List<&2, String>) -> {List.reverse(&2, String, x <> acc) == List.append(&2, String, List.reverse(&2, String, acc), [x]) : List<&2, String>}:
  lrev_go_app(acc, Nil{}, [x])

def joined_app(xs: List<&2, String>, -ys: List<&2, String>) -> {Main.joined.all(List.append(&2, String, xs, ys)) == Main.joined.all(xs) ++ Main.joined.all(ys) : String}:
  match xs:
    case Nil{}:
      {==}
    case x <> rest:
      Equal.trans(String, x ++ Main.joined.all(List.append(&2, String, rest, ys)), x ++ (Main.joined.all(rest) ++ Main.joined.all(ys)), (x ++ Main.joined.all(rest)) ++ Main.joined.all(ys),
        Equal.cong(String, String, z => x ++ z, Main.joined.all(List.append(&2, String, rest, ys)), Main.joined.all(rest) ++ Main.joined.all(ys), joined_app(rest, ys)),
        Equal.sym(String, (x ++ Main.joined.all(rest)) ++ Main.joined.all(ys), x ++ (Main.joined.all(rest) ++ Main.joined.all(ys)), app_assoc(x, Main.joined.all(rest), Main.joined.all(ys))))

def joined_take_drop(ws: List<&2, String>, n: Nat) -> {Main.joined.all(List.take(&2, String, ws, n)) ++ Main.joined.all(List.drop(&2, String, ws, n)) == Main.joined.all(ws) : String}:
  match ws n:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+p:
      {==}
    case h <> t 0n:
      {==}
    case h <> t 1n+p:
      Equal.trans(String, (h ++ Main.joined.all(List.take(&2, String, t, p))) ++ Main.joined.all(List.drop(&2, String, t, p)), h ++ (Main.joined.all(List.take(&2, String, t, p)) ++ Main.joined.all(List.drop(&2, String, t, p))), h ++ Main.joined.all(t),
        app_assoc(h, Main.joined.all(List.take(&2, String, t, p)), Main.joined.all(List.drop(&2, String, t, p))),
        Equal.cong(String, String, z => h ++ z, Main.joined.all(List.take(&2, String, t, p)) ++ Main.joined.all(List.drop(&2, String, t, p)), Main.joined.all(t), joined_take_drop(t, p)))

# A marked line
# -------------

# The pieces of a marked side are its words, whichever chunks marked them.
def marked_text(cs: List<&2, Main.Chunk>, +ws: List<&2, String>, +old: Bool) -> {Main.pieces.text(Main.marked.go(cs, ws, old)) == Main.joined.all(ws) : String}:
  match cs:
    case Nil{}:
      Eq.app_nil(Main.joined.all(ws))
    case Main.Chunk.Keep{+n} <> +rest:
      Equal.trans(String, Main.joined.all(List.take(&2, String, ws, n)) ++ Main.pieces.text(Main.marked.go(rest, List.drop(&2, String, ws, n), old)), Main.joined.all(List.take(&2, String, ws, n)) ++ Main.joined.all(List.drop(&2, String, ws, n)), Main.joined.all(ws),
        Equal.cong(String, String, z => Main.joined.all(List.take(&2, String, ws, n)) ++ z, Main.pieces.text(Main.marked.go(rest, List.drop(&2, String, ws, n), old)), Main.joined.all(List.drop(&2, String, ws, n)), marked_text(rest, List.drop(&2, String, ws, n), old)),
        joined_take_drop(ws, n))
    case Main.Chunk.Change{+l, +g} <> +rest:
      Equal.trans(String, Main.joined.all(List.take(&2, String, ws, Bool.pick(Nat, old, l, g))) ++ Main.pieces.text(Main.marked.go(rest, List.drop(&2, String, ws, Bool.pick(Nat, old, l, g)), old)), Main.joined.all(List.take(&2, String, ws, Bool.pick(Nat, old, l, g))) ++ Main.joined.all(List.drop(&2, String, ws, Bool.pick(Nat, old, l, g))), Main.joined.all(ws),
        Equal.cong(String, String, z => Main.joined.all(List.take(&2, String, ws, Bool.pick(Nat, old, l, g))) ++ z, Main.pieces.text(Main.marked.go(rest, List.drop(&2, String, ws, Bool.pick(Nat, old, l, g)), old)), Main.joined.all(List.drop(&2, String, ws, Bool.pick(Nat, old, l, g))), marked_text(rest, List.drop(&2, String, ws, Bool.pick(Nat, old, l, g)), old)),
        joined_take_drop(ws, Bool.pick(Nat, old, l, g)))

# Words
# -----

# What a cut in progress has read: the finished words, then the run being
# gathered, which is kept reversed.
def read(w: Main.Words) -> String:
  match w:
    case Main.Words{run, acc}:
      Main.joined.all(List.reverse(&2, String, acc)) ++ String.reverse(run)

def flush_text(run: String, +acc: List<&2, String>) -> {Main.joined.all(List.reverse(&2, String, Main.words.flush(run, acc))) == Main.joined.all(List.reverse(&2, String, acc)) ++ String.reverse(run) : String}:
  match run:
    case SNil{}:
      Equal.sym(String, Main.joined.all(List.reverse(&2, String, acc)) ++ SNil{}, Main.joined.all(List.reverse(&2, String, acc)), Eq.app_nil(Main.joined.all(List.reverse(&2, String, acc))))
    case SCon{+c, +t}:
      Equal.trans(String, Main.joined.all(List.reverse(&2, String, String.reverse(SCon{c, t}) <> acc)), Main.joined.all(List.append(&2, String, List.reverse(&2, String, acc), [String.reverse(SCon{c, t})])), Main.joined.all(List.reverse(&2, String, acc)) ++ String.reverse(SCon{c, t}),
        Equal.cong(List<&2, String>, String, l => Main.joined.all(l), List.reverse(&2, String, String.reverse(SCon{c, t}) <> acc), List.append(&2, String, List.reverse(&2, String, acc), [String.reverse(SCon{c, t})]), lrev_snoc(String.reverse(SCon{c, t}), acc)),
        Equal.trans(String, Main.joined.all(List.append(&2, String, List.reverse(&2, String, acc), [String.reverse(SCon{c, t})])), Main.joined.all(List.reverse(&2, String, acc)) ++ (String.reverse(SCon{c, t}) ++ SNil{}), Main.joined.all(List.reverse(&2, String, acc)) ++ String.reverse(SCon{c, t}),
          joined_app(List.reverse(&2, String, acc), [String.reverse(SCon{c, t})]),
          Equal.cong(String, String, z => Main.joined.all(List.reverse(&2, String, acc)) ++ z, String.reverse(SCon{c, t}) ++ SNil{}, String.reverse(SCon{c, t}), Eq.app_nil(String.reverse(SCon{c, t})))))

def done_text(w: Main.Words) -> {Main.joined.all(Main.words.done(w)) == read(w) : String}:
  match w:
    case Main.Words{run, +acc}:
      flush_text(run, acc)

# One character read: a letter or digit grows the run, anything else ends
# it and is a word of its own.
def char_text(w: Main.Words, +c: Char, lettered: Bool, +t: String) -> {read(Main.words.char(w, c, lettered)) ++ t == read(w) ++ SCon{c, t} : String}:
  match w:
    case Main.Words{+run, +acc}:
      match lettered:
        case True{}:
          Equal.trans(String, (Main.joined.all(List.reverse(&2, String, acc)) ++ String.reverse(SCon{c, run})) ++ t, (Main.joined.all(List.reverse(&2, String, acc)) ++ (String.reverse(run) ++ SCon{c, SNil{}})) ++ t, (Main.joined.all(List.reverse(&2, String, acc)) ++ String.reverse(run)) ++ SCon{c, t},
            Equal.cong(String, String, z => (Main.joined.all(List.reverse(&2, String, acc)) ++ z) ++ t, String.reverse(SCon{c, run}), String.reverse(run) ++ SCon{c, SNil{}}, rev_cons(c, run)),
            Equal.trans(String, (Main.joined.all(List.reverse(&2, String, acc)) ++ (String.reverse(run) ++ SCon{c, SNil{}})) ++ t, Main.joined.all(List.reverse(&2, String, acc)) ++ ((String.reverse(run) ++ SCon{c, SNil{}}) ++ t), (Main.joined.all(List.reverse(&2, String, acc)) ++ String.reverse(run)) ++ SCon{c, t},
              app_assoc(Main.joined.all(List.reverse(&2, String, acc)), String.reverse(run) ++ SCon{c, SNil{}}, t),
              Equal.trans(String, Main.joined.all(List.reverse(&2, String, acc)) ++ ((String.reverse(run) ++ SCon{c, SNil{}}) ++ t), Main.joined.all(List.reverse(&2, String, acc)) ++ (String.reverse(run) ++ SCon{c, t}), (Main.joined.all(List.reverse(&2, String, acc)) ++ String.reverse(run)) ++ SCon{c, t},
                Equal.cong(String, String, z => Main.joined.all(List.reverse(&2, String, acc)) ++ z, (String.reverse(run) ++ SCon{c, SNil{}}) ++ t, String.reverse(run) ++ SCon{c, t}, app_assoc(String.reverse(run), SCon{c, SNil{}}, t)),
                Equal.sym(String, (Main.joined.all(List.reverse(&2, String, acc)) ++ String.reverse(run)) ++ SCon{c, t}, Main.joined.all(List.reverse(&2, String, acc)) ++ (String.reverse(run) ++ SCon{c, t}), app_assoc(Main.joined.all(List.reverse(&2, String, acc)), String.reverse(run), SCon{c, t})))))
        case False{}:
          Equal.trans(String, (Main.joined.all(List.reverse(&2, String, SCon{c, SNil{}} <> Main.words.flush(run, acc))) ++ SNil{}) ++ t, Main.joined.all(List.reverse(&2, String, SCon{c, SNil{}} <> Main.words.flush(run, acc))) ++ t, (Main.joined.all(List.reverse(&2, String, acc)) ++ String.reverse(run)) ++ SCon{c, t},
            Equal.cong(String, String, z => z ++ t, Main.joined.all(List.reverse(&2, String, SCon{c, SNil{}} <> Main.words.flush(run, acc))) ++ SNil{}, Main.joined.all(List.reverse(&2, String, SCon{c, SNil{}} <> Main.words.flush(run, acc))), Eq.app_nil(Main.joined.all(List.reverse(&2, String, SCon{c, SNil{}} <> Main.words.flush(run, acc))))),
            Equal.trans(String, Main.joined.all(List.reverse(&2, String, SCon{c, SNil{}} <> Main.words.flush(run, acc))) ++ t, Main.joined.all(List.append(&2, String, List.reverse(&2, String, Main.words.flush(run, acc)), [SCon{c, SNil{}}])) ++ t, (Main.joined.all(List.reverse(&2, String, acc)) ++ String.reverse(run)) ++ SCon{c, t},
              Equal.cong(List<&2, String>, String, l => Main.joined.all(l) ++ t, List.reverse(&2, String, SCon{c, SNil{}} <> Main.words.flush(run, acc)), List.append(&2, String, List.reverse(&2, String, Main.words.flush(run, acc)), [SCon{c, SNil{}}]), lrev_snoc(SCon{c, SNil{}}, Main.words.flush(run, acc))),
              Equal.trans(String, Main.joined.all(List.append(&2, String, List.reverse(&2, String, Main.words.flush(run, acc)), [SCon{c, SNil{}}])) ++ t, (Main.joined.all(List.reverse(&2, String, Main.words.flush(run, acc))) ++ (SCon{c, SNil{}} ++ SNil{})) ++ t, (Main.joined.all(List.reverse(&2, String, acc)) ++ String.reverse(run)) ++ SCon{c, t},
                Equal.cong(String, String, z => z ++ t, Main.joined.all(List.append(&2, String, List.reverse(&2, String, Main.words.flush(run, acc)), [SCon{c, SNil{}}])), Main.joined.all(List.reverse(&2, String, Main.words.flush(run, acc))) ++ (SCon{c, SNil{}} ++ SNil{}), joined_app(List.reverse(&2, String, Main.words.flush(run, acc)), [SCon{c, SNil{}}])),
                Equal.trans(String, (Main.joined.all(List.reverse(&2, String, Main.words.flush(run, acc))) ++ SCon{c, SNil{}}) ++ t, Main.joined.all(List.reverse(&2, String, Main.words.flush(run, acc))) ++ SCon{c, t}, (Main.joined.all(List.reverse(&2, String, acc)) ++ String.reverse(run)) ++ SCon{c, t},
                  app_assoc(Main.joined.all(List.reverse(&2, String, Main.words.flush(run, acc))), SCon{c, SNil{}}, t),
                  Equal.cong(String, String, z => z ++ SCon{c, t}, Main.joined.all(List.reverse(&2, String, Main.words.flush(run, acc))), Main.joined.all(List.reverse(&2, String, acc)) ++ String.reverse(run), flush_text(run, acc))))))

def go_text(s: String, +w: Main.Words) -> {Main.joined.all(Main.words.done(Main.words.go(s, w))) == read(w) ++ s : String}:
  match s:
    case SNil{}:
      Equal.trans(String, Main.joined.all(Main.words.done(w)), read(w), read(w) ++ SNil{}, done_text(w), Equal.sym(String, read(w) ++ SNil{}, read(w), Eq.app_nil(read(w))))
    case SCon{+c, +t}:
      Equal.trans(String, Main.joined.all(Main.words.done(Main.words.go(t, Main.words.char(w, c, Uni.is_alnum(c))))), read(Main.words.char(w, c, Uni.is_alnum(c))) ++ t, read(w) ++ SCon{c, t},
        go_text(t, Main.words.char(w, c, Uni.is_alnum(c))),
        char_text(w, c, Uni.is_alnum(c), t))

# The words of a line are the line.
def words_text(s: String) -> {Main.joined.all(Main.words(s)) == s : String}:
  go_text(s, Main.Words{SNil{}, Nil{}})

# The two sides
# -------------

def mdisc(m: Maybe<&2, Main.Marked>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      Empty

def none_some(-x: Main.Marked, e: {None{} == Some{x} : Maybe<&2, Main.Marked>}) -> Empty:
  %e : {mdisc(_) : Type}
  Unit{}

def was_of(m: Maybe<&2, Main.Marked>, d: List<&2, Main.Piece>) -> List<&2, Main.Piece>:
  match m:
    case None{}:
      d
    case Some{Main.Marked{w, n}}:
      w

def now_of(m: Maybe<&2, Main.Marked>, d: List<&2, Main.Piece>) -> List<&2, Main.Piece>:
  match m:
    case None{}:
      d
    case Some{Main.Marked{w, n}}:
      n

def chunks_was(+old: List<&2, String>, +new: List<&2, String>, +cs: List<&2, Main.Chunk>, c: Bool, -w: List<&2, Main.Piece>, -n: List<&2, Main.Piece>, e: {Bool.pick(Maybe<&2, Main.Marked>, c, Some{Main.Marked{Main.marked.go(cs, old, True{}), Main.marked.go(cs, new, False{})}}, None{}) == Some{Main.Marked{w, n}} : Maybe<&2, Main.Marked>}) -> {Main.pieces.text(w) == Main.joined.all(old) : String}:
  match c:
    case True{}:
      (%Equal.cong(Maybe<&2, Main.Marked>, List<&2, Main.Piece>, m => was_of(m, w), Some{Main.Marked{Main.marked.go(cs, old, True{}), Main.marked.go(cs, new, False{})}}, Some{Main.Marked{w, n}}, e) : {Main.pieces.text(_) == Main.joined.all(old) : String}
        marked_text(cs, old, True{}))
    case False{}:
      Empty.absurd({Main.pieces.text(w) == Main.joined.all(old) : String}, none_some(Main.Marked{w, n}, e))

def chunks_now(+old: List<&2, String>, +new: List<&2, String>, +cs: List<&2, Main.Chunk>, c: Bool, -w: List<&2, Main.Piece>, -n: List<&2, Main.Piece>, e: {Bool.pick(Maybe<&2, Main.Marked>, c, Some{Main.Marked{Main.marked.go(cs, old, True{}), Main.marked.go(cs, new, False{})}}, None{}) == Some{Main.Marked{w, n}} : Maybe<&2, Main.Marked>}) -> {Main.pieces.text(n) == Main.joined.all(new) : String}:
  match c:
    case True{}:
      (%Equal.cong(Maybe<&2, Main.Marked>, List<&2, Main.Piece>, m => now_of(m, n), Some{Main.Marked{Main.marked.go(cs, old, True{}), Main.marked.go(cs, new, False{})}}, Some{Main.Marked{w, n}}, e) : {Main.pieces.text(_) == Main.joined.all(new) : String}
        marked_text(cs, new, False{}))
    case False{}:
      Empty.absurd({Main.pieces.text(n) == Main.joined.all(new) : String}, none_some(Main.Marked{w, n}, e))

def of_was(+old: List<&2, String>, +new: List<&2, String>, short: Bool, -w: List<&2, Main.Piece>, -n: List<&2, Main.Piece>, e: {Main.apart.of(old, new, short) == Some{Main.Marked{w, n}} : Maybe<&2, Main.Marked>}) -> {Main.pieces.text(w) == Main.joined.all(old) : String}:
  match short:
    case False{}:
      Empty.absurd({Main.pieces.text(w) == Main.joined.all(old) : String}, none_some(Main.Marked{w, n}, e))
    case True{}:
      chunks_was(old, new, Main.chunks.go(Sim.myers.words(old, new), 0n, 0n, Nil{}), Bool.and(Main.shared.go(Main.chunks.go(Sim.myers.words(old, new), 0n, 0n, Nil{}), old), Main.changed(Main.chunks.go(Sim.myers.words(old, new), 0n, 0n, Nil{}))), w, n, e)

def of_now(+old: List<&2, String>, +new: List<&2, String>, short: Bool, -w: List<&2, Main.Piece>, -n: List<&2, Main.Piece>, e: {Main.apart.of(old, new, short) == Some{Main.Marked{w, n}} : Maybe<&2, Main.Marked>}) -> {Main.pieces.text(n) == Main.joined.all(new) : String}:
  match short:
    case False{}:
      Empty.absurd({Main.pieces.text(n) == Main.joined.all(new) : String}, none_some(Main.Marked{w, n}, e))
    case True{}:
      chunks_now(old, new, Main.chunks.go(Sim.myers.words(old, new), 0n, 0n, Nil{}), Bool.and(Main.shared.go(Main.chunks.go(Sim.myers.words(old, new), 0n, 0n, Nil{}), old), Main.changed(Main.chunks.go(Sim.myers.words(old, new), 0n, 0n, Nil{}))), w, n, e)

def apart_was(+was: String, +now: String, -w: List<&2, Main.Piece>, -n: List<&2, Main.Piece>, e: {Main.apart(was, now) == Some{Main.Marked{w, n}} : Maybe<&2, Main.Marked>}) -> {Main.pieces.text(w) == was : String}:
  Equal.trans(String, Main.pieces.text(w), Main.joined.all(Main.words(was)), was,
    of_was(Main.words(was), Main.words(now), Bool.and(Nat.is_le(List.length(&2, String, Main.words(was)), 1024n), Nat.is_le(List.length(&2, String, Main.words(now)), 1024n)), w, n, e),
    words_text(was))

def apart_now(+was: String, +now: String, -w: List<&2, Main.Piece>, -n: List<&2, Main.Piece>, e: {Main.apart(was, now) == Some{Main.Marked{w, n}} : Maybe<&2, Main.Marked>}) -> {Main.pieces.text(n) == now : String}:
  Equal.trans(String, Main.pieces.text(n), Main.joined.all(Main.words(now)), now,
    of_now(Main.words(was), Main.words(now), Bool.and(Nat.is_le(List.length(&2, String, Main.words(was)), 1024n), Nat.is_le(List.length(&2, String, Main.words(now)), 1024n)), w, n, e),
    words_text(now))
