# The line a file of the folder's position is read along is the first-parent
# line back from the position, whole: `chain` begins at the revision named,
# each revision after it is the first parent of the one before, every one a
# revision the store holds, and it stops where that line does — or after
# 1 + n revisions of a store of n, which only a cycle could reach.
import Base
import ./revision.bend as Rev
import ./commands.bend as Main
import ./string_lemmas.bend as S
import ./blamed_lemmas.bend as B
import ./anchor_lemmas.bend as AL

def find_at_id(b: Bool, +i: String, +change: String, +parents: List<&2, String>, +supersedes: List<&2, String>, +author: String, +when: String, +revised_by: Maybe<&2, String>, +revised: Maybe<&2, String>, +facts: List<&2, Rev.Header>, +message: String, +rest: List<&2, Main.Full>, +x: String, +g: Main.Full, eb: {String.eq(i, x) == b : Bool}, e: {Bool.pick(Maybe<&2, Main.Full>, b, Some{Main.Full{i, change, parents, supersedes, author, when, revised_by, revised, facts, message}}, Main.find(rest, x)) == Some{g} : Maybe<&2, Main.Full>}, ih: {Main.find(rest, x) == Some{g} : Maybe<&2, Main.Full>} -> {String.eq(x, Main.id_of(g)) == True{} : Bool}) -> {String.eq(x, Main.id_of(g)) == True{} : Bool}:
  match b:
    case True{}:
      +d = B.some_eq_f(Main.Full{i, change, parents, supersedes, author, when, revised_by, revised, facts, message}, g, e)
      %d : {String.eq(x, Main.id_of(_)) == True{} : Bool}
      +ix = S.eq_true(i, x, eb)
      %ix : {String.eq(_, i) == True{} : Bool}
      S.eq_refl(i)
    case False{}:
      ih(e)

# What `find` finds under a name is the revision of that name.
def find_id(fs: List<&2, Main.Full>, +x: String, +g: Main.Full, e: {Main.find(fs, x) == Some{g} : Maybe<&2, Main.Full>}) -> {String.eq(x, Main.id_of(g)) == True{} : Bool}:
  match fs:
    case Nil{}:
      Empty.absurd({String.eq(x, Main.id_of(g)) == True{} : Bool}, (%e : {B.mdisc_f(_) : Type} Unit{}))
    case Main.Full{+i, +change, +parents, +supersedes, +author, +when, +revised_by, +revised, +facts, +message} <> +rest:
      find_at_id(String.eq(i, x), i, change, parents, supersedes, author, when, revised_by, revised, facts, message, rest, x, g, {==}, e, h => find_id(rest, x, g, h))

# A revision with no parent ends the line.
def none_line(fuel: Nat, +fs: List<&2, Main.Full>) -> {Main.first_parents(fs, Main.chain.go(fuel, fs, None{}), None{}) == True{} : Bool}:
  match fuel:
    case 0n:
      {==}
    case 1n+q:
      {==}

# From whatever `find` answers for a name, the walk is a first-parent line
# beginning at that name.
def line_at(fuel: Nat, +fs: List<&2, Main.Full>, m: Maybe<&2, Main.Full>, +w: String, +em: {Main.find(fs, w) == m : Maybe<&2, Main.Full>}) -> {Main.first_parents(fs, Main.chain.go(fuel, fs, m), Some{w}) == True{} : Bool}:
  match fuel m:
    case 0n _:
      {==}
    case 1n+q None{}:
      {==}
    case 1n+q Some{Main.Full{+i, +change, parents, +supersedes, +author, +when, +revised_by, +revised, +facts, +message}}:
      match parents:
        case Nil{}:
          AL.and_intro(Bool.and(Rev.member(Main.ids(fs), i), String.eq(w, i)), Main.first_parents(fs, Main.chain.go(q, fs, None{}), None{}),
            AL.and_intro(Rev.member(Main.ids(fs), i), String.eq(w, i),
              B.find_mem(fs, w, Main.Full{i, change, Nil{}, supersedes, author, when, revised_by, revised, facts, message}, em),
              find_id(fs, w, Main.Full{i, change, Nil{}, supersedes, author, when, revised_by, revised, facts, message}, em)),
            none_line(q, fs))
        case +p <> +ps:
          AL.and_intro(Bool.and(Rev.member(Main.ids(fs), i), String.eq(w, i)), Main.first_parents(fs, Main.chain.go(q, fs, Main.find(fs, p)), Some{p}),
            AL.and_intro(Rev.member(Main.ids(fs), i), String.eq(w, i),
              B.find_mem(fs, w, Main.Full{i, change, p <> ps, supersedes, author, when, revised_by, revised, facts, message}, em),
              find_id(fs, w, Main.Full{i, change, p <> ps, supersedes, author, when, revised_by, revised, facts, message}, em)),
            line_at(q, fs, Main.find(fs, p), p, {==}))

# The first-parent line from the revision a position names.
def chain_line(+fs: List<&2, Main.Full>, +id: String) -> {Main.first_parents(fs, Main.chain(fs, Some{id}), Some{id}) == True{} : Bool}:
  line_at(1n+List.length(&2, Main.Full, fs), fs, Main.find(fs, id), id, {==})

# Where the walk stops
# --------------------

def sdisc_f(m: Maybe<&2, Main.Full>) -> Type:
  match m:
    case None{}:
      Empty
    case Some{x}:
      Unit

def find_none_at(b: Bool, +i: String, +change: String, +parents: List<&2, String>, +supersedes: List<&2, String>, +author: String, +when: String, +revised_by: Maybe<&2, String>, +revised: Maybe<&2, String>, +facts: List<&2, Rev.Header>, +message: String, +rest: List<&2, Main.Full>, +w: String, e: {Bool.pick(Maybe<&2, Main.Full>, b, Some{Main.Full{i, change, parents, supersedes, author, when, revised_by, revised, facts, message}}, Main.find(rest, w)) == None{} : Maybe<&2, Main.Full>}, ih: {Main.find(rest, w) == None{} : Maybe<&2, Main.Full>} -> {Rev.member(Main.ids(rest), w) == False{} : Bool}) -> {Bool.or(b, Rev.member(Main.ids(rest), w)) == False{} : Bool}:
  match b:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, (%e : {sdisc_f(_) : Type} Unit{}))
    case False{}:
      ih(e)

# A name `find` finds nothing under is not one the store holds.
def find_none(fs: List<&2, Main.Full>, +w: String, e: {Main.find(fs, w) == None{} : Maybe<&2, Main.Full>}) -> {Rev.member(Main.ids(fs), w) == False{} : Bool}:
  match fs:
    case Nil{}:
      {==}
    case Main.Full{+i, +change, +parents, +supersedes, +author, +when, +revised_by, +revised, +facts, +message} <> +rest:
      find_none_at(String.eq(i, w), i, change, parents, supersedes, author, when, revised_by, revised, facts, message, rest, w, e, h => find_none(rest, w, h))

def or_l(a: Bool, -b: Bool, e: {a == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({Bool.or(False{}, b) == True{} : Bool}, S.false_true(e))

def or_r(a: Bool, -b: Bool, e: {b == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      e

def none_stops(fuel: Nat, +fs: List<&2, Main.Full>, -b: Bool) -> {Bool.or(Main.line.stops(fs, Main.chain.go(fuel, fs, None{}), None{}), b) == True{} : Bool}:
  match fuel:
    case 0n:
      {==}
    case 1n+q:
      {==}

# The walk stops where the line does, unless it has spent its fuel.
def stops_at(fuel: Nat, +fs: List<&2, Main.Full>, m: Maybe<&2, Main.Full>, +w: String, +em: {Main.find(fs, w) == m : Maybe<&2, Main.Full>}) -> {Bool.or(Main.line.stops(fs, Main.chain.go(fuel, fs, m), Some{w}), Nat.is_eq(List.length(&2, Main.Full, Main.chain.go(fuel, fs, m)), fuel)) == True{} : Bool}:
  match fuel m:
    case 0n _:
      or_r(Main.line.stops(fs, Nil{}, Some{w}), True{}, {==})
    case 1n+q None{}:
      or_l(Bool.not(Rev.member(Main.ids(fs), w)), Nat.is_eq(0n, 1n+q), AL.not_true(Rev.member(Main.ids(fs), w), find_none(fs, w, em)))
    case 1n+q Some{Main.Full{+i, +change, parents, +supersedes, +author, +when, +revised_by, +revised, +facts, +message}}:
      match parents:
        case Nil{}:
          none_stops(q, fs, Nat.is_eq(List.length(&2, Main.Full, Main.chain.go(q, fs, None{})), q))
        case +p <> +ps:
          stops_at(q, fs, Main.find(fs, p), p, {==})

# The first-parent line from the revision a position names, whole.
def chain_whole(+fs: List<&2, Main.Full>, +id: String) -> {Bool.and(Main.first_parents(fs, Main.chain(fs, Some{id}), Some{id}), Bool.or(Main.line.stops(fs, Main.chain(fs, Some{id}), Some{id}), Nat.is_eq(List.length(&2, Main.Full, Main.chain(fs, Some{id})), 1n+List.length(&2, Main.Full, fs)))) == True{} : Bool}:
  AL.and_intro(Main.first_parents(fs, Main.chain(fs, Some{id}), Some{id}), Bool.or(Main.line.stops(fs, Main.chain(fs, Some{id}), Some{id}), Nat.is_eq(List.length(&2, Main.Full, Main.chain(fs, Some{id})), 1n+List.length(&2, Main.Full, fs))), chain_line(fs, id), stops_at(1n+List.length(&2, Main.Full, fs), fs, Main.find(fs, id), id, {==}))
