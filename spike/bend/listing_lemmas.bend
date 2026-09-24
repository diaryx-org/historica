# What the reading commands list. `files` prints the tree's entries sorted
# by path and file — each no smaller than the one before, and under each
# path and file the entries the tree holds there — one line each, ending
# with the entry's file identifier. `names` reads the bookmarks in name
# order and prints a line for each, beginning with its name, and says a
# revision pin or a change resolves to an abbreviation of a revision the
# store holds, or why there is none.
import Base
import ./commands.bend as Main
import ./tree.bend as Tree
import ./text.bend as T
import ./sort_lemmas.bend as SortL
import ./blamed_lemmas.bend as B
import ./bookmark.bend as Bm
import ./revision.bend as Rev
import ./string_lemmas.bend as S
import ./graph_lemmas.bend as GL
import ./anchor_lemmas.bend as AL
import ./abbrev_lemmas.bend as Abbrev
import ./target_lemmas.bend as TG

# `files`
# -------

def files_sorted(+t: Tree.Tree()) -> {SortL.sorted(~Tree.Entry, ~(e => Main.files.key(e)), Main.files.listed(t)) == True{} : Bool}:
  SortL.sort_sorted(~Tree.Entry, ~(e => Main.files.key(e)), t)

def files_keyed(+t: Tree.Tree(), +k: String) -> {SortL.keyed(~Tree.Entry, ~(e => Main.files.key(e)), k, Main.files.listed(t)) == SortL.keyed(~Tree.Entry, ~(e => Main.files.key(e)), k, t) : Tree.Tree()}:
  SortL.sort_keyed(~Tree.Entry, ~(e => Main.files.key(e)), t, k)

def lines_end(es: Tree.Tree(), +w: Nat) -> {Main.ends_all(Main.files.lines(es, w), T.map(~Tree.Entry, ~String, ~(e => Tree.entry_file(e)), es)) == True{} : Bool}:
  match es:
    case Nil{}:
      {==}
    case +e <> +rest:
      B.and_tt(String.ends_with(Main.pad(Tree.entry_path(e), w) ++ "  " ++ Tree.entry_file(e), Tree.entry_file(e)), Main.ends_all(Main.files.lines(rest, w), T.map(~Tree.Entry, ~String, ~(e => Tree.entry_file(e)), rest)),
        B.ends_pre(Main.pad(Tree.entry_path(e), w), "  " ++ Tree.entry_file(e), Tree.entry_file(e), B.ends_pre("  ", Tree.entry_file(e), Tree.entry_file(e), B.ends_refl(Tree.entry_file(e)))),
        lines_end(rest, w))

# Each line `files` prints ends with the identifier of the entry it lists.
def said_ends(+t: Tree.Tree()) -> {Main.ends_all(Main.files.said(t), Main.files.ends(t)) == True{} : Bool}:
  match t:
    case Nil{}:
      B.and_tt(String.ends_with("no files here", "no files here"), True{}, B.ends_refl("no files here"), {==})
    case +e <> +rest:
      lines_end(Main.files.listed(e <> rest), Main.widest(e <> rest))

# `names`
# -------

# The bookmarks are read in name order.
def order_sorted(+ps: List<&2, String>) -> {SortL.sorted(~Main.Named, ~(n => Main.named.name(n)), Main.bookmarks.order(ps)) == True{} : Bool}:
  SortL.sort_sorted(~Main.Named, ~(n => Main.named.name(n)), Main.named(ps))

def begins(+n: String, +w: Nat, +rest: String) -> {String.starts_with(String.append(Main.pad(n, w), rest), n) == True{} : Bool}:
  B.sw_ext(Main.pad(n, w), n, rest, B.sw_ext(n, n, String.repeat(" ", Nat.sub(w, String.length(n))), B.sw_refl(n)))

def lines_begin(bs: List<&2, Bm.Bookmark>, +h: Rev.History(), +ids: List<&2, String>, +here: Maybe<&2, Tree.Tree()>, +w: Nat) -> {Main.names.begin(Main.names.lines(bs, h, ids, here, w), bs) == True{} : Bool}:
  match bs:
    case Nil{}:
      {==}
    case +b <> +rest:
      B.and_tt(String.starts_with(Main.pad(Bm.name_of(b), w) ++ "  " ++ Bm.show(b) ++ "  ->  " ++ Main.names.resolution(h, ids, here, Bm.target_of(b)), Bm.name_of(b)), Main.names.begin(Main.names.lines(rest, h, ids, here, w), rest),
        begins(Bm.name_of(b), w, "  " ++ Bm.show(b) ++ "  ->  " ++ Main.names.resolution(h, ids, here, Bm.target_of(b))),
        lines_begin(rest, h, ids, here, w))

# `names` prints a line for each bookmark, in the order read, beginning
# with its name.
def said_begun(+fs: List<&2, Main.Full>, bs: List<&2, Bm.Bookmark>) -> {Main.names.begun(bs, Main.names.said(fs, bs)) == True{} : Bool}:
  match bs:
    case Nil{}:
      {==}
    case +b <> +rest:
      lines_begin(b <> rest, Main.history(fs), Main.ids(fs), Main.names.here(Tree.merge(Main.events_of(Main.picked(Main.reached.all(fs, Main.current_heads(Main.history(fs))), Main.Pick{Main.waiting(fs), Nil{}})))), Main.names.widest(b <> rest))

def prefix_at(held: List<&2, String>, +s: String, +i: String, m: {Rev.member(held, i) == True{} : Bool}, +h: {String.starts_with(i, s) == True{} : Bool}) -> {Main.names.prefix(held, s) == True{} : Bool}:
  match held:
    case Nil{}:
      Empty.absurd({Main.names.prefix(Nil{}, s) == True{} : Bool}, S.false_true(m))
    case +y <> +rest:
      GL.member_cons({Main.names.prefix(y <> rest, s) == True{} : Bool}, y, rest, i, m,
        yi => (%Equal.sym(String, y, i, yi) : {Bool.or(String.starts_with(_, s), Main.names.prefix(rest, s)) == True{} : Bool}
          AL.or_left(String.starts_with(i, s), Main.names.prefix(rest, s), h)),
        mr => AL.or_right(String.starts_with(y, s), Main.names.prefix(rest, s), prefix_at(rest, s, i, mr, h)))

def abbrev_held(+ids: List<&2, String>, +id: String, m: {Rev.member(ids, id) == True{} : Bool}) -> {Bool.or(String.starts_with(Main.abbreviate(id, ids), "("), Main.names.prefix(ids, Main.abbreviate(id, ids))) == True{} : Bool}:
  AL.or_right(String.starts_with(Main.abbreviate(id, ids), "("), Main.names.prefix(ids, Main.abbreviate(id, ids)), prefix_at(ids, Main.abbreviate(id, ids), id, m, Abbrev.prefix_ok(id, ids)))

def pin_held(b: Bool, +ids: List<&2, String>, +id: String, eb: {Rev.member(ids, id) == b : Bool}) -> {Bool.or(String.starts_with(Bool.pick(String, b, Main.abbreviate(id, ids), "(not here yet)"), "("), Main.names.prefix(ids, Bool.pick(String, b, Main.abbreviate(id, ids), "(not here yet)"))) == True{} : Bool}:
  match b:
    case True{}:
      abbrev_held(ids, id, eb)
    case False{}:
      {==}

def current_of(+h: Rev.History(), +c: String, +id: String, es: {Rev.change_state(h, c) == Rev.Resolved{id} : Rev.ChangeState}) -> {Main.current(Rev.change_state(h, c), c, c) == Done{id} : Result<&2, &2, String, String>}:
  %Equal.sym(Rev.ChangeState, Rev.change_state(h, c), Rev.Resolved{id}, es) : {Main.current(_, c, c) == Done{id} : Result<&2, &2, String, String>}
  {==}

def change_held(+fs: List<&2, Main.Full>, +c: String, state: Rev.ChangeState, es: {Rev.change_state(Main.history(fs), c) == state : Rev.ChangeState}) -> {Bool.or(String.starts_with(Main.names.change(state, Main.ids(fs)), "("), Main.names.prefix(Main.ids(fs), Main.names.change(state, Main.ids(fs)))) == True{} : Bool}:
  match state:
    case Rev.Resolved{+id}:
      abbrev_held(Main.ids(fs), id, TG.change_mem(Main.history(fs), c, c, id, Main.ids(fs), TG.history_ok(fs), current_of(Main.history(fs), c, id, es)))
    case Rev.UnknownChange{}:
      {==}
    case Rev.Abandoned{}:
      {==}
    case Rev.Divergent{+rs}:
      AL.or_left(String.starts_with(Main.names.change(Rev.Divergent{rs}, Main.ids(fs)), "("), Main.names.prefix(Main.ids(fs), Main.names.change(Rev.Divergent{rs}, Main.ids(fs))),
        B.sw_nil(Nat.show(List.length(&2, String, rs)) ++ " current revisions; divergent)"))

# A revision pin or a change resolves, as `names` says it, to an
# abbreviation of a revision the store holds, or to a reason in
# parentheses.
def resolution_held(+fs: List<&2, Main.Full>, +here: Maybe<&2, Tree.Tree()>, t: Bm.Target) -> {Main.names.held(fs, t, Main.names.resolution(Main.history(fs), Main.ids(fs), here, t)) == True{} : Bool}:
  match t:
    case Bm.Target.File{f}:
      {==}
    case Bm.Target.Revision{+id}:
      pin_held(Rev.member(Main.ids(fs), id), Main.ids(fs), id, {==})
    case Bm.Target.Change{+c}:
      change_held(fs, c, Rev.change_state(Main.history(fs), c), {==})
