# What the reading commands list. `files` prints the tree's entries sorted
# by path and file — each no smaller than the one before, and under each
# path and file the entries the tree holds there — one line each, ending
# with the entry's file identifier. `names` reads the bookmarks in name
# order, none dropped or repeated, and prints a line for each, beginning
# with its name and two spaces and ending with where it resolves: a pin or
# a change's one current revision as an abbreviation of its digest that no
# other held digest of its length begins with, or else why there is none.
# `log --fields` prints its header and then lines each beginning with the
# digest of a revision the span shows that every filter admits, no more
# than the limit; and a log entry's figures are what its revision's facts
# state.
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
import ./composition_lemmas.bend as Comp
import ./presentation_lemmas.bend as PL
import ./abbrev_lemmas.bend as Abbrev
import ./target_lemmas.bend as TG
import ./diff_lemmas.bend as Diff
import ./show_lemmas.bend as ShowL

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

# And holds every bookmark it was given: under each name, the ones found
# under it, in the order found.
def order_keyed(+ps: List<&2, String>, +k: String) -> {SortL.keyed(~Main.Named, ~(n => Main.named.name(n)), k, Main.bookmarks.order(ps)) == SortL.keyed(~Main.Named, ~(n => Main.named.name(n)), k, Main.named(ps)) : List<&2, Main.Named>}:
  SortL.sort_keyed(~Main.Named, ~(n => Main.named.name(n)), Main.named(ps), k)

# What starts with `c` still does behind the same prefix.
def sw_prefix(a: String, +b: String, +c: String, h: {String.starts_with(b, c) == True{} : Bool}) -> {String.starts_with(String.append(a, b), String.append(a, c)) == True{} : Bool}:
  match a:
    case SNil{}:
      h
    case SCon{+x, t}:
      %Equal.sym(Bool, Char.is_eq(x, x), True{}, Diff.char_eq_refl(x)) : {String.starts_with.if(String.append(t, b), String.append(t, c), _) == True{} : Bool}
      sw_prefix(t, b, c, h)

# The column a name is padded to is followed by two spaces, so a line
# begins with its name and at least two spaces, whatever the width.
def sp1(k: Nat, +r: String) -> {String.starts_with(String.append(String.repeat(" ", k), String.append(" ", r)), " ") == True{} : Bool}:
  match k:
    case 0n:
      B.sw_ext(" ", " ", r, B.sw_refl(" "))
    case 1n+p:
      B.sw_nil(String.append(String.repeat(" ", p), String.append(" ", r)))

def sp2(k: Nat, +r: String) -> {String.starts_with(String.append(String.repeat(" ", k), String.append("  ", r)), "  ") == True{} : Bool}:
  match k:
    case 0n:
      B.sw_ext("  ", "  ", r, B.sw_refl("  "))
    case 1n+p:
      sp1(p, String.append(" ", r))

def name_gap(+n: String, +w: Nat, +z: String) -> {String.starts_with(String.append(Main.pad(n, w), String.append("  ", z)), String.append(n, "  ")) == True{} : Bool}:
  %Equal.sym(String, String.append(String.append(n, String.repeat(" ", Nat.sub(w, String.length(n)))), String.append("  ", z)), String.append(n, String.append(String.repeat(" ", Nat.sub(w, String.length(n))), String.append("  ", z))), B.app_assoc(n, String.repeat(" ", Nat.sub(w, String.length(n))), String.append("  ", z))) : {String.starts_with(_, String.append(n, "  ")) == True{} : Bool}
  sw_prefix(n, String.append(String.repeat(" ", Nat.sub(w, String.length(n))), String.append("  ", z)), "  ", sp2(Nat.sub(w, String.length(n)), z))

# A pin's or a change's line ends with where it resolves, whatever the
# folder's tree.
def ends_ok(+fs: List<&2, Main.Full>, +here: Maybe<&2, Tree.Tree()>, +a: String, +b: String, t: Bm.Target) -> {Main.names.ends(fs, a ++ "  " ++ b ++ "  ->  " ++ Main.names.resolution(Main.history(fs), Main.ids(fs), here, t), t) == True{} : Bool}:
  match t:
    case Bm.Target.File{f}:
      {==}
    case Bm.Target.Revision{+id}:
      B.ends_pre(a, "  " ++ b ++ "  ->  " ++ Main.names.resolution(Main.history(fs), Main.ids(fs), None{}, Bm.Target.Revision{id}), "  ->  " ++ Main.names.resolution(Main.history(fs), Main.ids(fs), None{}, Bm.Target.Revision{id}),
        B.ends_pre("  ", b ++ "  ->  " ++ Main.names.resolution(Main.history(fs), Main.ids(fs), None{}, Bm.Target.Revision{id}), "  ->  " ++ Main.names.resolution(Main.history(fs), Main.ids(fs), None{}, Bm.Target.Revision{id}),
          B.ends_pre(b, "  ->  " ++ Main.names.resolution(Main.history(fs), Main.ids(fs), None{}, Bm.Target.Revision{id}), "  ->  " ++ Main.names.resolution(Main.history(fs), Main.ids(fs), None{}, Bm.Target.Revision{id}),
            B.ends_refl("  ->  " ++ Main.names.resolution(Main.history(fs), Main.ids(fs), None{}, Bm.Target.Revision{id})))))
    case Bm.Target.Change{+c}:
      B.ends_pre(a, "  " ++ b ++ "  ->  " ++ Main.names.resolution(Main.history(fs), Main.ids(fs), None{}, Bm.Target.Change{c}), "  ->  " ++ Main.names.resolution(Main.history(fs), Main.ids(fs), None{}, Bm.Target.Change{c}),
        B.ends_pre("  ", b ++ "  ->  " ++ Main.names.resolution(Main.history(fs), Main.ids(fs), None{}, Bm.Target.Change{c}), "  ->  " ++ Main.names.resolution(Main.history(fs), Main.ids(fs), None{}, Bm.Target.Change{c}),
          B.ends_pre(b, "  ->  " ++ Main.names.resolution(Main.history(fs), Main.ids(fs), None{}, Bm.Target.Change{c}), "  ->  " ++ Main.names.resolution(Main.history(fs), Main.ids(fs), None{}, Bm.Target.Change{c}),
            B.ends_refl("  ->  " ++ Main.names.resolution(Main.history(fs), Main.ids(fs), None{}, Bm.Target.Change{c})))))

def lines_ok(+fs: List<&2, Main.Full>, bs: List<&2, Bm.Bookmark>, +here: Maybe<&2, Tree.Tree()>, +w: Nat) -> {Main.names.begin(fs, Main.names.lines(bs, Main.history(fs), Main.ids(fs), here, w), bs) == True{} : Bool}:
  match bs:
    case Nil{}:
      {==}
    case Bm.Bookmark{+n, +t, +p} <> +rest:
      B.and_tt(Main.names.line(fs, Main.pad(n, w) ++ "  " ++ Bm.show(Bm.Bookmark{n, t, p}) ++ "  ->  " ++ Main.names.resolution(Main.history(fs), Main.ids(fs), here, t), Bm.Bookmark{n, t, p}), Main.names.begin(fs, Main.names.lines(rest, Main.history(fs), Main.ids(fs), here, w), rest),
        B.and_tt(String.starts_with(Main.pad(n, w) ++ "  " ++ Bm.show(Bm.Bookmark{n, t, p}) ++ "  ->  " ++ Main.names.resolution(Main.history(fs), Main.ids(fs), here, t), n ++ "  "), Main.names.ends(fs, Main.pad(n, w) ++ "  " ++ Bm.show(Bm.Bookmark{n, t, p}) ++ "  ->  " ++ Main.names.resolution(Main.history(fs), Main.ids(fs), here, t), t),
          name_gap(n, w, Bm.show(Bm.Bookmark{n, t, p}) ++ "  ->  " ++ Main.names.resolution(Main.history(fs), Main.ids(fs), here, t)),
          ends_ok(fs, here, Main.pad(n, w), Bm.show(Bm.Bookmark{n, t, p}), t)),
        lines_ok(fs, rest, here, w))

# `names` prints a line for each bookmark, in the order read, beginning
# with its name and two spaces and, for a pin or a change, ending with where
# it resolves; with none, it says so.
def said_begun(+fs: List<&2, Main.Full>, bs: List<&2, Bm.Bookmark>) -> {Main.names.begun(fs, bs, Main.names.said(fs, bs)) == True{} : Bool}:
  match bs:
    case Nil{}:
      {==}
    case +b <> +rest:
      lines_ok(fs, b <> rest, Main.names.here(Tree.merge(Main.events_of(Main.picked(Main.reached.all(fs, Main.current_heads(Main.history(fs))), Main.Pick{Main.waiting(fs), Nil{}})))), Main.names.widest(b <> rest))

# The abbreviation
# ----------------

# A longer cut of a string begins with a shorter one.
def take_mono(s: String, m: Nat, n: Nat, le: {Nat.is_le(m, n) == True{} : Bool}) -> {String.starts_with(String.take(s, n), String.take(s, m)) == True{} : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      match m:
        case 0n:
          B.sw_nil(String.take(SCon{h, t}, n))
        case 1n+q:
          match n:
            case 0n:
              Empty.absurd({String.starts_with(String.take(SCon{h, t}, 0n), String.take(SCon{h, t}, 1n+q)) == True{} : Bool}, S.false_true(le))
            case 1n+r:
              (%Equal.sym(Bool, Char.is_eq(h, h), True{}, Abbrev.char_refl(h)) : {String.starts_with.if(String.take(t, r), String.take(t, q), _) == True{} : Bool}
                take_mono(t, q, r, le))

# An abbreviation is the digest's first eight characters at least.
def eight(+id: String, +among: List<&2, String>) -> {String.starts_with(Main.abbreviate(id, among), String.take(id, 8n)) == True{} : Bool}:
  take_mono(id, 8n, Nat.max(8n, 1n+Main.longest_shared(id, among)), Abbrev.ge_le(Nat.max(8n, 1n+Main.longest_shared(id, among)), 8n, Nat.max_ge_l(8n, 1n+Main.longest_shared(id, among))))

def alone_one(+o: String, +id: String, +among: List<&2, String>, m: {Rev.member(among, o) == True{} : Bool}, b1: Bool, e1: {String.eq(o, id) == b1 : Bool}, b2: Bool, e2: {Nat.is_eq(String.length(o), String.length(id)) == b2 : Bool}) -> {Bool.or(b1, Bool.or(Bool.not(b2), Bool.not(String.starts_with(o, Main.abbreviate(id, among))))) == True{} : Bool}:
  match b1:
    case True{}:
      {==}
    case False{}:
      match b2:
        case False{}:
          {==}
        case True{}:
          %Equal.sym(Bool, String.starts_with(o, Main.abbreviate(id, among)), False{}, Abbrev.unique(id, among, o, m, e1, Comp.eq_of_is_eq(String.length(o), String.length(id), e2))) : {Bool.or(False{}, Bool.or(Bool.not(True{}), Bool.not(_))) == True{} : Bool}
          {==}

# No other digest among these of the same length begins with it.
def alone_ok(xs: List<&2, String>, +id: String, +among: List<&2, String>, +hs: {Tree.subset_ids(xs, among) == True{} : Bool}) -> {Main.names.alone(xs, id, Main.abbreviate(id, among)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +o <> +rest:
      B.and_tt(Bool.or(String.eq(o, id), Bool.or(Bool.not(Nat.is_eq(String.length(o), String.length(id))), Bool.not(String.starts_with(o, Main.abbreviate(id, among))))), Main.names.alone(rest, id, Main.abbreviate(id, among)),
        alone_one(o, id, among, Comp.and_left(Rev.member(among, o), Tree.subset_ids(rest, among), hs), String.eq(o, id), {==}, Nat.is_eq(String.length(o), String.length(id)), {==}),
        alone_ok(rest, id, among, Comp.and_right(Rev.member(among, o), Tree.subset_ids(rest, among), hs)))

# What `names` prints of a revision abbreviates it.
def abbrev_ok(+among: List<&2, String>, +id: String) -> {Main.names.abbreviates(among, id, Main.abbreviate(id, among)) == True{} : Bool}:
  B.and_tt(Bool.and(String.starts_with(id, Main.abbreviate(id, among)), String.starts_with(Main.abbreviate(id, among), String.take(id, 8n))), Main.names.alone(among, id, Main.abbreviate(id, among)),
    B.and_tt(String.starts_with(id, Main.abbreviate(id, among)), String.starts_with(Main.abbreviate(id, among), String.take(id, 8n)), Abbrev.prefix_ok(id, among), eight(id, among)),
    alone_ok(among, id, among, GL.subset_refl(among)))

def pin_ok(b: Bool, +ids: List<&2, String>, +id: String) -> {Bool.pick(Bool, b, Main.names.abbreviates(ids, id, Bool.pick(String, b, Main.abbreviate(id, ids), "(not here yet)")), String.eq(Bool.pick(String, b, Main.abbreviate(id, ids), "(not here yet)"), "(not here yet)")) == True{} : Bool}:
  match b:
    case True{}:
      abbrev_ok(ids, id)
    case False{}:
      {==}

def current_of(+h: Rev.History(), +c: String, +id: String, es: {Rev.change_state(h, c) == Rev.Resolved{id} : Rev.ChangeState}) -> {Main.current(Rev.change_state(h, c), c, c) == Done{id} : Result<&2, &2, String, String>}:
  %Equal.sym(Rev.ChangeState, Rev.change_state(h, c), Rev.Resolved{id}, es) : {Main.current(_, c, c) == Done{id} : Result<&2, &2, String, String>}
  {==}

def change_ok(+fs: List<&2, Main.Full>, +c: String, state: Rev.ChangeState, es: {Rev.change_state(Main.history(fs), c) == state : Rev.ChangeState}) -> {Main.names.change_said(Main.ids(fs), state, Main.names.change(state, Main.ids(fs))) == True{} : Bool}:
  match state:
    case Rev.Resolved{+id}:
      B.and_tt(Rev.member(Main.ids(fs), id), Main.names.abbreviates(Main.ids(fs), id, Main.abbreviate(id, Main.ids(fs))),
        TG.change_mem(Main.history(fs), c, c, id, Main.ids(fs), TG.history_ok(fs), current_of(Main.history(fs), c, id, es)),
        abbrev_ok(Main.ids(fs), id))
    case Rev.UnknownChange{}:
      {==}
    case Rev.Abandoned{}:
      {==}
    case Rev.Divergent{+rs}:
      B.and_tt(String.starts_with("(" ++ Nat.show(List.length(&2, String, rs)) ++ " current revisions; divergent)", "("), String.ends_with("(" ++ Nat.show(List.length(&2, String, rs)) ++ " current revisions; divergent)", ")"),
        B.sw_ext("(", "(", Nat.show(List.length(&2, String, rs)) ++ " current revisions; divergent)", B.sw_refl("(")),
        B.ends_pre("(", Nat.show(List.length(&2, String, rs)) ++ " current revisions; divergent)", ")",
          B.ends_pre(Nat.show(List.length(&2, String, rs)), " current revisions; divergent)", ")", {==})))

# Where `names` says a pin or a change resolves: the abbreviation of the
# revision pinned, or of the change's one current revision, where the store
# holds it; `(not here yet)` for a pin it lacks; a reason in parentheses
# for a change with no one current revision.
def resolution_ok(+fs: List<&2, Main.Full>, +here: Maybe<&2, Tree.Tree()>, t: Bm.Target) -> {Main.names.held(fs, t, Main.names.resolution(Main.history(fs), Main.ids(fs), here, t)) == True{} : Bool}:
  match t:
    case Bm.Target.File{f}:
      {==}
    case Bm.Target.Revision{+id}:
      pin_ok(Rev.member(Main.ids(fs), id), Main.ids(fs), id)
    case Bm.Target.Change{+c}:
      change_ok(fs, c, Rev.change_state(Main.history(fs), c), {==})

# `log`
# -----

def from_at(held: List<&2, String>, +l: String, +i: String, m: {Rev.member(held, i) == True{} : Bool}, +h: {String.starts_with(l, i ++ " ") == True{} : Bool}) -> {Main.log.fields.from(held, l) == True{} : Bool}:
  match held:
    case Nil{}:
      Empty.absurd({Main.log.fields.from(Nil{}, l) == True{} : Bool}, S.false_true(m))
    case +y <> +rest:
      GL.member_cons({Main.log.fields.from(y <> rest, l) == True{} : Bool}, y, rest, i, m,
        yi => (%Equal.sym(String, y, i, yi) : {Bool.or(String.starts_with(l, _ ++ " "), Main.log.fields.from(rest, l)) == True{} : Bool}
          AL.or_left(String.starts_with(l, i ++ " "), Main.log.fields.from(rest, l), h)),
        mr => AL.or_right(String.starts_with(l, y ++ " "), Main.log.fields.from(rest, l), from_at(rest, l, i, mr, h)))

# Every revision here has its digest among these.
def ins(+L: List<&2, String>, fs: List<&2, Main.Full>) -> Bool:
  match fs:
    case Nil{}:
      True{}
    case +f <> rest:
      Bool.and(Rev.member(L, Main.id_of(f)), ins(L, rest))

# A line for each revision listed, beginning with its digest and a space.
def fields_each(fs: List<&2, Main.Full>, +L: List<&2, String>, +heads: List<&2, String>, +gone: List<&2, String>, +h: Rev.History(), +hi: {ins(L, fs) == True{} : Bool}) -> {Main.log.fields.each(Main.fields.lines(fs, heads, gone, h), L) == True{} : Bool}:
  match fs:
    case Nil{}:
      {==}
    case Main.Full{+id, +change, +parents, +supersedes, +author, +when, +revised_by, +revised, +facts, +message} <> +rest:
      B.and_tt(Main.log.fields.from(L, Main.fields_line(Main.Full{id, change, parents, supersedes, author, when, revised_by, revised, facts, message}, heads, gone, h)), Main.log.fields.each(Main.fields.lines(rest, heads, gone, h), L),
        from_at(L, Main.fields_line(Main.Full{id, change, parents, supersedes, author, when, revised_by, revised, facts, message}, heads, gone, h), id, Comp.and_left(Rev.member(L, id), ins(L, rest), hi),
          sw_prefix(id, " " ++ (change ++ " " ++ when ++ " " ++ Main.found(id, change, heads, gone, h) ++ String.concat(T.map(~String, ~String, ~(p => " " ++ p), parents))), " ",
            B.sw_nil(change ++ " " ++ when ++ " " ++ Main.found(id, change, heads, gone, h) ++ String.concat(T.map(~String, ~String, ~(p => " " ++ p), parents))))),
        fields_each(rest, L, heads, gone, h, Comp.and_right(Rev.member(L, id), ins(L, rest), hi)))

def lines_len(fs: List<&2, Main.Full>, +heads: List<&2, String>, +gone: List<&2, String>, +h: Rev.History()) -> {List.length(&2, String, Main.fields.lines(fs, heads, gone, h)) == List.length(&2, Main.Full, fs) : Nat}:
  match fs:
    case Nil{}:
      {==}
    case f <> rest:
      Equal.cong(Nat, Nat, n => 1n+n, List.length(&2, String, Main.fields.lines(rest, heads, gone, h)), List.length(&2, Main.Full, rest), lines_len(rest, heads, gone, h))

def take_le(xs: List<&2, Main.Full>, n: Nat) -> {Nat.is_le(List.length(&2, Main.Full, List.take(&2, Main.Full, xs, n)), n) == True{} : Bool}:
  match xs:
    case Nil{}:
      match n:
        case 0n:
          {==}
        case 1n+p:
          {==}
    case x <> t:
      match n:
        case 0n:
          {==}
        case 1n+p:
          take_le(t, p)

# No more lines than the limit allows.
def within_ok(+xs: List<&2, Main.Full>, limit: Maybe<&2, Nat>, +heads: List<&2, String>, +gone: List<&2, String>, +h: Rev.History()) -> {Main.log.fields.within(Main.fields.lines(Main.limited(xs, limit), heads, gone, h), limit) == True{} : Bool}:
  match limit:
    case None{}:
      {==}
    case Some{+n}:
      %Equal.sym(Nat, List.length(&2, String, Main.fields.lines(List.take(&2, Main.Full, xs, n), heads, gone, h)), List.length(&2, Main.Full, List.take(&2, Main.Full, xs, n)), lines_len(List.take(&2, Main.Full, xs, n), heads, gone, h)) : {Nat.is_le(_, n) == True{} : Bool}
      take_le(xs, n)

def kept_one(+L: List<&2, String>, b: Bool, +f: Main.Full, +rest: List<&2, Main.Full>, ho: {Bool.or(Bool.not(b), Rev.member(L, Main.id_of(f))) == True{} : Bool}, +hr: {ins(L, rest) == True{} : Bool}) -> {ins(L, Main.keep_full(b, f, rest)) == True{} : Bool}:
  match b:
    case True{}:
      AL.and_intro(Rev.member(L, Main.id_of(f)), ins(L, rest), ho, hr)
    case False{}:
      hr

# What every filter keeps of what the walk presents has its digest among
# these, where what it was shown does.
def kept_in(+fl: Main.Filter, +L: List<&2, String>, fs: List<&2, Main.Full>, +h: {PL.every(fl, L, fs) == True{} : Bool}) -> {ins(L, Main.kept(fl, fs)) == True{} : Bool}:
  match fs:
    case Nil{}:
      {==}
    case +f <> +rest:
      kept_one(L, Main.keeps(fl, f), f, Main.kept(fl, rest), Comp.and_left(PL.ok(fl, L, f), PL.every(fl, L, rest), h), kept_in(fl, L, rest, Comp.and_right(PL.ok(fl, L, f), PL.every(fl, L, rest), h)))

def take_in(+L: List<&2, String>, xs: List<&2, Main.Full>, n: Nat, +h: {ins(L, xs) == True{} : Bool}) -> {ins(L, List.take(&2, Main.Full, xs, n)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      match n:
        case 0n:
          {==}
        case 1n+p:
          AL.and_intro(Rev.member(L, Main.id_of(x)), ins(L, List.take(&2, Main.Full, t, p)), Comp.and_left(Rev.member(L, Main.id_of(x)), ins(L, t), h), take_in(L, t, p, Comp.and_right(Rev.member(L, Main.id_of(x)), ins(L, t), h)))

def limited_in(+L: List<&2, String>, +xs: List<&2, Main.Full>, limit: Maybe<&2, Nat>, +h: {ins(L, xs) == True{} : Bool}) -> {ins(L, Main.limited(xs, limit)) == True{} : Bool}:
  match limit:
    case None{}:
      h
    case Some{n}:
      take_in(L, xs, n, h)

def head_ok(b: Bool, +x: String, +R: List<&2, String>, +L: List<&2, String>, +h: {Tree.subset_ids(Rev.keep(b, x, R), L) == True{} : Bool}) -> {Bool.or(Bool.not(b), Rev.member(L, x)) == True{} : Bool}:
  match b:
    case True{}:
      Comp.and_left(Rev.member(L, x), Tree.subset_ids(R, L), h)
    case False{}:
      {==}

def rest_sub(b: Bool, +x: String, +R: List<&2, String>, +L: List<&2, String>, +h: {Tree.subset_ids(Rev.keep(b, x, R), L) == True{} : Bool}) -> {Tree.subset_ids(R, L) == True{} : Bool}:
  match b:
    case True{}:
      Comp.and_right(Rev.member(L, x), Tree.subset_ids(R, L), h)
    case False{}:
      h

# Each revision shown that a filter admits has its digest among those of
# the revisions shown that every filter admits.
def admitted_every(+fl: Main.Filter, xs: List<&2, Main.Full>, +L: List<&2, String>, +hs: {Tree.subset_ids(Main.log.admitted(fl, xs), L) == True{} : Bool}) -> {PL.every(fl, L, xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +f <> +rest:
      AL.and_intro(PL.ok(fl, L, f), PL.every(fl, L, rest),
        head_ok(Main.keeps(fl, f), Main.id_of(f), Main.log.admitted(fl, rest), L, hs),
        admitted_every(fl, rest, L, rest_sub(Main.keeps(fl, f), Main.id_of(f), Main.log.admitted(fl, rest), L, hs)))

# `log --fields` prints its header, and then a line for each revision it
# lists, each beginning with the digest of a revision it was shown that
# every filter admits, no more of them than the limit.
def fields_listed(+fs: List<&2, Main.Full>, +bs: List<&2, Bm.Bookmark>, +sp: Main.Span, +shown: List<&2, Main.Full>, +fl: Main.Filter, +limit: Maybe<&2, Nat>) -> {Main.log.fields.ok(Main.log.shown.lines(fs, bs, sp, shown, fl, True{}, limit), Main.log.admitted(fl, shown), limit) == True{} : Bool}:
  %Equal.sym(Bool, Bool.and(List.is_empty(&2, Main.Full, shown), False{}), False{}, AL.and_false_r(List.is_empty(&2, Main.Full, shown))) : {Main.log.fields.ok(Bool.pick(List<&2, String>, _, [Main.log.empty(fs, bs, sp)], Main.log.listed.lines(fs, Main.limited(Main.kept(fl, Main.presentation(shown)), limit), True{}, Main.selects(fl))), Main.log.admitted(fl, shown), limit) == True{} : Bool}
  B.and_tt(Main.log.fields.each(Main.fields.lines(Main.limited(Main.kept(fl, Main.presentation(shown)), limit), Rev.heads(Main.history(fs)), Rev.superseded(Main.history(fs)), Main.history(fs)), Main.log.admitted(fl, shown)), Main.log.fields.within(Main.fields.lines(Main.limited(Main.kept(fl, Main.presentation(shown)), limit), Rev.heads(Main.history(fs)), Rev.superseded(Main.history(fs)), Main.history(fs)), limit),
    fields_each(Main.limited(Main.kept(fl, Main.presentation(shown)), limit), Main.log.admitted(fl, shown), Rev.heads(Main.history(fs)), Rev.superseded(Main.history(fs)), Main.history(fs),
      limited_in(Main.log.admitted(fl, shown), Main.kept(fl, Main.presentation(shown)), limit,
        kept_in(fl, Main.log.admitted(fl, shown), Main.presentation(shown),
          PL.presentation_ok(fl, Main.log.admitted(fl, shown), shown, admitted_every(fl, shown, Main.log.admitted(fl, shown), GL.subset_refl(Main.log.admitted(fl, shown))))))),
    within_ok(Main.kept(fl, Main.presentation(shown)), limit, Rev.heads(Main.history(fs)), Rev.superseded(Main.history(fs)), Main.history(fs)))

def keep_len(b: Bool, -x: String, rest: List<&2, String>) -> {List.length(&2, String, Rev.keep(b, x, rest)) == Nat.add(Bool.pick(Nat, b, 1n, 0n), List.length(&2, String, rest)) : Nat}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def one_count(b: Bool, +added: Set(), +v: String) -> {Main.count_facts.one(added, False{}, v, b) == Bool.pick(Nat, b, 1n, 0n) : Nat}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# With nothing excluded, `log` counts every fact of a kind the revision
# states, once, whatever it added.
def counts_each(facts: List<&2, Rev.Header>, +key: String, +added: Set()) -> {Main.count_facts(facts, key, added, False{}) == List.length(&2, String, Rev.values_of(facts, key)) : Nat}:
  match facts:
    case Nil{}:
      {==}
    case Rev.Header{+k, +v} <> +rest:
      %Equal.sym(Nat, Main.count_facts.one(added, False{}, v, String.eq(k, key)), Bool.pick(Nat, String.eq(k, key), 1n, 0n), one_count(String.eq(k, key), added, v)) : {Nat.add(_, Main.count_facts(rest, key, added, False{})) == List.length(&2, String, Rev.keep(String.eq(k, key), v, Rev.values_of(rest, key))) : Nat}
      %Equal.sym(Nat, Main.count_facts(rest, key, added, False{}), List.length(&2, String, Rev.values_of(rest, key)), counts_each(rest, key, added)) : {Nat.add(Bool.pick(Nat, String.eq(k, key), 1n, 0n), _) == List.length(&2, String, Rev.keep(String.eq(k, key), v, Rev.values_of(rest, key))) : Nat}
      Equal.sym(Nat, List.length(&2, String, Rev.keep(String.eq(k, key), v, Rev.values_of(rest, key))), Nat.add(Bool.pick(Nat, String.eq(k, key), 1n, 0n), List.length(&2, String, Rev.values_of(rest, key))), keep_len(String.eq(k, key), v, Rev.values_of(rest, key)))

def put_len(a: Bool, -v: String, r: List<&2, String>) -> {Nat.add(Bool.pick(Nat, a, 0n, 1n), List.length(&2, String, r)) == List.length(&2, String, Rev.keep(Bool.not(a), v, r)) : Nat}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def unadded_one(~sets: @xs: List<&2, String> -> @x: String -> {Main.was_added(Set.from_list(xs), x) == Rev.member(xs, x) : Bool}, b: Bool, +F: List<&2, String>, +v: String, +r: List<&2, String>) -> {Nat.add(Main.count_facts.one(Set.from_list(F), True{}, v, b), List.length(&2, String, Main.facts.unadded.of(F, r))) == List.length(&2, String, Main.facts.unadded.of(F, Rev.keep(b, v, r))) : Nat}:
  match b:
    case False{}:
      {==}
    case True{}:
      %Equal.sym(Bool, Main.was_added(Set.from_list(F), T.word(v)), Rev.member(F, T.word(v)), sets(F, T.word(v))) : {Nat.add(Bool.pick(Nat, _, 0n, 1n), List.length(&2, String, Main.facts.unadded.of(F, r))) == List.length(&2, String, Rev.keep(Bool.not(Rev.member(F, T.word(v))), v, Main.facts.unadded.of(F, r))) : Nat}
      put_len(Rev.member(F, T.word(v)), v, Main.facts.unadded.of(F, r))

# Where the set answers exactly the files these name, a fact set aside for
# a file added is one about a file they name, and every other is counted.
def counts_unadded(~sets: @xs: List<&2, String> -> @x: String -> {Main.was_added(Set.from_list(xs), x) == Rev.member(xs, x) : Bool}, facts: List<&2, Rev.Header>, +key: String, +F: List<&2, String>) -> {Main.count_facts(facts, key, Set.from_list(F), True{}) == List.length(&2, String, Main.facts.unadded.of(F, Rev.values_of(facts, key))) : Nat}:
  match facts:
    case Nil{}:
      {==}
    case Rev.Header{+k, +v} <> +rest:
      %Equal.sym(Nat, Main.count_facts(rest, key, Set.from_list(F), True{}), List.length(&2, String, Main.facts.unadded.of(F, Rev.values_of(rest, key))), counts_unadded(~sets, rest, key, F)) : {Nat.add(Main.count_facts.one(Set.from_list(F), True{}, v, String.eq(k, key)), _) == List.length(&2, String, Main.facts.unadded.of(F, Rev.keep(String.eq(k, key), v, Rev.values_of(rest, key)))) : Nat}
      unadded_one(~sets, String.eq(k, key), F, v, Rev.values_of(rest, key))

# A log entry's figures, each what its revision states: the adds, moves,
# drops and edits all counted, and the modes, links and bytes counted but
# for a file an `add` fact names.
def figures_counted(~sets: @xs: List<&2, String> -> @x: String -> {Main.was_added(Set.from_list(xs), x) == Rev.member(xs, x) : Bool}, +facts: List<&2, Rev.Header>) -> {Main.tree_facts.figures(facts) == [Main.Figure{"added", Main.facts.stated(facts, "add")}, Main.Figure{"moved", Main.facts.stated(facts, "move")}, Main.Figure{"mode", Main.facts.unadded(facts, "mode")}, Main.Figure{"link", Main.facts.unadded(facts, "link")}, Main.Figure{"dropped", Main.facts.stated(facts, "drop")}, Main.Figure{"edited", Main.facts.stated(facts, "edit")}, Main.Figure{"stored", Main.facts.unadded(facts, "bytes")}] : List<&2, Main.Figure>}:
  +S = Set.from_list(Rev.files_of(facts, "add"))
  +F = Rev.files_of(facts, "add")
  %Equal.sym(Nat, Main.count_facts(facts, "add", S, False{}), Main.facts.stated(facts, "add"), counts_each(facts, "add", S)) : {[Main.Figure{"added", _}, Main.Figure{"moved", Main.count_facts(facts, "move", S, False{})}, Main.Figure{"mode", Main.count_facts(facts, "mode", S, True{})}, Main.Figure{"link", Main.count_facts(facts, "link", S, True{})}, Main.Figure{"dropped", Main.count_facts(facts, "drop", S, False{})}, Main.Figure{"edited", Main.count_facts(facts, "edit", S, False{})}, Main.Figure{"stored", Main.count_facts(facts, "bytes", S, True{})}] == [Main.Figure{"added", Main.facts.stated(facts, "add")}, Main.Figure{"moved", Main.facts.stated(facts, "move")}, Main.Figure{"mode", Main.facts.unadded(facts, "mode")}, Main.Figure{"link", Main.facts.unadded(facts, "link")}, Main.Figure{"dropped", Main.facts.stated(facts, "drop")}, Main.Figure{"edited", Main.facts.stated(facts, "edit")}, Main.Figure{"stored", Main.facts.unadded(facts, "bytes")}] : List<&2, Main.Figure>}
  %Equal.sym(Nat, Main.count_facts(facts, "move", S, False{}), Main.facts.stated(facts, "move"), counts_each(facts, "move", S)) : {[Main.Figure{"added", Main.facts.stated(facts, "add")}, Main.Figure{"moved", _}, Main.Figure{"mode", Main.count_facts(facts, "mode", S, True{})}, Main.Figure{"link", Main.count_facts(facts, "link", S, True{})}, Main.Figure{"dropped", Main.count_facts(facts, "drop", S, False{})}, Main.Figure{"edited", Main.count_facts(facts, "edit", S, False{})}, Main.Figure{"stored", Main.count_facts(facts, "bytes", S, True{})}] == [Main.Figure{"added", Main.facts.stated(facts, "add")}, Main.Figure{"moved", Main.facts.stated(facts, "move")}, Main.Figure{"mode", Main.facts.unadded(facts, "mode")}, Main.Figure{"link", Main.facts.unadded(facts, "link")}, Main.Figure{"dropped", Main.facts.stated(facts, "drop")}, Main.Figure{"edited", Main.facts.stated(facts, "edit")}, Main.Figure{"stored", Main.facts.unadded(facts, "bytes")}] : List<&2, Main.Figure>}
  %Equal.sym(Nat, Main.count_facts(facts, "mode", S, True{}), Main.facts.unadded(facts, "mode"), counts_unadded(~sets, facts, "mode", F)) : {[Main.Figure{"added", Main.facts.stated(facts, "add")}, Main.Figure{"moved", Main.facts.stated(facts, "move")}, Main.Figure{"mode", _}, Main.Figure{"link", Main.count_facts(facts, "link", S, True{})}, Main.Figure{"dropped", Main.count_facts(facts, "drop", S, False{})}, Main.Figure{"edited", Main.count_facts(facts, "edit", S, False{})}, Main.Figure{"stored", Main.count_facts(facts, "bytes", S, True{})}] == [Main.Figure{"added", Main.facts.stated(facts, "add")}, Main.Figure{"moved", Main.facts.stated(facts, "move")}, Main.Figure{"mode", Main.facts.unadded(facts, "mode")}, Main.Figure{"link", Main.facts.unadded(facts, "link")}, Main.Figure{"dropped", Main.facts.stated(facts, "drop")}, Main.Figure{"edited", Main.facts.stated(facts, "edit")}, Main.Figure{"stored", Main.facts.unadded(facts, "bytes")}] : List<&2, Main.Figure>}
  %Equal.sym(Nat, Main.count_facts(facts, "link", S, True{}), Main.facts.unadded(facts, "link"), counts_unadded(~sets, facts, "link", F)) : {[Main.Figure{"added", Main.facts.stated(facts, "add")}, Main.Figure{"moved", Main.facts.stated(facts, "move")}, Main.Figure{"mode", Main.facts.unadded(facts, "mode")}, Main.Figure{"link", _}, Main.Figure{"dropped", Main.count_facts(facts, "drop", S, False{})}, Main.Figure{"edited", Main.count_facts(facts, "edit", S, False{})}, Main.Figure{"stored", Main.count_facts(facts, "bytes", S, True{})}] == [Main.Figure{"added", Main.facts.stated(facts, "add")}, Main.Figure{"moved", Main.facts.stated(facts, "move")}, Main.Figure{"mode", Main.facts.unadded(facts, "mode")}, Main.Figure{"link", Main.facts.unadded(facts, "link")}, Main.Figure{"dropped", Main.facts.stated(facts, "drop")}, Main.Figure{"edited", Main.facts.stated(facts, "edit")}, Main.Figure{"stored", Main.facts.unadded(facts, "bytes")}] : List<&2, Main.Figure>}
  %Equal.sym(Nat, Main.count_facts(facts, "drop", S, False{}), Main.facts.stated(facts, "drop"), counts_each(facts, "drop", S)) : {[Main.Figure{"added", Main.facts.stated(facts, "add")}, Main.Figure{"moved", Main.facts.stated(facts, "move")}, Main.Figure{"mode", Main.facts.unadded(facts, "mode")}, Main.Figure{"link", Main.facts.unadded(facts, "link")}, Main.Figure{"dropped", _}, Main.Figure{"edited", Main.count_facts(facts, "edit", S, False{})}, Main.Figure{"stored", Main.count_facts(facts, "bytes", S, True{})}] == [Main.Figure{"added", Main.facts.stated(facts, "add")}, Main.Figure{"moved", Main.facts.stated(facts, "move")}, Main.Figure{"mode", Main.facts.unadded(facts, "mode")}, Main.Figure{"link", Main.facts.unadded(facts, "link")}, Main.Figure{"dropped", Main.facts.stated(facts, "drop")}, Main.Figure{"edited", Main.facts.stated(facts, "edit")}, Main.Figure{"stored", Main.facts.unadded(facts, "bytes")}] : List<&2, Main.Figure>}
  %Equal.sym(Nat, Main.count_facts(facts, "edit", S, False{}), Main.facts.stated(facts, "edit"), counts_each(facts, "edit", S)) : {[Main.Figure{"added", Main.facts.stated(facts, "add")}, Main.Figure{"moved", Main.facts.stated(facts, "move")}, Main.Figure{"mode", Main.facts.unadded(facts, "mode")}, Main.Figure{"link", Main.facts.unadded(facts, "link")}, Main.Figure{"dropped", Main.facts.stated(facts, "drop")}, Main.Figure{"edited", _}, Main.Figure{"stored", Main.count_facts(facts, "bytes", S, True{})}] == [Main.Figure{"added", Main.facts.stated(facts, "add")}, Main.Figure{"moved", Main.facts.stated(facts, "move")}, Main.Figure{"mode", Main.facts.unadded(facts, "mode")}, Main.Figure{"link", Main.facts.unadded(facts, "link")}, Main.Figure{"dropped", Main.facts.stated(facts, "drop")}, Main.Figure{"edited", Main.facts.stated(facts, "edit")}, Main.Figure{"stored", Main.facts.unadded(facts, "bytes")}] : List<&2, Main.Figure>}
  %Equal.sym(Nat, Main.count_facts(facts, "bytes", S, True{}), Main.facts.unadded(facts, "bytes"), counts_unadded(~sets, facts, "bytes", F)) : {[Main.Figure{"added", Main.facts.stated(facts, "add")}, Main.Figure{"moved", Main.facts.stated(facts, "move")}, Main.Figure{"mode", Main.facts.unadded(facts, "mode")}, Main.Figure{"link", Main.facts.unadded(facts, "link")}, Main.Figure{"dropped", Main.facts.stated(facts, "drop")}, Main.Figure{"edited", Main.facts.stated(facts, "edit")}, Main.Figure{"stored", _}] == [Main.Figure{"added", Main.facts.stated(facts, "add")}, Main.Figure{"moved", Main.facts.stated(facts, "move")}, Main.Figure{"mode", Main.facts.unadded(facts, "mode")}, Main.Figure{"link", Main.facts.unadded(facts, "link")}, Main.Figure{"dropped", Main.facts.stated(facts, "drop")}, Main.Figure{"edited", Main.facts.stated(facts, "edit")}, Main.Figure{"stored", Main.facts.unadded(facts, "bytes")}] : List<&2, Main.Figure>}
  {==}

def some_file(-a: String, -b: String, h: {Done{Some{a}} == Done{Some{b}} : Result<&2, &2, Main.Refused, Maybe<&2, String>>}) -> {a == b : String}:
  Equal.cong(Result<&2, &2, Main.Refused, Maybe<&2, String>>, String, r => Maybe.default(&2, String, Result.default(&2, &2, Main.Refused, Maybe<&2, String>, r, None{}), a), Done{Some{a}}, Done{Some{b}}, h)

def at_held(+fs: List<&2, Main.Full>, +bs: List<&2, Bm.Bookmark>, +p: String, +at: String, r: Result<&2, &2, Main.Refused, String>, +er: {Result.bind(&2, &2, Main.Refused, Tree.Tree(), String, Main.tree.r(fs, at), t => Main.file_in.r(at, bs, p, t)) == r : Result<&2, &2, Main.Refused, String>}, +file: String, e: {Result.map(&2, &2, Main.Refused, String, Maybe<&2, String>, f => Some{f}, r) == Done{Some{file}} : Result<&2, &2, Main.Refused, Maybe<&2, String>>}) -> {Main.tree.holds.r(Main.tree.r(fs, at), file) == True{} : Bool}:
  match r:
    case Fail{x}:
      Empty.absurd({Main.tree.holds.r(Main.tree.r(fs, at), file) == True{} : Bool}, B.fail_done(Maybe<&2, String>, x, Some{file}, e))
    case Done{+x}:
      %some_file(x, file, e) : {Main.tree.holds.r(Main.tree.r(fs, at), _) == True{} : Bool}
      ShowL.sf_bind(fs, bs, at, p, Main.tree.r(fs, at), {==}, x, er)

def followed_at(+fs: List<&2, Main.Full>, +bs: List<&2, Bm.Bookmark>, +sp: Main.Span, +p: String, +at: String, r: Result<&2, &2, Main.Refused, String>, +er: {Main.read_at.r(fs, bs, p, sp) == r : Result<&2, &2, Main.Refused, String>}, +ea: {Main.read_at.r(fs, bs, p, sp) == Done{at} : Result<&2, &2, Main.Refused, String>}, +file: String, e: {Result.bind(&2, &2, Main.Refused, String, Maybe<&2, String>, r, a => Main.followed.at.r(fs, bs, p, a)) == Done{Some{file}} : Result<&2, &2, Main.Refused, Maybe<&2, String>>}) -> {Main.tree.holds.r(Main.tree.r(fs, at), file) == True{} : Bool}:
  match r:
    case Fail{x}:
      Empty.absurd({Main.tree.holds.r(Main.tree.r(fs, at), file) == True{} : Bool}, B.fail_done(Maybe<&2, String>, x, Some{file}, e))
    case Done{+a}:
      +same = B.done_eq(String, a, at, Equal.trans(Result<&2, &2, Main.Refused, String>, Done{a}, Main.read_at.r(fs, bs, p, sp), Done{at}, Equal.sym(Result<&2, &2, Main.Refused, String>, Main.read_at.r(fs, bs, p, sp), Done{a}, er), ea))
      %same : {Main.tree.holds.r(Main.tree.r(fs, _), file) == True{} : Bool}
      at_held(fs, bs, p, a, Result.bind(&2, &2, Main.Refused, Tree.Tree(), String, Main.tree.r(fs, a), t => Main.file_in.r(a, bs, p, t)), {==}, file, e)

# The file `log --path` follows is one the tree holds at the revision the
# path is read at.
def followed_held(+fs: List<&2, Main.Full>, +bs: List<&2, Bm.Bookmark>, +sp: Main.Span, +p: String, +at: String, +file: String, +ea: {Main.read_at.r(fs, bs, p, sp) == Done{at} : Result<&2, &2, Main.Refused, String>}, e: {Main.followed.r(fs, bs, sp, Some{p}) == Done{Some{file}} : Result<&2, &2, Main.Refused, Maybe<&2, String>>}) -> {Main.tree.holds.r(Main.tree.r(fs, at), file) == True{} : Bool}:
  followed_at(fs, bs, sp, p, at, Main.read_at.r(fs, bs, p, sp), {==}, ea, file, e)
