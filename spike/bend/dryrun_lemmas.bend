# What `export -n` says it would do. Read back, its `write` lines name every
# path of the target's tree once, in path order, and nothing else; its
# `would withdraw` lines name every file a copy being updated gives up, in
# the order they go. And `--files-only -n`'s `write` lines name every path
# where the tree holds a file that is no link, and are what the real run
# names as `wrote`.
import Base
import ./export.bend as Export
import ./commands.bend as Main
import ./tree.bend as Tree
import ./revision.bend as Rev
import ./text.bend as T
import ./store.bend as Store
import ./prune.bend as Prune
import ./receive.bend as Receive
import ./bookmark.bend as Bm
import ./export_lemmas.bend as ExportL
import ./sort_lemmas.bend as SortL
import ./graph_lemmas.bend as GL
import ./rewrite_lemmas.bend as RewriteL
import ./fetch_lemmas.bend as FetchL
import ./forget_lemmas.bend as ForgetL
import ./receive_lemmas.bend as ReceiveL
import ./composition_lemmas.bend as Comp
import ./string_lemmas.bend as SL
import ./placed_lemmas.bend as PlacedL
import ./folder.bend as Folder

# Lines no prefix begins
# ----------------------

def quiet(ls: List<&2, String>, +pre: String) -> Bool:
  match ls:
    case Nil{}:
      True{}
    case +l <> rest:
      Bool.and(Bool.not(String.starts_with(l, pre)), quiet(rest, pre))

def keep_false(b: Bool, +l: String, +n: Nat, -rest: List<&2, String>, h: {Bool.not(b) == True{} : Bool}) -> {Export.said.keep(b, l, n, rest) == rest : List<&2, String>}:
  match b:
    case True{}:
      Empty.absurd({String.drop(l, n) <> rest == rest : List<&2, String>}, Comp.false_true(h))
    case False{}:
      {==}

def after_quiet(ls: List<&2, String>, +pre: String, +h: {quiet(ls, pre) == True{} : Bool}) -> {Export.said.after(ls, pre) == Nil{} : List<&2, String>}:
  match ls:
    case Nil{}:
      {==}
    case +l <> +rest:
      %Equal.sym(List<&2, String>, Export.said.keep(String.starts_with(l, pre), l, String.length(pre), Export.said.after(rest, pre)), Export.said.after(rest, pre), keep_false(String.starts_with(l, pre), l, String.length(pre), Export.said.after(rest, pre), ExportL.and_l(Bool.not(String.starts_with(l, pre)), quiet(rest, pre), h))) : {_ == Nil{} : List<&2, String>}
      after_quiet(rest, pre, ExportL.and_r(Bool.not(String.starts_with(l, pre)), quiet(rest, pre), h))

def quiet_app(xs: List<&2, String>, +ys: List<&2, String>, +pre: String, +hx: {quiet(xs, pre) == True{} : Bool}, hy: {quiet(ys, pre) == True{} : Bool}) -> {quiet(List.append(&2, String, xs, ys), pre) == True{} : Bool}:
  match xs:
    case Nil{}:
      hy
    case +l <> +rest:
      ExportL.and_tt(Bool.not(String.starts_with(l, pre)), quiet(List.append(&2, String, rest, ys), pre), ExportL.and_l(Bool.not(String.starts_with(l, pre)), quiet(rest, pre), hx), quiet_app(rest, ys, pre, ExportL.and_r(Bool.not(String.starts_with(l, pre)), quiet(rest, pre), hx), hy))

def quiet_if(b: Bool, +l: String, +pre: String, h: {String.starts_with(l, pre) == False{} : Bool}) -> {quiet(Export.line.if(b, l), pre) == True{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(Bool, String.starts_with(l, pre), False{}, h) : {Bool.and(Bool.not(_), True{}) == True{} : Bool}
      {==}
    case False{}:
      {==}

def keep_app(b: Bool, +l: String, +n: Nat, -xs: List<&2, String>, -ys: List<&2, String>) -> {Export.said.keep(b, l, n, List.append(&2, String, xs, ys)) == List.append(&2, String, Export.said.keep(b, l, n, xs), ys) : List<&2, String>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def after_app(xs: List<&2, String>, +ys: List<&2, String>, +pre: String) -> {Export.said.after(List.append(&2, String, xs, ys), pre) == List.append(&2, String, Export.said.after(xs, pre), Export.said.after(ys, pre)) : List<&2, String>}:
  match xs:
    case Nil{}:
      {==}
    case +l <> +rest:
      %Equal.sym(List<&2, String>, Export.said.after(List.append(&2, String, rest, ys), pre), List.append(&2, String, Export.said.after(rest, pre), Export.said.after(ys, pre)), after_app(rest, ys, pre)) : {Export.said.keep(String.starts_with(l, pre), l, String.length(pre), _) == List.append(&2, String, Export.said.keep(String.starts_with(l, pre), l, String.length(pre), Export.said.after(rest, pre)), Export.said.after(ys, pre)) : List<&2, String>}
      keep_app(String.starts_with(l, pre), l, String.length(pre), Export.said.after(rest, pre), Export.said.after(ys, pre))

def not_false(b: Bool, h: {b == False{} : Bool}) -> {Bool.not(b) == True{} : Bool}:
  %Equal.sym(Bool, b, False{}, h) : {Bool.not(_) == True{} : Bool}
  {==}

# Ten count lines, seven of them said only when there is something to
# count, none of them beginning with the prefix.
def counts_quiet(+b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +l1: String, +l2: String, +l3: String, +l4: String, +l5: String, +l6: String, +l7: String, +l8: String, +l9: String, +l10: String, +pre: String, h1: {String.starts_with(l1, pre) == False{} : Bool}, h2: {String.starts_with(l2, pre) == False{} : Bool}, h3: {String.starts_with(l3, pre) == False{} : Bool}, h4: {String.starts_with(l4, pre) == False{} : Bool}, h5: {String.starts_with(l5, pre) == False{} : Bool}, h6: {String.starts_with(l6, pre) == False{} : Bool}, h7: {String.starts_with(l7, pre) == False{} : Bool}, h8: {String.starts_with(l8, pre) == False{} : Bool}, h9: {String.starts_with(l9, pre) == False{} : Bool}, h10: {String.starts_with(l10, pre) == False{} : Bool}) -> {quiet(List.concat(&2, String, [[l1, l2, l3], Export.line.if(b1, l4), Export.line.if(b2, l5), Export.line.if(b3, l6), Export.line.if(b4, l7), Export.line.if(b5, l8), Export.line.if(b6, l9), Export.line.if(b7, l10)]), pre) == True{} : Bool}:
  +r7 = List.concat(&2, String, [Export.line.if(b7, l10)])
  +r6 = List.concat(&2, String, [Export.line.if(b6, l9), Export.line.if(b7, l10)])
  +r5 = List.concat(&2, String, [Export.line.if(b5, l8), Export.line.if(b6, l9), Export.line.if(b7, l10)])
  +r4 = List.concat(&2, String, [Export.line.if(b4, l7), Export.line.if(b5, l8), Export.line.if(b6, l9), Export.line.if(b7, l10)])
  +r3 = List.concat(&2, String, [Export.line.if(b3, l6), Export.line.if(b4, l7), Export.line.if(b5, l8), Export.line.if(b6, l9), Export.line.if(b7, l10)])
  +r2 = List.concat(&2, String, [Export.line.if(b2, l5), Export.line.if(b3, l6), Export.line.if(b4, l7), Export.line.if(b5, l8), Export.line.if(b6, l9), Export.line.if(b7, l10)])
  +r1 = List.concat(&2, String, [Export.line.if(b1, l4), Export.line.if(b2, l5), Export.line.if(b3, l6), Export.line.if(b4, l7), Export.line.if(b5, l8), Export.line.if(b6, l9), Export.line.if(b7, l10)])
  ExportL.and_tt(Bool.not(String.starts_with(l1, pre)), quiet(l2 <> l3 <> r1, pre), not_false(String.starts_with(l1, pre), h1),
    ExportL.and_tt(Bool.not(String.starts_with(l2, pre)), quiet(l3 <> r1, pre), not_false(String.starts_with(l2, pre), h2),
      ExportL.and_tt(Bool.not(String.starts_with(l3, pre)), quiet(r1, pre), not_false(String.starts_with(l3, pre), h3),
        quiet_app(Export.line.if(b1, l4), r2, pre, quiet_if(b1, l4, pre, h4),
          quiet_app(Export.line.if(b2, l5), r3, pre, quiet_if(b2, l5, pre, h5),
            quiet_app(Export.line.if(b3, l6), r4, pre, quiet_if(b3, l6, pre, h6),
              quiet_app(Export.line.if(b4, l7), r5, pre, quiet_if(b4, l7, pre, h7),
                quiet_app(Export.line.if(b5, l8), r6, pre, quiet_if(b5, l8, pre, h8),
                  quiet_app(Export.line.if(b6, l9), r7, pre, quiet_if(b6, l9, pre, h9),
                    quiet_app(Export.line.if(b7, l10), Nil{}, pre, quiet_if(b7, l10, pre, h10), {==}))))))))))

# What `export -n` counts begins neither `write` nor `would withdraw`.
def counts_write(c: Export.Counts, p: Export.Plan, +carried: Nat) -> {quiet(Export.said.counts("would export", "would hold back", "would leave", "would carry", c, p, carried), "write   ") == True{} : Bool}:
  match c:
    case Export.Counts{+nr, +nd, +np, +nf}:
      match p:
        case Export.Plan{revs, docs, pays, forg, paths, +rules, +w, n, res}:
          match n:
            case Export.Travel{+ns, +wn, +y}:
              counts_quiet(Export.nonzero(nf), Bool.or(Export.nonzero(List.length(&2, Receive.Ruled, rules)), Export.nonzero(w)), Export.nonzero(w), Bool.or(Export.nonzero(List.length(&2, Bm.Bookmark, ns)), Export.nonzero(wn)), Export.nonzero(wn), Export.nonzero(y), Export.nonzero(carried),
                Export.count.line("would export", nr, "revisions"), Export.count.line("would export", nd, "operation documents"), Export.count.line("would export", np, "payloads"),
                Export.count.line("would export", nf, "forgetting documents"), Export.count.line("would export", List.length(&2, Receive.Ruled, rules), "rules"), Export.count.line("would hold back", w, "private rules"),
                Export.count.line("would export", List.length(&2, Bm.Bookmark, ns), "bookmarks"), Export.count.line("would hold back", wn, "private bookmarks"), Export.count.line("would leave", y, "bookmarks pointing past this target"),
                Export.count.line("would carry", carried, "files another tool wrote"), "write   ",
                {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})

def counts_withdraw(c: Export.Counts, p: Export.Plan, +carried: Nat) -> {quiet(Export.said.counts("would export", "would hold back", "would leave", "would carry", c, p, carried), "would withdraw history/") == True{} : Bool}:
  match c:
    case Export.Counts{+nr, +nd, +np, +nf}:
      match p:
        case Export.Plan{revs, docs, pays, forg, paths, +rules, +w, n, res}:
          match n:
            case Export.Travel{+ns, +wn, +y}:
              counts_quiet(Export.nonzero(nf), Bool.or(Export.nonzero(List.length(&2, Receive.Ruled, rules)), Export.nonzero(w)), Export.nonzero(w), Bool.or(Export.nonzero(List.length(&2, Bm.Bookmark, ns)), Export.nonzero(wn)), Export.nonzero(wn), Export.nonzero(y), Export.nonzero(carried),
                Export.count.line("would export", nr, "revisions"), Export.count.line("would export", nd, "operation documents"), Export.count.line("would export", np, "payloads"),
                Export.count.line("would export", nf, "forgetting documents"), Export.count.line("would export", List.length(&2, Receive.Ruled, rules), "rules"), Export.count.line("would hold back", w, "private rules"),
                Export.count.line("would export", List.length(&2, Bm.Bookmark, ns), "bookmarks"), Export.count.line("would hold back", wn, "private bookmarks"), Export.count.line("would leave", y, "bookmarks pointing past this target"),
                Export.count.line("would carry", carried, "files another tool wrote"), "would withdraw history/",
                {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})

def withdrawn_write(ws: List<&2, String>) -> {quiet(Export.withdrawn.said(ws), "write   ") == True{} : Bool}:
  match ws:
    case Nil{}:
      {==}
    case w <> rest:
      withdrawn_write(rest)

def paths_withdraw(ps: List<&2, String>) -> {quiet(Export.paths.said("write  ", ps), "would withdraw history/") == True{} : Bool}:
  match ps:
    case Nil{}:
      {==}
    case p <> rest:
      paths_withdraw(rest)

def sw_nil(s: String) -> {String.starts_with(s, "") == True{} : Bool}:
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

# Read back, the `would withdraw` lines are the files given up.
def withdrawn_back(ws: List<&2, String>) -> {Export.said.after(Export.withdrawn.said(ws), "would withdraw history/") == ws : List<&2, String>}:
  match ws:
    case Nil{}:
      {==}
    case +w <> rest:
      %Equal.sym(Bool, String.starts_with(w, ""), True{}, sw_nil(w)) : {Export.said.keep(_, "would withdraw history/" ++ w, 23n, Export.said.after(Export.withdrawn.said(rest), "would withdraw history/")) == w <> rest : List<&2, String>}
      %Equal.sym(String, String.drop(w, 0n), w, drop_zero(w)) : {_ <> Export.said.after(Export.withdrawn.said(rest), "would withdraw history/") == w <> rest : List<&2, String>}
      %Equal.sym(List<&2, String>, Export.said.after(Export.withdrawn.said(rest), "would withdraw history/"), rest, withdrawn_back(rest)) : {w <> _ == w <> rest : List<&2, String>}
      {==}

# Read back, the `write` lines are the paths.
def paths_back(ps: List<&2, String>) -> {Export.said.after(Export.paths.said("write  ", ps), "write   ") == ps : List<&2, String>}:
  match ps:
    case Nil{}:
      {==}
    case +p <> rest:
      %Equal.sym(Bool, String.starts_with(p, ""), True{}, sw_nil(p)) : {Export.said.keep(_, "write  " ++ " " ++ p, 8n, Export.said.after(Export.paths.said("write  ", rest), "write   ")) == p <> rest : List<&2, String>}
      %Equal.sym(String, String.drop(p, 0n), p, drop_zero(p)) : {_ <> Export.said.after(Export.paths.said("write  ", rest), "write   ") == p <> rest : List<&2, String>}
      %Equal.sym(List<&2, String>, Export.said.after(Export.paths.said("write  ", rest), "write   "), rest, paths_back(rest)) : {p <> _ == p <> rest : List<&2, String>}
      {==}

def last_quiet(u: Bool, +spelled: String, +into: String, +pre: String, h: {String.starts_with("would " ++ Export.updating.said(u) ++ " of " ++ spelled ++ " at " ++ into, pre) == False{} : Bool}) -> {quiet(["would " ++ Export.updating.said(u) ++ " of " ++ spelled ++ " at " ++ into], pre) == True{} : Bool}:
  %Equal.sym(Bool, String.starts_with("would " ++ Export.updating.said(u) ++ " of " ++ spelled ++ " at " ++ into, pre), False{}, h) : {Bool.and(Bool.not(_), True{}) == True{} : Bool}
  {==}

def last_write(u: Bool, +spelled: String, +into: String) -> {String.starts_with("would " ++ Export.updating.said(u) ++ " of " ++ spelled ++ " at " ++ into, "write   ") == False{} : Bool}:
  match u:
    case True{}:
      {==}
    case False{}:
      {==}

def last_withdraw(u: Bool, +spelled: String, +into: String) -> {String.starts_with("would " ++ Export.updating.said(u) ++ " of " ++ spelled ++ " at " ++ into, "would withdraw history/") == False{} : Bool}:
  match u:
    case True{}:
      {==}
    case False{}:
      {==}

# Five groups of lines, three of them quiet: what the others say, in order.
def five_after(+c: List<&2, String>, +w: List<&2, String>, +d: List<&2, String>, +ps: List<&2, String>, +l: List<&2, String>, +pre: String, +qc: {quiet(c, pre) == True{} : Bool}, +qd: {quiet(d, pre) == True{} : Bool}, +ql: {quiet(l, pre) == True{} : Bool}) -> {Export.said.after(List.concat(&2, String, [c, w, d, ps, l]), pre) == List.append(&2, String, Export.said.after(w, pre), Export.said.after(ps, pre)) : List<&2, String>}:
  %Equal.sym(List<&2, String>, Export.said.after(List.append(&2, String, c, List.append(&2, String, w, List.append(&2, String, d, List.append(&2, String, ps, List.append(&2, String, l, Nil{}))))), pre), List.append(&2, String, Export.said.after(c, pre), Export.said.after(List.append(&2, String, w, List.append(&2, String, d, List.append(&2, String, ps, List.append(&2, String, l, Nil{})))), pre)), after_app(c, List.append(&2, String, w, List.append(&2, String, d, List.append(&2, String, ps, List.append(&2, String, l, Nil{})))), pre)) : {_ == List.append(&2, String, Export.said.after(w, pre), Export.said.after(ps, pre)) : List<&2, String>}
  %Equal.sym(List<&2, String>, Export.said.after(c, pre), Nil{}, after_quiet(c, pre, qc)) : {List.append(&2, String, _, Export.said.after(List.append(&2, String, w, List.append(&2, String, d, List.append(&2, String, ps, List.append(&2, String, l, Nil{})))), pre)) == List.append(&2, String, Export.said.after(w, pre), Export.said.after(ps, pre)) : List<&2, String>}
  %Equal.sym(List<&2, String>, Export.said.after(List.append(&2, String, w, List.append(&2, String, d, List.append(&2, String, ps, List.append(&2, String, l, Nil{})))), pre), List.append(&2, String, Export.said.after(w, pre), Export.said.after(List.append(&2, String, d, List.append(&2, String, ps, List.append(&2, String, l, Nil{}))), pre)), after_app(w, List.append(&2, String, d, List.append(&2, String, ps, List.append(&2, String, l, Nil{}))), pre)) : {_ == List.append(&2, String, Export.said.after(w, pre), Export.said.after(ps, pre)) : List<&2, String>}
  %Equal.sym(List<&2, String>, Export.said.after(List.append(&2, String, d, List.append(&2, String, ps, List.append(&2, String, l, Nil{}))), pre), List.append(&2, String, Export.said.after(d, pre), Export.said.after(List.append(&2, String, ps, List.append(&2, String, l, Nil{})), pre)), after_app(d, List.append(&2, String, ps, List.append(&2, String, l, Nil{})), pre)) : {List.append(&2, String, Export.said.after(w, pre), _) == List.append(&2, String, Export.said.after(w, pre), Export.said.after(ps, pre)) : List<&2, String>}
  %Equal.sym(List<&2, String>, Export.said.after(d, pre), Nil{}, after_quiet(d, pre, qd)) : {List.append(&2, String, Export.said.after(w, pre), List.append(&2, String, _, Export.said.after(List.append(&2, String, ps, List.append(&2, String, l, Nil{})), pre))) == List.append(&2, String, Export.said.after(w, pre), Export.said.after(ps, pre)) : List<&2, String>}
  %Equal.sym(List<&2, String>, Export.said.after(List.append(&2, String, ps, List.append(&2, String, l, Nil{})), pre), List.append(&2, String, Export.said.after(ps, pre), Export.said.after(List.append(&2, String, l, Nil{}), pre)), after_app(ps, List.append(&2, String, l, Nil{}), pre)) : {List.append(&2, String, Export.said.after(w, pre), _) == List.append(&2, String, Export.said.after(w, pre), Export.said.after(ps, pre)) : List<&2, String>}
  %Equal.sym(List<&2, String>, Export.said.after(List.append(&2, String, l, Nil{}), pre), List.append(&2, String, Export.said.after(l, pre), Export.said.after(Nil{}, pre)), after_app(l, Nil{}, pre)) : {List.append(&2, String, Export.said.after(w, pre), List.append(&2, String, Export.said.after(ps, pre), _)) == List.append(&2, String, Export.said.after(w, pre), Export.said.after(ps, pre)) : List<&2, String>}
  %Equal.sym(List<&2, String>, Export.said.after(l, pre), Nil{}, after_quiet(l, pre, ql)) : {List.append(&2, String, Export.said.after(w, pre), List.append(&2, String, Export.said.after(ps, pre), List.append(&2, String, _, Nil{}))) == List.append(&2, String, Export.said.after(w, pre), Export.said.after(ps, pre)) : List<&2, String>}
  %Equal.sym(List<&2, String>, List.append(&2, String, Export.said.after(ps, pre), Nil{}), Export.said.after(ps, pre), SortL.lapp_nil(String, Export.said.after(ps, pre))) : {List.append(&2, String, Export.said.after(w, pre), _) == List.append(&2, String, Export.said.after(w, pre), Export.said.after(ps, pre)) : List<&2, String>}
  {==}

def after_pw(+p: Export.Plan, +ws: List<&2, String>) -> {List.append(&2, String, Export.said.after(Export.withdrawn.said(ws), "would withdraw history/"), Export.said.after(Export.paths.said("write  ", Export.plan.paths(p)), "would withdraw history/")) == ws : List<&2, String>}:
  %Equal.sym(List<&2, String>, Export.said.after(Export.withdrawn.said(ws), "would withdraw history/"), ws, withdrawn_back(ws)) : {List.append(&2, String, _, Export.said.after(Export.paths.said("write  ", Export.plan.paths(p)), "would withdraw history/")) == ws : List<&2, String>}
  %Equal.sym(List<&2, String>, Export.said.after(Export.paths.said("write  ", Export.plan.paths(p)), "would withdraw history/"), Nil{}, after_quiet(Export.paths.said("write  ", Export.plan.paths(p)), "would withdraw history/", paths_withdraw(Export.plan.paths(p)))) : {List.append(&2, String, ws, _) == ws : List<&2, String>}
  SortL.lapp_nil(String, ws)

# Read back, the `would withdraw` lines of a dry run are the files given
# up, in the order given.
def withdraws_said(+p: Export.Plan, +c: Export.Counts, +ws: List<&2, String>, +n: Nat, +u: Bool, +spelled: String, +into: String) -> {Export.said.after(Export.said.plan(p, c, ws, n, u, spelled, into), "would withdraw history/") == ws : List<&2, String>}:
  Equal.trans(List<&2, String>, Export.said.after(Export.said.plan(p, c, ws, n, u, spelled, into), "would withdraw history/"), List.append(&2, String, Export.said.after(Export.withdrawn.said(ws), "would withdraw history/"), Export.said.after(Export.paths.said("write  ", Export.plan.paths(p)), "would withdraw history/")), ws,
    five_after(Export.said.counts("would export", "would hold back", "would leave", "would carry", c, p, List.length(&2, T.Split, Export.plan.reserved(p))), Export.withdrawn.said(ws), Export.line.if(Export.nonzero(n), Export.count.line("would destroy", n, "forgotten originals")), Export.paths.said("write  ", Export.plan.paths(p)), ["would " ++ Export.updating.said(u) ++ " of " ++ spelled ++ " at " ++ into], "would withdraw history/",
      counts_withdraw(c, p, List.length(&2, T.Split, Export.plan.reserved(p))), quiet_if(Export.nonzero(n), Export.count.line("would destroy", n, "forgotten originals"), "would withdraw history/", {==}), last_quiet(u, spelled, into, "would withdraw history/", last_withdraw(u, spelled, into))),
    after_pw(p, ws))

def after_wp(+p: Export.Plan, +ws: List<&2, String>) -> {List.append(&2, String, Export.said.after(Export.withdrawn.said(ws), "write   "), Export.said.after(Export.paths.said("write  ", Export.plan.paths(p)), "write   ")) == Export.plan.paths(p) : List<&2, String>}:
  %Equal.sym(List<&2, String>, Export.said.after(Export.withdrawn.said(ws), "write   "), Nil{}, after_quiet(Export.withdrawn.said(ws), "write   ", withdrawn_write(ws))) : {List.append(&2, String, _, Export.said.after(Export.paths.said("write  ", Export.plan.paths(p)), "write   ")) == Export.plan.paths(p) : List<&2, String>}
  paths_back(Export.plan.paths(p))

# Read back, the `write` lines of a dry run are the plan's paths.
def writes_said(+p: Export.Plan, +c: Export.Counts, +ws: List<&2, String>, +n: Nat, +u: Bool, +spelled: String, +into: String) -> {Export.said.after(Export.said.plan(p, c, ws, n, u, spelled, into), "write   ") == Export.plan.paths(p) : List<&2, String>}:
  Equal.trans(List<&2, String>, Export.said.after(Export.said.plan(p, c, ws, n, u, spelled, into), "write   "), List.append(&2, String, Export.said.after(Export.withdrawn.said(ws), "write   "), Export.said.after(Export.paths.said("write  ", Export.plan.paths(p)), "write   ")), Export.plan.paths(p),
    five_after(Export.said.counts("would export", "would hold back", "would leave", "would carry", c, p, List.length(&2, T.Split, Export.plan.reserved(p))), Export.withdrawn.said(ws), Export.line.if(Export.nonzero(n), Export.count.line("would destroy", n, "forgotten originals")), Export.paths.said("write  ", Export.plan.paths(p)), ["would " ++ Export.updating.said(u) ++ " of " ++ spelled ++ " at " ++ into], "write   ",
      counts_write(c, p, List.length(&2, T.Split, Export.plan.reserved(p))), quiet_if(Export.nonzero(n), Export.count.line("would destroy", n, "forgotten originals"), "write   ", {==}), last_quiet(u, spelled, into, "write   ", last_write(u, spelled, into))),
    after_wp(p, ws))

# The tree's paths
# ----------------

# Sorting and dropping repeats keeps exactly the strings given.
def sd_member(+xs: List<&2, String>, +x: String) -> {Rev.member(Main.sorted_distinct(xs), x) == Rev.member(xs, x) : Bool}:
  GL.bool_iff(Rev.member(Main.sorted_distinct(xs), x), Rev.member(xs, x),
    m => ForgetL.held_member(xs, Main.sorted_distinct(xs), x, RewriteL.dist_held(xs), m),
    m => ForgetL.held_member(Main.sorted_distinct(xs), xs, x, FetchL.ah_ds(xs, xs, ReceiveL.held_refl(xs)), m))

def same_strings(ws: List<&2, String>) -> {Main.strings.same(ws, ws) == True{} : Bool}:
  match ws:
    case Nil{}:
      {==}
    case +w <> +rest:
      ExportL.and_tt(String.eq(w, w), Main.strings.same(rest, rest), SL.eq_refl(w), same_strings(rest))

def tree_same(+t: Tree.Tree(), +x: String) -> {Export.bool.same(Rev.member(Main.sorted_distinct(Export.entry.paths(t)), x), Export.tree.holds(t, x)) == True{} : Bool}:
  %Equal.sym(Bool, Rev.member(Main.sorted_distinct(Export.entry.paths(t)), x), Rev.member(Export.entry.paths(t), x), sd_member(Export.entry.paths(t), x)) : {Export.bool.same(_, Export.tree.holds(t, x)) == True{} : Bool}
  %Equal.sym(Bool, Rev.member(Export.entry.paths(t), x), Export.tree.holds(t, x), PlacedL.paths_holds(t, x)) : {Export.bool.same(_, Export.tree.holds(t, x)) == True{} : Bool}
  ExportL.same_refl(Export.tree.holds(t, x))

# What `export -n` names: every file a copy being updated gives up, in the
# order they go, and every path of the target's tree, once each and in
# path order.
def dry_names(+held: List<&2, Main.Full>, +t: Tree.Tree(), +ds: List<&2, Store.Doc>, +ps: List<&2, T.Split>, +bodies: List<&2, Prune.Body>, +rs: List<&2, Receive.Ruled>, +bs: List<&2, Bm.Bookmark>, +claims: List<&2, T.Split>, +c: Export.Counts, +ws: List<&2, String>, +n: Nat, +u: Bool, +spelled: String, +into: String, +x: String) -> {Bool.and(Main.strings.same(Export.said.after(Export.said.plan(Export.plan.of(held, t, ds, ps, bodies, rs, bs, claims), c, ws, n, u, spelled, into), "would withdraw history/"), ws), Bool.and(Main.rising(Export.said.after(Export.said.plan(Export.plan.of(held, t, ds, ps, bodies, rs, bs, claims), c, ws, n, u, spelled, into), "write   ")), Export.bool.same(Rev.member(Export.said.after(Export.said.plan(Export.plan.of(held, t, ds, ps, bodies, rs, bs, claims), c, ws, n, u, spelled, into), "write   "), x), Export.tree.holds(t, x)))) == True{} : Bool}:
  +p = Export.plan.of(held, t, ds, ps, bodies, rs, bs, claims)
  +e = Main.sorted_distinct(Export.entry.paths(t))
  %Equal.sym(List<&2, String>, Export.said.after(Export.said.plan(p, c, ws, n, u, spelled, into), "would withdraw history/"), ws, withdraws_said(p, c, ws, n, u, spelled, into)) : {Bool.and(Main.strings.same(_, ws), Bool.and(Main.rising(Export.said.after(Export.said.plan(p, c, ws, n, u, spelled, into), "write   ")), Export.bool.same(Rev.member(Export.said.after(Export.said.plan(p, c, ws, n, u, spelled, into), "write   "), x), Export.tree.holds(t, x)))) == True{} : Bool}
  %Equal.sym(List<&2, String>, Export.said.after(Export.said.plan(p, c, ws, n, u, spelled, into), "write   "), e, writes_said(p, c, ws, n, u, spelled, into)) : {Bool.and(Main.strings.same(ws, ws), Bool.and(Main.rising(_), Export.bool.same(Rev.member(Export.said.after(Export.said.plan(p, c, ws, n, u, spelled, into), "write   "), x), Export.tree.holds(t, x)))) == True{} : Bool}
  %Equal.sym(List<&2, String>, Export.said.after(Export.said.plan(p, c, ws, n, u, spelled, into), "write   "), e, writes_said(p, c, ws, n, u, spelled, into)) : {Bool.and(Main.strings.same(ws, ws), Bool.and(Main.rising(e), Export.bool.same(Rev.member(_, x), Export.tree.holds(t, x)))) == True{} : Bool}
  ExportL.and_tt(Main.strings.same(ws, ws), Bool.and(Main.rising(e), Export.bool.same(Rev.member(e, x), Export.tree.holds(t, x))), same_strings(ws),
    ExportL.and_tt(Main.rising(e), Export.bool.same(Rev.member(e, x), Export.tree.holds(t, x)), RewriteL.sd_rising(Export.entry.paths(t)), tree_same(t, x)))

# What `export --files-only` says it would do, and says it did
# ------------------------------------------------------------

def puts_write(ps: List<&2, Export.Put>) -> {Export.said.after(Export.puts.said(ps), "write   ") == Export.put.paths(Export.file.puts(ps)) : List<&2, String>}:
  match ps:
    case Nil{}:
      {==}
    case p <> +rest:
      match p:
        case Export.Put.Text{+path, t, r}:
          %Equal.sym(Bool, String.starts_with(path, ""), True{}, sw_nil(path)) : {Export.said.keep(_, "write   " ++ path, 8n, Export.said.after(Export.puts.said(rest), "write   ")) == path <> Export.put.paths(Export.file.puts(rest)) : List<&2, String>}
          %Equal.sym(String, String.drop(path, 0n), path, drop_zero(path)) : {_ <> Export.said.after(Export.puts.said(rest), "write   ") == path <> Export.put.paths(Export.file.puts(rest)) : List<&2, String>}
          %Equal.sym(List<&2, String>, Export.said.after(Export.puts.said(rest), "write   "), Export.put.paths(Export.file.puts(rest)), puts_write(rest)) : {path <> _ == path <> Export.put.paths(Export.file.puts(rest)) : List<&2, String>}
          {==}
        case Export.Put.Bytes{+path, f, d, r}:
          %Equal.sym(Bool, String.starts_with(path, ""), True{}, sw_nil(path)) : {Export.said.keep(_, "write   " ++ path, 8n, Export.said.after(Export.puts.said(rest), "write   ")) == path <> Export.put.paths(Export.file.puts(rest)) : List<&2, String>}
          %Equal.sym(String, String.drop(path, 0n), path, drop_zero(path)) : {_ <> Export.said.after(Export.puts.said(rest), "write   ") == path <> Export.put.paths(Export.file.puts(rest)) : List<&2, String>}
          %Equal.sym(List<&2, String>, Export.said.after(Export.puts.said(rest), "write   "), Export.put.paths(Export.file.puts(rest)), puts_write(rest)) : {path <> _ == path <> Export.put.paths(Export.file.puts(rest)) : List<&2, String>}
          {==}
        case Export.Put.Link{path, t}:
          puts_write(rest)

def wrote_back(ps: List<&2, String>) -> {Export.said.after(Export.paths.said("wrote  ", ps), "wrote   ") == ps : List<&2, String>}:
  match ps:
    case Nil{}:
      {==}
    case +p <> rest:
      %Equal.sym(Bool, String.starts_with(p, ""), True{}, sw_nil(p)) : {Export.said.keep(_, "wrote  " ++ " " ++ p, 8n, Export.said.after(Export.paths.said("wrote  ", rest), "wrote   ")) == p <> rest : List<&2, String>}
      %Equal.sym(String, String.drop(p, 0n), p, drop_zero(p)) : {_ <> Export.said.after(Export.paths.said("wrote  ", rest), "wrote   ") == p <> rest : List<&2, String>}
      %Equal.sym(List<&2, String>, Export.said.after(Export.paths.said("wrote  ", rest), "wrote   "), rest, wrote_back(rest)) : {p <> _ == p <> rest : List<&2, String>}
      {==}

# Of three or four groups of lines, all quiet but one: what that one says.
def three_first(+a: List<&2, String>, +b: List<&2, String>, +c: List<&2, String>, +pre: String, +qb: {quiet(b, pre) == True{} : Bool}, +qc: {quiet(c, pre) == True{} : Bool}) -> {Export.said.after(List.concat(&2, String, [a, b, c]), pre) == Export.said.after(a, pre) : List<&2, String>}:
  %Equal.sym(List<&2, String>, Export.said.after(List.append(&2, String, a, List.append(&2, String, b, List.append(&2, String, c, Nil{}))), pre), List.append(&2, String, Export.said.after(a, pre), Export.said.after(List.append(&2, String, b, List.append(&2, String, c, Nil{})), pre)), after_app(a, List.append(&2, String, b, List.append(&2, String, c, Nil{})), pre)) : {_ == Export.said.after(a, pre) : List<&2, String>}
  %Equal.sym(List<&2, String>, Export.said.after(List.append(&2, String, b, List.append(&2, String, c, Nil{})), pre), List.append(&2, String, Export.said.after(b, pre), Export.said.after(List.append(&2, String, c, Nil{}), pre)), after_app(b, List.append(&2, String, c, Nil{}), pre)) : {List.append(&2, String, Export.said.after(a, pre), _) == Export.said.after(a, pre) : List<&2, String>}
  %Equal.sym(List<&2, String>, Export.said.after(b, pre), Nil{}, after_quiet(b, pre, qb)) : {List.append(&2, String, Export.said.after(a, pre), List.append(&2, String, _, Export.said.after(List.append(&2, String, c, Nil{}), pre))) == Export.said.after(a, pre) : List<&2, String>}
  %Equal.sym(List<&2, String>, Export.said.after(List.append(&2, String, c, Nil{}), pre), List.append(&2, String, Export.said.after(c, pre), Export.said.after(Nil{}, pre)), after_app(c, Nil{}, pre)) : {List.append(&2, String, Export.said.after(a, pre), _) == Export.said.after(a, pre) : List<&2, String>}
  %Equal.sym(List<&2, String>, Export.said.after(c, pre), Nil{}, after_quiet(c, pre, qc)) : {List.append(&2, String, Export.said.after(a, pre), List.append(&2, String, _, Export.said.after(Nil{}, pre))) == Export.said.after(a, pre) : List<&2, String>}
  %Equal.sym(List<&2, String>, List.append(&2, String, Export.said.after(a, pre), Nil{}), Export.said.after(a, pre), SortL.lapp_nil(String, Export.said.after(a, pre))) : {_ == Export.said.after(a, pre) : List<&2, String>}
  {==}

def four_first(+a: List<&2, String>, +b: List<&2, String>, +c: List<&2, String>, +d: List<&2, String>, +pre: String, +qb: {quiet(b, pre) == True{} : Bool}, +qc: {quiet(c, pre) == True{} : Bool}, +qd: {quiet(d, pre) == True{} : Bool}) -> {Export.said.after(List.concat(&2, String, [a, b, c, d]), pre) == Export.said.after(a, pre) : List<&2, String>}:
  %Equal.sym(List<&2, String>, Export.said.after(List.append(&2, String, a, List.append(&2, String, b, List.append(&2, String, c, List.append(&2, String, d, Nil{})))), pre), List.append(&2, String, Export.said.after(a, pre), Export.said.after(List.append(&2, String, b, List.append(&2, String, c, List.append(&2, String, d, Nil{}))), pre)), after_app(a, List.append(&2, String, b, List.append(&2, String, c, List.append(&2, String, d, Nil{}))), pre)) : {_ == Export.said.after(a, pre) : List<&2, String>}
  %Equal.sym(List<&2, String>, Export.said.after(List.append(&2, String, b, List.append(&2, String, c, List.append(&2, String, d, Nil{}))), pre), List.append(&2, String, Export.said.after(b, pre), Export.said.after(List.append(&2, String, c, List.append(&2, String, d, Nil{})), pre)), after_app(b, List.append(&2, String, c, List.append(&2, String, d, Nil{})), pre)) : {List.append(&2, String, Export.said.after(a, pre), _) == Export.said.after(a, pre) : List<&2, String>}
  %Equal.sym(List<&2, String>, Export.said.after(b, pre), Nil{}, after_quiet(b, pre, qb)) : {List.append(&2, String, Export.said.after(a, pre), List.append(&2, String, _, Export.said.after(List.append(&2, String, c, List.append(&2, String, d, Nil{})), pre))) == Export.said.after(a, pre) : List<&2, String>}
  %Equal.sym(List<&2, String>, Export.said.after(List.append(&2, String, c, List.append(&2, String, d, Nil{})), pre), List.append(&2, String, Export.said.after(c, pre), Export.said.after(List.append(&2, String, d, Nil{}), pre)), after_app(c, List.append(&2, String, d, Nil{}), pre)) : {List.append(&2, String, Export.said.after(a, pre), _) == Export.said.after(a, pre) : List<&2, String>}
  %Equal.sym(List<&2, String>, Export.said.after(c, pre), Nil{}, after_quiet(c, pre, qc)) : {List.append(&2, String, Export.said.after(a, pre), List.append(&2, String, _, Export.said.after(List.append(&2, String, d, Nil{}), pre))) == Export.said.after(a, pre) : List<&2, String>}
  %Equal.sym(List<&2, String>, Export.said.after(List.append(&2, String, d, Nil{}), pre), List.append(&2, String, Export.said.after(d, pre), Export.said.after(Nil{}, pre)), after_app(d, Nil{}, pre)) : {List.append(&2, String, Export.said.after(a, pre), _) == Export.said.after(a, pre) : List<&2, String>}
  %Equal.sym(List<&2, String>, Export.said.after(d, pre), Nil{}, after_quiet(d, pre, qd)) : {List.append(&2, String, Export.said.after(a, pre), List.append(&2, String, _, Export.said.after(Nil{}, pre))) == Export.said.after(a, pre) : List<&2, String>}
  %Equal.sym(List<&2, String>, List.append(&2, String, Export.said.after(a, pre), Nil{}), Export.said.after(a, pre), SortL.lapp_nil(String, Export.said.after(a, pre))) : {_ == Export.said.after(a, pre) : List<&2, String>}
  {==}

def links_write(ps: List<&2, Export.Put>) -> {quiet(Export.links.said("link    ", ps), "write   ") == True{} : Bool}:
  match ps:
    case Nil{}:
      {==}
    case p <> rest:
      match p:
        case Export.Put.Link{path, t}:
          links_write(rest)
        case Export.Put.Text{path, t, r}:
          links_write(rest)
        case Export.Put.Bytes{path, f, d, r}:
          links_write(rest)

def linked_wrote(ps: List<&2, Export.Put>) -> {quiet(Export.links.said("linked  ", ps), "wrote   ") == True{} : Bool}:
  match ps:
    case Nil{}:
      {==}
    case p <> rest:
      match p:
        case Export.Put.Link{path, t}:
          linked_wrote(rest)
        case Export.Put.Text{path, t, r}:
          linked_wrote(rest)
        case Export.Put.Bytes{path, f, d, r}:
          linked_wrote(rest)

def modes_wrote(ps: List<&2, String>) -> {quiet(Export.modes.said(ps), "wrote   ") == True{} : Bool}:
  match ps:
    case Nil{}:
      {==}
    case p <> rest:
      modes_wrote(rest)

# What `export --files-only -n` says it would write is the tree: read back,
# its `write` lines are the paths where the tree holds a file that is no
# link, each once and in path order, and the real run's `wrote` lines are
# the same.
def folder_said(+t: Tree.Tree(), +fs: List<&2, Main.Full>, +ds: List<&2, Store.Doc>, +id: String, +pays: List<&2, T.Split>, +bs: List<&2, Prune.Body>, +rules: List<&2, Folder.Scope>, +qs: List<&2, Export.Put>, +set: List<&2, String>, +spelled: String, +into: String, +at: String, +x: String, +h: {Export.folder.r(t, fs, ds, id, pays, bs, rules) == Done{qs} : Result<&2, &2, Main.Refused, List<&2, Export.Put>>}) -> {Bool.and(Main.strings.same(Export.said.after(Export.said.folder(qs, spelled, into), "write   "), Export.said.after(Export.said.laid(qs, set, spelled, at), "wrote   ")), Bool.and(Main.rising(Export.said.after(Export.said.folder(qs, spelled, into), "write   ")), Export.bool.same(Rev.member(Export.said.after(Export.said.folder(qs, spelled, into), "write   "), x), Export.tree.file(t, x)))) == True{} : Bool}:
  +fp = Export.put.paths(Export.file.puts(qs))
  +w = Export.said.after(Export.said.folder(qs, spelled, into), "write   ")
  +r = Export.said.after(Export.said.laid(qs, set, spelled, at), "wrote   ")
  +eq1 = Equal.trans(List<&2, String>, w, Export.said.after(Export.puts.said(qs), "write   "), fp, three_first(Export.puts.said(qs), Export.links.said("link    ", qs), ["would write the folder " ++ spelled ++ " has at " ++ into ++ ", and no history beside it"], "write   ", links_write(qs), {==}), puts_write(qs))
  +eq2 = Equal.trans(List<&2, String>, r, Export.said.after(Export.paths.said("wrote  ", fp), "wrote   "), fp, four_first(Export.paths.said("wrote  ", fp), Export.modes.said(set), Export.links.said("linked  ", qs), ["the folder " ++ spelled ++ " has, at " ++ at ++ ", and no history beside it"], "wrote   ", modes_wrote(set), linked_wrote(qs), {==}), wrote_back(fp))
  %Equal.sym(List<&2, String>, w, fp, eq1) : {Bool.and(Main.strings.same(_, r), Bool.and(Main.rising(_), Export.bool.same(Rev.member(_, x), Export.tree.file(t, x)))) == True{} : Bool}
  %Equal.sym(List<&2, String>, r, fp, eq2) : {Bool.and(Main.strings.same(fp, _), Bool.and(Main.rising(fp), Export.bool.same(Rev.member(fp, x), Export.tree.file(t, x)))) == True{} : Bool}
  ExportL.and_tt(Main.strings.same(fp, fp), Bool.and(Main.rising(fp), Export.bool.same(Rev.member(fp, x), Export.tree.file(t, x))), same_strings(fp),
    PlacedL.files_laid_out(t, fs, ds, id, pays, bs, rules, qs, x, h))
