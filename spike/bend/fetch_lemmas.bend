# What a reading command asks the store for covers what it reads. `diff
# <target>` asks for every document a revision states for each file whose
# content it replays; `diff` over the folder, for each file of lines no
# statement settles; and after either, every document a resolution among
# those fetched keeps.
import Base
import ./text.bend as T
import ./tree.bend as Tree
import ./revision.bend as Rev
import ./store.bend as Store
import ./resolution.bend as Res
import ./commands.bend as Main
import ./anchor_lemmas.bend as AL
import ./composition_lemmas.bend as Comp
import ./graph_lemmas.bend as GL
import ./status_lemmas.bend as StatusL
import ./plan_lemmas.bend as PlanL

# Where the laws look
# -------------------

# Every file compared whose content is replayed — one side lacks it, or the
# two were stated by different revisions — has every document a revision
# states for it among those asked for.
def fetched.each(+fs: List<&2, Main.Full>, +ws: Map<&2, List<&2, String>>, +ns: Map<&2, List<&2, String>>, +docs: List<&2, String>, files: List<&2, Main.Both>) -> Bool:
  match files:
    case Nil{}:
      True{}
    case Main.Both{+f, +was, +now} <> rest:
      Bool.and(Bool.or(Bool.not(Main.compare.needed(ws, ns, f, was, now)), Main.all_held(docs, Main.wanted(fs, f))), fetched.each(fs, ws, ns, docs, rest))

# Every one of the files has every document a revision states for it among
# those asked for.
def fetched.files(+fs: List<&2, Main.Full>, +docs: List<&2, String>, files: List<&2, String>) -> Bool:
  match files:
    case Nil{}:
      True{}
    case +f <> rest:
      Bool.and(Main.all_held(docs, Main.wanted(fs, f)), fetched.files(fs, docs, rest))

# Every resolution among the documents has every document it keeps among
# those asked for.
def kept.each(ds: List<&2, Store.Doc>, +docs: List<&2, String>) -> Bool:
  match ds:
    case Nil{}:
      True{}
    case Store.Doc{path, id, size, +text} <> rest:
      Bool.and(Bool.or(Bool.not(Res.is_resolution(text)), Main.all_held(docs, Res.keeps(Res.parse(text)))), kept.each(rest, docs))

# What is asked for
# -----------------

def ah_left(+docs: List<&2, String>, xs: List<&2, String>, +ys: List<&2, String>, +h: {Main.all_held(docs, List.append(&2, String, xs, ys)) == True{} : Bool}) -> {Main.all_held(docs, xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      AL.and_intro(Rev.member(docs, x), Main.all_held(docs, rest), Comp.and_left(Rev.member(docs, x), Main.all_held(docs, List.append(&2, String, rest, ys)), h),
        ah_left(docs, rest, ys, Comp.and_right(Rev.member(docs, x), Main.all_held(docs, List.append(&2, String, rest, ys)), h)))

def ah_right(+docs: List<&2, String>, xs: List<&2, String>, +ys: List<&2, String>, +h: {Main.all_held(docs, List.append(&2, String, xs, ys)) == True{} : Bool}) -> {Main.all_held(docs, ys) == True{} : Bool}:
  match xs:
    case Nil{}:
      h
    case +x <> +rest:
      ah_right(docs, rest, ys, Comp.and_right(Rev.member(docs, x), Main.all_held(docs, List.append(&2, String, rest, ys)), h))

def ah_refl(xs: List<&2, String>) -> {Main.all_held(xs, xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      AL.and_intro(Rev.member(x <> rest, x), Main.all_held(x <> rest, rest), GL.member_head(x, rest), StatusL.ah_weak(x, rest, rest, ah_refl(rest)))

# `diff <target>`
# ---------------

def one_fetched(n: Bool, +fs: List<&2, Main.Full>, +f: String, +docs: List<&2, String>, h: {Main.all_held(docs, Main.compare.wanted_one(fs, f, n)) == True{} : Bool}) -> {Bool.or(Bool.not(n), Main.all_held(docs, Main.wanted(fs, f))) == True{} : Bool}:
  match n:
    case True{}:
      h
    case False{}:
      {==}

def each_fetched(+fs: List<&2, Main.Full>, +ws: Map<&2, List<&2, String>>, +ns: Map<&2, List<&2, String>>, +docs: List<&2, String>, files: List<&2, Main.Both>, +h: {Main.all_held(docs, Main.compare.wanted_docs(fs, ws, ns, files)) == True{} : Bool}) -> {fetched.each(fs, ws, ns, docs, files) == True{} : Bool}:
  match files:
    case Nil{}:
      {==}
    case Main.Both{+f, +was, +now} <> +rest:
      AL.and_intro(Bool.or(Bool.not(Main.compare.needed(ws, ns, f, was, now)), Main.all_held(docs, Main.wanted(fs, f))), fetched.each(fs, ws, ns, docs, rest),
        one_fetched(Main.compare.needed(ws, ns, f, was, now), fs, f, docs, ah_left(docs, Main.compare.wanted_one(fs, f, Main.compare.needed(ws, ns, f, was, now)), Main.compare.wanted_docs(fs, ws, ns, rest), h)),
        each_fetched(fs, ws, ns, docs, rest, ah_right(docs, Main.compare.wanted_one(fs, f, Main.compare.needed(ws, ns, f, was, now)), Main.compare.wanted_docs(fs, ws, ns, rest), h)))

# `diff <target>` asks for every document a revision states for each file
# whose content it replays.
def diff_fetched(+fs: List<&2, Main.Full>, +ws: Map<&2, List<&2, String>>, +ns: Map<&2, List<&2, String>>, +files: List<&2, Main.Both>) -> {fetched.each(fs, ws, ns, Main.compare.wanted_docs(fs, ws, ns, files), files) == True{} : Bool}:
  each_fetched(fs, ws, ns, Main.compare.wanted_docs(fs, ws, ns, files), files, ah_refl(Main.compare.wanted_docs(fs, ws, ns, files)))

# The folder
# ----------

def files_fetched(+fs: List<&2, Main.Full>, +docs: List<&2, String>, files: List<&2, String>, +h: {Main.all_held(docs, Main.wanted_all(fs, files)) == True{} : Bool}) -> {fetched.files(fs, docs, files) == True{} : Bool}:
  match files:
    case Nil{}:
      {==}
    case +f <> +rest:
      AL.and_intro(Main.all_held(docs, Main.wanted(fs, f)), fetched.files(fs, docs, rest),
        ah_left(docs, Main.wanted(fs, f), Main.wanted_all(fs, rest), h),
        files_fetched(fs, docs, rest, ah_right(docs, Main.wanted(fs, f), Main.wanted_all(fs, rest), h)))

# `diff` over the folder asks for every document a revision states for
# each file of lines no statement settles.
def folder_fetched(+fs: List<&2, Main.Full>, +dg: Map<&2, String>, +os: Map<&2, T.Split>, +eds: List<&2, Store.Doc>, +hs: List<&2, Main.Here>) -> {fetched.files(fs, Main.wanted_all(fs, Main.planned.replayed(Main.plans(dg, os, eds, hs))), Main.unsettled.files(dg, os, eds, hs)) == True{} : Bool}:
  %Equal.sym(List<&2, String>, Main.planned.replayed(Main.plans(dg, os, eds, hs)), Main.unsettled.files(dg, os, eds, hs), PlanL.replayed_unsettled(dg, os, eds, hs)) : {fetched.files(fs, Main.wanted_all(fs, _), Main.unsettled.files(dg, os, eds, hs)) == True{} : Bool}
  files_fetched(fs, Main.wanted_all(fs, Main.unsettled.files(dg, os, eds, hs)), Main.unsettled.files(dg, os, eds, hs), ah_refl(Main.wanted_all(fs, Main.unsettled.files(dg, os, eds, hs))))

# What resolutions keep
# ---------------------

def kept_one(r: Bool, +text: String, +docs: List<&2, String>, h: {Main.all_held(docs, Main.kept_digests.of(text, r)) == True{} : Bool}) -> {Bool.or(Bool.not(r), Main.all_held(docs, Res.keeps(Res.parse(text)))) == True{} : Bool}:
  match r:
    case True{}:
      h
    case False{}:
      {==}

def kept_each(ds: List<&2, Store.Doc>, +docs: List<&2, String>, +h: {Main.all_held(docs, Main.kept_digests(ds)) == True{} : Bool}) -> {kept.each(ds, docs) == True{} : Bool}:
  match ds:
    case Nil{}:
      {==}
    case Store.Doc{+path, +id, +size, +text} <> +rest:
      AL.and_intro(Bool.or(Bool.not(Res.is_resolution(text)), Main.all_held(docs, Res.keeps(Res.parse(text)))), kept.each(rest, docs),
        kept_one(Res.is_resolution(text), text, docs, ah_left(docs, Main.kept_digests.of(text, Res.is_resolution(text)), Main.kept_digests(rest), h)),
        kept_each(rest, docs, ah_right(docs, Main.kept_digests.of(text, Res.is_resolution(text)), Main.kept_digests(rest), h)))

# A reading command asks, after the documents it fetched, for every
# document a resolution among them keeps.
def kept_fetched(+ds: List<&2, Store.Doc>) -> {kept.each(ds, Main.kept_digests(ds)) == True{} : Bool}:
  kept_each(ds, Main.kept_digests(ds), ah_refl(Main.kept_digests(ds)))
