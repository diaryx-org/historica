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
import ./sort_lemmas.bend as SortL
import ./string_lemmas.bend as S

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

# Every file of lines whose folder holds a regular file, and whose nearest
# statement is an `edit`, has that document among those asked for: the
# result it states is what can settle the file.
def edits.each(+os: Map<&2, T.Split>, +docs: List<&2, String>, hs: List<&2, Main.Here>) -> Bool:
  match hs:
    case Nil{}:
      True{}
    case +h <> rest:
      Bool.and(Bool.or(Bool.not(Bool.and(Main.here.lines(h), Main.here.regular(h))), Main.all_held(docs, Main.edit_of.split(Main.origin(os, Main.here.file(h))))), edits.each(os, docs, rest))

# The payload a side names, where it is a file of bytes.
def side.bytes(s: Maybe<&2, Main.Side>) -> List<&2, String>:
  match s:
    case Some{Main.Side.Whole{d, n}}:
      [d]
    case _:
      Nil{}

# Every file of bytes compared has its payload among those asked about.
def payloads.each(+docs: List<&2, String>, cs: List<&2, Main.Compared>) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case Main.Compared{f, t, b, a, m, g} <> rest:
      Bool.and(Bool.and(Main.all_held(docs, side.bytes(b)), Main.all_held(docs, side.bytes(a))), payloads.each(docs, rest))

# Whether the host located payload `d` at path `p`: the answer for it,
# among those the host gave for the payloads asked about, in order.
def located.at(ds: List<&2, String>, at: List<&2, String>, +d: String, +p: String) -> Bool:
  match ds at:
    case +x <> xr +y <> yr:
      Bool.or(Bool.and(String.eq(x, d), String.eq(y, p)), located.at(xr, yr, d, p))
    case _ _:
      False{}

# Every payload asked the stat of is paired with a path the host located it
# at, and none with `-`, the answer for a payload it could not find.
def located.each(+ds: List<&2, String>, +at: List<&2, String>, found: List<&2, T.Split>) -> Bool:
  match found:
    case Nil{}:
      True{}
    case T.Split{+d, +p} <> rest:
      Bool.and(Bool.and(located.at(ds, at, d, p), Bool.not(String.eq(p, "-"))), located.each(ds, at, rest))

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

# Sorted and each once
# --------------------

def mem_keyed.of(b: Bool, +x: String, +rest: List<&2, String>, +d: String, eb: {String.eq(x, d) == b : Bool}, m: {Bool.or(b, Rev.member(rest, d)) == True{} : Bool}, ih: {Rev.member(rest, d) == True{} : Bool} -> {List.is_empty(&2, String, SortL.keyed(~String, ~(s => s), d, rest)) == False{} : Bool}) -> {List.is_empty(&2, String, Bool.pick(List<&2, String>, b, x <> SortL.keyed(~String, ~(s => s), d, rest), SortL.keyed(~String, ~(s => s), d, rest))) == False{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      ih(m)

# What a list holds, the items it keys under that name hold.
def mem_keyed(xs: List<&2, String>, +d: String, m: {Rev.member(xs, d) == True{} : Bool}) -> {List.is_empty(&2, String, SortL.keyed(~String, ~(s => s), d, xs)) == False{} : Bool}:
  match xs:
    case Nil{}:
      Empty.absurd({List.is_empty(&2, String, Nil{}) == False{} : Bool}, S.false_true(m))
    case +x <> +rest:
      mem_keyed.of(String.eq(x, d), x, rest, d, {==}, m, h => mem_keyed(rest, d, h))

def keyed_mem.of(b: Bool, +x: String, +rest: List<&2, String>, +d: String, h: {List.is_empty(&2, String, Bool.pick(List<&2, String>, b, x <> SortL.keyed(~String, ~(s => s), d, rest), SortL.keyed(~String, ~(s => s), d, rest))) == False{} : Bool}, ih: {List.is_empty(&2, String, SortL.keyed(~String, ~(s => s), d, rest)) == False{} : Bool} -> {Rev.member(rest, d) == True{} : Bool}) -> {Bool.or(b, Rev.member(rest, d)) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      ih(h)

def keyed_mem(ys: List<&2, String>, +d: String, h: {List.is_empty(&2, String, SortL.keyed(~String, ~(s => s), d, ys)) == False{} : Bool}) -> {Rev.member(ys, d) == True{} : Bool}:
  match ys:
    case Nil{}:
      Empty.absurd({Rev.member(Nil{}, d) == True{} : Bool}, S.true_false(h))
    case +y <> +rest:
      keyed_mem.of(String.eq(y, d), y, rest, d, h, t => keyed_mem(rest, d, t))

# Sorting keeps every item.
def sort_mem(+xs: List<&2, String>, +d: String, m: {Rev.member(xs, d) == True{} : Bool}) -> {Rev.member(List.sort(~String, ~(a => b => String.is_le(a, b)), xs), d) == True{} : Bool}:
  keyed_mem(List.sort(~String, ~(a => b => String.is_le(a, b)), xs), d,
    (%Equal.sym(List<&2, String>, SortL.keyed(~String, ~(s => s), d, List.sort(~String, ~(a => b => String.is_le(a, b)), xs)), SortL.keyed(~String, ~(s => s), d, xs), SortL.sort_keyed(~String, ~(s => s), xs, d)) : {List.is_empty(&2, String, _) == False{} : Bool}; mem_keyed(xs, d, m)))

def distinct_head(c: Bool, +a: String, +b: String, +rest: List<&2, String>, +d: String, +ec: {String.eq(a, b) == c : Bool}, +ad: {a == d : String}, ih: {Rev.member(b <> rest, b) == True{} : Bool} -> {Rev.member(Main.distinct(b <> rest), b) == True{} : Bool}) -> {Rev.member(Main.distinct.keep(a, Main.distinct(b <> rest), c), d) == True{} : Bool}:
  match c:
    case True{}:
      +ab = S.eq_true(a, b, ec)
      %Equal.trans(String, b, a, d, Equal.sym(String, a, b, ab), ad) : {Rev.member(Main.distinct(b <> rest), _) == True{} : Bool}
      ih(GL.member_head(b, rest))
    case False{}:
      %Equal.sym(String, a, d, ad) : {Rev.member(_ <> Main.distinct(b <> rest), d) == True{} : Bool}
      GL.member_head(d, Main.distinct(b <> rest))

def distinct_rest(c: Bool, +a: String, +b: String, +rest: List<&2, String>, +d: String, m: {Rev.member(Main.distinct(b <> rest), d) == True{} : Bool}) -> {Rev.member(Main.distinct.keep(a, Main.distinct(b <> rest), c), d) == True{} : Bool}:
  match c:
    case True{}:
      m
    case False{}:
      GL.member_tail(a, Main.distinct(b <> rest), d, m)

# Leaving each item once keeps every item.
def distinct_mem(xs: List<&2, String>, +d: String, m: {Rev.member(xs, d) == True{} : Bool}) -> {Rev.member(Main.distinct(xs), d) == True{} : Bool}:
  match xs:
    case Nil{}:
      m
    case +a <> Nil{}:
      m
    case +a <> +b <> +rest:
      GL.member_cons({Rev.member(Main.distinct.keep(a, Main.distinct(b <> rest), String.eq(a, b)), d) == True{} : Bool}, a, b <> rest, d, m,
        h => distinct_head(String.eq(a, b), a, b, rest, d, {==}, h, t => distinct_mem(b <> rest, b, t)),
        t => distinct_rest(String.eq(a, b), a, b, rest, d, distinct_mem(b <> rest, d, t)))

# Everything a list holds, the list sorted and each once holds.
def ah_ds(+ys: List<&2, String>, xs: List<&2, String>, +h: {Main.all_held(ys, xs) == True{} : Bool}) -> {Main.all_held(Main.distinct(List.sort(~String, ~(a => b => String.is_le(a, b)), ys)), xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      AL.and_intro(Rev.member(Main.distinct(List.sort(~String, ~(a => b => String.is_le(a, b)), ys)), x), Main.all_held(Main.distinct(List.sort(~String, ~(a => b => String.is_le(a, b)), ys)), rest),
        distinct_mem(List.sort(~String, ~(a => b => String.is_le(a, b)), ys), x, sort_mem(ys, x, Comp.and_left(Rev.member(ys, x), Main.all_held(ys, rest), h))),
        ah_ds(ys, rest, Comp.and_right(Rev.member(ys, x), Main.all_held(ys, rest), h)))

# The `edit` documents
# --------------------

def edit_one(n: Bool, +os: Map<&2, T.Split>, +h: Main.Here, +docs: List<&2, String>, e: {Main.all_held(docs, Main.edit_of(os, h, n)) == True{} : Bool}) -> {Bool.or(Bool.not(n), Main.all_held(docs, Main.edit_of.split(Main.origin(os, Main.here.file(h))))) == True{} : Bool}:
  match n:
    case True{}:
      e
    case False{}:
      {==}

def edits_ok(+os: Map<&2, T.Split>, +docs: List<&2, String>, hs: List<&2, Main.Here>, +e: {Main.all_held(docs, Main.edits_of(os, hs)) == True{} : Bool}) -> {edits.each(os, docs, hs) == True{} : Bool}:
  match hs:
    case Nil{}:
      {==}
    case +h <> +rest:
      AL.and_intro(Bool.or(Bool.not(Bool.and(Main.here.lines(h), Main.here.regular(h))), Main.all_held(docs, Main.edit_of.split(Main.origin(os, Main.here.file(h))))), edits.each(os, docs, rest),
        edit_one(Bool.and(Main.here.lines(h), Main.here.regular(h)), os, h, docs, ah_left(docs, Main.edit_of(os, h, Bool.and(Main.here.lines(h), Main.here.regular(h))), Main.edits_of(os, rest), e)),
        edits_ok(os, docs, rest, ah_right(docs, Main.edit_of(os, h, Bool.and(Main.here.lines(h), Main.here.regular(h))), Main.edits_of(os, rest), e)))

# `diff` over the folder asks for the `edit` document of every file of lines
# its folder holds a regular file for, whose nearest statement is one.
def edits_fetched(+os: Map<&2, T.Split>, +hs: List<&2, Main.Here>) -> {edits.each(os, Main.distinct(List.sort(~String, ~(a => b => String.is_le(a, b)), Main.edits_of(os, hs))), hs) == True{} : Bool}:
  edits_ok(os, Main.distinct(List.sort(~String, ~(a => b => String.is_le(a, b)), Main.edits_of(os, hs))), hs, ah_ds(Main.edits_of(os, hs), Main.edits_of(os, hs), ah_refl(Main.edits_of(os, hs))))

# The payloads
# ------------

def payload_side(+docs: List<&2, String>, s: Maybe<&2, Main.Side>, +e: {Main.all_held(docs, Main.side.payload(s)) == True{} : Bool}) -> {Main.all_held(docs, side.bytes(s)) == True{} : Bool}:
  match s:
    case None{}:
      {==}
    case Some{Main.Side.Lines{items}}:
      {==}
    case Some{Main.Side.Whole{d, n}}:
      e

def payloads_ok(+docs: List<&2, String>, cs: List<&2, Main.Compared>, +e: {Main.all_held(docs, Main.payloads_of(cs)) == True{} : Bool}) -> {payloads.each(docs, cs) == True{} : Bool}:
  match cs:
    case Nil{}:
      {==}
    case Main.Compared{+f, +t, +b, +a, +m, +g} <> +rest:
      +eb = ah_left(docs, Main.side.payload(b), List.append(&2, String, Main.side.payload(a), Main.payloads_of(rest)), e)
      +er = ah_right(docs, Main.side.payload(b), List.append(&2, String, Main.side.payload(a), Main.payloads_of(rest)), e)
      AL.and_intro(Bool.and(Main.all_held(docs, side.bytes(b)), Main.all_held(docs, side.bytes(a))), payloads.each(docs, rest),
        AL.and_intro(Main.all_held(docs, side.bytes(b)), Main.all_held(docs, side.bytes(a)), payload_side(docs, b, eb), payload_side(docs, a, ah_left(docs, Main.side.payload(a), Main.payloads_of(rest), er))),
        payloads_ok(docs, rest, ah_right(docs, Main.side.payload(a), Main.payloads_of(rest), er)))

# `diff` asks the host about the payload of every file of bytes it shows.
def payloads_asked(+cs: List<&2, Main.Compared>) -> {payloads.each(Main.distinct(List.sort(~String, ~(a => b => String.is_le(a, b)), Main.payloads_of(cs))), cs) == True{} : Bool}:
  payloads_ok(Main.distinct(List.sort(~String, ~(a => b => String.is_le(a, b)), Main.payloads_of(cs))), cs, ah_ds(Main.payloads_of(cs), Main.payloads_of(cs), ah_refl(Main.payloads_of(cs))))

# The paths asked about
# ---------------------

def located_weak(+x: String, +y: String, +xr: List<&2, String>, +yr: List<&2, String>, found: List<&2, T.Split>, +h: {located.each(xr, yr, found) == True{} : Bool}) -> {located.each(x <> xr, y <> yr, found) == True{} : Bool}:
  match found:
    case Nil{}:
      {==}
    case T.Split{+d, +p} <> +rest:
      +hd = Comp.and_left(Bool.and(located.at(xr, yr, d, p), Bool.not(String.eq(p, "-"))), located.each(xr, yr, rest), h)
      AL.and_intro(Bool.and(located.at(x <> xr, y <> yr, d, p), Bool.not(String.eq(p, "-"))), located.each(x <> xr, y <> yr, rest),
        AL.and_intro(located.at(x <> xr, y <> yr, d, p), Bool.not(String.eq(p, "-")),
          AL.or_right(Bool.and(String.eq(x, d), String.eq(y, p)), located.at(xr, yr, d, p), Comp.and_left(located.at(xr, yr, d, p), Bool.not(String.eq(p, "-")), hd)),
          Comp.and_right(located.at(xr, yr, d, p), Bool.not(String.eq(p, "-")), hd)),
        located_weak(x, y, xr, yr, rest, Comp.and_right(Bool.and(located.at(xr, yr, d, p), Bool.not(String.eq(p, "-"))), located.each(xr, yr, rest), h)))

def keep_located(missing: Bool, +d: String, +p: String, +rest: List<&2, String>, +more: List<&2, String>, +found: List<&2, T.Split>, +em: {String.eq(p, "-") == missing : Bool}, +h: {located.each(rest, more, found) == True{} : Bool}) -> {located.each(d <> rest, p <> more, Main.sizes.keep(d, p, found, missing)) == True{} : Bool}:
  match missing:
    case True{}:
      located_weak(d, p, rest, more, found, h)
    case False{}:
      AL.and_intro(Bool.and(located.at(d <> rest, p <> more, d, p), Bool.not(String.eq(p, "-"))), located.each(d <> rest, p <> more, found),
        AL.and_intro(located.at(d <> rest, p <> more, d, p), Bool.not(String.eq(p, "-")),
          AL.or_left(Bool.and(String.eq(d, d), String.eq(p, p)), located.at(rest, more, d, p), AL.and_intro(String.eq(d, d), String.eq(p, p), S.eq_refl(d), S.eq_refl(p))),
          (%Equal.sym(Bool, String.eq(p, "-"), False{}, em) : {Bool.not(_) == True{} : Bool}; {==})),
        located_weak(d, p, rest, more, found, h))

# `diff` asks the stat only of paths the host located a payload at, each
# with the payload it located there, and never of a payload it could not
# find.
def sizes_located(+root: String, ds: List<&2, String>, at: List<&2, String>) -> {located.each(ds, at, Main.sizes.of(root, ds, at)) == True{} : Bool}:
  match ds at:
    case +d <> +rest +p <> +more:
      keep_located(String.eq(p, "-"), d, p, rest, more, Main.sizes.of(root, rest, more), {==}, sizes_located(root, rest, more))
    case Nil{} y:
      {==}
    case x <> xr Nil{}:
      {==}
