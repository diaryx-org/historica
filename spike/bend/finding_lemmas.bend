# What `check` says of what it found, and whether it fails: the Rust
# tool's `render::report` and `Report::is_ok`, held to a reading of the
# findings as a list rather than to the folds the port prints them with.
import Base
import ./check.bend as Check
import ./string_lemmas.bend as S
import ./commands.bend as Main
import ./revision.bend as Rev
import ./bookmark.bend as Bm
import ./bookmark_lemmas.bend as BmL
import ./text.bend as T
import ./skip_lemmas.bend as SkipL
import ./composition_lemmas.bend as Comp
import ./sort_lemmas.bend as SortL

# The report
# ----------

def text.of(f: Check.Finding) -> String:
  match f:
    case Check.Finding{e, t, h}:
      t

# Each finding on a line of its own, after the word that opens it.
def lined(+word: String, fs: List<&2, Check.Finding>) -> String:
  match fs:
    case Nil{}:
      SNil{}
    case f <> rest:
      (word ++ text.of(f) ++ "\n") ++ lined(word, rest)

def errors(+fs: List<&2, Check.Finding>) -> List<&2, Check.Finding>:
  List.filter(~Check.Finding, ~(f => Check.is_error(f)), fs)

def notes(+fs: List<&2, Check.Finding>) -> List<&2, Check.Finding>:
  List.filter(~Check.Finding, ~(f => Bool.not(Check.is_error(f))), fs)

def heads(+fs: List<&2, Check.Finding>) -> List<&2, Check.Finding>:
  List.filter(~Check.Finding, ~(f => Check.is_head(f)), fs)

# The report `render::report` writes: every error, in the order found, then
# every note; then how many of each, or `nothing to report` where nothing
# was found at all; then, where some head cannot be produced, how many, and
# `--complete` named to a caller who did not ask for it.
def reported(+fs: List<&2, Check.Finding>, +shown: String, complete: Bool) -> String:
  lined("error: ", errors(fs)) ++ lined("note: ", notes(fs)) ++ shown ++ ": " ++ Bool.pick(String, List.is_empty(&2, Check.Finding, fs), "nothing to report", Check.counted(List.length(&2, Check.Finding, errors(fs)), "error") ++ ", " ++ Check.counted(List.length(&2, Check.Finding, notes(fs)), "note")) ++ "\n" ++ Bool.pick(String, List.is_empty(&2, Check.Finding, heads(fs)), SNil{}, shown ++ ": " ++ Check.counted(List.length(&2, Check.Finding, heads(fs)), "head") ++ " here cannot be produced from what is here\n" ++ Bool.pick(String, complete, SNil{}, "`check --complete` is the run that fails on that\n"))

def said_errors.at(+word: String, e: Bool, +t: String, +h: Bool, +rest: List<&2, Check.Finding>, ih: {Check.said.of(word, rest, True{}) == lined(word, errors(rest)) : String}) -> {Check.said.of(word, Check.Finding{e, t, h} <> rest, True{}) == lined(word, errors(Check.Finding{e, t, h} <> rest)) : String}:
  match e:
    case True{}:
      Equal.cong(String, String, x => (word ++ t ++ "\n") ++ x, Check.said.of(word, rest, True{}), lined(word, errors(rest)), ih)
    case False{}:
      ih

def said_of_errors(+word: String, fs: List<&2, Check.Finding>) -> {Check.said.of(word, fs, True{}) == lined(word, errors(fs)) : String}:
  match fs:
    case Nil{}:
      {==}
    case Check.Finding{e, +t, +h} <> +rest:
      said_errors.at(word, e, t, h, rest, said_of_errors(word, rest))

def said_notes.at(+word: String, e: Bool, +t: String, +h: Bool, +rest: List<&2, Check.Finding>, ih: {Check.said.of(word, rest, False{}) == lined(word, notes(rest)) : String}) -> {Check.said.of(word, Check.Finding{e, t, h} <> rest, False{}) == lined(word, notes(Check.Finding{e, t, h} <> rest)) : String}:
  match e:
    case False{}:
      Equal.cong(String, String, x => (word ++ t ++ "\n") ++ x, Check.said.of(word, rest, False{}), lined(word, notes(rest)), ih)
    case True{}:
      ih

def said_of_notes(+word: String, fs: List<&2, Check.Finding>) -> {Check.said.of(word, fs, False{}) == lined(word, notes(fs)) : String}:
  match fs:
    case Nil{}:
      {==}
    case Check.Finding{e, +t, +h} <> +rest:
      said_notes.at(word, e, t, h, rest, said_of_notes(word, rest))

def said_errors(+fs: List<&2, Check.Finding>) -> {Check.said.of("error: ", fs, True{}) == lined("error: ", errors(fs)) : String}:
  said_of_errors("error: ", fs)

def said_notes(+fs: List<&2, Check.Finding>) -> {Check.said.of("note: ", fs, False{}) == lined("note: ", notes(fs)) : String}:
  said_of_notes("note: ", fs)

def succ_cong(-a: Nat, -b: Nat, e: {a == b : Nat}) -> {1n+a == 1n+b : Nat}:
  Equal.cong(Nat, Nat, n => 1n+n, a, b, e)

def count_errors.at(e: Bool, -t: String, -h: Bool, +rest: List<&2, Check.Finding>, ih: {Check.count.of(rest, True{}) == List.length(&2, Check.Finding, errors(rest)) : Nat}) -> {Check.count.of(Check.Finding{e, t, h} <> rest, True{}) == List.length(&2, Check.Finding, errors(Check.Finding{e, t, h} <> rest)) : Nat}:
  match e:
    case True{}:
      succ_cong(Check.count.of(rest, True{}), List.length(&2, Check.Finding, errors(rest)), ih)
    case False{}:
      ih

def count_errors(fs: List<&2, Check.Finding>) -> {Check.count.of(fs, True{}) == List.length(&2, Check.Finding, errors(fs)) : Nat}:
  match fs:
    case Nil{}:
      {==}
    case Check.Finding{e, t, h} <> +rest:
      count_errors.at(e, t, h, rest, count_errors(rest))

def count_notes.at(e: Bool, -t: String, -h: Bool, +rest: List<&2, Check.Finding>, ih: {Check.count.of(rest, False{}) == List.length(&2, Check.Finding, notes(rest)) : Nat}) -> {Check.count.of(Check.Finding{e, t, h} <> rest, False{}) == List.length(&2, Check.Finding, notes(Check.Finding{e, t, h} <> rest)) : Nat}:
  match e:
    case False{}:
      succ_cong(Check.count.of(rest, False{}), List.length(&2, Check.Finding, notes(rest)), ih)
    case True{}:
      ih

def count_notes(fs: List<&2, Check.Finding>) -> {Check.count.of(fs, False{}) == List.length(&2, Check.Finding, notes(fs)) : Nat}:
  match fs:
    case Nil{}:
      {==}
    case Check.Finding{e, t, h} <> +rest:
      count_notes.at(e, t, h, rest, count_notes(rest))

def count_heads.at(-e: Bool, -t: String, h: Bool, +rest: List<&2, Check.Finding>, ih: {Check.heads.of(rest) == List.length(&2, Check.Finding, heads(rest)) : Nat}) -> {Check.heads.of(Check.Finding{e, t, h} <> rest) == List.length(&2, Check.Finding, heads(Check.Finding{e, t, h} <> rest)) : Nat}:
  match h:
    case True{}:
      succ_cong(Check.heads.of(rest), List.length(&2, Check.Finding, heads(rest)), ih)
    case False{}:
      ih

def count_heads(fs: List<&2, Check.Finding>) -> {Check.heads.of(fs) == List.length(&2, Check.Finding, heads(fs)) : Nat}:
  match fs:
    case Nil{}:
      {==}
    case Check.Finding{e, t, h} <> +rest:
      count_heads.at(e, t, h, rest, count_heads(rest))

def and_false(b: Bool) -> {Bool.and(b, False{}) == False{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def nothing_empty.at(e: Bool, -t: String, -h: Bool, +rest: List<&2, Check.Finding>) -> {Bool.and(Nat.is_eq(Check.count.of(Check.Finding{e, t, h} <> rest, True{}), 0n), Nat.is_eq(Check.count.of(Check.Finding{e, t, h} <> rest, False{}), 0n)) == False{} : Bool}:
  match e:
    case True{}:
      {==}
    case False{}:
      and_false(Nat.is_eq(Check.count.of(rest, True{}), 0n))

# Nothing counted is nothing found: every finding is an error or a note.
def nothing_empty(fs: List<&2, Check.Finding>) -> {Bool.and(Nat.is_eq(Check.count.of(fs, True{}), 0n), Nat.is_eq(Check.count.of(fs, False{}), 0n)) == List.is_empty(&2, Check.Finding, fs) : Bool}:
  match fs:
    case Nil{}:
      {==}
    case Check.Finding{e, t, h} <> +rest:
      nothing_empty.at(e, t, h, rest)

def heads_empty.at(-e: Bool, -t: String, h: Bool, +rest: List<&2, Check.Finding>, ih: {Nat.is_eq(Check.heads.of(rest), 0n) == List.is_empty(&2, Check.Finding, heads(rest)) : Bool}) -> {Nat.is_eq(Check.heads.of(Check.Finding{e, t, h} <> rest), 0n) == List.is_empty(&2, Check.Finding, heads(Check.Finding{e, t, h} <> rest)) : Bool}:
  match h:
    case True{}:
      {==}
    case False{}:
      ih

def heads_empty(fs: List<&2, Check.Finding>) -> {Nat.is_eq(Check.heads.of(fs), 0n) == List.is_empty(&2, Check.Finding, heads(fs)) : Bool}:
  match fs:
    case Nil{}:
      {==}
    case Check.Finding{e, t, h} <> +rest:
      heads_empty.at(e, t, h, rest, heads_empty(rest))

def report_is(+fs: List<&2, Check.Finding>, +shown: String, +complete: Bool) -> {Check.report(fs, shown, complete) == reported(fs, shown, complete) : String}:
  %Equal.sym(String, Check.said.of("error: ", fs, True{}), lined("error: ", errors(fs)), said_errors(fs)) : {_ ++ Check.said.of("note: ", fs, False{}) ++ shown ++ ": " ++ Bool.pick(String, Bool.and(Nat.is_eq(Check.count.of(fs, True{}), 0n), Nat.is_eq(Check.count.of(fs, False{}), 0n)), "nothing to report", Check.counted(Check.count.of(fs, True{}), "error") ++ ", " ++ Check.counted(Check.count.of(fs, False{}), "note")) ++ "\n" ++ Bool.pick(String, Nat.is_eq(Check.heads.of(fs), 0n), SNil{}, shown ++ ": " ++ Check.counted(Check.heads.of(fs), "head") ++ " here cannot be produced from what is here\n" ++ Bool.pick(String, complete, SNil{}, "`check --complete` is the run that fails on that\n")) == reported(fs, shown, complete) : String}
  %Equal.sym(String, Check.said.of("note: ", fs, False{}), lined("note: ", notes(fs)), said_notes(fs)) : {lined("error: ", errors(fs)) ++ _ ++ shown ++ ": " ++ Bool.pick(String, Bool.and(Nat.is_eq(Check.count.of(fs, True{}), 0n), Nat.is_eq(Check.count.of(fs, False{}), 0n)), "nothing to report", Check.counted(Check.count.of(fs, True{}), "error") ++ ", " ++ Check.counted(Check.count.of(fs, False{}), "note")) ++ "\n" ++ Bool.pick(String, Nat.is_eq(Check.heads.of(fs), 0n), SNil{}, shown ++ ": " ++ Check.counted(Check.heads.of(fs), "head") ++ " here cannot be produced from what is here\n" ++ Bool.pick(String, complete, SNil{}, "`check --complete` is the run that fails on that\n")) == reported(fs, shown, complete) : String}
  %Equal.sym(Bool, Bool.and(Nat.is_eq(Check.count.of(fs, True{}), 0n), Nat.is_eq(Check.count.of(fs, False{}), 0n)), List.is_empty(&2, Check.Finding, fs), nothing_empty(fs)) : {lined("error: ", errors(fs)) ++ lined("note: ", notes(fs)) ++ shown ++ ": " ++ Bool.pick(String, _, "nothing to report", Check.counted(Check.count.of(fs, True{}), "error") ++ ", " ++ Check.counted(Check.count.of(fs, False{}), "note")) ++ "\n" ++ Bool.pick(String, Nat.is_eq(Check.heads.of(fs), 0n), SNil{}, shown ++ ": " ++ Check.counted(Check.heads.of(fs), "head") ++ " here cannot be produced from what is here\n" ++ Bool.pick(String, complete, SNil{}, "`check --complete` is the run that fails on that\n")) == reported(fs, shown, complete) : String}
  %Equal.sym(Nat, Check.count.of(fs, True{}), List.length(&2, Check.Finding, errors(fs)), count_errors(fs)) : {lined("error: ", errors(fs)) ++ lined("note: ", notes(fs)) ++ shown ++ ": " ++ Bool.pick(String, List.is_empty(&2, Check.Finding, fs), "nothing to report", Check.counted(_, "error") ++ ", " ++ Check.counted(Check.count.of(fs, False{}), "note")) ++ "\n" ++ Bool.pick(String, Nat.is_eq(Check.heads.of(fs), 0n), SNil{}, shown ++ ": " ++ Check.counted(Check.heads.of(fs), "head") ++ " here cannot be produced from what is here\n" ++ Bool.pick(String, complete, SNil{}, "`check --complete` is the run that fails on that\n")) == reported(fs, shown, complete) : String}
  %Equal.sym(Nat, Check.count.of(fs, False{}), List.length(&2, Check.Finding, notes(fs)), count_notes(fs)) : {lined("error: ", errors(fs)) ++ lined("note: ", notes(fs)) ++ shown ++ ": " ++ Bool.pick(String, List.is_empty(&2, Check.Finding, fs), "nothing to report", Check.counted(List.length(&2, Check.Finding, errors(fs)), "error") ++ ", " ++ Check.counted(_, "note")) ++ "\n" ++ Bool.pick(String, Nat.is_eq(Check.heads.of(fs), 0n), SNil{}, shown ++ ": " ++ Check.counted(Check.heads.of(fs), "head") ++ " here cannot be produced from what is here\n" ++ Bool.pick(String, complete, SNil{}, "`check --complete` is the run that fails on that\n")) == reported(fs, shown, complete) : String}
  %Equal.sym(Bool, Nat.is_eq(Check.heads.of(fs), 0n), List.is_empty(&2, Check.Finding, heads(fs)), heads_empty(fs)) : {lined("error: ", errors(fs)) ++ lined("note: ", notes(fs)) ++ shown ++ ": " ++ Bool.pick(String, List.is_empty(&2, Check.Finding, fs), "nothing to report", Check.counted(List.length(&2, Check.Finding, errors(fs)), "error") ++ ", " ++ Check.counted(List.length(&2, Check.Finding, notes(fs)), "note")) ++ "\n" ++ Bool.pick(String, _, SNil{}, shown ++ ": " ++ Check.counted(Check.heads.of(fs), "head") ++ " here cannot be produced from what is here\n" ++ Bool.pick(String, complete, SNil{}, "`check --complete` is the run that fails on that\n")) == reported(fs, shown, complete) : String}
  %Equal.sym(Nat, Check.heads.of(fs), List.length(&2, Check.Finding, heads(fs)), count_heads(fs)) : {lined("error: ", errors(fs)) ++ lined("note: ", notes(fs)) ++ shown ++ ": " ++ Bool.pick(String, List.is_empty(&2, Check.Finding, fs), "nothing to report", Check.counted(List.length(&2, Check.Finding, errors(fs)), "error") ++ ", " ++ Check.counted(List.length(&2, Check.Finding, notes(fs)), "note")) ++ "\n" ++ Bool.pick(String, List.is_empty(&2, Check.Finding, heads(fs)), SNil{}, shown ++ ": " ++ Check.counted(_, "head") ++ " here cannot be produced from what is here\n" ++ Bool.pick(String, complete, SNil{}, "`check --complete` is the run that fails on that\n")) == reported(fs, shown, complete) : String}
  {==}

# Failing
# -------

def any_errors.at(e: Bool, -t: String, -h: Bool, +rest: List<&2, Check.Finding>, ih: {Bool.not(Nat.is_eq(Check.count.of(rest, True{}), 0n)) == List.any(~&2, ~Check.Finding, ~(f => Check.is_error(f)), rest) : Bool}) -> {Bool.not(Nat.is_eq(Check.count.of(Check.Finding{e, t, h} <> rest, True{}), 0n)) == List.any(~&2, ~Check.Finding, ~(f => Check.is_error(f)), Check.Finding{e, t, h} <> rest) : Bool}:
  match e:
    case True{}:
      {==}
    case False{}:
      ih

# Some error counted is some finding an error.
def any_errors(fs: List<&2, Check.Finding>) -> {Bool.not(Nat.is_eq(Check.count.of(fs, True{}), 0n)) == List.any(~&2, ~Check.Finding, ~(f => Check.is_error(f)), fs) : Bool}:
  match fs:
    case Nil{}:
      {==}
    case Check.Finding{e, t, h} <> +rest:
      any_errors.at(e, t, h, rest, any_errors(rest))

def any_heads.at(-e: Bool, -t: String, h: Bool, +rest: List<&2, Check.Finding>, ih: {Bool.not(Nat.is_eq(Check.heads.of(rest), 0n)) == List.any(~&2, ~Check.Finding, ~(f => Check.is_head(f)), rest) : Bool}) -> {Bool.not(Nat.is_eq(Check.heads.of(Check.Finding{e, t, h} <> rest), 0n)) == List.any(~&2, ~Check.Finding, ~(f => Check.is_head(f)), Check.Finding{e, t, h} <> rest) : Bool}:
  match h:
    case True{}:
      {==}
    case False{}:
      ih

def any_heads(fs: List<&2, Check.Finding>) -> {Bool.not(Nat.is_eq(Check.heads.of(fs), 0n)) == List.any(~&2, ~Check.Finding, ~(f => Check.is_head(f)), fs) : Bool}:
  match fs:
    case Nil{}:
      {==}
    case Check.Finding{e, t, h} <> +rest:
      any_heads.at(e, t, h, rest, any_heads(rest))

# `check` fails where it found an error; with `--complete`, where it found
# a head it cannot produce as well; and never for a note.
def fails_is(+fs: List<&2, Check.Finding>, complete: Bool) -> {Check.fails(fs, complete) == Bool.or(List.any(~&2, ~Check.Finding, ~(f => Check.is_error(f)), fs), Bool.and(complete, List.any(~&2, ~Check.Finding, ~(f => Check.is_head(f)), fs))) : Bool}:
  %any_errors(fs) : {Check.fails(fs, complete) == Bool.or(_, Bool.and(complete, List.any(~&2, ~Check.Finding, ~(f => Check.is_head(f)), fs))) : Bool}
  %any_heads(fs) : {Check.fails(fs, complete) == Bool.or(Bool.not(Nat.is_eq(Check.count.of(fs, True{}), 0n)), Bool.and(complete, _)) : Bool}
  {==}

# Bookmarks
# ---------

# Whether a key is one of the facts a revision states about a file.
def keyed(ks: List<&2, String>, +k: String) -> Bool:
  match ks:
    case Nil{}:
      False{}
    case +x <> rest:
      Bool.or(String.eq(k, x), keyed(rest, k))

def fact_key(+k: String) -> Bool:
  keyed(["add", "move", "drop", "edit", "text", "bytes"], k)

# Whether a revision's headers state a fact about the file: a fact's key,
# and the file's identifier its first word.
def speaks(hs: List<&2, Rev.Header>, +f: String) -> Bool:
  match hs:
    case Nil{}:
      False{}
    case Rev.Header{+k, +v} <> rest:
      Bool.or(Bool.and(fact_key(k), String.eq(T.word(v), f)), speaks(rest, f))

def speaks.any(ds: List<&2, Main.Full>, +f: String) -> Bool:
  match ds:
    case Nil{}:
      False{}
    case d <> rest:
      Bool.or(speaks(Check.facts(d), f), speaks.any(rest, f))

# Whether what a bookmark points at is here (decision 0024): the revision
# by its digest, a revision of the change, or a revision stating a fact
# about the file.
def here(+docs: List<&2, Main.Full>, t: Bm.Target) -> Bool:
  match t:
    case Bm.Target.Change{c}:
      Rev.member(T.map(~Main.Full, ~String, ~(d => Main.change_of(d)), docs), c)
    case Bm.Target.Revision{r}:
      Rev.member(T.map(~Main.Full, ~String, ~(d => Main.id_of(d)), docs), r)
    case Bm.Target.File{f}:
      speaks.any(docs, f)

def six_or(a: Bool, b: Bool, c: Bool, d: Bool, e: Bool, f: Bool) -> {Bool.or(Bool.or(a, b), Bool.or(Bool.or(c, d), Bool.or(e, f))) == Bool.or(a, Bool.or(b, Bool.or(c, Bool.or(d, Bool.or(e, Bool.or(f, False{})))))) : Bool}:
  match a b c d e:
    case True{} _ _ _ _:
      {==}
    case False{} True{} _ _ _:
      {==}
    case False{} False{} True{} _ _:
      {==}
    case False{} False{} False{} True{} _:
      {==}
    case False{} False{} False{} False{} True{}:
      {==}
    case False{} False{} False{} False{} False{}:
      match f:
        case True{}:
          {==}
        case False{}:
          {==}

def speaks.at(c: Bool, +x: String, +more: List<&2, String>, +f: String, -rest: Bool, ih: {Rev.member(more, f) == rest : Bool}) -> {Rev.member(Bool.pick(List<&2, String>, c, x <> more, more), f) == Bool.or(Bool.and(c, String.eq(x, f)), rest) : Bool}:
  match c:
    case True{}:
      Equal.cong(Bool, Bool, b => Bool.or(String.eq(x, f), b), Rev.member(more, f), rest, ih)
    case False{}:
      ih

# The files a revision's facts name, as `check` gathers them, hold the file
# exactly where its headers state a fact about it.
def files_speak(hs: List<&2, Rev.Header>, +f: String) -> {Rev.member(Check.facts.files(hs), f) == speaks(hs, f) : Bool}:
  match hs:
    case Nil{}:
      {==}
    case Rev.Header{+k, +v} <> +rest:
      %six_or(String.eq(k, "add"), String.eq(k, "move"), String.eq(k, "drop"), String.eq(k, "edit"), String.eq(k, "text"), String.eq(k, "bytes")) : {Rev.member(Check.facts.files(Rev.Header{k, v} <> rest), f) == Bool.or(Bool.and(_, String.eq(T.word(v), f)), speaks(rest, f)) : Bool}
      speaks.at(Bool.or(Bool.or(String.eq(k, "add"), String.eq(k, "move")), Bool.or(Bool.or(String.eq(k, "drop"), String.eq(k, "edit")), Bool.or(String.eq(k, "text"), String.eq(k, "bytes")))), T.word(v), Check.facts.files(rest), f, speaks(rest, f), files_speak(rest, f))

def pointed_file(ds: List<&2, Main.Full>, +f: String) -> {Check.pointed(ds, Bm.Target.File{f}) == speaks.any(ds, f) : Bool}:
  match ds:
    case Nil{}:
      {==}
    case +d <> +rest:
      %Equal.sym(Bool, Rev.member(Check.facts.files(Check.facts(d)), f), speaks(Check.facts(d), f), files_speak(Check.facts(d), f)) : {Bool.or(_, Check.pointed(rest, Bm.Target.File{f})) == Bool.or(speaks(Check.facts(d), f), speaks.any(rest, f)) : Bool}
      Equal.cong(Bool, Bool, b => Bool.or(speaks(Check.facts(d), f), b), Check.pointed(rest, Bm.Target.File{f}), speaks.any(rest, f), pointed_file(rest, f))

def pointed_revision(ds: List<&2, Main.Full>, +r: String) -> {Check.pointed(ds, Bm.Target.Revision{r}) == Rev.member(T.map(~Main.Full, ~String, ~(d => Main.id_of(d)), ds), r) : Bool}:
  match ds:
    case Nil{}:
      {==}
    case +d <> +rest:
      Equal.cong(Bool, Bool, b => Bool.or(String.eq(Main.id_of(d), r), b), Check.pointed(rest, Bm.Target.Revision{r}), Rev.member(T.map(~Main.Full, ~String, ~(d => Main.id_of(d)), rest), r), pointed_revision(rest, r))

def change_same(d: Main.Full) -> {Check.change.of(d) == Main.change_of(d) : String}:
  match d:
    case Main.Full{id, change, parents, supersedes, author, when, revised_by, revised, facts, message}:
      {==}

def pointed_change(ds: List<&2, Main.Full>, +c: String) -> {Check.pointed(ds, Bm.Target.Change{c}) == Rev.member(T.map(~Main.Full, ~String, ~(d => Main.change_of(d)), ds), c) : Bool}:
  match ds:
    case Nil{}:
      {==}
    case +d <> +rest:
      %Equal.sym(String, Check.change.of(d), Main.change_of(d), change_same(d)) : {Bool.or(String.eq(_, c), Check.pointed(rest, Bm.Target.Change{c})) == Rev.member(T.map(~Main.Full, ~String, ~(d => Main.change_of(d)), d <> rest), c) : Bool}
      Equal.cong(Bool, Bool, b => Bool.or(String.eq(Main.change_of(d), c), b), Check.pointed(rest, Bm.Target.Change{c}), Rev.member(T.map(~Main.Full, ~String, ~(d => Main.change_of(d)), rest), c), pointed_change(rest, c))

# A bookmark points at something here exactly where `here` says.
def pointed_here(+ds: List<&2, Main.Full>, t: Bm.Target) -> {Check.pointed(ds, t) == here(ds, t) : Bool}:
  match t:
    case Bm.Target.Change{+c}:
      pointed_change(ds, c)
    case Bm.Target.Revision{+r}:
      pointed_revision(ds, r)
    case Bm.Target.File{+f}:
      pointed_file(ds, f)

# What `check` finds in a bookmark file `name` wrote for a well-formed
# target: nothing where what it points at is here, and otherwise a note,
# and only a note, that it is not here yet.
def name_read(+docs: List<&2, Main.Full>, +path: String, +n: String, +t: Bm.Target, +p: Bool, +h: {Bm.target_ok(t) == True{} : Bool}) -> {Check.name.text(docs, path, n, Done{Bm.write(Bm.Stated{t, p})}) == Bool.pick(List<&2, Check.Finding>, here(docs, t), Nil{}, [Check.note("`" ++ n ++ "` points at `" ++ Bm.show_target(t) ++ "`, which is not here yet")]) : List<&2, Check.Finding>}:
  %Equal.sym(Result<&2, &2, String, Bm.Stated>, Bm.parse(Bm.write(Bm.Stated{t, p})), Done{Bm.Stated{t, p}}, BmL.reads_back(t, p, h)) : {Check.bookmark.finding(docs, path, n, _) == Bool.pick(List<&2, Check.Finding>, here(docs, t), Nil{}, [Check.note("`" ++ n ++ "` points at `" ++ Bm.show_target(t) ++ "`, which is not here yet")]) : List<&2, Check.Finding>}
  %Equal.sym(Bool, Check.pointed(docs, t), here(docs, t), pointed_here(docs, t)) : {Bool.pick(List<&2, Check.Finding>, _, Nil{}, [Check.note("`" ++ n ++ "` points at `" ++ Bm.show_target(t) ++ "`, which is not here yet")]) == Bool.pick(List<&2, Check.Finding>, here(docs, t), Nil{}, [Check.note("`" ++ n ++ "` points at `" ++ Bm.show_target(t) ++ "`, which is not here yet")]) : List<&2, Check.Finding>}
  {==}

# The walk
# --------

# One entry of a directory's listing, as the host lists it: a directory, a
# file with its execute bit and size, a link and its target, a link whose
# target cannot be spelled, a name that is not UTF-8, or anything else.
type Listed is Data:
  Listed.Dir{name: String}
  Listed.File{exec: Bool, size: String, name: String}
  Listed.Link{name: String, target: String}
  Listed.Unspelled{name: String}
  Listed.Lossy{name: String}
  Listed.Other{name: String}

# Its lines, as `Store.folder` writes them: `d`, `f` with the bit and the
# size, `l` with the target on the next line, `L`, `u` and `o`.
def line(e: Listed) -> String:
  match e:
    case Listed.Dir{n}:
      "d " ++ n
    case Listed.File{x, z, n}:
      "f " ++ Bool.pick(String, x, "1", "0") ++ " " ++ z ++ " " ++ n
    case Listed.Link{n, t}:
      "l " ++ n ++ "\n" ++ t
    case Listed.Unspelled{n}:
      "L " ++ n
    case Listed.Lossy{n}:
      "u " ++ n
    case Listed.Other{n}:
      "o " ++ n

# What the host lists: no name, and no target, holding a line break, and
# no size a space.
def spelt(e: Listed) -> Bool:
  match e:
    case Listed.Dir{+n}:
      Bool.not(T.has_char(n, '\n'))
    case Listed.File{x, +z, +n}:
      Bool.and(Bool.not(T.has_char(z, ' ')), Bool.and(Bool.not(T.has_char(z, '\n')), Bool.not(T.has_char(n, '\n'))))
    case Listed.Link{+n, +t}:
      Bool.and(Bool.not(T.has_char(n, '\n')), Bool.not(T.has_char(t, '\n')))
    case Listed.Unspelled{+n}:
      Bool.not(T.has_char(n, '\n'))
    case Listed.Lossy{+n}:
      Bool.not(T.has_char(n, '\n'))
    case Listed.Other{+n}:
      Bool.not(T.has_char(n, '\n'))

# What reading the entry finds, under the directory listed: a directory to
# walk next, a file, or a link, which is never followed.
def found(e: Listed, +dir: String, +fs: List<&2, String>, +ls: List<&2, String>) -> Check.Seen:
  match e:
    case Listed.Dir{n}:
      Check.Seen{[dir ++ "/" ++ n], fs, ls, False{}}
    case Listed.File{x, z, n}:
      Check.Seen{Nil{}, (dir ++ "/" ++ n) <> fs, ls, False{}}
    case Listed.Link{n, t}:
      Check.Seen{Nil{}, fs, (dir ++ "/" ++ n) <> ls, False{}}
    case Listed.Unspelled{n}:
      Check.Seen{Nil{}, fs, (dir ++ "/" ++ n) <> ls, False{}}
    case Listed.Lossy{n}:
      Check.Seen{Nil{}, fs, ls, False{}}
    case Listed.Other{n}:
      Check.Seen{Nil{}, fs, ls, False{}}

def split_nl.at(b: Bool, +c: Char, +t: String, +rest: String, h: {Bool.or(b, T.has_char(t, '\n')) == False{} : Bool}, ih: {T.has_char(t, '\n') == False{} : Bool} -> {String.split(String.append(t, SCon{'\n', rest}), '\n') == t <> String.split(rest, '\n') : List<&2, String>}) -> {String.split.fin(c, String.split(String.append(t, SCon{'\n', rest}), '\n'), b) == SCon{c, t} <> String.split(rest, '\n') : List<&2, String>}:
  match b:
    case True{}:
      Empty.absurd({String.split.fin(c, String.split(String.append(t, SCon{'\n', rest}), '\n'), True{}) == SCon{c, t} <> String.split(rest, '\n') : List<&2, String>}, S.true_false(h))
    case False{}:
      %Equal.sym(List<&2, String>, String.split(String.append(t, SCon{'\n', rest}), '\n'), t <> String.split(rest, '\n'), ih(h)) : {String.split.fin(c, _, False{}) == SCon{c, t} <> String.split(rest, '\n') : List<&2, String>}
      {==}

# A line with no break in it, a newline, and the rest: that line, and the
# rest's lines.
def split_nl(l: String, +rest: String, h: {T.has_char(l, '\n') == False{} : Bool}) -> {String.split(String.append(l, SCon{'\n', rest}), '\n') == l <> String.split(rest, '\n') : List<&2, String>}:
  match l:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      split_nl.at(Char.is_eq(c, '\n'), c, t, rest, h, ht => split_nl(t, rest, ht))

def has_char_app(a: String, +b: String, +c: Char) -> {T.has_char(String.append(a, b), c) == Bool.or(T.has_char(a, c), T.has_char(b, c)) : Bool}:
  match a:
    case SNil{}:
      {==}
    case SCon{+x, +t}:
      %Equal.sym(Bool, T.has_char(String.append(t, b), c), Bool.or(T.has_char(t, c), T.has_char(b, c)), has_char_app(t, b, c)) : {Bool.or(Char.is_eq(x, c), _) == Bool.or(Bool.or(Char.is_eq(x, c), T.has_char(t, c)), T.has_char(b, c)) : Bool}
      SkipL.or_assoc(Char.is_eq(x, c), T.has_char(t, c), T.has_char(b, c))

def or_false(a: Bool, -b: Bool, ea: {a == False{} : Bool}, eb: {b == False{} : Bool}) -> {Bool.or(a, b) == False{} : Bool}:
  %Equal.sym(Bool, a, False{}, ea) : {Bool.or(_, b) == False{} : Bool}
  eb

def so.at(b: Bool, +c: Char, +zt: String, +acc: String, +n: String, h: {Bool.or(b, T.has_char(zt, ' ')) == False{} : Bool}, ih: {T.has_char(zt, ' ') == False{} : Bool} -> {T.split_once.fast(String.append(zt, SCon{' ', n}), SCon{c, acc}, T.space_first(String.append(zt, SCon{' ', n}))) == Some{T.Split{String.reverse(String.reverse.go(zt, SCon{c, acc})), n}} : Maybe<&2, T.Split>}) -> {T.split_once.fast(SCon{c, String.append(zt, SCon{' ', n})}, acc, b) == Some{T.Split{String.reverse(String.reverse.go(zt, SCon{c, acc})), n}} : Maybe<&2, T.Split>}:
  match b:
    case True{}:
      Empty.absurd({T.split_once.fast(SCon{c, String.append(zt, SCon{' ', n})}, acc, True{}) == Some{T.Split{String.reverse(String.reverse.go(zt, SCon{c, acc})), n}} : Maybe<&2, T.Split>}, S.true_false(h))
    case False{}:
      ih(h)

# Cut at its first space, a word with no space in it, a space, and the
# rest is that word and the rest.
def so_fast(z: String, +acc: String, +n: String, h: {T.has_char(z, ' ') == False{} : Bool}) -> {T.split_once.fast(String.append(z, SCon{' ', n}), acc, T.space_first(String.append(z, SCon{' ', n}))) == Some{T.Split{String.reverse(String.reverse.go(z, acc)), n}} : Maybe<&2, T.Split>}:
  match z:
    case SNil{}:
      {==}
    case SCon{+c, +zt}:
      so.at(Char.is_eq(c, ' '), c, zt, acc, n, h, hz => so_fast(zt, SCon{c, acc}, n, hz))

def split_once_at(+z: String, +n: String, h: {T.has_char(z, ' ') == False{} : Bool}) -> {T.split_once(z ++ " " ++ n) == Some{T.Split{z, n}} : Maybe<&2, T.Split>}:
  %Equal.sym(Maybe<&2, T.Split>, T.split_once(z ++ " " ++ n), Some{T.Split{String.reverse(String.reverse(z)), n}}, so_fast(z, SNil{}, n, h)) : {_ == Some{T.Split{z, n}} : Maybe<&2, T.Split>}
  Equal.cong(String, Maybe<&2, T.Split>, y => Some{T.Split{y, n}}, String.reverse(String.reverse(z)), z, SkipL.rev_rev(z))

def not_has(+s: String, c: Char, h: {Bool.not(T.has_char(s, c)) == True{} : Bool}) -> {T.has_char(s, c) == False{} : Bool}:
  SkipL.not_true_false(T.has_char(s, c), h)

# A file's line holds no break where neither its size nor its name does.
def file_nl(+z: String, +n: String, hz: {T.has_char(z, '\n') == False{} : Bool}, hn: {T.has_char(n, '\n') == False{} : Bool}) -> {T.has_char(String.append(z, SCon{' ', n}), '\n') == False{} : Bool}:
  %Equal.sym(Bool, T.has_char(String.append(z, SCon{' ', n}), '\n'), Bool.or(T.has_char(z, '\n'), T.has_char(SCon{' ', n}, '\n')), has_char_app(z, SCon{' ', n}, '\n')) : {_ == False{} : Bool}
  or_false(T.has_char(z, '\n'), T.has_char(SCon{' ', n}, '\n'), hz, hn)

def reads_dir(+fs: List<&2, String>, +ls: List<&2, String>, +dir: String, +n: String, +rest: String, hn: {T.has_char(n, '\n') == False{} : Bool}) -> {Check.seen.go(String.split(String.append("d " ++ n, SCon{'\n', rest}), '\n'), dir, Check.Seen{Nil{}, fs, ls, False{}}) == Check.seen.go(String.split(rest, '\n'), dir, found(Listed.Dir{n}, dir, fs, ls)) : Check.Seen}:
  %Equal.sym(List<&2, String>, String.split(String.append("d " ++ n, SCon{'\n', rest}), '\n'), ("d " ++ n) <> String.split(rest, '\n'), split_nl("d " ++ n, rest, hn)) : {Check.seen.go(_, dir, Check.Seen{Nil{}, fs, ls, False{}}) == Check.seen.go(String.split(rest, '\n'), dir, found(Listed.Dir{n}, dir, fs, ls)) : Check.Seen}
  %SkipL.drop_none(n) : {Check.seen.go(String.split(rest, '\n'), dir, Check.Seen{[dir ++ "/" ++ _], fs, ls, False{}}) == Check.seen.go(String.split(rest, '\n'), dir, found(Listed.Dir{n}, dir, fs, ls)) : Check.Seen}
  {==}

def reads_file(+fs: List<&2, String>, +ls: List<&2, String>, +dir: String, +l: String, +z: String, +n: String, +rest: String, hl: {T.has_char(l, '\n') == False{} : Bool}, el: {String.drop(l, 4n) == String.append(z, SCon{' ', n}) : String}, ek: {Check.kind.of(l) == Check.Entry.File{} : Check.Entry}, hz: {T.has_char(z, ' ') == False{} : Bool}) -> {Check.seen.go(String.split(String.append(l, SCon{'\n', rest}), '\n'), dir, Check.Seen{Nil{}, fs, ls, False{}}) == Check.seen.go(String.split(rest, '\n'), dir, Check.Seen{Nil{}, (dir ++ "/" ++ n) <> fs, ls, False{}}) : Check.Seen}:
  %Equal.sym(List<&2, String>, String.split(String.append(l, SCon{'\n', rest}), '\n'), l <> String.split(rest, '\n'), split_nl(l, rest, hl)) : {Check.seen.go(_, dir, Check.Seen{Nil{}, fs, ls, False{}}) == Check.seen.go(String.split(rest, '\n'), dir, Check.Seen{Nil{}, (dir ++ "/" ++ n) <> fs, ls, False{}}) : Check.Seen}
  %Equal.sym(Check.Entry, Check.kind.of(l), Check.Entry.File{}, ek) : {Check.seen.go(String.split(rest, '\n'), dir, Check.seen.kind(Check.Seen{Nil{}, fs, ls, False{}}, dir, l, _)) == Check.seen.go(String.split(rest, '\n'), dir, Check.Seen{Nil{}, (dir ++ "/" ++ n) <> fs, ls, False{}}) : Check.Seen}
  %Equal.sym(String, String.drop(l, 4n), String.append(z, SCon{' ', n}), el) : {Check.seen.go(String.split(rest, '\n'), dir, Check.Seen{Nil{}, (dir ++ "/" ++ Check.file.name(T.split_once(_))) <> fs, ls, False{}}) == Check.seen.go(String.split(rest, '\n'), dir, Check.Seen{Nil{}, (dir ++ "/" ++ n) <> fs, ls, False{}}) : Check.Seen}
  %Equal.sym(Maybe<&2, T.Split>, T.split_once(String.append(z, SCon{' ', n})), Some{T.Split{z, n}}, split_once_at(z, n, hz)) : {Check.seen.go(String.split(rest, '\n'), dir, Check.Seen{Nil{}, (dir ++ "/" ++ Check.file.name(_)) <> fs, ls, False{}}) == Check.seen.go(String.split(rest, '\n'), dir, Check.Seen{Nil{}, (dir ++ "/" ++ n) <> fs, ls, False{}}) : Check.Seen}
  {==}

def reads_link(+fs: List<&2, String>, +ls: List<&2, String>, +dir: String, +n: String, +t: String, +rest: String, hn: {T.has_char(n, '\n') == False{} : Bool}, ht: {T.has_char(t, '\n') == False{} : Bool}) -> {Check.seen.go(String.split(String.append("l " ++ n, SCon{'\n', String.append(t, SCon{'\n', rest})}), '\n'), dir, Check.Seen{Nil{}, fs, ls, False{}}) == Check.seen.go(String.split(rest, '\n'), dir, found(Listed.Link{n, t}, dir, fs, ls)) : Check.Seen}:
  %Equal.sym(List<&2, String>, String.split(String.append("l " ++ n, SCon{'\n', String.append(t, SCon{'\n', rest})}), '\n'), ("l " ++ n) <> String.split(String.append(t, SCon{'\n', rest}), '\n'), split_nl("l " ++ n, String.append(t, SCon{'\n', rest}), hn)) : {Check.seen.go(_, dir, Check.Seen{Nil{}, fs, ls, False{}}) == Check.seen.go(String.split(rest, '\n'), dir, found(Listed.Link{n, t}, dir, fs, ls)) : Check.Seen}
  %Equal.sym(List<&2, String>, String.split(String.append(t, SCon{'\n', rest}), '\n'), t <> String.split(rest, '\n'), split_nl(t, rest, ht)) : {Check.seen.go(_, dir, Check.Seen{Nil{}, fs, (dir ++ "/" ++ String.drop(n, 0n)) <> ls, True{}}) == Check.seen.go(String.split(rest, '\n'), dir, found(Listed.Link{n, t}, dir, fs, ls)) : Check.Seen}
  %SkipL.drop_none(n) : {Check.seen.go(String.split(rest, '\n'), dir, Check.Seen{Nil{}, fs, (dir ++ "/" ++ _) <> ls, False{}}) == Check.seen.go(String.split(rest, '\n'), dir, found(Listed.Link{n, t}, dir, fs, ls)) : Check.Seen}
  {==}

def reads_unspelled(+fs: List<&2, String>, +ls: List<&2, String>, +dir: String, +n: String, +rest: String, hn: {T.has_char(n, '\n') == False{} : Bool}) -> {Check.seen.go(String.split(String.append("L " ++ n, SCon{'\n', rest}), '\n'), dir, Check.Seen{Nil{}, fs, ls, False{}}) == Check.seen.go(String.split(rest, '\n'), dir, found(Listed.Unspelled{n}, dir, fs, ls)) : Check.Seen}:
  %Equal.sym(List<&2, String>, String.split(String.append("L " ++ n, SCon{'\n', rest}), '\n'), ("L " ++ n) <> String.split(rest, '\n'), split_nl("L " ++ n, rest, hn)) : {Check.seen.go(_, dir, Check.Seen{Nil{}, fs, ls, False{}}) == Check.seen.go(String.split(rest, '\n'), dir, found(Listed.Unspelled{n}, dir, fs, ls)) : Check.Seen}
  %SkipL.drop_none(n) : {Check.seen.go(String.split(rest, '\n'), dir, Check.Seen{Nil{}, fs, (dir ++ "/" ++ _) <> ls, False{}}) == Check.seen.go(String.split(rest, '\n'), dir, found(Listed.Unspelled{n}, dir, fs, ls)) : Check.Seen}
  {==}

def reads_other(+fs: List<&2, String>, +ls: List<&2, String>, +dir: String, +l: String, +rest: String, hl: {T.has_char(l, '\n') == False{} : Bool}, ek: {Check.kind.of(l) == Check.Entry.Other{} : Check.Entry}) -> {Check.seen.go(String.split(String.append(l, SCon{'\n', rest}), '\n'), dir, Check.Seen{Nil{}, fs, ls, False{}}) == Check.seen.go(String.split(rest, '\n'), dir, Check.Seen{Nil{}, fs, ls, False{}}) : Check.Seen}:
  %Equal.sym(List<&2, String>, String.split(String.append(l, SCon{'\n', rest}), '\n'), l <> String.split(rest, '\n'), split_nl(l, rest, hl)) : {Check.seen.go(_, dir, Check.Seen{Nil{}, fs, ls, False{}}) == Check.seen.go(String.split(rest, '\n'), dir, Check.Seen{Nil{}, fs, ls, False{}}) : Check.Seen}
  %Equal.sym(Check.Entry, Check.kind.of(l), Check.Entry.Other{}, ek) : {Check.seen.go(String.split(rest, '\n'), dir, Check.seen.kind(Check.Seen{Nil{}, fs, ls, False{}}, dir, l, _)) == Check.seen.go(String.split(rest, '\n'), dir, Check.Seen{Nil{}, fs, ls, False{}}) : Check.Seen}
  {==}

def file_drop(x: Bool, +z: String, +n: String) -> {String.drop("f " ++ Bool.pick(String, x, "1", "0") ++ " " ++ z ++ " " ++ n, 4n) == String.append(z, SCon{' ', n}) : String}:
  match x:
    case True{}:
      Equal.sym(String, String.append(z, SCon{' ', n}), String.drop(String.append(z, SCon{' ', n}), 0n), SkipL.drop_none(String.append(z, SCon{' ', n})))
    case False{}:
      Equal.sym(String, String.append(z, SCon{' ', n}), String.drop(String.append(z, SCon{' ', n}), 0n), SkipL.drop_none(String.append(z, SCon{' ', n})))

def file_kind(x: Bool, +z: String, +n: String) -> {Check.kind.of("f " ++ Bool.pick(String, x, "1", "0") ++ " " ++ z ++ " " ++ n) == Check.Entry.File{} : Check.Entry}:
  match x:
    case True{}:
      {==}
    case False{}:
      {==}

def file_line_nl(x: Bool, +z: String, +n: String, h: {T.has_char(String.append(z, SCon{' ', n}), '\n') == False{} : Bool}) -> {T.has_char("f " ++ Bool.pick(String, x, "1", "0") ++ " " ++ z ++ " " ++ n, '\n') == False{} : Bool}:
  match x:
    case True{}:
      h
    case False{}:
      h

# `check` reads each line of a directory's listing as the host writes it,
# whatever was found before and whatever follows.
def reads_line(+ds: List<&2, String>, +fs: List<&2, String>, +ls: List<&2, String>, t: Bool, +dir: String, e: Listed, +rest: String, +h: {spelt(e) == True{} : Bool}) -> {Check.walk.step(Check.Seen{ds, fs, ls, t}, dir, Done{line(e) ++ "\n" ++ rest}) == Check.seen.go(String.split(rest, '\n'), dir, found(e, dir, fs, ls)) : Check.Seen}:
  match e:
    case Listed.Dir{+n}:
      reads_dir(fs, ls, dir, n, rest, not_has(n, '\n', h))
    case Listed.File{+x, +z, +n}:
      +hz : {T.has_char(z, ' ') == False{} : Bool} = not_has(z, ' ', Comp.and_left(Bool.not(T.has_char(z, ' ')), Bool.and(Bool.not(T.has_char(z, '\n')), Bool.not(T.has_char(n, '\n'))), h))
      +h2 : {Bool.and(Bool.not(T.has_char(z, '\n')), Bool.not(T.has_char(n, '\n'))) == True{} : Bool} = Comp.and_right(Bool.not(T.has_char(z, ' ')), Bool.and(Bool.not(T.has_char(z, '\n')), Bool.not(T.has_char(n, '\n'))), h)
      +hzn : {T.has_char(z, '\n') == False{} : Bool} = not_has(z, '\n', Comp.and_left(Bool.not(T.has_char(z, '\n')), Bool.not(T.has_char(n, '\n')), h2))
      +hnn : {T.has_char(n, '\n') == False{} : Bool} = not_has(n, '\n', Comp.and_right(Bool.not(T.has_char(z, '\n')), Bool.not(T.has_char(n, '\n')), h2))
      reads_file(fs, ls, dir, "f " ++ Bool.pick(String, x, "1", "0") ++ " " ++ z ++ " " ++ n, z, n, rest, file_line_nl(x, z, n, file_nl(z, n, hzn, hnn)), file_drop(x, z, n), file_kind(x, z, n), hz)
    case Listed.Link{+n, +tg}:
      +hn : {T.has_char(n, '\n') == False{} : Bool} = not_has(n, '\n', Comp.and_left(Bool.not(T.has_char(n, '\n')), Bool.not(T.has_char(tg, '\n')), h))
      +ht : {T.has_char(tg, '\n') == False{} : Bool} = not_has(tg, '\n', Comp.and_right(Bool.not(T.has_char(n, '\n')), Bool.not(T.has_char(tg, '\n')), h))
      %Equal.sym(String, String.append(String.append(n, SCon{'\n', tg}), SCon{'\n', rest}), String.append(n, String.append(SCon{'\n', tg}, SCon{'\n', rest})), SkipL.app_assoc(n, SCon{'\n', tg}, SCon{'\n', rest})) : {Check.seen.go(String.split(SCon{'l', SCon{' ', _}}, '\n'), dir, Check.Seen{Nil{}, fs, ls, False{}}) == Check.seen.go(String.split(rest, '\n'), dir, found(Listed.Link{n, tg}, dir, fs, ls)) : Check.Seen}
      reads_link(fs, ls, dir, n, tg, rest, hn, ht)
    case Listed.Unspelled{+n}:
      reads_unspelled(fs, ls, dir, n, rest, not_has(n, '\n', h))
    case Listed.Lossy{+n}:
      reads_other(fs, ls, dir, "u " ++ n, rest, not_has(n, '\n', h), {==})
    case Listed.Other{+n}:
      reads_other(fs, ls, dir, "o " ++ n, rest, not_has(n, '\n', h), {==})

# The text payloads read
# ----------------------

# Whether the store holds a payload of this digest at this path.
def holds(ps: List<&2, Check.Stored>, +id: String, +path: String) -> Bool:
  match ps:
    case Nil{}:
      False{}
    case Check.Stored{+i, +q} <> rest:
      Bool.or(Bool.and(String.eq(i, id), String.eq(q, path)), holds(rest, id, path))

# Whether every payload a plan reads is one the store holds at the path
# read, under the digest it is read for, a digest `wanted` holds.
def reads_held(plan: List<&2, T.Split>, +ps: List<&2, Check.Stored>, +wanted: List<&2, String>) -> Bool:
  match plan:
    case Nil{}:
      True{}
    case T.Split{+id, +p} <> rest:
      Bool.and(Bool.and(Rev.member(wanted, id), holds(ps, id, p)), reads_held(rest, ps, wanted))

def md(m: Maybe<&2, String>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      Empty

def none_some(-p: String, e: {None{} == Some{p} : Maybe<&2, String>}) -> Empty:
  %e : {md(_) : Type}
  Unit{}

def some_inj(-a: String, +b: String, e: {Some{a} == Some{b} : Maybe<&2, String>}) -> {a == b : String}:
  Equal.cong(Maybe<&2, String>, String, m => Maybe.default(&2, String, m, b), Some{a}, Some{b}, e)

def or_true_right(a: Bool, -b: Bool, h: {b == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      h

def at_holds.at(c: Bool, +i: String, +q: String, +rest: List<&2, Check.Stored>, +id: String, +p: String, ec: {String.eq(i, id) == c : Bool}, e: {Bool.pick(Maybe<&2, String>, c, Some{q}, Check.stored.at(rest, id)) == Some{p} : Maybe<&2, String>}, ih: {Check.stored.at(rest, id) == Some{p} : Maybe<&2, String>} -> {holds(rest, id, p) == True{} : Bool}) -> {Bool.or(Bool.and(c, String.eq(q, p)), holds(rest, id, p)) == True{} : Bool}:
  match c:
    case True{}:
      +qe : {q == p : String} = some_inj(q, p, e)
      %qe : {Bool.or(Bool.and(True{}, String.eq(q, _)), holds(rest, id, p)) == True{} : Bool}
      %Equal.sym(Bool, String.eq(q, q), True{}, S.eq_refl(q)) : {Bool.or(_, holds(rest, id, p)) == True{} : Bool}
      {==}
    case False{}:
      or_true_right(False{}, holds(rest, id, p), ih(e))

# Where `stored.at` finds a payload, the store holds it there.
def at_holds(ps: List<&2, Check.Stored>, +id: String, +p: String, e: {Check.stored.at(ps, id) == Some{p} : Maybe<&2, String>}) -> {holds(ps, id, p) == True{} : Bool}:
  match ps:
    case Nil{}:
      Empty.absurd({holds(Nil{}, id, p) == True{} : Bool}, none_some(p, e))
    case Check.Stored{+i, +q} <> +rest:
      at_holds.at(String.eq(i, id), i, q, rest, id, p, {==}, e, er => at_holds(rest, id, p, er))

def and3(a: Bool, -b: Bool, -c: Bool, ea: {a == True{} : Bool}, eb: {b == True{} : Bool}, ec: {c == True{} : Bool}) -> {Bool.and(Bool.and(a, b), c) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ea) : {Bool.and(Bool.and(_, b), c) == True{} : Bool}
  %Equal.sym(Bool, b, True{}, eb) : {Bool.and(Bool.and(True{}, _), c) == True{} : Bool}
  ec

def and3.two(a: Bool, -b: Bool, ea: {a == True{} : Bool}, eb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ea) : {Bool.and(_, b) == True{} : Bool}
  eb

def planned_held(+id: String, at: Maybe<&2, String>, +ps: List<&2, Check.Stored>, +wanted: List<&2, String>, +more: List<&2, T.Split>, ea: {Check.stored.at(ps, id) == at : Maybe<&2, String>}, hw: {Rev.member(wanted, id) == True{} : Bool}, hm: {reads_held(more, ps, wanted) == True{} : Bool}) -> {reads_held(Check.texts.planned(id, at, more), ps, wanted) == True{} : Bool}:
  match at:
    case None{}:
      hm
    case Some{+p}:
      and3(Rev.member(wanted, id), holds(ps, id, p), reads_held(more, ps, wanted), hw, at_holds(ps, id, p, ea), hm)

# Every payload the plan reads is held where it is read, under a digest
# asked for — of digests each one `wanted` holds.
def plan_held(ids: List<&2, String>, +ps: List<&2, Check.Stored>, +wanted: List<&2, String>, +h: {SortL.all_at(~String, ~List<&2, String>, ~(c => a => Rev.member(c, a)), wanted, ids) == True{} : Bool}) -> {reads_held(Check.texts.plan(ids, ps), ps, wanted) == True{} : Bool}:
  match ids:
    case Nil{}:
      {==}
    case +id <> +rest:
      planned_held(id, Check.stored.at(ps, id), ps, wanted, Check.texts.plan(rest, ps), {==}, Comp.and_left(Rev.member(wanted, id), SortL.all_at(~String, ~List<&2, String>, ~(c => a => Rev.member(c, a)), wanted, rest), h), plan_held(rest, ps, wanted, Comp.and_right(Rev.member(wanted, id), SortL.all_at(~String, ~List<&2, String>, ~(c => a => Rev.member(c, a)), wanted, rest), h)))

def among_cons(ys: List<&2, String>, +z: String, +zs: List<&2, String>, +h: {SortL.all_at(~String, ~List<&2, String>, ~(c => a => Rev.member(c, a)), zs, ys) == True{} : Bool}) -> {SortL.all_at(~String, ~List<&2, String>, ~(c => a => Rev.member(c, a)), z <> zs, ys) == True{} : Bool}:
  match ys:
    case Nil{}:
      {==}
    case +y <> rest:
      and3.two(Bool.or(String.eq(z, y), Rev.member(zs, y)), SortL.all_at(~String, ~List<&2, String>, ~(c => a => Rev.member(c, a)), z <> zs, rest), or_true_right(String.eq(z, y), Rev.member(zs, y), Comp.and_left(Rev.member(zs, y), SortL.all_at(~String, ~List<&2, String>, ~(c => a => Rev.member(c, a)), zs, rest), h)), among_cons(rest, z, zs, Comp.and_right(Rev.member(zs, y), SortL.all_at(~String, ~List<&2, String>, ~(c => a => Rev.member(c, a)), zs, rest), h)))

def among_self(xs: List<&2, String>) -> {SortL.all_at(~String, ~List<&2, String>, ~(c => a => Rev.member(c, a)), xs, xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      %Equal.sym(Bool, String.eq(x, x), True{}, S.eq_refl(x)) : {Bool.and(Bool.or(_, Rev.member(rest, x)), SortL.all_at(~String, ~List<&2, String>, ~(c => a => Rev.member(c, a)), x <> rest, rest)) == True{} : Bool}
      among_cons(rest, x, rest, among_self(rest))

# Keeping each digest once keeps no digest it was not given.
def distinct_among(xs: List<&2, String>, +last: Maybe<&2, String>, dup: Bool, +w: List<&2, String>, +h: {SortL.all_at(~String, ~List<&2, String>, ~(c => a => Rev.member(c, a)), w, xs) == True{} : Bool}) -> {SortL.all_at(~String, ~List<&2, String>, ~(c => a => Rev.member(c, a)), w, Check.distinct.go(xs, last, dup)) == True{} : Bool}:
  match xs dup:
    case Nil{} _:
      {==}
    case +x <> +rest True{}:
      distinct_among(rest, last, Check.distinct.dup(rest, last), w, Comp.and_right(Rev.member(w, x), SortL.all_at(~String, ~List<&2, String>, ~(c => a => Rev.member(c, a)), w, rest), h))
    case +x <> +rest False{}:
      and3.two(Rev.member(w, x), SortL.all_at(~String, ~List<&2, String>, ~(c => a => Rev.member(c, a)), w, Check.distinct.go(rest, Some{x}, Check.distinct.dup(rest, Some{x}))), Comp.and_left(Rev.member(w, x), SortL.all_at(~String, ~List<&2, String>, ~(c => a => Rev.member(c, a)), w, rest), h), distinct_among(rest, Some{x}, Check.distinct.dup(rest, Some{x}), w, Comp.and_right(Rev.member(w, x), SortL.all_at(~String, ~List<&2, String>, ~(c => a => Rev.member(c, a)), w, rest), h)))

# The set of some digests holds none but them.
def set_among(+xs: List<&2, String>) -> {SortL.all_at(~String, ~List<&2, String>, ~(c => a => Rev.member(c, a)), xs, Check.set.of(xs)) == True{} : Bool}:
  distinct_among(Check.by_digest(xs), None{}, False{}, xs, SortL.all_sort_at(~String, ~(a => b => String.is_le(a, b)), ~List<&2, String>, ~(c => a => Rev.member(c, a)), xs, xs, among_self(xs)))

# `check` reads as a file's lines only payloads the store holds under a
# digest some revision's `text` header names, each from where it holds it.
def reads_text(+docs: List<&2, Main.Full>, +ps: List<&2, Check.Stored>) -> {reads_held(Check.texts.plan(Check.set.of(Check.text.ids(docs)), ps), ps, Check.text.ids(docs)) == True{} : Bool}:
  plan_held(Check.set.of(Check.text.ids(docs)), ps, Check.text.ids(docs), set_among(Check.text.ids(docs)))
