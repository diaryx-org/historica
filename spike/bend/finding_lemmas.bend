# What `check` says of what it found, and whether it fails: the Rust
# tool's `render::report` and `Report::is_ok`, held to a reading of the
# findings as a list rather than to the folds the port prints them with.
import Base
import ./check.bend as Check
import ./string_lemmas.bend as S

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
