# What each command reads its words as, said as plain facts about the
# words rather than through the command's own reading of them: a flag
# counts where it is among the words, wherever it stands; a command line is
# accepted exactly where every word starting `-` is one of the command's
# flags and the other words are as many as it takes; and those other words,
# in the order they were typed, are what the command holds.
import Base
import ./text.bend as T
import ./revision.bend as Rev
import ./tree.bend as Tree
import ./commands.bend as Main
import ./arrange.bend as Arrange
import ./prune.bend as Prune
import ./receive.bend as Receive
import ./offer.bend as Offer
import ./export.bend as Export
import ./string_lemmas.bend as S
import ./survey_lemmas.bend as SurveyL

# Booleans
# --------

def or_true_r(a: Bool) -> {True{} == Bool.or(a, True{}) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def or_false(c: Bool) -> {c == Bool.or(c, False{}) : Bool}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

def or_mid(y: Bool, a: Bool, -b: Bool) -> {Bool.or(y, Bool.or(a, b)) == Bool.or(a, Bool.or(y, b)) : Bool}:
  match y:
    case True{}:
      or_true_r(a)
    case False{}:
      {==}

# Two flags counted word by word are each counted over the words.
def or_swap(x: Bool, y: Bool, a: Bool, -b: Bool) -> {Bool.or(Bool.or(x, y), Bool.or(a, b)) == Bool.or(Bool.or(x, a), Bool.or(y, b)) : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      or_mid(y, a, b)

def or3.b(b: Bool, c: Bool) -> {Bool.or(b, c) == Bool.or(b, Bool.or(c, False{})) : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      or_false(c)

def or3(a: Bool, b: Bool, c: Bool) -> {Bool.or(Bool.or(a, b), c) == Bool.or(a, Bool.or(b, Bool.or(c, False{}))) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      or3.b(b, c)

def pick_and(-A: Type, a: Bool, -b: Bool, -x: A, -n: A) -> {Bool.pick(A, a, Bool.pick(A, b, x, n), n) == Bool.pick(A, Bool.and(a, b), x, n) : A}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

# Three flags: a word is one of them exactly where it is among them.
def among3(+w: String, +a: String, +b: String, +c: String) -> {Bool.or(Bool.or(String.eq(w, a), String.eq(w, b)), String.eq(w, c)) == Rev.member([a, b, c], w) : Bool}:
  %SurveyL.eq_sym(w, a) : {Bool.or(Bool.or(String.eq(w, a), String.eq(w, b)), String.eq(w, c)) == Bool.or(_, Bool.or(String.eq(b, w), Bool.or(String.eq(c, w), False{}))) : Bool}
  %SurveyL.eq_sym(w, b) : {Bool.or(Bool.or(String.eq(w, a), String.eq(w, b)), String.eq(w, c)) == Bool.or(String.eq(w, a), Bool.or(_, Bool.or(String.eq(c, w), False{}))) : Bool}
  %SurveyL.eq_sym(w, c) : {Bool.or(Bool.or(String.eq(w, a), String.eq(w, b)), String.eq(w, c)) == Bool.or(String.eq(w, a), Bool.or(String.eq(w, b), Bool.or(_, False{}))) : Bool}
  or3(String.eq(w, a), String.eq(w, b), String.eq(w, c))

# The words that do not start `-`, kept one at a time.
def keep_put(c: Bool, +w: String, -r: List<&2, String>) -> {Tree.keep(~String, c, w, r) == List.filter.put(String, w, r, c) : List<&2, String>}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

# `arrange`
# ---------

def arr.dry(ws: List<&2, String>) -> {Arrange.any_dry(ws) == Bool.or(Rev.member(ws, "-n"), Rev.member(ws, "--dry-run")) : Bool}:
  match ws:
    case Nil{}:
      {==}
    case +w <> +rest:
      %Equal.sym(Bool, Arrange.any_dry(rest), Bool.or(Rev.member(rest, "-n"), Rev.member(rest, "--dry-run")), arr.dry(rest)) : {Bool.or(Bool.or(String.eq(w, "-n"), String.eq(w, "--dry-run")), _) == Bool.or(Rev.member(w <> rest, "-n"), Rev.member(w <> rest, "--dry-run")) : Bool}
      or_swap(String.eq(w, "-n"), String.eq(w, "--dry-run"), Rev.member(rest, "-n"), Rev.member(rest, "--dry-run"))

def arr.refile(ws: List<&2, String>) -> {Arrange.any_refile(ws) == Rev.member(ws, "--refile") : Bool}:
  match ws:
    case Nil{}:
      {==}
    case +w <> +rest:
      Equal.cong(Bool, Bool, x => Bool.or(String.eq(w, "--refile"), x), Arrange.any_refile(rest), Rev.member(rest, "--refile"), arr.refile(rest))

def arr.step(c: Bool, +d: Bool, +r: Bool, +w: String, -rest: List<&2, String>, ih: {Arrange.accepted(Arrange.ArrangeCmd, Arrange.args.of(d, r, Arrange.first_other(rest))) == Bool.pick(Maybe<&2, Arrange.ArrangeCmd>, List.all(~&2, ~String, ~(v => Rev.member(["-n", "--dry-run", "--refile"], v)), rest), Some{Arrange.ArrangeCmd{d, r}}, None{}) : Maybe<&2, Arrange.ArrangeCmd>}) -> {Arrange.accepted(Arrange.ArrangeCmd, Arrange.args.of(d, r, Bool.pick(Maybe<&2, String>, c, Arrange.first_other(rest), Some{w}))) == Bool.pick(Maybe<&2, Arrange.ArrangeCmd>, Bool.and(c, List.all(~&2, ~String, ~(v => Rev.member(["-n", "--dry-run", "--refile"], v)), rest)), Some{Arrange.ArrangeCmd{d, r}}, None{}) : Maybe<&2, Arrange.ArrangeCmd>}:
  match c:
    case True{}:
      ih
    case False{}:
      {==}

def arr.shape(+d: Bool, +r: Bool, ws: List<&2, String>) -> {Arrange.accepted(Arrange.ArrangeCmd, Arrange.args.of(d, r, Arrange.first_other(ws))) == Bool.pick(Maybe<&2, Arrange.ArrangeCmd>, List.all(~&2, ~String, ~(v => Rev.member(["-n", "--dry-run", "--refile"], v)), ws), Some{Arrange.ArrangeCmd{d, r}}, None{}) : Maybe<&2, Arrange.ArrangeCmd>}:
  match ws:
    case Nil{}:
      {==}
    case +w <> +rest:
      %among3(w, "-n", "--dry-run", "--refile") : {Arrange.accepted(Arrange.ArrangeCmd, Arrange.args.of(d, r, Arrange.first_other(w <> rest))) == Bool.pick(Maybe<&2, Arrange.ArrangeCmd>, Bool.and(_, List.all(~&2, ~String, ~(v => Rev.member(["-n", "--dry-run", "--refile"], v)), rest)), Some{Arrange.ArrangeCmd{d, r}}, None{}) : Maybe<&2, Arrange.ArrangeCmd>}
      arr.step(Arrange.is_flag(w), d, r, w, rest, arr.shape(d, r, rest))

# `arrange` accepts a command line exactly where every word is `-n`,
# `--dry-run` or `--refile`, and then plans only where one of the first two
# is among them and refiles only where the third is.
def arrange_words(+ws: List<&2, String>) -> {Arrange.accepted(Arrange.ArrangeCmd, Arrange.args.r(ws)) == Bool.pick(Maybe<&2, Arrange.ArrangeCmd>, List.all(~&2, ~String, ~(w => Rev.member(["-n", "--dry-run", "--refile"], w)), ws), Some{Arrange.ArrangeCmd{Bool.or(Rev.member(ws, "-n"), Rev.member(ws, "--dry-run")), Rev.member(ws, "--refile")}}, None{}) : Maybe<&2, Arrange.ArrangeCmd>}:
  %arr.dry(ws) : {Arrange.accepted(Arrange.ArrangeCmd, Arrange.args.r(ws)) == Bool.pick(Maybe<&2, Arrange.ArrangeCmd>, List.all(~&2, ~String, ~(w => Rev.member(["-n", "--dry-run", "--refile"], w)), ws), Some{Arrange.ArrangeCmd{_, Rev.member(ws, "--refile")}}, None{}) : Maybe<&2, Arrange.ArrangeCmd>}
  %arr.refile(ws) : {Arrange.accepted(Arrange.ArrangeCmd, Arrange.args.r(ws)) == Bool.pick(Maybe<&2, Arrange.ArrangeCmd>, List.all(~&2, ~String, ~(w => Rev.member(["-n", "--dry-run", "--refile"], w)), ws), Some{Arrange.ArrangeCmd{Arrange.any_dry(ws), _}}, None{}) : Maybe<&2, Arrange.ArrangeCmd>}
  arr.shape(Arrange.any_dry(ws), Arrange.any_refile(ws), ws)

# `prune`
# -------

def prn.dry(ws: List<&2, String>) -> {Prune.any_dry(ws) == Bool.or(Rev.member(ws, "-n"), Rev.member(ws, "--dry-run")) : Bool}:
  match ws:
    case Nil{}:
      {==}
    case +w <> +rest:
      %Equal.sym(Bool, Prune.any_dry(rest), Bool.or(Rev.member(rest, "-n"), Rev.member(rest, "--dry-run")), prn.dry(rest)) : {Bool.or(Bool.or(String.eq(w, "-n"), String.eq(w, "--dry-run")), _) == Bool.or(Rev.member(w <> rest, "-n"), Rev.member(w <> rest, "--dry-run")) : Bool}
      or_swap(String.eq(w, "-n"), String.eq(w, "--dry-run"), Rev.member(rest, "-n"), Rev.member(rest, "--dry-run"))

def prn.fields(ws: List<&2, String>) -> {Prune.any_fields(ws) == Rev.member(ws, "--fields") : Bool}:
  match ws:
    case Nil{}:
      {==}
    case +w <> +rest:
      Equal.cong(Bool, Bool, x => Bool.or(String.eq(w, "--fields"), x), Prune.any_fields(rest), Rev.member(rest, "--fields"), prn.fields(rest))

def prn.planned(d: Bool, f: Bool) -> {Arrange.accepted(Prune.PruneCmd, Prune.args.planned(d, f)) == Bool.pick(Maybe<&2, Prune.PruneCmd>, Bool.not(Bool.and(d, f)), Some{Prune.PruneCmd{d, f}}, None{}) : Maybe<&2, Prune.PruneCmd>}:
  match d:
    case True{}:
      match f:
        case True{}:
          {==}
        case False{}:
          {==}
    case False{}:
      {==}

def prn.step(c: Bool, +d: Bool, +f: Bool, +w: String, -rest: List<&2, String>, ih: {Arrange.accepted(Prune.PruneCmd, Prune.args.of(d, f, Prune.first_other(rest))) == Bool.pick(Maybe<&2, Prune.PruneCmd>, List.all(~&2, ~String, ~(v => Rev.member(["-n", "--dry-run", "--fields"], v)), rest), Arrange.accepted(Prune.PruneCmd, Prune.args.planned(d, f)), None{}) : Maybe<&2, Prune.PruneCmd>}) -> {Arrange.accepted(Prune.PruneCmd, Prune.args.of(d, f, Bool.pick(Maybe<&2, String>, c, Prune.first_other(rest), Some{w}))) == Bool.pick(Maybe<&2, Prune.PruneCmd>, Bool.and(c, List.all(~&2, ~String, ~(v => Rev.member(["-n", "--dry-run", "--fields"], v)), rest)), Arrange.accepted(Prune.PruneCmd, Prune.args.planned(d, f)), None{}) : Maybe<&2, Prune.PruneCmd>}:
  match c:
    case True{}:
      ih
    case False{}:
      {==}

def prn.shape(+d: Bool, +f: Bool, ws: List<&2, String>) -> {Arrange.accepted(Prune.PruneCmd, Prune.args.of(d, f, Prune.first_other(ws))) == Bool.pick(Maybe<&2, Prune.PruneCmd>, List.all(~&2, ~String, ~(v => Rev.member(["-n", "--dry-run", "--fields"], v)), ws), Arrange.accepted(Prune.PruneCmd, Prune.args.planned(d, f)), None{}) : Maybe<&2, Prune.PruneCmd>}:
  match ws:
    case Nil{}:
      {==}
    case +w <> +rest:
      %among3(w, "-n", "--dry-run", "--fields") : {Arrange.accepted(Prune.PruneCmd, Prune.args.of(d, f, Prune.first_other(w <> rest))) == Bool.pick(Maybe<&2, Prune.PruneCmd>, Bool.and(_, List.all(~&2, ~String, ~(v => Rev.member(["-n", "--dry-run", "--fields"], v)), rest)), Arrange.accepted(Prune.PruneCmd, Prune.args.planned(d, f)), None{}) : Maybe<&2, Prune.PruneCmd>}
      prn.step(Prune.is_flag(w), d, f, w, rest, prn.shape(d, f, rest))

# `prune` accepts a command line exactly where every word is `-n`,
# `--dry-run` or `--fields` and it does not hold both a flag asking for a
# plan and `--fields`; and then it plans only where one of the first two is
# among them, and states what is on disk only where `--fields` is.
def prune_words(+ws: List<&2, String>) -> {Arrange.accepted(Prune.PruneCmd, Prune.args.r(ws)) == Bool.pick(Maybe<&2, Prune.PruneCmd>, Bool.and(List.all(~&2, ~String, ~(w => Rev.member(["-n", "--dry-run", "--fields"], w)), ws), Bool.not(Bool.and(Bool.or(Rev.member(ws, "-n"), Rev.member(ws, "--dry-run")), Rev.member(ws, "--fields")))), Some{Prune.PruneCmd{Bool.or(Rev.member(ws, "-n"), Rev.member(ws, "--dry-run")), Rev.member(ws, "--fields")}}, None{}) : Maybe<&2, Prune.PruneCmd>}:
  %prn.dry(ws) : {Arrange.accepted(Prune.PruneCmd, Prune.args.r(ws)) == Bool.pick(Maybe<&2, Prune.PruneCmd>, Bool.and(List.all(~&2, ~String, ~(w => Rev.member(["-n", "--dry-run", "--fields"], w)), ws), Bool.not(Bool.and(_, Rev.member(ws, "--fields")))), Some{Prune.PruneCmd{_, Rev.member(ws, "--fields")}}, None{}) : Maybe<&2, Prune.PruneCmd>}
  %prn.fields(ws) : {Arrange.accepted(Prune.PruneCmd, Prune.args.r(ws)) == Bool.pick(Maybe<&2, Prune.PruneCmd>, Bool.and(List.all(~&2, ~String, ~(w => Rev.member(["-n", "--dry-run", "--fields"], w)), ws), Bool.not(Bool.and(Prune.any_dry(ws), _))), Some{Prune.PruneCmd{Prune.any_dry(ws), _}}, None{}) : Maybe<&2, Prune.PruneCmd>}
  %pick_and(Maybe<&2, Prune.PruneCmd>, List.all(~&2, ~String, ~(w => Rev.member(["-n", "--dry-run", "--fields"], w)), ws), Bool.not(Bool.and(Prune.any_dry(ws), Prune.any_fields(ws))), Some{Prune.PruneCmd{Prune.any_dry(ws), Prune.any_fields(ws)}}, None{}) : {Arrange.accepted(Prune.PruneCmd, Prune.args.r(ws)) == _ : Maybe<&2, Prune.PruneCmd>}
  %prn.planned(Prune.any_dry(ws), Prune.any_fields(ws)) : {Arrange.accepted(Prune.PruneCmd, Prune.args.r(ws)) == Bool.pick(Maybe<&2, Prune.PruneCmd>, List.all(~&2, ~String, ~(w => Rev.member(["-n", "--dry-run", "--fields"], w)), ws), _, None{}) : Maybe<&2, Prune.PruneCmd>}
  prn.shape(Prune.any_dry(ws), Prune.any_fields(ws), ws)

# `offer`
# -------

def off.plain(ws: List<&2, String>) -> {Offer.args.read(Offer.args.plain(ws)) == Bool.pick(Maybe<&2, List<&2, String>>, Nat.is_eq(List.length(&2, String, ws), 1n), Some{ws}, None{}) : Maybe<&2, List<&2, String>>}:
  match ws:
    case Nil{}:
      {==}
    case +w <> rest:
      match rest:
        case Nil{}:
          {==}
        case x <> more:
          {==}

def off.step(c: Bool, +w: String, +ws0: List<&2, String>, -rest: List<&2, String>, ih: {Offer.args.read(Offer.args.of(ws0, Offer.first_dash(rest))) == Bool.pick(Maybe<&2, List<&2, String>>, List.all(~&2, ~String, ~(v => Bool.not(String.starts_with(v, "-"))), rest), Offer.args.read(Offer.args.plain(ws0)), None{}) : Maybe<&2, List<&2, String>>}) -> {Offer.args.read(Offer.args.of(ws0, Bool.pick(Maybe<&2, String>, c, Some{w}, Offer.first_dash(rest)))) == Bool.pick(Maybe<&2, List<&2, String>>, Bool.and(Bool.not(c), List.all(~&2, ~String, ~(v => Bool.not(String.starts_with(v, "-"))), rest)), Offer.args.read(Offer.args.plain(ws0)), None{}) : Maybe<&2, List<&2, String>>}:
  match c:
    case True{}:
      {==}
    case False{}:
      ih

def off.shape(+ws0: List<&2, String>, ws: List<&2, String>) -> {Offer.args.read(Offer.args.of(ws0, Offer.first_dash(ws))) == Bool.pick(Maybe<&2, List<&2, String>>, List.all(~&2, ~String, ~(v => Bool.not(String.starts_with(v, "-"))), ws), Offer.args.read(Offer.args.plain(ws0)), None{}) : Maybe<&2, List<&2, String>>}:
  match ws:
    case Nil{}:
      {==}
    case +w <> +rest:
      off.step(String.starts_with(w, "-"), w, ws0, rest, off.shape(ws0, rest))

# `offer` accepts a command line exactly where it is one word, not starting
# `-`, and then that word is the directory.
def offer_words(+ws: List<&2, String>) -> {Offer.args.read(Offer.args.r(ws)) == Bool.pick(Maybe<&2, List<&2, String>>, Bool.and(List.all(~&2, ~String, ~(w => Bool.not(String.starts_with(w, "-"))), ws), Nat.is_eq(List.length(&2, String, ws), 1n)), Some{ws}, None{}) : Maybe<&2, List<&2, String>>}:
  %pick_and(Maybe<&2, List<&2, String>>, List.all(~&2, ~String, ~(w => Bool.not(String.starts_with(w, "-"))), ws), Nat.is_eq(List.length(&2, String, ws), 1n), Some{ws}, None{}) : {Offer.args.read(Offer.args.r(ws)) == _ : Maybe<&2, List<&2, String>>}
  %off.plain(ws) : {Offer.args.read(Offer.args.r(ws)) == Bool.pick(Maybe<&2, List<&2, String>>, List.all(~&2, ~String, ~(w => Bool.not(String.starts_with(w, "-"))), ws), _, None{}) : Maybe<&2, List<&2, String>>}
  off.shape(ws, ws)

# `export`
# --------

def exp.dry(ws: List<&2, String>) -> {Export.any_dry(ws) == Bool.or(Rev.member(ws, "-n"), Rev.member(ws, "--dry-run")) : Bool}:
  match ws:
    case Nil{}:
      {==}
    case +w <> +rest:
      %Equal.sym(Bool, Export.any_dry(rest), Bool.or(Rev.member(rest, "-n"), Rev.member(rest, "--dry-run")), exp.dry(rest)) : {Bool.or(Bool.or(String.eq(w, "-n"), String.eq(w, "--dry-run")), _) == Bool.or(Rev.member(w <> rest, "-n"), Rev.member(w <> rest, "--dry-run")) : Bool}
      or_swap(String.eq(w, "-n"), String.eq(w, "--dry-run"), Rev.member(rest, "-n"), Rev.member(rest, "--dry-run"))

def exp.files(ws: List<&2, String>) -> {Export.any_files(ws) == Rev.member(ws, "--files-only") : Bool}:
  match ws:
    case Nil{}:
      {==}
    case +w <> +rest:
      Equal.cong(Bool, Bool, x => Bool.or(String.eq(w, "--files-only"), x), Export.any_files(rest), Rev.member(rest, "--files-only"), exp.files(rest))

def exp.plain(ws: List<&2, String>) -> {Export.plain(ws) == List.filter(~String, ~(w => Bool.not(String.starts_with(w, "-"))), ws) : List<&2, String>}:
  match ws:
    case Nil{}:
      {==}
    case +w <> +rest:
      %exp.plain(rest) : {Tree.keep(~String, Bool.not(String.starts_with(w, "-")), w, Export.plain(rest)) == List.filter.put(String, w, _, Bool.not(String.starts_with(w, "-"))) : List<&2, String>}
      keep_put(Bool.not(String.starts_with(w, "-")), w, Export.plain(rest))

def exp.words(+d: Bool, +f: Bool, ps: List<&2, String>) -> {Export.args.read(Export.args.words(d, f, ps)) == Bool.pick(Maybe<&2, Export.Said>, Bool.and(Nat.is_le(1n, List.length(&2, String, ps)), Nat.is_le(List.length(&2, String, ps), 2n)), Some{Export.Said{d, f, ps}}, None{}) : Maybe<&2, Export.Said>}:
  match ps:
    case Nil{}:
      {==}
    case +a <> rest:
      match rest:
        case Nil{}:
          {==}
        case +b <> more:
          match more:
            case Nil{}:
              {==}
            case x <> tail:
              {==}

def exp.flag(f: Bool, +w: String, +ws0: List<&2, String>, -rest: List<&2, String>, ih: {Export.args.read(Export.args.of(ws0, Export.stray(rest))) == Bool.pick(Maybe<&2, Export.Said>, List.all(~&2, ~String, ~(v => Rev.member(["-n", "--dry-run", "--files-only"], v)), List.filter(~String, ~(u => String.starts_with(u, "-")), rest)), Export.args.read(Export.args.words(Export.any_dry(ws0), Export.any_files(ws0), Export.plain(ws0))), None{}) : Maybe<&2, Export.Said>}) -> {Export.args.read(Export.args.of(ws0, Bool.pick(Maybe<&2, String>, Bool.not(f), Some{w}, Export.stray(rest)))) == Bool.pick(Maybe<&2, Export.Said>, Bool.and(f, List.all(~&2, ~String, ~(v => Rev.member(["-n", "--dry-run", "--files-only"], v)), List.filter(~String, ~(u => String.starts_with(u, "-")), rest))), Export.args.read(Export.args.words(Export.any_dry(ws0), Export.any_files(ws0), Export.plain(ws0))), None{}) : Maybe<&2, Export.Said>}:
  match f:
    case True{}:
      ih
    case False{}:
      {==}

def exp.step(s: Bool, f: Bool, +w: String, +ws0: List<&2, String>, -rest: List<&2, String>, ek: {f == Rev.member(["-n", "--dry-run", "--files-only"], w) : Bool}, ih: {Export.args.read(Export.args.of(ws0, Export.stray(rest))) == Bool.pick(Maybe<&2, Export.Said>, List.all(~&2, ~String, ~(v => Rev.member(["-n", "--dry-run", "--files-only"], v)), List.filter(~String, ~(u => String.starts_with(u, "-")), rest)), Export.args.read(Export.args.words(Export.any_dry(ws0), Export.any_files(ws0), Export.plain(ws0))), None{}) : Maybe<&2, Export.Said>}) -> {Export.args.read(Export.args.of(ws0, Bool.pick(Maybe<&2, String>, Bool.and(s, Bool.not(f)), Some{w}, Export.stray(rest)))) == Bool.pick(Maybe<&2, Export.Said>, List.all(~&2, ~String, ~(v => Rev.member(["-n", "--dry-run", "--files-only"], v)), List.filter.put(String, w, List.filter(~String, ~(u => String.starts_with(u, "-")), rest), s)), Export.args.read(Export.args.words(Export.any_dry(ws0), Export.any_files(ws0), Export.plain(ws0))), None{}) : Maybe<&2, Export.Said>}:
  match s:
    case False{}:
      ih
    case True{}:
      %ek : {Export.args.read(Export.args.of(ws0, Bool.pick(Maybe<&2, String>, Bool.not(f), Some{w}, Export.stray(rest)))) == Bool.pick(Maybe<&2, Export.Said>, Bool.and(_, List.all(~&2, ~String, ~(v => Rev.member(["-n", "--dry-run", "--files-only"], v)), List.filter(~String, ~(u => String.starts_with(u, "-")), rest))), Export.args.read(Export.args.words(Export.any_dry(ws0), Export.any_files(ws0), Export.plain(ws0))), None{}) : Maybe<&2, Export.Said>}
      exp.flag(f, w, ws0, rest, ih)

def exp.shape(+ws0: List<&2, String>, ws: List<&2, String>) -> {Export.args.read(Export.args.of(ws0, Export.stray(ws))) == Bool.pick(Maybe<&2, Export.Said>, List.all(~&2, ~String, ~(v => Rev.member(["-n", "--dry-run", "--files-only"], v)), List.filter(~String, ~(u => String.starts_with(u, "-")), ws)), Export.args.read(Export.args.words(Export.any_dry(ws0), Export.any_files(ws0), Export.plain(ws0))), None{}) : Maybe<&2, Export.Said>}:
  match ws:
    case Nil{}:
      {==}
    case +w <> +rest:
      exp.step(String.starts_with(w, "-"), Export.is_flag(w), w, ws0, rest, among3(w, "-n", "--dry-run", "--files-only"), exp.shape(ws0, rest))

# `export` accepts a command line exactly where the words starting `-` are
# all `-n`, `--dry-run` or `--files-only` and one or two words do not start
# `-`; and then it plans only where one of the first two flags is among
# them, writes the files alone only where the third is, and its directory
# and target, written back, are those other words in the order typed.
def export_words(+ws: List<&2, String>) -> {Export.args.read(Export.args.r(ws)) == Bool.pick(Maybe<&2, Export.Said>, Bool.and(List.all(~&2, ~String, ~(w => Rev.member(["-n", "--dry-run", "--files-only"], w)), List.filter(~String, ~(w => String.starts_with(w, "-")), ws)), Bool.and(Nat.is_le(1n, List.length(&2, String, List.filter(~String, ~(w => Bool.not(String.starts_with(w, "-"))), ws))), Nat.is_le(List.length(&2, String, List.filter(~String, ~(w => Bool.not(String.starts_with(w, "-"))), ws)), 2n))), Some{Export.Said{Bool.or(Rev.member(ws, "-n"), Rev.member(ws, "--dry-run")), Rev.member(ws, "--files-only"), List.filter(~String, ~(w => Bool.not(String.starts_with(w, "-"))), ws)}}, None{}) : Maybe<&2, Export.Said>}:
  %exp.dry(ws) : {Export.args.read(Export.args.r(ws)) == Bool.pick(Maybe<&2, Export.Said>, Bool.and(List.all(~&2, ~String, ~(w => Rev.member(["-n", "--dry-run", "--files-only"], w)), List.filter(~String, ~(w => String.starts_with(w, "-")), ws)), Bool.and(Nat.is_le(1n, List.length(&2, String, List.filter(~String, ~(w => Bool.not(String.starts_with(w, "-"))), ws))), Nat.is_le(List.length(&2, String, List.filter(~String, ~(w => Bool.not(String.starts_with(w, "-"))), ws)), 2n))), Some{Export.Said{_, Rev.member(ws, "--files-only"), List.filter(~String, ~(w => Bool.not(String.starts_with(w, "-"))), ws)}}, None{}) : Maybe<&2, Export.Said>}
  %exp.files(ws) : {Export.args.read(Export.args.r(ws)) == Bool.pick(Maybe<&2, Export.Said>, Bool.and(List.all(~&2, ~String, ~(w => Rev.member(["-n", "--dry-run", "--files-only"], w)), List.filter(~String, ~(w => String.starts_with(w, "-")), ws)), Bool.and(Nat.is_le(1n, List.length(&2, String, List.filter(~String, ~(w => Bool.not(String.starts_with(w, "-"))), ws))), Nat.is_le(List.length(&2, String, List.filter(~String, ~(w => Bool.not(String.starts_with(w, "-"))), ws)), 2n))), Some{Export.Said{Export.any_dry(ws), _, List.filter(~String, ~(w => Bool.not(String.starts_with(w, "-"))), ws)}}, None{}) : Maybe<&2, Export.Said>}
  %exp.plain(ws) : {Export.args.read(Export.args.r(ws)) == Bool.pick(Maybe<&2, Export.Said>, Bool.and(List.all(~&2, ~String, ~(w => Rev.member(["-n", "--dry-run", "--files-only"], w)), List.filter(~String, ~(w => String.starts_with(w, "-")), ws)), Bool.and(Nat.is_le(1n, List.length(&2, String, _)), Nat.is_le(List.length(&2, String, _), 2n))), Some{Export.Said{Export.any_dry(ws), Export.any_files(ws), _}}, None{}) : Maybe<&2, Export.Said>}
  %pick_and(Maybe<&2, Export.Said>, List.all(~&2, ~String, ~(w => Rev.member(["-n", "--dry-run", "--files-only"], w)), List.filter(~String, ~(w => String.starts_with(w, "-")), ws)), Bool.and(Nat.is_le(1n, List.length(&2, String, Export.plain(ws))), Nat.is_le(List.length(&2, String, Export.plain(ws)), 2n)), Some{Export.Said{Export.any_dry(ws), Export.any_files(ws), Export.plain(ws)}}, None{}) : {Export.args.read(Export.args.r(ws)) == _ : Maybe<&2, Export.Said>}
  %exp.words(Export.any_dry(ws), Export.any_files(ws), Export.plain(ws)) : {Export.args.read(Export.args.r(ws)) == Bool.pick(Maybe<&2, Export.Said>, List.all(~&2, ~String, ~(w => Rev.member(["-n", "--dry-run", "--files-only"], w)), List.filter(~String, ~(w => String.starts_with(w, "-")), ws)), _, None{}) : Maybe<&2, Export.Said>}
  exp.shape(ws, ws)

# `receive`
# ---------

# `receive` reads its words in one pass, each flag setting what it asks
# for and the first other word being the source; what that pass has read
# so far and what the rest of the words say come to what the whole of the
# words says.

def recv.known(+v: String) -> Bool:
  Bool.or(String.eq(v, "-n"), Bool.or(String.eq(v, "--dry-run"), Bool.or(String.eq(v, "--fields"), Bool.or(String.eq(v, "--join-unrelated"), False{}))))

def recv.aq(ws: List<&2, String>) -> Bool:
  match ws:
    case Nil{}:
      True{}
    case +w <> rest:
      Bool.and(Bool.or(Bool.not(String.starts_with(w, "-")), recv.known(w)), recv.aq(rest))

def recv.dq(ws: List<&2, String>) -> Bool:
  match ws:
    case Nil{}:
      False{}
    case +w <> rest:
      Bool.or(Bool.or(String.eq(w, "-n"), String.eq(w, "--dry-run")), recv.dq(rest))

def recv.src(m: Maybe<&2, String>) -> List<&2, String>:
  match m:
    case None{}:
      Nil{}
    case Some{x}:
      [x]

# What reading these words says, given what was read before them.
def recv.goal(+ws: List<&2, String>, +d: Bool, +f: Bool, +j: Bool, +src: Maybe<&2, String>) -> Type:
  {Receive.args.read(Receive.args.go(ws, Receive.rword.of(ws), d, f, j, src)) == Bool.pick(Maybe<&2, Receive.Said>, Bool.and(recv.aq(ws), Bool.and(Nat.is_eq(List.length(&2, String, List.append(&2, String, recv.src(src), List.filter(~String, ~(u => Bool.not(String.starts_with(u, "-"))), ws))), 1n), Bool.not(Bool.and(Bool.or(d, recv.dq(ws)), Bool.or(f, Rev.member(ws, "--fields")))))), Some{Receive.Said{Bool.or(d, recv.dq(ws)), Bool.or(f, Rev.member(ws, "--fields")), Bool.or(j, Rev.member(ws, "--join-unrelated")), List.append(&2, String, recv.src(src), List.filter(~String, ~(u => Bool.not(String.starts_with(u, "-"))), ws))}}, None{}) : Maybe<&2, Receive.Said>}

# The same, for words `w <> rest` whose first word's kind is said by
# `e1`..`e4` and `s`.
def recv.step.goal(+e1: Bool, +e2: Bool, +e3: Bool, +e4: Bool, +s: Bool, +w: String, +rest: List<&2, String>, +d: Bool, +f: Bool, +j: Bool, +src: Maybe<&2, String>) -> Type:
  {Receive.args.read(Receive.args.go(w <> rest, Bool.pick(Receive.RWord, Bool.or(e1, e2), Receive.RWord.Dry{}, Bool.pick(Receive.RWord, e3, Receive.RWord.Fields{}, Bool.pick(Receive.RWord, e4, Receive.RWord.Join{}, Bool.pick(Receive.RWord, s, Receive.RWord.Flag{}, Receive.RWord.Plain{})))), d, f, j, src)) == Bool.pick(Maybe<&2, Receive.Said>, Bool.and(Bool.and(Bool.or(Bool.not(s), Bool.or(e1, Bool.or(e2, Bool.or(e3, Bool.or(e4, False{}))))), recv.aq(rest)), Bool.and(Nat.is_eq(List.length(&2, String, List.append(&2, String, recv.src(src), List.filter.put(String, w, List.filter(~String, ~(u => Bool.not(String.starts_with(u, "-"))), rest), Bool.not(s)))), 1n), Bool.not(Bool.and(Bool.or(d, Bool.or(Bool.or(e1, e2), recv.dq(rest))), Bool.or(f, Bool.or(e3, Rev.member(rest, "--fields"))))))), Some{Receive.Said{Bool.or(d, Bool.or(Bool.or(e1, e2), recv.dq(rest))), Bool.or(f, Bool.or(e3, Rev.member(rest, "--fields"))), Bool.or(j, Bool.or(e4, Rev.member(rest, "--join-unrelated"))), List.append(&2, String, recv.src(src), List.filter.put(String, w, List.filter(~String, ~(u => Bool.not(String.starts_with(u, "-"))), rest), Bool.not(s)))}}, None{}) : Maybe<&2, Receive.Said>}

# Two of the flags' spellings are one word only where they are one.
def clash(+w: String, +a: String, +b: String, ha: {String.eq(w, a) == True{} : Bool}, hb: {String.eq(w, b) == True{} : Bool}, hab: {String.eq(a, b) == False{} : Bool}) -> Empty:
  S.true_false(Equal.trans(Bool, True{}, String.eq(a, b), False{}, Equal.trans(Bool, True{}, String.eq(w, b), String.eq(a, b), Equal.sym(Bool, String.eq(w, b), True{}, hb), Equal.cong(String, Bool, x => String.eq(x, b), w, a, S.eq_true(w, a, ha))), hab))

# And every one of them starts `-`.
def clash_s(+w: String, +a: String, ha: {String.eq(w, a) == True{} : Bool}, hs: {String.starts_with(w, "-") == False{} : Bool}, has: {String.starts_with(a, "-") == True{} : Bool}) -> Empty:
  S.true_false(Equal.trans(Bool, True{}, String.starts_with(a, "-"), False{}, Equal.sym(Bool, String.starts_with(a, "-"), True{}, has), Equal.trans(Bool, String.starts_with(a, "-"), String.starts_with(w, "-"), False{}, Equal.sym(Bool, String.starts_with(w, "-"), String.starts_with(a, "-"), Equal.cong(String, Bool, x => String.starts_with(x, "-"), w, a, S.eq_true(w, a, ha))), hs)))

def recv.none(a: Bool, -n: Bool, -x: Maybe<&2, Receive.Said>) -> {None{} == Bool.pick(Maybe<&2, Receive.Said>, Bool.and(a, Bool.and(False{}, n)), x, None{}) : Maybe<&2, Receive.Said>}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

# At the end of the words.
def recv.nil(d: Bool, f: Bool, j: Bool, src: Maybe<&2, String>) -> recv.goal(Nil{}, d, f, j, src):
  match d:
    case True{}:
      match f:
        case True{}:
          match j:
            case True{}:
              match src:
                case None{}:
                  {==}
                case Some{s0}:
                  {==}
            case False{}:
              match src:
                case None{}:
                  {==}
                case Some{s0}:
                  {==}
        case False{}:
          match j:
            case True{}:
              match src:
                case None{}:
                  {==}
                case Some{s0}:
                  {==}
            case False{}:
              match src:
                case None{}:
                  {==}
                case Some{s0}:
                  {==}
    case False{}:
      match f:
        case True{}:
          match j:
            case True{}:
              match src:
                case None{}:
                  {==}
                case Some{s0}:
                  {==}
            case False{}:
              match src:
                case None{}:
                  {==}
                case Some{s0}:
                  {==}
        case False{}:
          match j:
            case True{}:
              match src:
                case None{}:
                  {==}
                case Some{s0}:
                  {==}
            case False{}:
              match src:
                case None{}:
                  {==}
                case Some{s0}:
                  {==}

# A flag asking for a plan.
def recv.dry1.c(+e2: Bool, d: Bool, +w: String, +rest: List<&2, String>, +f: Bool, +j: Bool, +src: Maybe<&2, String>, ih: @d2: Bool -> @f2: Bool -> @j2: Bool -> @s2: Maybe<&2, String> -> recv.goal(rest, d2, f2, j2, s2)) -> recv.step.goal(True{}, e2, False{}, False{}, True{}, w, rest, d, f, j, src):
  match d:
    case True{}:
      ih(True{}, f, j, src)
    case False{}:
      ih(True{}, f, j, src)

def recv.dry1.b(+e2: Bool, e4: Bool, +w: String, +rest: List<&2, String>, +d: Bool, +f: Bool, +j: Bool, +src: Maybe<&2, String>, hl: {String.eq(w, "-n") == True{} : Bool}, h4: {String.eq(w, "--join-unrelated") == e4 : Bool}, ih: @d2: Bool -> @f2: Bool -> @j2: Bool -> @s2: Maybe<&2, String> -> recv.goal(rest, d2, f2, j2, s2)) -> recv.step.goal(True{}, e2, False{}, e4, True{}, w, rest, d, f, j, src):
  match e4:
    case True{}:
      Empty.absurd(recv.step.goal(True{}, e2, False{}, True{}, True{}, w, rest, d, f, j, src), clash(w, "-n", "--join-unrelated", hl, h4, {==}))
    case False{}:
      recv.dry1.c(e2, d, w, rest, f, j, src, ih)

def recv.dry1.a(+e2: Bool, e3: Bool, +e4: Bool, +w: String, +rest: List<&2, String>, +d: Bool, +f: Bool, +j: Bool, +src: Maybe<&2, String>, hl: {String.eq(w, "-n") == True{} : Bool}, h3: {String.eq(w, "--fields") == e3 : Bool}, h4: {String.eq(w, "--join-unrelated") == e4 : Bool}, ih: @d2: Bool -> @f2: Bool -> @j2: Bool -> @s2: Maybe<&2, String> -> recv.goal(rest, d2, f2, j2, s2)) -> recv.step.goal(True{}, e2, e3, e4, True{}, w, rest, d, f, j, src):
  match e3:
    case True{}:
      Empty.absurd(recv.step.goal(True{}, e2, True{}, e4, True{}, w, rest, d, f, j, src), clash(w, "-n", "--fields", hl, h3, {==}))
    case False{}:
      recv.dry1.b(e2, e4, w, rest, d, f, j, src, hl, h4, ih)

def recv.dry1(+e2: Bool, +e3: Bool, +e4: Bool, s: Bool, +w: String, +rest: List<&2, String>, +d: Bool, +f: Bool, +j: Bool, +src: Maybe<&2, String>, hl: {String.eq(w, "-n") == True{} : Bool}, h3: {String.eq(w, "--fields") == e3 : Bool}, h4: {String.eq(w, "--join-unrelated") == e4 : Bool}, hs: {String.starts_with(w, "-") == s : Bool}, ih: @d2: Bool -> @f2: Bool -> @j2: Bool -> @s2: Maybe<&2, String> -> recv.goal(rest, d2, f2, j2, s2)) -> recv.step.goal(True{}, e2, e3, e4, s, w, rest, d, f, j, src):
  match s:
    case False{}:
      Empty.absurd(recv.step.goal(True{}, e2, e3, e4, False{}, w, rest, d, f, j, src), clash_s(w, "-n", hl, hs, {==}))
    case True{}:
      recv.dry1.a(e2, e3, e4, w, rest, d, f, j, src, hl, h3, h4, ih)

def recv.dry2.c(d: Bool, +w: String, +rest: List<&2, String>, +f: Bool, +j: Bool, +src: Maybe<&2, String>, ih: @d2: Bool -> @f2: Bool -> @j2: Bool -> @s2: Maybe<&2, String> -> recv.goal(rest, d2, f2, j2, s2)) -> recv.step.goal(False{}, True{}, False{}, False{}, True{}, w, rest, d, f, j, src):
  match d:
    case True{}:
      ih(True{}, f, j, src)
    case False{}:
      ih(True{}, f, j, src)

def recv.dry2.b(e4: Bool, +w: String, +rest: List<&2, String>, +d: Bool, +f: Bool, +j: Bool, +src: Maybe<&2, String>, hl: {String.eq(w, "--dry-run") == True{} : Bool}, h4: {String.eq(w, "--join-unrelated") == e4 : Bool}, ih: @d2: Bool -> @f2: Bool -> @j2: Bool -> @s2: Maybe<&2, String> -> recv.goal(rest, d2, f2, j2, s2)) -> recv.step.goal(False{}, True{}, False{}, e4, True{}, w, rest, d, f, j, src):
  match e4:
    case True{}:
      Empty.absurd(recv.step.goal(False{}, True{}, False{}, True{}, True{}, w, rest, d, f, j, src), clash(w, "--dry-run", "--join-unrelated", hl, h4, {==}))
    case False{}:
      recv.dry2.c(d, w, rest, f, j, src, ih)

def recv.dry2.a(e3: Bool, +e4: Bool, +w: String, +rest: List<&2, String>, +d: Bool, +f: Bool, +j: Bool, +src: Maybe<&2, String>, hl: {String.eq(w, "--dry-run") == True{} : Bool}, h3: {String.eq(w, "--fields") == e3 : Bool}, h4: {String.eq(w, "--join-unrelated") == e4 : Bool}, ih: @d2: Bool -> @f2: Bool -> @j2: Bool -> @s2: Maybe<&2, String> -> recv.goal(rest, d2, f2, j2, s2)) -> recv.step.goal(False{}, True{}, e3, e4, True{}, w, rest, d, f, j, src):
  match e3:
    case True{}:
      Empty.absurd(recv.step.goal(False{}, True{}, True{}, e4, True{}, w, rest, d, f, j, src), clash(w, "--dry-run", "--fields", hl, h3, {==}))
    case False{}:
      recv.dry2.b(e4, w, rest, d, f, j, src, hl, h4, ih)

def recv.dry2(+e3: Bool, +e4: Bool, s: Bool, +w: String, +rest: List<&2, String>, +d: Bool, +f: Bool, +j: Bool, +src: Maybe<&2, String>, hl: {String.eq(w, "--dry-run") == True{} : Bool}, h3: {String.eq(w, "--fields") == e3 : Bool}, h4: {String.eq(w, "--join-unrelated") == e4 : Bool}, hs: {String.starts_with(w, "-") == s : Bool}, ih: @d2: Bool -> @f2: Bool -> @j2: Bool -> @s2: Maybe<&2, String> -> recv.goal(rest, d2, f2, j2, s2)) -> recv.step.goal(False{}, True{}, e3, e4, s, w, rest, d, f, j, src):
  match s:
    case False{}:
      Empty.absurd(recv.step.goal(False{}, True{}, e3, e4, False{}, w, rest, d, f, j, src), clash_s(w, "--dry-run", hl, hs, {==}))
    case True{}:
      recv.dry2.a(e3, e4, w, rest, d, f, j, src, hl, h3, h4, ih)

# `--fields`.
def recv.fields.b(f: Bool, +w: String, +rest: List<&2, String>, +d: Bool, +j: Bool, +src: Maybe<&2, String>, ih: @d2: Bool -> @f2: Bool -> @j2: Bool -> @s2: Maybe<&2, String> -> recv.goal(rest, d2, f2, j2, s2)) -> recv.step.goal(False{}, False{}, True{}, False{}, True{}, w, rest, d, f, j, src):
  match f:
    case True{}:
      ih(d, True{}, j, src)
    case False{}:
      ih(d, True{}, j, src)

def recv.fields.a(e4: Bool, +w: String, +rest: List<&2, String>, +d: Bool, +f: Bool, +j: Bool, +src: Maybe<&2, String>, h3: {String.eq(w, "--fields") == True{} : Bool}, h4: {String.eq(w, "--join-unrelated") == e4 : Bool}, ih: @d2: Bool -> @f2: Bool -> @j2: Bool -> @s2: Maybe<&2, String> -> recv.goal(rest, d2, f2, j2, s2)) -> recv.step.goal(False{}, False{}, True{}, e4, True{}, w, rest, d, f, j, src):
  match e4:
    case True{}:
      Empty.absurd(recv.step.goal(False{}, False{}, True{}, True{}, True{}, w, rest, d, f, j, src), clash(w, "--fields", "--join-unrelated", h3, h4, {==}))
    case False{}:
      recv.fields.b(f, w, rest, d, j, src, ih)

def recv.fields(+e4: Bool, s: Bool, +w: String, +rest: List<&2, String>, +d: Bool, +f: Bool, +j: Bool, +src: Maybe<&2, String>, h3: {String.eq(w, "--fields") == True{} : Bool}, h4: {String.eq(w, "--join-unrelated") == e4 : Bool}, hs: {String.starts_with(w, "-") == s : Bool}, ih: @d2: Bool -> @f2: Bool -> @j2: Bool -> @s2: Maybe<&2, String> -> recv.goal(rest, d2, f2, j2, s2)) -> recv.step.goal(False{}, False{}, True{}, e4, s, w, rest, d, f, j, src):
  match s:
    case False{}:
      Empty.absurd(recv.step.goal(False{}, False{}, True{}, e4, False{}, w, rest, d, f, j, src), clash_s(w, "--fields", h3, hs, {==}))
    case True{}:
      recv.fields.a(e4, w, rest, d, f, j, src, h3, h4, ih)

# `--join-unrelated`.
def recv.join.a(j: Bool, +w: String, +rest: List<&2, String>, +d: Bool, +f: Bool, +src: Maybe<&2, String>, ih: @d2: Bool -> @f2: Bool -> @j2: Bool -> @s2: Maybe<&2, String> -> recv.goal(rest, d2, f2, j2, s2)) -> recv.step.goal(False{}, False{}, False{}, True{}, True{}, w, rest, d, f, j, src):
  match j:
    case True{}:
      ih(d, f, True{}, src)
    case False{}:
      ih(d, f, True{}, src)

def recv.join(s: Bool, +w: String, +rest: List<&2, String>, +d: Bool, +f: Bool, +j: Bool, +src: Maybe<&2, String>, h4: {String.eq(w, "--join-unrelated") == True{} : Bool}, hs: {String.starts_with(w, "-") == s : Bool}, ih: @d2: Bool -> @f2: Bool -> @j2: Bool -> @s2: Maybe<&2, String> -> recv.goal(rest, d2, f2, j2, s2)) -> recv.step.goal(False{}, False{}, False{}, True{}, s, w, rest, d, f, j, src):
  match s:
    case False{}:
      Empty.absurd(recv.step.goal(False{}, False{}, False{}, True{}, False{}, w, rest, d, f, j, src), clash_s(w, "--join-unrelated", h4, hs, {==}))
    case True{}:
      recv.join.a(j, w, rest, d, f, src, ih)

# Any other word: refused if it starts `-`, and otherwise the source, if
# none was read before it.
def recv.other.a(src: Maybe<&2, String>, +w: String, +rest: List<&2, String>, +d: Bool, +f: Bool, +j: Bool, ih: @d2: Bool -> @f2: Bool -> @j2: Bool -> @s2: Maybe<&2, String> -> recv.goal(rest, d2, f2, j2, s2)) -> recv.step.goal(False{}, False{}, False{}, False{}, False{}, w, rest, d, f, j, src):
  match src:
    case None{}:
      ih(d, f, j, Some{w})
    case Some{s0}:
      recv.none(recv.aq(rest), Bool.not(Bool.and(Bool.or(d, recv.dq(rest)), Bool.or(f, Rev.member(rest, "--fields")))), Some{Receive.Said{Bool.or(d, recv.dq(rest)), Bool.or(f, Rev.member(rest, "--fields")), Bool.or(j, Rev.member(rest, "--join-unrelated")), s0 <> w <> List.filter(~String, ~(u => Bool.not(String.starts_with(u, "-"))), rest)}})

def recv.other(s: Bool, +w: String, +rest: List<&2, String>, +d: Bool, +f: Bool, +j: Bool, +src: Maybe<&2, String>, ih: @d2: Bool -> @f2: Bool -> @j2: Bool -> @s2: Maybe<&2, String> -> recv.goal(rest, d2, f2, j2, s2)) -> recv.step.goal(False{}, False{}, False{}, False{}, s, w, rest, d, f, j, src):
  match s:
    case True{}:
      {==}
    case False{}:
      recv.other.a(src, w, rest, d, f, j, ih)

def recv.step.d(e4: Bool, +s: Bool, +w: String, +rest: List<&2, String>, +d: Bool, +f: Bool, +j: Bool, +src: Maybe<&2, String>, h4: {String.eq(w, "--join-unrelated") == e4 : Bool}, hs: {String.starts_with(w, "-") == s : Bool}, ih: @d2: Bool -> @f2: Bool -> @j2: Bool -> @s2: Maybe<&2, String> -> recv.goal(rest, d2, f2, j2, s2)) -> recv.step.goal(False{}, False{}, False{}, e4, s, w, rest, d, f, j, src):
  match e4:
    case True{}:
      recv.join(s, w, rest, d, f, j, src, h4, hs, ih)
    case False{}:
      recv.other(s, w, rest, d, f, j, src, ih)

def recv.step.c(e3: Bool, +e4: Bool, +s: Bool, +w: String, +rest: List<&2, String>, +d: Bool, +f: Bool, +j: Bool, +src: Maybe<&2, String>, h3: {String.eq(w, "--fields") == e3 : Bool}, h4: {String.eq(w, "--join-unrelated") == e4 : Bool}, hs: {String.starts_with(w, "-") == s : Bool}, ih: @d2: Bool -> @f2: Bool -> @j2: Bool -> @s2: Maybe<&2, String> -> recv.goal(rest, d2, f2, j2, s2)) -> recv.step.goal(False{}, False{}, e3, e4, s, w, rest, d, f, j, src):
  match e3:
    case True{}:
      recv.fields(e4, s, w, rest, d, f, j, src, h3, h4, hs, ih)
    case False{}:
      recv.step.d(e4, s, w, rest, d, f, j, src, h4, hs, ih)

def recv.step.b(e2: Bool, +e3: Bool, +e4: Bool, +s: Bool, +w: String, +rest: List<&2, String>, +d: Bool, +f: Bool, +j: Bool, +src: Maybe<&2, String>, h2: {String.eq(w, "--dry-run") == e2 : Bool}, h3: {String.eq(w, "--fields") == e3 : Bool}, h4: {String.eq(w, "--join-unrelated") == e4 : Bool}, hs: {String.starts_with(w, "-") == s : Bool}, ih: @d2: Bool -> @f2: Bool -> @j2: Bool -> @s2: Maybe<&2, String> -> recv.goal(rest, d2, f2, j2, s2)) -> recv.step.goal(False{}, e2, e3, e4, s, w, rest, d, f, j, src):
  match e2:
    case True{}:
      recv.dry2(e3, e4, s, w, rest, d, f, j, src, h2, h3, h4, hs, ih)
    case False{}:
      recv.step.c(e3, e4, s, w, rest, d, f, j, src, h3, h4, hs, ih)

def recv.step(e1: Bool, +e2: Bool, +e3: Bool, +e4: Bool, +s: Bool, +w: String, +rest: List<&2, String>, +d: Bool, +f: Bool, +j: Bool, +src: Maybe<&2, String>, h1: {String.eq(w, "-n") == e1 : Bool}, h2: {String.eq(w, "--dry-run") == e2 : Bool}, h3: {String.eq(w, "--fields") == e3 : Bool}, h4: {String.eq(w, "--join-unrelated") == e4 : Bool}, hs: {String.starts_with(w, "-") == s : Bool}, ih: @d2: Bool -> @f2: Bool -> @j2: Bool -> @s2: Maybe<&2, String> -> recv.goal(rest, d2, f2, j2, s2)) -> recv.step.goal(e1, e2, e3, e4, s, w, rest, d, f, j, src):
  match e1:
    case True{}:
      recv.dry1(e2, e3, e4, s, w, rest, d, f, j, src, h1, h3, h4, hs, ih)
    case False{}:
      recv.step.b(e2, e3, e4, s, w, rest, d, f, j, src, h2, h3, h4, hs, ih)

def recv.go(ws: List<&2, String>, +d: Bool, +f: Bool, +j: Bool, +src: Maybe<&2, String>) -> recv.goal(ws, d, f, j, src):
  match ws:
    case Nil{}:
      recv.nil(d, f, j, src)
    case +w <> +rest:
      recv.step(String.eq(w, "-n"), String.eq(w, "--dry-run"), String.eq(w, "--fields"), String.eq(w, "--join-unrelated"), String.starts_with(w, "-"), w, rest, d, f, j, src, {==}, {==}, {==}, {==}, {==}, d2 => f2 => j2 => s2 => recv.go(rest, d2, f2, j2, s2))

# Four flags: a word is one of them exactly where it is among them.
def among4(+w: String, +a: String, +b: String, +c: String, +e: String) -> {Bool.or(String.eq(w, a), Bool.or(String.eq(w, b), Bool.or(String.eq(w, c), Bool.or(String.eq(w, e), False{})))) == Rev.member([a, b, c, e], w) : Bool}:
  %SurveyL.eq_sym(w, a) : {Bool.or(String.eq(w, a), Bool.or(String.eq(w, b), Bool.or(String.eq(w, c), Bool.or(String.eq(w, e), False{})))) == Bool.or(_, Bool.or(String.eq(b, w), Bool.or(String.eq(c, w), Bool.or(String.eq(e, w), False{})))) : Bool}
  %SurveyL.eq_sym(w, b) : {Bool.or(String.eq(w, a), Bool.or(String.eq(w, b), Bool.or(String.eq(w, c), Bool.or(String.eq(w, e), False{})))) == Bool.or(String.eq(w, a), Bool.or(_, Bool.or(String.eq(c, w), Bool.or(String.eq(e, w), False{})))) : Bool}
  %SurveyL.eq_sym(w, c) : {Bool.or(String.eq(w, a), Bool.or(String.eq(w, b), Bool.or(String.eq(w, c), Bool.or(String.eq(w, e), False{})))) == Bool.or(String.eq(w, a), Bool.or(String.eq(w, b), Bool.or(_, Bool.or(String.eq(e, w), False{})))) : Bool}
  %SurveyL.eq_sym(w, e) : {Bool.or(String.eq(w, a), Bool.or(String.eq(w, b), Bool.or(String.eq(w, c), Bool.or(String.eq(w, e), False{})))) == Bool.or(String.eq(w, a), Bool.or(String.eq(w, b), Bool.or(String.eq(w, c), Bool.or(_, False{})))) : Bool}
  {==}

def recv.a.step(s: Bool, +w: String, -rest: List<&2, String>, ek: {recv.known(w) == Rev.member(["-n", "--dry-run", "--fields", "--join-unrelated"], w) : Bool}, ih: {recv.aq(rest) == List.all(~&2, ~String, ~(v => Rev.member(["-n", "--dry-run", "--fields", "--join-unrelated"], v)), List.filter(~String, ~(u => String.starts_with(u, "-")), rest)) : Bool}) -> {Bool.and(Bool.or(Bool.not(s), recv.known(w)), recv.aq(rest)) == List.all(~&2, ~String, ~(v => Rev.member(["-n", "--dry-run", "--fields", "--join-unrelated"], v)), List.filter.put(String, w, List.filter(~String, ~(u => String.starts_with(u, "-")), rest), s)) : Bool}:
  match s:
    case False{}:
      ih
    case True{}:
      %ek : {Bool.and(recv.known(w), recv.aq(rest)) == Bool.and(_, List.all(~&2, ~String, ~(v => Rev.member(["-n", "--dry-run", "--fields", "--join-unrelated"], v)), List.filter(~String, ~(u => String.starts_with(u, "-")), rest))) : Bool}
      %ih : {Bool.and(recv.known(w), recv.aq(rest)) == Bool.and(recv.known(w), _) : Bool}
      {==}

def recv.a(ws: List<&2, String>) -> {recv.aq(ws) == List.all(~&2, ~String, ~(v => Rev.member(["-n", "--dry-run", "--fields", "--join-unrelated"], v)), List.filter(~String, ~(u => String.starts_with(u, "-")), ws)) : Bool}:
  match ws:
    case Nil{}:
      {==}
    case +w <> +rest:
      recv.a.step(String.starts_with(w, "-"), w, rest, among4(w, "-n", "--dry-run", "--fields", "--join-unrelated"), recv.a(rest))

def recv.d(ws: List<&2, String>) -> {recv.dq(ws) == Bool.or(Rev.member(ws, "-n"), Rev.member(ws, "--dry-run")) : Bool}:
  match ws:
    case Nil{}:
      {==}
    case +w <> +rest:
      %Equal.sym(Bool, recv.dq(rest), Bool.or(Rev.member(rest, "-n"), Rev.member(rest, "--dry-run")), recv.d(rest)) : {Bool.or(Bool.or(String.eq(w, "-n"), String.eq(w, "--dry-run")), _) == Bool.or(Rev.member(w <> rest, "-n"), Rev.member(w <> rest, "--dry-run")) : Bool}
      or_swap(String.eq(w, "-n"), String.eq(w, "--dry-run"), Rev.member(rest, "-n"), Rev.member(rest, "--dry-run"))

# `receive` accepts a command line exactly where the words starting `-`
# are all `-n`, `--dry-run`, `--fields` or `--join-unrelated`, one word
# does not start `-`, and it does not hold both a flag asking for a plan
# and `--fields`; and then it plans only where one of the first two flags
# is among them, states what is on disk only where `--fields` is, joins
# unrelated histories only where `--join-unrelated` is, and its source is
# that one other word.
def receive_words(+ws: List<&2, String>) -> {Receive.args.read(Receive.args.r(ws)) == Bool.pick(Maybe<&2, Receive.Said>, Bool.and(List.all(~&2, ~String, ~(w => Rev.member(["-n", "--dry-run", "--fields", "--join-unrelated"], w)), List.filter(~String, ~(w => String.starts_with(w, "-")), ws)), Bool.and(Nat.is_eq(List.length(&2, String, List.filter(~String, ~(w => Bool.not(String.starts_with(w, "-"))), ws)), 1n), Bool.not(Bool.and(Bool.or(Rev.member(ws, "-n"), Rev.member(ws, "--dry-run")), Rev.member(ws, "--fields"))))), Some{Receive.Said{Bool.or(Rev.member(ws, "-n"), Rev.member(ws, "--dry-run")), Rev.member(ws, "--fields"), Rev.member(ws, "--join-unrelated"), List.filter(~String, ~(w => Bool.not(String.starts_with(w, "-"))), ws)}}, None{}) : Maybe<&2, Receive.Said>}:
  %recv.d(ws) : {Receive.args.read(Receive.args.r(ws)) == Bool.pick(Maybe<&2, Receive.Said>, Bool.and(List.all(~&2, ~String, ~(w => Rev.member(["-n", "--dry-run", "--fields", "--join-unrelated"], w)), List.filter(~String, ~(w => String.starts_with(w, "-")), ws)), Bool.and(Nat.is_eq(List.length(&2, String, List.filter(~String, ~(w => Bool.not(String.starts_with(w, "-"))), ws)), 1n), Bool.not(Bool.and(_, Rev.member(ws, "--fields"))))), Some{Receive.Said{_, Rev.member(ws, "--fields"), Rev.member(ws, "--join-unrelated"), List.filter(~String, ~(w => Bool.not(String.starts_with(w, "-"))), ws)}}, None{}) : Maybe<&2, Receive.Said>}
  %recv.a(ws) : {Receive.args.read(Receive.args.r(ws)) == Bool.pick(Maybe<&2, Receive.Said>, Bool.and(_, Bool.and(Nat.is_eq(List.length(&2, String, List.filter(~String, ~(w => Bool.not(String.starts_with(w, "-"))), ws)), 1n), Bool.not(Bool.and(recv.dq(ws), Rev.member(ws, "--fields"))))), Some{Receive.Said{recv.dq(ws), Rev.member(ws, "--fields"), Rev.member(ws, "--join-unrelated"), List.filter(~String, ~(w => Bool.not(String.starts_with(w, "-"))), ws)}}, None{}) : Maybe<&2, Receive.Said>}
  recv.go(ws, False{}, False{}, False{}, None{})
