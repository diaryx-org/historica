# The command line reads `-C <dir>` as often as it is given, the last
# counting, and hands the command word and every word after it to the
# command as written — a `-C` after the command word is the command's.
import Base
import ./argv.bend as Argv
import ./string_lemmas.bend as S

# Past `-C` and its directory the reading starts again on what follows,
# with that directory the one so far; at the command word it stops.
def go(ds: List<&2, String>, +w: String, +rest: List<&2, String>, +b: Maybe<&2, String>, e: {Argv.lead.of(w) == Argv.Lead.Word{} : Argv.Lead}) -> {Argv.read.go(Argv.spelled(ds, w, rest), b, Argv.lead(Argv.spelled(ds, w, rest))) == Argv.Asked.Command{Argv.last(ds, b), w, rest} : Argv.Asked}:
  match ds:
    case Nil{}:
      %Equal.sym(Argv.Lead, Argv.lead.of(w), Argv.Lead.Word{}, e) : {Argv.read.go(w <> rest, b, _) == Argv.Asked.Command{b, w, rest} : Argv.Asked}
      {==}
    case d <> more:
      go(more, w, rest, Some{d}, e)

def reads(ds: List<&2, String>, +w: String, +rest: List<&2, String>, e: {Argv.lead.of(w) == Argv.Lead.Word{} : Argv.Lead}) -> {Argv.read(Argv.spelled(ds, w, rest)) == Argv.Asked.Command{Argv.last(ds, None{}), w, rest} : Argv.Asked}:
  go(ds, w, rest, None{}, e)

# Asking for the version or for help ends the reading where it stands,
# whatever `-C`s came before it and whatever follows.
def stops(ds: List<&2, String>, +w: String, +rest: List<&2, String>, +b: Maybe<&2, String>, +k: Argv.Lead, +a: Argv.Asked, +e: {Argv.lead.of(w) == k : Argv.Lead}, any: @b2: Maybe<&2, String> -> {Argv.read.go(w <> rest, b2, k) == a : Argv.Asked}) -> {Argv.read.go(Argv.spelled(ds, w, rest), b, Argv.lead(Argv.spelled(ds, w, rest))) == a : Argv.Asked}:
  match ds:
    case Nil{}:
      %Equal.sym(Argv.Lead, Argv.lead.of(w), k, e) : {Argv.read.go(w <> rest, b, _) == a : Argv.Asked}
      any(b)
    case d <> more:
      stops(more, w, rest, Some{d}, k, a, e, any)

def version.at(+v: String, x: Bool, ex: {String.eq(v, "-V") == x : Bool}, y: Bool, ey: {String.eq(v, "--version") == y : Bool}, h: {Bool.or(x, y) == True{} : Bool}) -> {Argv.lead.of(v) == Argv.Lead.Version{} : Argv.Lead}:
  match x y:
    case True{} _:
      +ve : {v == "-V" : String} = S.eq_true(v, "-V", ex)
      (%Equal.sym(String, v, "-V", ve) : {Argv.lead.of(_) == Argv.Lead.Version{} : Argv.Lead} {==})
    case False{} True{}:
      +ve : {v == "--version" : String} = S.eq_true(v, "--version", ey)
      (%Equal.sym(String, v, "--version", ve) : {Argv.lead.of(_) == Argv.Lead.Version{} : Argv.Lead} {==})
    case False{} False{}:
      Empty.absurd({Argv.lead.of(v) == Argv.Lead.Version{} : Argv.Lead}, S.false_true(h))

# `-V` and `--version` read as the version asked for.
def reads_version(ds: List<&2, String>, +v: String, +rest: List<&2, String>, h: {Bool.or(String.eq(v, "-V"), String.eq(v, "--version")) == True{} : Bool}) -> {Argv.read(Argv.spelled(ds, v, rest)) == Argv.Asked.Version{} : Argv.Asked}:
  +e : {Argv.lead.of(v) == Argv.Lead.Version{} : Argv.Lead} = version.at(v, String.eq(v, "-V"), {==}, String.eq(v, "--version"), {==}, h)
  stops(ds, v, rest, None{}, Argv.Lead.Version{}, Argv.Asked.Version{}, e, b2 => {==})

def help.at(+v: String, x: Bool, ex: {String.eq(v, "help") == x : Bool}, y: Bool, ey: {String.eq(v, "-h") == y : Bool}, z: Bool, ez: {String.eq(v, "--help") == z : Bool}, h: {Bool.or(x, Bool.or(y, z)) == True{} : Bool}) -> {Argv.lead.of(v) == Argv.Lead.Usage{} : Argv.Lead}:
  match x y z:
    case True{} _ _:
      +ve : {v == "help" : String} = S.eq_true(v, "help", ex)
      (%Equal.sym(String, v, "help", ve) : {Argv.lead.of(_) == Argv.Lead.Usage{} : Argv.Lead} {==})
    case False{} True{} _:
      +ve : {v == "-h" : String} = S.eq_true(v, "-h", ey)
      (%Equal.sym(String, v, "-h", ve) : {Argv.lead.of(_) == Argv.Lead.Usage{} : Argv.Lead} {==})
    case False{} False{} True{}:
      +ve : {v == "--help" : String} = S.eq_true(v, "--help", ez)
      (%Equal.sym(String, v, "--help", ve) : {Argv.lead.of(_) == Argv.Lead.Usage{} : Argv.Lead} {==})
    case False{} False{} False{}:
      Empty.absurd({Argv.lead.of(v) == Argv.Lead.Usage{} : Argv.Lead}, S.false_true(h))

# `help`, `-h` and `--help` read as the usage asked for.
def reads_help(ds: List<&2, String>, +v: String, +rest: List<&2, String>, h: {Bool.or(String.eq(v, "help"), Bool.or(String.eq(v, "-h"), String.eq(v, "--help"))) == True{} : Bool}) -> {Argv.read(Argv.spelled(ds, v, rest)) == Argv.Asked.Usage{} : Argv.Asked}:
  +e : {Argv.lead.of(v) == Argv.Lead.Usage{} : Argv.Lead} = help.at(v, String.eq(v, "help"), {==}, String.eq(v, "-h"), {==}, String.eq(v, "--help"), {==}, h)
  stops(ds, v, rest, None{}, Argv.Lead.Usage{}, Argv.Asked.Usage{}, e, b2 => {==})
