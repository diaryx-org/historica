# The command line reads `-C <dir>` as often as it is given, the last
# counting, and hands the command word and every word after it to the
# command as written — a `-C` after the command word is the command's.
import Base
import ./argv.bend as Argv

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
