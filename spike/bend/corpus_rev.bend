# The revision corpora, run: every valid document round-trips through the
# parser byte for byte and is named by the digest its manifest states,
# every invalid one is refused, and the seven-revision history resolves as
# the core says it must.
#
#   cd historica/spike/bend && bend corpus_rev.bend

import Base
import ./utf8.bend as Utf8
import ./sha256.bend as Sha
import ./revision.bend as Rev

def corpus() -> String:
  "../../tests/corpus/"

def verdict(ok: Bool, what: String) -> IO(Unit):
  match ok:
    case True{}:
      IO.print("ok    " ++ what)
    case False{}:
      IO.die(Unit, 1, "FAIL  " ++ what)

def round_trip.of(name: String, s: String, parsed: Result<&2, &2, String, Rev.Rev>) -> IO(Unit):
  match parsed:
    case Fail{e}:
      verdict(False{}, name ++ " refused: " ++ e)
    case Done{doc}:
      verdict(String.eq(Rev.write(doc), s), name ++ " round-trips")

def round_trip.read(name: String, +s: String) -> IO(Unit):
  round_trip.of(name, s, Rev.parse(s))

def round_trip(+name: String) -> IO(Unit):
  do IO<Unit>:
    bs : List<&2, U32> <- Utf8.read_file(corpus() ++ name)
    round_trip.read(name, Utf8.decode(bs))

def refused.of(name: String, parsed: Result<&2, &2, String, Rev.Rev>) -> IO(Unit):
  match parsed:
    case Fail{e}:
      verdict(True{}, name ++ " refused: " ++ e)
    case Done{doc}:
      verdict(False{}, name ++ " accepted")

def refused(+name: String) -> IO(Unit):
  do IO<Unit>:
    bs : List<&2, U32> <- Utf8.read_file(corpus() ++ name)
    refused.of(name, Rev.parse(Utf8.decode(bs)))

# The history: each document read, hashed, parsed, and inserted under its
# digest.
def load.of(h: Rev.History(), id: String, parsed: Result<&2, &2, String, Rev.Rev>) -> Rev.History():
  match parsed:
    case Fail{e}:
      h
    case Done{doc}:
      Rev.insert(h, Rev.of_doc(id, doc))

def load(names: List<&2, String>, h: Rev.History()) -> IO(Rev.History()):
  match names:
    case Nil{}:
      IO.pure(Rev.History(), h)
    case name <> rest:
      do IO<Rev.History()>:
        bs : List<&2, U32> <- Utf8.read_file(corpus() ++ "revisions/" ++ name)
        +bs2 : List<&2, U32> = bs
        load(rest, load.of(h, Sha.digest(bs2), Rev.parse(Utf8.decode(bs2))))

def same_set(+xs: List<&2, String>, +ys: List<&2, String>) -> Bool:
  Bool.and(Rev.subset(xs, ys), Rev.subset(ys, xs))

def show_state(s: Rev.ChangeState) -> String:
  match s:
    case Rev.UnknownChange{}:
      "unknown"
    case Rev.Resolved{id}:
      "resolved to " ++ String.take(id, 12n)
    case Rev.Divergent{ids}:
      "divergent"
    case Rev.Abandoned{}:
      "abandoned"

def is_resolved_to(s: Rev.ChangeState, +id: String) -> Bool:
  match s:
    case Rev.Resolved{found}:
      String.eq(found, id)
    case _:
      False{}

def is_divergent(s: Rev.ChangeState) -> Bool:
  match s:
    case Rev.Divergent{ids}:
      True{}
    case _:
      False{}

def history_facts(+h: Rev.History()) -> IO(Unit):
  do IO<Unit>:
    verdict(same_set(Rev.heads(h), ["e322f484ef48c6e2ca855159c31c47e5431226e84fcfca51e5dee08aae35ad51", "a66227c7e9cae693801037a64e9f3a6a021667e18f91142bcb8e4da292a1a1f1", "049ed3990c667473c2dd870844595224a202c41f4ce369e0e813135f10ab7cc4"]), "heads are 04, 06 and 07 (04 is superseded, and still a head of the graph)")
    verdict(same_set(Rev.superseded(h), ["8d50ecd737fffc320547b5ecfe428ae62313322956e543624e47f0b3533cc260", "a66227c7e9cae693801037a64e9f3a6a021667e18f91142bcb8e4da292a1a1f1"]), "02 and 04 are superseded")
    verdict(List.is_empty(&2, String, Rev.missing_parents(h)), "no parent is missing")
    verdict(is_resolved_to(Rev.change_state(h, "kxryzmornsvltwqpuzkymxol"), "cf15f95b23533e9dabf08f810b842c69ea5b248b718a1b2b90d37fc1fd707c1e"), "the amended change resolves to 05")
    verdict(is_resolved_to(Rev.change_state(h, "nwlxsqotvkzmuprysltnwxqk"), "e322f484ef48c6e2ca855159c31c47e5431226e84fcfca51e5dee08aae35ad51"), "the rebased merge resolves to 06")
    IO.print("      " ++ show_state(Rev.change_state(h, "zzzzzzzzzzzzzzzzzzzzzzzz")))

# A second amendment of 02's change, made without seeing 05.
def other_amendment() -> String:
  "historica\nchange kxryzmornsvltwqpuzkymxol\nparent 73385a447df87bc06804ed64336a27840e69caea1c806e39cf669b1a446111ea\nsupersedes 8d50ecd737fffc320547b5ecfe428ae62313322956e543624e47f0b3533cc260\nauthor Adam Harris <adam@example.com>\nwhen 2025-08-19T09:02:40-06:00\nrevised 2025-08-21T10:00:00-06:00\n\nDetect, then refuse, two revisions claiming one digest\n"

def divergence.of(+h: Rev.History()) -> IO(Unit):
  do IO<Unit>:
    verdict(is_divergent(Rev.change_state(h, "kxryzmornsvltwqpuzkymxol")), "two amendments of one change that saw neither diverge")
    verdict(same_set(Rev.missing_parents(h), Nil{}), "and nothing is missing")

def divergence(h: Rev.History()) -> IO(Unit):
  divergence.of(load.of(h, Sha.digest(Utf8.encode(other_amendment())), Rev.parse(other_amendment())))

def main() -> IO(Unit):
  do IO<Unit>:
    List.for_each(~&2, ~String, ~(n => round_trip(n)), ["revisions/01-root.rev.txt", "revisions/02-concurrent.rev.txt", "revisions/03-other.rev.txt", "revisions/04-merge.rev.txt", "revisions/05-amended.rev.txt", "revisions/06-rebased.rev.txt", "revisions/07-verbatim-message.rev.txt",
      "tree/revisions/01-start.rev.txt", "tree/revisions/02-entry.rev.txt", "tree/revisions/03-move.rev.txt", "tree/revisions/04-drop.rev.txt",
      "links/revisions/01-start.rev.txt", "links/revisions/02-august.rev.txt", "links/revisions/03-renamed.rev.txt", "links/revisions/04-gone.rev.txt",
      "modes/revisions/01-start.rev.txt", "modes/revisions/02-runnable.rev.txt", "modes/revisions/03-plain.rev.txt",
      "whole/revisions/01-start.rev.txt", "whole/revisions/02-crop.rev.txt",
      "merged/revisions/01-root.rev.txt", "merged/revisions/02-left.rev.txt", "merged/revisions/03-right.rev.txt", "merged/revisions/04-merge.rev.txt", "merged/revisions/05-after.rev.txt"])
    List.for_each(~&2, ~String, ~(n => refused(n)), ["revisions/invalid/carriage-returns.rev.txt", "revisions/invalid/change-id-in-the-digest-alphabet.rev.txt", "revisions/invalid/empty-body-after-separator.rev.txt", "revisions/invalid/empty-header-value.rev.txt", "revisions/invalid/headers-out-of-order.rev.txt", "revisions/invalid/missing-version-header.rev.txt", "revisions/invalid/unknown-required-header.rev.txt", "revisions/invalid/unknown-version.rev.txt", "revisions/invalid/unsorted-parents.rev.txt",
      "links/invalid/drop-and-link.rev.txt", "links/invalid/link-and-text.rev.txt", "links/invalid/link-stated-twice.rev.txt", "links/invalid/malformed-file-reference.rev.txt",
      "modes/invalid/drop-and-mode.rev.txt", "modes/invalid/mode-stated-twice.rev.txt", "modes/invalid/unknown-mode.rev.txt",
      "whole/invalid/add-with-edit.rev.txt", "whole/invalid/drop-and-bytes.rev.txt", "whole/invalid/edit-and-bytes.rev.txt", "whole/invalid/text-and-bytes.rev.txt", "whole/invalid/text-without-add.rev.txt"])
    h : Rev.History() <- load(["01-root.rev.txt", "02-concurrent.rev.txt", "03-other.rev.txt", "04-merge.rev.txt", "05-amended.rev.txt", "06-rebased.rev.txt", "07-verbatim-message.rev.txt"], Rev.empty())
    history_facts(h)
    h2 : Rev.History() <- load(["01-root.rev.txt", "02-concurrent.rev.txt", "05-amended.rev.txt"], Rev.empty())
    divergence(h2)
