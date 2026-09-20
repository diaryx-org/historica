# The operations corpus, run: every valid document round-trips through the
# parser byte for byte, every invalid one is refused, the history replays to
# the hand-written states, and the diff writes the pinned fixtures.
#
#   cd historica/spike/bend && bend corpus_ops.bend

import Base
import ./utf8.bend as Utf8
import ./sha256.bend as Sha
import ./ops.bend as Ops

def corpus() -> String:
  "../../tests/corpus/operations/"

def read_text(path: String) -> IO(String):
  do IO<String>:
    bs : List<&2, U32> <- Utf8.read_file(path)
    return Utf8.decode(bs)

def verdict(ok: Bool, what: String) -> IO(Unit):
  match ok:
    case True{}:
      IO.print("ok    " ++ what)
    case False{}:
      IO.die(Unit, 1, "FAIL  " ++ what)

# A valid document parses, and writes back to the bytes it came from.
def round_trip.of(name: String, s: String, parsed: Result<&2, &2, String, Ops.Doc>) -> IO(Unit):
  match parsed:
    case Fail{e}:
      verdict(False{}, name ++ " refused: " ++ e)
    case Done{doc}:
      verdict(String.eq(Ops.write(doc), s), name ++ " round-trips")

def round_trip.read(name: String, +s: String) -> IO(Unit):
  round_trip.of(name, s, Ops.parse(s))

def round_trip(+name: String) -> IO(Unit):
  do IO<Unit>:
    s : String <- read_text(corpus() ++ name)
    round_trip.read(name, s)

def refused.of(name: String, parsed: Result<&2, &2, String, Ops.Doc>) -> IO(Unit):
  match parsed:
    case Fail{e}:
      verdict(True{}, name ++ " refused: " ++ e)
    case Done{doc}:
      verdict(False{}, name ++ " accepted")

def refused(+name: String) -> IO(Unit):
  do IO<Unit>:
    s : String <- read_text(corpus() ++ "invalid/" ++ name)
    refused.of(name, Ops.parse(s))

# A replay: the parent state, the document, and the child it must produce.
def replay.applied(name: String, +expected: String, applied: Result<&2, &2, String, List<&2, Ops.Item>>) -> IO(Unit):
  match applied:
    case Fail{e}:
      verdict(False{}, name ++ " failed to replay: " ++ e)
    case Done{items}:
      verdict(String.eq(Ops.text(items), expected), name ++ " replays to its state")

def replay.of(name: String, +expected: String, parent: List<&2, Ops.Item>, parsed: Result<&2, &2, String, Ops.Doc>) -> IO(Unit):
  match parsed:
    case Fail{e}:
      verdict(False{}, name ++ " refused: " ++ e)
    case Done{doc}:
      replay.applied(name, expected, Ops.apply(parent, doc))

def replay(+name: String, parent: String, child: String) -> IO(Unit):
  do IO<Unit>:
    s : String <- read_text(corpus() ++ name)
    p : String <- read_text(corpus() ++ "states/" ++ parent)
    c : String <- read_text(corpus() ++ "states/" ++ child)
    replay.of(name, c, Ops.from_text(p), Ops.parse(s))

# A diff: the parent, the child, and the document the writer must produce.
def diffed.of(name: String, +recorded: String, d: Maybe<&2, Ops.Doc>) -> IO(Unit):
  match d:
    case None{}:
      verdict(False{}, name ++ " diffed to nothing")
    case Some{doc}:
      verdict(String.eq(Ops.write(doc), recorded), name ++ " diffs to the recorded document")

def diffed(+name: String) -> IO(Unit):
  do IO<Unit>:
    p : String <- read_text("../../tests/corpus/diffs/" ++ name ++ "/parent.txt")
    c : String <- read_text("../../tests/corpus/diffs/" ++ name ++ "/child.txt")
    r : String <- read_text("../../tests/corpus/diffs/" ++ name ++ "/recorded.ops.txt")
    diffed.of(name, r, Ops.diff(Ops.from_text(p), Ops.from_text(c)))

def main() -> IO(Unit):
  do IO<Unit>:
    List.for_each(~&2, ~String, ~(n => round_trip(n)), ["01-root.ops.txt", "02-concurrent.ops.txt", "03-other.ops.txt", "05-amended.ops.txt", "crlf.ops.txt", "no-newline.ops.txt", "result-stated.ops.txt", "verbatim-items.ops.txt"])
    List.for_each(~&2, ~String, ~(n => refused(n)), ["adjacent-deletes.ops.txt", "carriage-return-in-an-operation.ops.txt", "content-without-operation.ops.txt", "delete-after-insert.ops.txt", "delete-count-disagrees.ops.txt", "empty-delete.ops.txt", "empty-insert.ops.txt", "inserts-at-one-position.ops.txt", "leading-zero-position.ops.txt", "malformed-operation.ops.txt", "malformed-result.ops.txt", "missing-separator.ops.txt", "no-newline-not-last.ops.txt", "no-newline-without-item.ops.txt", "no-operations.ops.txt", "operations-out-of-order.ops.txt", "overlapping-operations.ops.txt", "result-of-forgetting.ops.txt", "unknown-operation.ops.txt"])
    replay("02-concurrent.ops.txt", "01-root.txt", "02-concurrent.txt")
    replay("03-other.ops.txt", "01-root.txt", "03-other.txt")
    replay("05-amended.ops.txt", "01-root.txt", "05-amended.txt")
    List.for_each(~&2, ~String, ~(n => diffed(n)), ["replacement-anchor", "surviving-line", "final-newline-gained", "final-newline-lost"])
