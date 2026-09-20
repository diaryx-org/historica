# Executable checks against the independent Verus-style output oracle.
# Full item equality matters: text alone loses forgetting and newline flags.
import Base
import ./ops.bend as Ops
import ./replay_spec.bend as Spec
import ./cursor_spec.bend as Cursor

def check(ok: Bool, name: String) -> IO(Unit):
  match ok:
    case True{}:
      IO.pure(Unit, Unit{})
    case False{}:
      IO.die(Unit, 1, "FAIL replay: " ++ name)

def items_equal(a: List<&2, Ops.Item>, b: List<&2, Ops.Item>) -> Bool:
  match a b:
    case Nil{} Nil{}:
      True{}
    case Ops.Item{a, n, f} <> ar Ops.Item{b, m, g} <> br:
      Bool.and(String.eq(a, b), Bool.and(Bool.not(Bool.xor(n, m)), Bool.and(Bool.not(Bool.xor(f, g)), items_equal(ar, br))))
    case _ _:
      False{}

def accepted(name: String, expected: List<&2, Ops.Item>, actual: Result<&2, &2, String, List<&2, Ops.Item>>) -> IO(Unit):
  match actual:
    case Fail{+e}:
      IO.die(Unit, 1, name ++ ": unexpectedly refused: " ++ e)
    case Done{items}:
      check(items_equal(expected, items), name)

def refused(name: String, expected: String, actual: Result<&2, &2, String, List<&2, Ops.Item>>) -> IO(Unit):
  match actual:
    case Fail{+e}:
      check(String.eq(expected, e), name ++ ": wrong refusal: " ++ e)
    case Done{items}:
      IO.die(Unit, 1, name ++ ": unexpectedly accepted")

def oracle(+name: String, +parent: List<&2, Ops.Item>, +ops: List<&2, Ops.Op>) -> IO(Unit):
  do IO<Unit>:
    accepted("cursor spec: " ++ name, Spec.result(parent, ops), Cursor.apply(parent, Ops.Doc{None{}, None{}, ops}))
    accepted(name, Spec.result(parent, ops), Ops.apply(parent, Ops.Doc{None{}, None{}, ops}))

# Compare failures as well as full successful states, including hand-built
# Docs outside the positional specification's canonical-input contract.
def outcomes_equal(a: Result<&2, &2, String, List<&2, Ops.Item>>, b: Result<&2, &2, String, List<&2, Ops.Item>>) -> Bool:
  match a b:
    case Fail{a} Fail{b}:
      String.eq(a, b)
    case Done{a} Done{b}:
      items_equal(a, b)
    case _ _:
      False{}

def cursor_case(name: String, +parent: List<&2, Ops.Item>, +doc: Ops.Doc) -> IO(Unit):
  check(outcomes_equal(Ops.apply(parent, doc), Cursor.apply(parent, doc)), name)

# Every deletion interval and replacement anchor for this parent and gap.
def intervals(+n: Nat, +at: Nat, +parent: List<&2, Ops.Item>) -> IO(Unit):
  match n:
    case 0n:
      IO.pure(Unit, Unit{})
    case 1n+p:
      do IO<Unit>:
        quoted : List<&2, Ops.Item> = List.take(&2, Ops.Item, List.drop(&2, Ops.Item, parent, at), 1n+p)
        oracle("delete interval", parent, [Ops.Op{Ops.Delete{}, at, quoted}])
        quoted : List<&2, Ops.Item> = List.take(&2, Ops.Item, List.drop(&2, Ops.Item, parent, at), 1n+p)
        oracle("replacement anchor", parent, [Ops.Op{Ops.Delete{}, at, quoted}, Ops.Op{Ops.Insert{}, at, [Ops.line("new"), Ops.line("run")]}])
        quoted : List<&2, Ops.Item> = List.take(&2, Ops.Item, List.drop(&2, Ops.Item, parent, at), 1n+p)
        oracle("insert after deleted interval", parent, [Ops.Op{Ops.Delete{}, at, quoted}, Ops.Op{Ops.Insert{}, Nat.add(at, 1n+p), [Ops.line("new")]}])
        intervals(p, at, parent)

def gap(+at: Nat, +parent: List<&2, Ops.Item>) -> IO(Unit):
  do IO<Unit>:
    oracle("insert at gap", parent, [Ops.Op{Ops.Insert{}, at, [Ops.line("new"), Ops.forgotten()]}])
    intervals(Nat.sub(List.length(&2, Ops.Item, parent), at), at, parent)

def gaps(+n: Nat, +parent: List<&2, Ops.Item>) -> IO(Unit):
  match n:
    case 0n:
      gap(0n, parent)
    case 1n+p:
      do IO<Unit>:
        gap(1n+p, parent)
        gaps(p, parent)

def parent_cases(parents: List<&2, List<&2, Ops.Item>>) -> IO(Unit):
  match parents:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case +parent <> rest:
      do IO<Unit>:
        oracle("no operations", parent, Nil{})
        gaps(List.length(&2, Ops.Item, parent), parent)
        parent_cases(rest)

def main() -> IO(Unit):
  do IO<Unit>:
    parent_cases([Nil{}, [Ops.line("a")], [Ops.line("a"), Ops.line("b")], [Ops.line("a"), Ops.line("b"), Ops.line("c")], [Ops.line("same"), Ops.line("same"), Ops.forgotten(), Ops.line("end")]])
    oracle("trailing gap after unterminated removal", [Ops.line("a"), Ops.unterminated("b")], [Ops.Op{Ops.Delete{}, 1n, [Ops.unterminated("b")]}, Ops.Op{Ops.Insert{}, 2n, [Ops.unterminated("c")]}])
    oracle("two disjoint deletes and inserts", Ops.from_text("a\nb\nc\nd\ne\n"), [Ops.Op{Ops.Delete{}, 0n, [Ops.line("a")]}, Ops.Op{Ops.Insert{}, 0n, [Ops.line("x")]}, Ops.Op{Ops.Delete{}, 3n, [Ops.line("d")]}, Ops.Op{Ops.Insert{}, 5n, [Ops.line("y")]}])
    refused("forgotten quote preserves newline", "a delete at 0 quotes lines the parent does not hold", Ops.apply([Ops.unterminated("secret")], Ops.Doc{None{}, None{}, [Ops.Op{Ops.Delete{}, 0n, [Ops.forgotten()]}]}))
    refused("forgotten parent preserves newline", "a delete at 0 quotes lines the parent does not hold", Ops.apply([Ops.forgotten()], Ops.Doc{None{}, None{}, [Ops.Op{Ops.Delete{}, 0n, [Ops.unterminated("secret")]}]}))
    oracle("forgotten quote matches terminated text", [Ops.line("secret")], [Ops.Op{Ops.Delete{}, 0n, [Ops.forgotten()]}])
    oracle("forgotten parent matches terminated quote", [Ops.forgotten()], [Ops.Op{Ops.Delete{}, 0n, [Ops.line("secret")]}])
    refused("insert past end", "an operation counts past the end of the parent", Ops.apply(Nil{}, Ops.Doc{None{}, None{}, [Ops.Op{Ops.Insert{}, 1n, [Ops.line("x")]}]}))
    refused("delete past end", "an operation counts past the end of the parent", Ops.apply([Ops.line("a")], Ops.Doc{None{}, None{}, [Ops.Op{Ops.Delete{}, 0n, [Ops.line("a"), Ops.line("b")]}]}))
    refused("text disagreement", "a delete at 0 quotes lines the parent does not hold", Ops.apply([Ops.line("a")], Ops.Doc{None{}, None{}, [Ops.Op{Ops.Delete{}, 0n, [Ops.line("b")]}]}))
    refused("unterminated item not last", "line 0: an item without a newline that is not the last", Ops.apply([Ops.unterminated("a")], Ops.Doc{None{}, None{}, [Ops.Op{Ops.Insert{}, 1n, [Ops.line("b")]}]}))
    accepted("matching result digest", [Ops.line("a")], Ops.apply(Nil{}, Ops.Doc{None{}, Some{Ops.state_digest([Ops.line("a")])}, [Ops.Op{Ops.Insert{}, 0n, [Ops.line("a")]}]}))
    refused("wrong result digest", "the result stated is wrong but the replay produced " ++ Ops.state_digest([Ops.line("a")]), Ops.apply(Nil{}, Ops.Doc{None{}, Some{"wrong"}, [Ops.Op{Ops.Insert{}, 0n, [Ops.line("a")]}]}))
    accepted("forgotten result skips digest", [Ops.forgotten()], Ops.apply(Nil{}, Ops.Doc{None{}, Some{"unavailable"}, [Ops.Op{Ops.Insert{}, 0n, [Ops.forgotten()]}]}))
    # Repeated inserts at one gap are deliberately outside the parser's
    # contract: swapping them changes the specification's result.
    check(Bool.not(items_equal(Spec.result(Nil{}, [Ops.Op{Ops.Insert{}, 0n, [Ops.line("a")]}, Ops.Op{Ops.Insert{}, 0n, [Ops.line("b")]}]), Spec.result(Nil{}, [Ops.Op{Ops.Insert{}, 0n, [Ops.line("b")]}, Ops.Op{Ops.Insert{}, 0n, [Ops.line("a")]}]))), "order independence needs distinct insert positions")
    cursor_case("raw reversed insert positions", Ops.from_text("a\nb\nc\n"), Ops.Doc{None{}, None{}, [Ops.Op{Ops.Insert{}, 2n, [Ops.line("x")]}, Ops.Op{Ops.Insert{}, 0n, [Ops.line("y")]}]})
    cursor_case("raw repeated insert position", [Ops.line("a")], Ops.Doc{None{}, None{}, [Ops.Op{Ops.Insert{}, 0n, [Ops.line("x")]}, Ops.Op{Ops.Insert{}, 0n, [Ops.line("y")]}]})
    cursor_case("raw overlapping deletes", Ops.from_text("a\nb\nc\n"), Ops.Doc{None{}, None{}, [Ops.Op{Ops.Delete{}, 0n, [Ops.line("a"), Ops.line("b")]}, Ops.Op{Ops.Delete{}, 1n, [Ops.line("b")]}]})
    cursor_case("range error precedes disagreement", [Ops.line("a")], Ops.Doc{None{}, None{}, [Ops.Op{Ops.Delete{}, 0n, [Ops.line("wrong")]}, Ops.Op{Ops.Insert{}, 9n, [Ops.line("new")]}]})
    cursor_case("first disagreement survives later failure", Ops.from_text("a\nb\nc\n"), Ops.Doc{None{}, None{}, [Ops.Op{Ops.Delete{}, 0n, [Ops.line("wrong")]}, Ops.Op{Ops.Delete{}, 2n, [Ops.line("also wrong")]}]})
    refused("first disagreement is retained", "a delete at 0 quotes lines the parent does not hold", Ops.apply(Ops.from_text("a\nb\nc\n"), Ops.Doc{None{}, None{}, [Ops.Op{Ops.Delete{}, 0n, [Ops.line("wrong")]}, Ops.Op{Ops.Delete{}, 2n, [Ops.line("also wrong")]}]}))
    cursor_case("newline failure precedes digest failure", [Ops.unterminated("a")], Ops.Doc{None{}, Some{"wrong"}, [Ops.Op{Ops.Insert{}, 1n, [Ops.line("b")]}]})
    cursor_case("digest failure", Nil{}, Ops.Doc{None{}, Some{"wrong"}, [Ops.Op{Ops.Insert{}, 0n, [Ops.line("a")]}]})
    IO.print("ok    positional/cursor oracles and refusal regressions")
