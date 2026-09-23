# Executable checks against the independent Verus-style output oracle.
# Full item equality matters: text alone loses forgetting and newline flags.
import Base
import ./ops.bend as Ops
import ./replay_spec.bend as Spec
import ./cursor_spec.bend as Cursor
import ./semantic_replay.bend as Block
import ./text.bend as T
import ./merge.bend as Merge

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

# Exercise both compiled sides of the semantic theorem on successes and
# refusals, comparing complete results rather than only the rendered text.
def block_case(name: String, +before: List<&2, Ops.Item>, +after: List<&2, Ops.Item>, +stated: Maybe<&2, String>, +edit: Ops.Edit) -> IO(Unit):
  check(outcomes_equal(Ops.apply(List.append(&2, Ops.Item, before, after), Ops.Doc{None{}, stated, Ops.operations(List.length(&2, Ops.Item, before), edit)}), Block.apply(before, after, stated, edit)), name)

# Both compiled sides of the script theorem, on successes and refusals.
def script_case(name: String, +parent: List<&2, Ops.Item>, +stated: Maybe<&2, String>, +steps: List<&2, Ops.Step>) -> IO(Unit):
  check(outcomes_equal(Ops.apply(parent, Ops.Doc{None{}, stated, Ops.script(steps, 0n)}), Block.replay(parent, stated, steps)), name)

# The same theorem over raw operations, once they are ordered.
def ordered_case(+name: String, +parent: List<&2, Ops.Item>, +stated: Maybe<&2, String>, +ops: List<&2, Ops.Op>) -> IO(Unit):
  do IO<Unit>:
    check(Block.ordered(ops, 0n), name ++ ": ordered")
    check(outcomes_equal(Ops.apply(parent, Ops.Doc{None{}, stated, ops}), Block.replay_ops(parent, stated, ops)), name)

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
        quoted : List<&2, Ops.Item> = List.take(&2, Ops.Item, List.drop(&2, Ops.Item, parent, at), 1n+p)
        block_case("semantic deletion", List.take(&2, Ops.Item, parent, at), List.drop(&2, Ops.Item, parent, at), None{}, Ops.Deletion{quoted})
        quoted : List<&2, Ops.Item> = List.take(&2, Ops.Item, List.drop(&2, Ops.Item, parent, at), 1n+p)
        block_case("semantic replacement", List.take(&2, Ops.Item, parent, at), List.drop(&2, Ops.Item, parent, at), None{}, Ops.Replacement{quoted, [Ops.line("new"), Ops.line("run")]})
        intervals(p, at, parent)

def gap(+at: Nat, +parent: List<&2, Ops.Item>) -> IO(Unit):
  do IO<Unit>:
    oracle("insert at gap", parent, [Ops.Op{Ops.Insert{}, at, [Ops.line("new"), Ops.forgotten()]}])
    block_case("semantic insertion", List.take(&2, Ops.Item, parent, at), List.drop(&2, Ops.Item, parent, at), None{}, Ops.Insertion{[Ops.line("new"), Ops.forgotten()]})
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

def reads_back(m: Maybe<&2, Nat>, n: Nat) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{k}:
      Nat.is_eq(k, n)

# The decimal layer: every value has one spelling, which reads back, and
# `T.spell` agrees with Base's `Nat.show` where both are defined.
def spelled(+n: Nat) -> IO(Unit):
  do IO<Unit>:
    check(String.eq(T.spell(n), Nat.show(n)), "spell agrees with Nat.show at " ++ Nat.show(n))
    check(reads_back(T.number(T.spell(n)), n), "number reads back spell at " ++ Nat.show(n))

def unspelled(+s: String) -> IO(Unit):
  check(Maybe.is_none(&2, Nat, T.number(s)), "number refuses " ++ s)

# The round trip, run: what parses writes back byte for byte.
def round_trip.of(+s: String, parsed: Result<&2, &2, String, Ops.Doc>) -> IO(Unit):
  match parsed:
    case Fail{e}:
      IO.die(Unit, 1, "FAIL round trip: refused: " ++ e)
    case Done{doc}:
      check(String.eq(Ops.write(doc), s), "round trip of " ++ s)

def round_trip(+s: String) -> IO(Unit):
  round_trip.of(s, Ops.parse(s))

# `diff_applies`, run on shapes the corpus lacks: forgotten parent items,
# an unterminated last line on either side, and identical states.
def diff_case.of(+name: String, +parent: List<&2, Ops.Item>, +child: List<&2, Ops.Item>, d: Maybe<&2, Ops.Doc>) -> IO(Unit):
  match d:
    case None{}:
      check(items_equal(parent, child), name ++ ": no diff between different states")
    case Some{doc}:
      accepted(name, child, Ops.apply(parent, doc))

def diff_case(+name: String, +parent: List<&2, Ops.Item>, +child: List<&2, Ops.Item>) -> IO(Unit):
  diff_case.of(name, parent, child, Ops.diff(parent, child))

# `refusal_has_cause` and `no_cause_replays`, run: a refusal has a cause
# and no cause means the positional result.
def cause_case.of(+name: String, +parent: List<&2, Ops.Item>, +stated: Maybe<&2, String>, +ops: List<&2, Ops.Op>, applied: Result<&2, &2, String, List<&2, Ops.Item>>) -> IO(Unit):
  match applied:
    case Fail{e}:
      check(Block.cause(parent, stated, ops), name ++ ": refused without a cause: " ++ e)
    case Done{items}:
      check(Bool.and(Bool.not(Block.cause(parent, stated, ops)), items_equal(items, Spec.result(parent, ops))), name ++ ": accepted with a cause, or not positionally")

def cause_case(+name: String, +parent: List<&2, Ops.Item>, +stated: Maybe<&2, String>, +ops: List<&2, Ops.Op>) -> IO(Unit):
  cause_case.of(name, parent, stated, ops, Ops.apply(parent, Ops.Doc{None{}, stated, ops}))


# The merge model, held to what `merge.rs`'s tests expect: each order of
# one graph merges to the stated file, or refuses.
def merged_equal(a: Maybe<&2, List<&2, Ops.Item>>, b: Maybe<&2, List<&2, Ops.Item>>) -> Bool:
  match a b:
    case None{} None{}:
      True{}
    case Some{x} Some{y}:
      items_equal(x, y)
    case _ _:
      False{}

def merge_each(+name: String, +g: List<&2, Merge.Rev>, +expected: Maybe<&2, List<&2, Ops.Item>>, +first: List<&2, Nat>, os: List<&2, List<&2, Nat>>) -> IO(Unit):
  match os:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case +o <> rest:
      do IO<Unit>:
        check(Merge.orders(g, first, o), name ++ ": two causal orders of one graph")
        check(merged_equal(Merge.merged(g, o), expected), name)
        merge_each(name, g, expected, first, rest)

def merge_case(+name: String, +g: List<&2, Merge.Rev>, +expected: Maybe<&2, List<&2, Ops.Item>>, os: List<&2, List<&2, Nat>>) -> IO(Unit):
  match os:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case +first <> rest:
      merge_each(name, g, expected, first, first <> rest)

def stated(past: List<&2, Nat>, ops: List<&2, Ops.Op>) -> Merge.Rev:
  Merge.Rev{past, Some{ops}}

def abc() -> Merge.Rev:
  stated(Nil{}, [Ops.Op{Ops.Insert{}, 0n, Ops.from_text("a\nb\nc\n")}])

# One line of history: a replacement, an insert at the end, an insert at
# the front with a delete. The walk reads what the replay wrote.
# Two concurrent edits of `abc`, then an event that had seen both and
# edits what they merged to.
def after_merge_doc() -> List<&2, Ops.Op>:
  [Ops.Op{Ops.Delete{}, 2n, [Ops.line("b")]}, Ops.Op{Ops.Insert{}, 5n, [Ops.line("end")]}]

def after_merge() -> List<&2, Merge.Rev>:
  [abc(), stated([0n], [Ops.Op{Ops.Insert{}, 0n, [Ops.line("top")]}]), stated([0n], [Ops.Op{Ops.Insert{}, 3n, [Ops.line("bottom")]}]), stated([0n, 1n, 2n], after_merge_doc())]

def chain_docs() -> List<&2, List<&2, Ops.Op>>:
  [[Ops.Op{Ops.Insert{}, 0n, Ops.from_text("a\nb\nc\n")}],
   [Ops.Op{Ops.Delete{}, 1n, [Ops.line("b")]}, Ops.Op{Ops.Insert{}, 1n, [Ops.line("x")]}, Ops.Op{Ops.Insert{}, 3n, [Ops.line("y")]}],
   [Ops.Op{Ops.Insert{}, 0n, [Ops.line("z")]}, Ops.Op{Ops.Delete{}, 3n, [Ops.line("y")]}]]

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
    block_case("semantic quote disagreement", [Ops.line("before")], [Ops.line("a")], None{}, Ops.Deletion{[Ops.line("wrong")]})
    block_case("semantic delete out of range", Nil{}, [Ops.line("a")], None{}, Ops.Replacement{[Ops.line("a"), Ops.line("b")], [Ops.line("new")]})
    block_case("semantic unterminated suffix", [Ops.line("before")], [Ops.unterminated("last")], None{}, Ops.Replacement{[Ops.unterminated("last")], [Ops.unterminated("new")]})
    block_case("semantic forgotten terminator mismatch", Nil{}, [Ops.unterminated("last")], None{}, Ops.Deletion{[Ops.forgotten()]})
    block_case("semantic matching digest", Nil{}, Nil{}, Some{Ops.state_digest([Ops.line("new")])}, Ops.Insertion{[Ops.line("new")]})
    block_case("semantic wrong digest", Nil{}, Nil{}, Some{"wrong"}, Ops.Insertion{[Ops.line("new")]})
    block_case("semantic forgotten digest exception", Nil{}, Nil{}, Some{"wrong"}, Ops.Insertion{[Ops.forgotten()]})
    block_case("semantic invalid resulting terminator", [Ops.unterminated("before")], Nil{}, None{}, Ops.Insertion{[Ops.line("after")]})
    script_case("script: no blocks", Ops.from_text("a\nb\n"), None{}, Nil{})
    script_case("script: replacement then insert then delete", Ops.from_text("a\nb\nc\nd\ne\n"), None{}, [Ops.Step{0n, Ops.Replacement{[Ops.line("a")], [Ops.line("x")]}}, Ops.Step{1n, Ops.Insertion{[Ops.line("y")]}}, Ops.Step{1n, Ops.Deletion{[Ops.line("d")]}}])
    script_case("script: insert at a deleted run's end", Ops.from_text("a\nb\nc\n"), None{}, [Ops.Step{1n, Ops.Deletion{[Ops.line("b")]}}, Ops.Step{0n, Ops.Insertion{[Ops.line("x")]}}])
    script_case("script: two inserts at one gap", Ops.from_text("a\n"), None{}, [Ops.Step{1n, Ops.Insertion{[Ops.line("x")]}}, Ops.Step{0n, Ops.Insertion{[Ops.line("y")]}}])
    script_case("script: adjacent deletions", Ops.from_text("a\nb\nc\n"), None{}, [Ops.Step{0n, Ops.Deletion{[Ops.line("a")]}}, Ops.Step{0n, Ops.Deletion{[Ops.line("b")]}}])
    script_case("script: trailing insertion after replacement", [Ops.line("a"), Ops.unterminated("b")], None{}, [Ops.Step{1n, Ops.Replacement{[Ops.unterminated("b")], [Ops.line("b")]}}, Ops.Step{0n, Ops.Insertion{[Ops.unterminated("c")]}}])
    script_case("script: everything replaced on an empty parent", Nil{}, Some{Ops.state_digest([Ops.line("only")])}, [Ops.Step{0n, Ops.Insertion{[Ops.line("only")]}}])
    script_case("script: second block disagrees", Ops.from_text("a\nb\nc\n"), None{}, [Ops.Step{0n, Ops.Insertion{[Ops.line("x")]}}, Ops.Step{1n, Ops.Deletion{[Ops.line("wrong")]}}])
    script_case("script: first disagreement wins", Ops.from_text("a\nb\nc\n"), None{}, [Ops.Step{0n, Ops.Deletion{[Ops.line("wrong")]}}, Ops.Step{1n, Ops.Deletion{[Ops.line("also wrong")]}}])
    script_case("script: later block out of range", Ops.from_text("a\nb\n"), None{}, [Ops.Step{0n, Ops.Deletion{[Ops.line("a")]}}, Ops.Step{3n, Ops.Insertion{[Ops.line("x")]}}])
    script_case("script: deletion past the end", Ops.from_text("a\nb\n"), None{}, [Ops.Step{1n, Ops.Deletion{[Ops.line("b"), Ops.line("c")]}}])
    script_case("script: forgotten quote and wrong digest", [Ops.forgotten(), Ops.line("b")], Some{"wrong"}, [Ops.Step{0n, Ops.Replacement{[Ops.line("secret")], [Ops.line("x")]}}, Ops.Step{1n, Ops.Insertion{[Ops.line("y")]}}])
    script_case("script: unterminated item left in the middle", [Ops.unterminated("a")], None{}, [Ops.Step{1n, Ops.Insertion{[Ops.line("b")]}}])
    ordered_case("ordered: replacement then insert then delete", Ops.from_text("a\nb\nc\nd\ne\n"), None{}, [Ops.Op{Ops.Delete{}, 0n, [Ops.line("a")]}, Ops.Op{Ops.Insert{}, 0n, [Ops.line("x")]}, Ops.Op{Ops.Insert{}, 2n, [Ops.line("y")]}, Ops.Op{Ops.Delete{}, 3n, [Ops.line("d")]}])
    ordered_case("ordered: insert at a deleted run's end", Ops.from_text("a\nb\nc\n"), None{}, [Ops.Op{Ops.Delete{}, 1n, [Ops.line("b")]}, Ops.Op{Ops.Insert{}, 2n, [Ops.line("x")]}])
    ordered_case("ordered: adjacent deletions", Ops.from_text("a\nb\nc\n"), None{}, [Ops.Op{Ops.Delete{}, 0n, [Ops.line("a")]}, Ops.Op{Ops.Delete{}, 1n, [Ops.line("b")]}])
    ordered_case("ordered: replacement of nothing", Ops.from_text("a\n"), None{}, [Ops.Op{Ops.Delete{}, 1n, Nil{}}, Ops.Op{Ops.Insert{}, 1n, [Ops.line("b")]}])
    ordered_case("ordered: second replacement disagrees", Ops.from_text("a\nb\nc\n"), None{}, [Ops.Op{Ops.Delete{}, 0n, [Ops.line("a")]}, Ops.Op{Ops.Insert{}, 0n, [Ops.line("x")]}, Ops.Op{Ops.Delete{}, 2n, [Ops.line("wrong")]}, Ops.Op{Ops.Insert{}, 2n, [Ops.line("y")]}])
    check(Bool.not(Block.ordered([Ops.Op{Ops.Insert{}, 2n, [Ops.line("x")]}, Ops.Op{Ops.Insert{}, 0n, [Ops.line("y")]}], 0n)), "reversed inserts are not ordered")
    check(Bool.not(Block.ordered([Ops.Op{Ops.Delete{}, 0n, [Ops.line("a"), Ops.line("b")]}, Ops.Op{Ops.Delete{}, 1n, [Ops.line("b")]}], 0n)), "overlapping deletes are not ordered")
    check(Bool.not(Block.ordered([Ops.Op{Ops.Delete{}, 0n, [Ops.line("a"), Ops.line("b")]}, Ops.Op{Ops.Insert{}, 0n, [Ops.line("x")]}, Ops.Op{Ops.Delete{}, 1n, [Ops.line("b")]}], 0n)), "a delete hidden behind a replacement is not ordered")
    check(Bool.not(Block.ordered([Ops.Op{Ops.Delete{}, 1n, [Ops.line("b"), Ops.line("c")]}, Ops.Op{Ops.Insert{}, 2n, [Ops.line("x")]}], 0n)), "an insert inside a deleted run is not ordered")
    refused("script: second block disagreement is reported", "a delete at 1 quotes lines the parent does not hold", Block.replay(Ops.from_text("a\nb\nc\n"), None{}, [Ops.Step{0n, Ops.Insertion{[Ops.line("x")]}}, Ops.Step{1n, Ops.Deletion{[Ops.line("wrong")]}}]))
    accepted("script: positional result of three blocks", Ops.from_text("x\nb\ny\nc\ne\n"), Block.replay(Ops.from_text("a\nb\nc\nd\ne\n"), None{}, [Ops.Step{0n, Ops.Replacement{[Ops.line("a")], [Ops.line("x")]}}, Ops.Step{1n, Ops.Insertion{[Ops.line("y")]}}, Ops.Step{1n, Ops.Deletion{[Ops.line("d")]}}]))
    List.for_each(~&2, ~Nat, ~(n => spelled(n)), [0n, 1n, 9n, 10n, 11n, 99n, 100n, 101n, 4090n, 65535n, 1000000n])
    List.for_each(~&2, ~String, ~(s => unspelled(s)), ["", "042", "00", "1 2", "-1", "1a", " 1"])
    List.for_each(~&2, ~String, ~(s => round_trip(s)), ["historica\n\ninsert 0\n+a\n", "historica\nforgets 0000000000000000000000000000000000000000000000000000000000000000\n\ndelete 10 2\n-x\n-y\n", "historica\nresult 0000000000000000000000000000000000000000000000000000000000000000\n\ndelete 3 1\n-old\ninsert 3\n+new\n\\ no newline\n", "historica\n\ndelete 0 2\n-a\n\\ forgotten\ninsert 5\n+b\r\n+\\ no newline, read here as prose\n"])
    diff_case("diff: identical states", Ops.from_text("a\nb\n"), Ops.from_text("a\nb\n"))
    diff_case("diff: everything replaced", Ops.from_text("a\nb\n"), Ops.from_text("x\ny\nz\n"))
    diff_case("diff: forgotten parent item removed", [Ops.line("a"), Ops.forgotten(), Ops.line("c")], Ops.from_text("a\nc\n"))
    diff_case("diff: forgotten parent item kept beside edits", [Ops.forgotten(), Ops.line("b")], [Ops.line("x"), Ops.forgotten(), Ops.line("b"), Ops.line("y")])
    diff_case("diff: last line gains its newline", Ops.from_text("a\nb"), Ops.from_text("a\nb\n"))
    diff_case("diff: last line loses its newline", Ops.from_text("a\nb\n"), Ops.from_text("a\nb"))
    diff_case("diff: empty parent", Nil{}, Ops.from_text("a\n"))
    diff_case("diff: empty child", Ops.from_text("a\nb\n"), Nil{})
    diff_case("diff: repeated lines", Ops.from_text("a\na\na\n"), Ops.from_text("a\nb\na\na\n"))
    cause_case("cause: none", Ops.from_text("a\nb\n"), None{}, [Ops.Op{Ops.Delete{}, 0n, [Ops.line("a")]}])
    cause_case("cause: past the end", Ops.from_text("a\n"), None{}, [Ops.Op{Ops.Insert{}, 2n, [Ops.line("x")]}])
    cause_case("cause: disagreeing quote", Ops.from_text("a\nb\n"), None{}, [Ops.Op{Ops.Delete{}, 1n, [Ops.line("x")]}])
    cause_case("cause: forgotten quote agrees", Ops.from_text("a\nb\n"), None{}, [Ops.Op{Ops.Delete{}, 1n, [Ops.forgotten()]}])
    cause_case("cause: unterminated item not last", Ops.from_text("a\nb\n"), None{}, [Ops.Op{Ops.Insert{}, 0n, [Ops.unterminated("x")]}])
    cause_case("cause: right digest", Ops.from_text("a\nb\n"), Some{Ops.state_digest(Ops.from_text("b\n"))}, [Ops.Op{Ops.Delete{}, 0n, [Ops.line("a")]}])
    cause_case("cause: wrong digest", Ops.from_text("a\nb\n"), Some{Ops.state_digest(Ops.from_text("a\n"))}, [Ops.Op{Ops.Delete{}, 0n, [Ops.line("a")]}])
    cause_case("cause: wrong digest excused by forgetting", [Ops.forgotten(), Ops.line("b")], Some{Ops.state_digest(Ops.from_text("a\n"))}, [Ops.Op{Ops.Delete{}, 1n, [Ops.line("b")]}])
    merge_case("merge: a chain", [abc(), stated([0n], [Ops.Op{Ops.Delete{}, 1n, [Ops.line("b")]}, Ops.Op{Ops.Insert{}, 1n, [Ops.line("B")]}]), stated([0n, 1n], [Ops.Op{Ops.Insert{}, 3n, [Ops.line("d")]}])], Some{Ops.from_text("a\nB\nc\nd\n")}, [[0n, 1n, 2n]])
    merge_case("merge: concurrent edits in different places", [abc(), stated([0n], [Ops.Op{Ops.Insert{}, 0n, [Ops.line("top")]}]), stated([0n], [Ops.Op{Ops.Insert{}, 3n, [Ops.line("bottom")]}])], Some{Ops.from_text("top\na\nb\nc\nbottom\n")}, [[0n, 1n, 2n], [0n, 2n, 1n]])
    merge_case("merge: concurrent runs do not interleave", [abc(), stated([0n], [Ops.Op{Ops.Insert{}, 1n, Ops.from_text("x1\nx2\nx3\n")}]), stated([0n], [Ops.Op{Ops.Insert{}, 1n, Ops.from_text("y1\ny2\ny3\n")}])], Some{Ops.from_text("a\nx1\nx2\nx3\ny1\ny2\ny3\nb\nc\n")}, [[0n, 1n, 2n], [0n, 2n, 1n]])
    merge_case("merge: runs written backwards do not interleave", [abc(), stated([0n], [Ops.Op{Ops.Insert{}, 1n, [Ops.line("x1")]}]), stated([0n, 1n], [Ops.Op{Ops.Insert{}, 1n, [Ops.line("x2")]}]), stated([0n], [Ops.Op{Ops.Insert{}, 1n, [Ops.line("y1")]}]), stated([0n, 3n], [Ops.Op{Ops.Insert{}, 1n, [Ops.line("y2")]}])], Some{Ops.from_text("a\nx2\nx1\ny2\ny1\nb\nc\n")}, [[0n, 1n, 2n, 3n, 4n], [0n, 3n, 4n, 1n, 2n], [0n, 1n, 3n, 2n, 4n], [0n, 3n, 1n, 4n, 2n]])
    merge_case("merge: concurrent deletions agree", [abc(), stated([0n], [Ops.Op{Ops.Delete{}, 1n, [Ops.line("b")]}]), stated([0n], [Ops.Op{Ops.Delete{}, 1n, [Ops.line("b")]}])], Some{Ops.from_text("a\nc\n")}, [[0n, 1n, 2n], [0n, 2n, 1n]])
    merge_case("merge: a deletion beside a concurrent insertion", [abc(), stated([0n], [Ops.Op{Ops.Delete{}, 1n, [Ops.line("b")]}]), stated([0n], [Ops.Op{Ops.Insert{}, 2n, [Ops.line("new")]}])], Some{Ops.from_text("a\nnew\nc\n")}, [[0n, 1n, 2n], [0n, 2n, 1n]])
    merge_case("merge: a merge that records nothing changes nothing", [abc(), stated([0n], [Ops.Op{Ops.Insert{}, 0n, [Ops.line("top")]}]), stated([0n], [Ops.Op{Ops.Insert{}, 3n, [Ops.line("bottom")]}]), Merge.Rev{[0n, 1n, 2n], None{}}], Some{Ops.from_text("top\na\nb\nc\nbottom\n")}, [[0n, 1n, 2n, 3n], [0n, 2n, 1n, 3n]])
    merge_case("merge: the result does not depend on the order", [abc(), stated([0n], [Ops.Op{Ops.Insert{}, 1n, Ops.from_text("x1\nx2\n")}]), stated([0n], [Ops.Op{Ops.Insert{}, 1n, [Ops.line("y")]}, Ops.Op{Ops.Delete{}, 2n, [Ops.line("c")]}]), stated([0n, 1n], [Ops.Op{Ops.Insert{}, 0n, [Ops.line("first")]}])], Some{Ops.from_text("first\na\nx1\nx2\ny\nb\n")}, [[0n, 1n, 2n, 3n], [0n, 2n, 1n, 3n], [0n, 1n, 3n, 2n]])
    merge_case("merge: an insert after an element whose right child is a tombstone", [stated(Nil{}, [Ops.Op{Ops.Insert{}, 0n, [Ops.line("a")]}]), stated([0n], [Ops.Op{Ops.Insert{}, 1n, [Ops.line("x")]}]), stated([0n, 1n], [Ops.Op{Ops.Insert{}, 2n, [Ops.line("w")]}]), stated([0n, 1n, 2n], [Ops.Op{Ops.Delete{}, 1n, [Ops.line("x")]}]), stated([0n, 1n, 2n, 3n], [Ops.Op{Ops.Insert{}, 1n, [Ops.line("y")]}])], Some{Ops.from_text("a\ny\nw\n")}, [[0n, 1n, 2n, 3n, 4n]])
    merge_case("merge: an insert whose descent passes a tombstone", [abc(), stated([0n], [Ops.Op{Ops.Insert{}, 1n, [Ops.line("x")]}]), stated([0n, 1n], [Ops.Op{Ops.Insert{}, 2n, [Ops.line("w")]}]), stated([0n, 1n, 2n], [Ops.Op{Ops.Delete{}, 1n, [Ops.line("x")]}]), stated([0n, 1n, 2n, 3n], [Ops.Op{Ops.Insert{}, 1n, [Ops.line("y")]}])], Some{Ops.from_text("a\ny\nw\nb\nc\n")}, [[0n, 1n, 2n, 3n, 4n]])
    merge_case("merge: a document that disagrees with its view is refused", [abc(), stated([0n], [Ops.Op{Ops.Delete{}, 1n, [Ops.line("not-b")]}]), stated([0n], [Ops.Op{Ops.Insert{}, 0n, [Ops.line("top")]}])], None{}, [[0n, 1n, 2n], [0n, 2n, 1n]])
    merge_case("merge: a document past its view is refused", [abc(), stated([0n], [Ops.Op{Ops.Insert{}, 4n, [Ops.line("far")]}])], None{}, [[0n, 1n]])
    check(Bool.not(Merge.orders([abc(), stated([0n], Nil{})], [0n, 1n], [1n, 0n])), "merge: an order before its past is not causal")
    check(Bool.not(Merge.orders([abc(), stated([0n], Nil{})], [0n, 1n], [0n, 1n, 1n])), "merge: an order with an event twice is not distinct")
    accepted("merge: a chain replays", Ops.from_text("z\na\nx\nc\n"), Merge.replay(chain_docs(), Done{Nil{}}))
    check(merged_equal(Merge.merged(Merge.chain(chain_docs()), Merge.upto(3n)), Some{Ops.from_text("z\na\nx\nc\n")}), "merge: a chain merges to its replay")
    accepted("merge: a document on a merged history replays", Ops.from_text("top\na\nc\nbottom\nend\n"), Ops.apply(Ops.from_text("top\na\nb\nc\nbottom\n"), Ops.Doc{None{}, None{}, after_merge_doc()}))
    check(merged_equal(Merge.merged(after_merge(), [0n, 1n, 2n, 3n]), Some{Ops.from_text("top\na\nc\nbottom\nend\n")}), "merge: an event that saw a concurrent history applies its document")
    check(merged_equal(Merge.merged(after_merge(), [0n, 2n, 1n, 3n]), Some{Ops.from_text("top\na\nc\nbottom\nend\n")}), "merge: and does so in either order of that history")
    IO.print("ok    positional/cursor/block/script/diff/cause/merge oracles, spelling and refusal regressions")
