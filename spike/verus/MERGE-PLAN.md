# Proving `merge.rs` converges: the plan

`merge_model.rs` is the specification: `walk(g, order, k)` is what
`Tree::replay` computes after `k` events of a causal order, and
`theorem_convergence` says two causal orders of one graph produce the same
file or the same refusal. This document is the proof, on paper, in the order
the lemmas will be mechanised. It is written so that a session that picks it
up cold can see what is done and what is next.

## Why it is true

`anchor` reads only siblings whose author the event *knows*, and `visible`
only elements the event *saw* and nothing it saw removed. So what an event
does to the tree is a function of the part of the tree its author's causal
past built — and that part is the same whichever order built it, by
induction. The rest is bookkeeping: two walks assign different indices to
the same elements, so the thing that is equal is the tree up to renaming, and
`items` has to be shown to depend only on that.

## Definitions to add

- **Name.** `(author, minted)`. Unique across a walk, because each event
  mints its own count and an event is replayed once.
- **Abstract tree** `Abs = Map<Name, (parent: Option<Name>, right: bool,
  item: ItemS, deleted: Set<int>)>`, and `abs(T)` for an index tree `T`,
  mapping each node's parent index to that node's name.
- **Restriction** `restrict(A, S)` for a set of events `S`: the elements
  whose author is in `S`, with `deleted` cut down to events in `S`.
- **Closed** `closed(g, S)`: `e ∈ S ∧ knows(e, o) ⇒ o ∈ S`. Every prefix
  of a valid order is closed, and so is `knows(e)` and `knows(e) \ {e}`.
- **Walk well-formedness** `wf_tree(T, g)`: a parent's index is below its
  child's; a parent's author is known by the child's author; names are
  unique; `deleted` only holds events that saw the element's author.
  Every `walk(g, o, k)` satisfies it — Lemma W.

## The lemmas

**Lemma W (the walk builds well-formed trees).** Induction on `k`;
`attach` places under an anchor whose author the event knows (by `anchor`'s
own filter), and `delete` marks with the event replaying, which saw the
target's author (it was in `visible`).

**Lemma 0 (`items` is a function of `abs`).** `abs(T1) == abs(T2)` and both
well-formed ⇒ `T1.items() == T2.items()`. The in-order reading of an index
tree, mapped through names, equals the in-order reading of the abstract tree
(children of a node, sorted by name, are the same set in both). Induction
over `read`/`read_all`; the sibling lists are sorted by name and names are
unique, so the lists correspond one to one.

**Lemma R (restriction commutes with reading).** For well-formed `T` and any
`e`: `T.visible(g, e)` is the in-order reading of `restrict(abs(T),
knows(e) \ {e})`, filtered to elements nothing in that set removed. Because
parents are known by their children's authors, the known elements form a
sub-forest closed under parent; removing unknown siblings from a name-sorted
list keeps the known ones in order. Same induction as Lemma 0.

**Lemma A (`anchor` reads only the restriction).** `T.anchor(g, e, left)`,
expressed in names, equals the anchor computed in `restrict(abs(T),
knows(e))`. `first_known` over a sibling list is the head of that list
filtered to known authors, and filtering commutes with sorted insertion.
`leftmost_known` is the same, down the left spine.

**Lemma E (one event reads only its restriction).** `abs(replay_event(T, g,
e))` is `abs(T)` plus the elements and marks that `replay_event` on
`restrict(abs(T), knows(e))` would add — and `replay_event(T, g, e)` is
`None` exactly when the restricted replay is. Induction over `replay_ops`,
`insert_run`, `delete_run`, using R for `prepare` and A for each anchor.
Note `knows(e, e)`: an event's own fresh elements are in its restriction,
which is what makes a run attach to itself.

**Lemma M (later events do not touch an earlier restriction).** For closed
`S ⊆ set(o[0..k])` and `k' ≥ k`: `restrict(abs(walk(o, k')), S) ==
restrict(abs(walk(o, k)), S)`. An event `f ∉ S` adds elements authored by
`f` and marks by `f`; both fall outside the restriction.

**Lemma C (two walks agree on every closed set they share).** For valid
`o1, o2` and `k1, k2`, for every closed `S ⊆ set(o1[0..k1]) ∩
set(o2[0..k2])`: `restrict(abs(walk(o1, k1)), S) == restrict(abs(walk(o2,
k2)), S)`, and `walk(o1, k1)` is `None` iff some event of the shared prefix
fails, which is a property of the event's restriction alone. Induction on
`k1 + k2`. Step, `o1` gaining `f`: for `S ∌ f` nothing changes on the left
(Lemma M's argument for one step). For `S ∋ f`: `S \ {f}` is closed and
shared (nothing in a prefix of `o1` up to `f` knows `f`), so by induction the
two restrictions to `S \ {f}` agree, and to `knows(f) \ {f}` in particular;
by Lemma E, `f`'s contribution on each side is a function of that; on the
right, `f` was replayed at some earlier `k2' < k2`, and Lemma M carries the
restriction to `knows(f) \ {f}` from `k2'` to `k2`.

**Theorem.** `k1 = k2 = n`, `S = ` every event: the abstract trees are equal,
so by Lemma 0 the files are; and the refusals agree by Lemma C's second half.

## What is out of scope of the theorem as stated

- **Resolutions** (decision 0032). `Tree::resolution` is a second way to
  state an event; the model has only `Tree::operations`. Adding it is more
  definitions and a second case in Lemma E, not a new idea.
- **`contested`.** The report is "computed from the finished structure", so
  it is a function of `abs` too, but it is not in `merged`.
- **`linear == walk` on chains.** A separate, easier theorem: on a chain the
  restriction is the whole tree and `visible` is the whole file.
- **No interleaving.** Fugue's guarantee is a theorem about the *ordering*,
  not about convergence, and is where a Lean formalisation of the paper
  would be the reference. Not attempted.

## Status

| Piece | State |
|---|---|
| Model: graph, tree, `children`, `read`, `visible`, `anchor`, `replay_*`, `walk` | verified (terminating, well-typed) |
| Attach-unfolding lemmas (`lemma_children_attach`, `_hang`, `_none/_one/_two`) | verified |
| Example: two concurrent inserts tie by digest, both orders | verified |
| `theorem_convergence` | stated, `admit()` |
| Lemma W (`lemma_walk_wf` and the `replay_ops`/`insert_run`/`delete_run` chain under it) | verified |
| Lemma 0 | not started |
| Lemma R | not started |
| Lemma A | not started |
| Lemma E | not started |
| Lemma M | not started |
| Lemma C | not started |

## Lessons from the model so far

- Z3 will not evaluate the model on a concrete input by itself; every step
  is a `reveal_with_fuel` and an `=~=`, and a proof function that does more
  than one step runs for minutes. Keep example lemmas to one unfolding each.
- `Set::is_empty` costs cardinality axioms; `forall d. !contains(d)` is free.
- Facts that mention `Seq::filter` should be established inside `assert ...
  by` blocks so the filter lemmas do not stay in the outer context.
