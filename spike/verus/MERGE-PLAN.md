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
- **Agreement** `agree(t, u, S)` — in place of an abstract tree: every
  element of `t` authored in `S` has a same-named twin in `u` with the same
  item, side, parent *name* and `deleted ∩ S`, and vice versa. Two walks
  assign different indices; names are what they share.
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

**Proven.** `theorem_convergence` verifies with no `admit`, no `assume`,
at Verus's default resource limit: 122 proof obligations, about 2.5 s, in
`merge_model.rs` (~2950 lines, roughly 450 of model and 2500 of proof).

| Piece | State |
|---|---|
| Model: graph, tree, `children`, `read`, `visible`, `anchor`, `replay_*`, `walk` | verified (terminating) |
| Example: two concurrent inserts tie by digest, both orders | verified; a flipped tie-break fails it |
| Lemma W (`lemma_walk_wf`) | verified |
| Lemma R (`lemma_visible_agree`, via R1–R5 on `sub_read`) | verified |
| Lemma A (`lemma_anchor_agree`) | verified; `anchor` without its `knows` filter fails it |
| Lemma E (`lemma_replay_event_agree`) | verified |
| Lemma M (`lemma_walk_outside`) | verified |
| Lemma C (`lemma_walks_agree`) | verified |
| `items` from agreement on every event (`lemma_items_agree`) | verified |
| Refusal transfers (`lemma_refusal_transfers`) | verified |
| **`theorem_convergence`** | **verified** |

## What the theorem rests on

The proof is about `merge_model.rs`, which is a transcription of
`merge.rs` by hand. Nothing here connects the two mechanically; the model
is read against the code, not derived from it. What is assumed:

- `knows` has the properties `GraphS::wf` lists — reflexive, transitive,
  acyclic, relating events only. That `ancestry.rs` computes such a
  relation from the parent edges is a separate, executable proof, and a
  natural next one.
- Events are indexed in digest order, so a comparison of indices is a
  comparison of digests; and an element is named `(author, minted)`
  rather than `(revision, op + offset)`. Sibling ties are broken by the
  author half, and two elements of one author are never same-side
  siblings, so the second half never decides an order — but that last
  fact is *not* proven here; the model simply never compares them.
- Resolutions (decision 0032) are not modelled, nor is `contested`.

## What the proof found in the code's argument

- **`visible` and `anchor` filter by different relations, and both are
  needed.** `visible` uses `saw` (strictly the past); `anchor` uses
  `knows` (the past and the event itself). The proof needs exactly this:
  an event's own fresh elements must be anchors for the rest of its run
  (`insert_run` passes `Some(t.len())` as the next left neighbour), and
  must *not* count into the positions of the document being replayed.
- **A mark's direction.** A removal recorded on an element is by an event
  that *saw the author*; an element of `f`'s can only be marked by events
  after `f`. Lemma C's union step depends on nothing in the shared set
  having seen `f`, which is exactly what "walked before `f`" gives. Getting
  the direction wrong the first time is what surfaced it.
- **`(revision, op + offset)` can collide within one revision.** The
  model sidesteps it; the code relies on same-author elements never
  meeting as siblings. Worth a comment in `Tree::attach`, or a proof.

## Lessons from mechanising it

- **Opaque by default for anything with a quantifier inside.** `order`,
  `visible`, `items` and `same_deleted` are opaque and revealed where used.
  Left open, `visible = order().filter(..)` met vstd's broadcast
  `filter_distributes_over_add` over a sum of `read`s and Z3 ran for
  minutes; `same_deleted`'s `forall d` was instantiated 1.6 million times.
- **Two-directional definitions feed themselves.** `agree` as one
  definition with both directions hung Z3 through fresh witnesses: clause
  one's twin `j` mentions `u.nodes[j]`, which fires clause two, whose
  witness fires clause one. As `half(t, u) && half(u, t)` with a symmetry
  lemma, every proof about it is a call to a lemma about `half`.
- **Name witnesses.** `exists` in a postcondition went brittle as the
  context grew; `src(s, p, q)` — the index `sel(s, p)[q]` came from — is
  stable.
- **A local filter.** `sel` is `Seq::filter` re-spelled so its four lemmas
  are the whole interface, with no broadcast triggers.
- **Triggers on set membership, not on nodes.** `agree`'s quantifier
  triggers on `set.contains(t.nodes[i].author)`; `same_node` never
  produces that term, so nothing cycles.
- The resource limit does not cap matching loops. Run each function alone
  with a wall-clock timeout to find the one that hangs, then bisect with
  `assume(false)`.
