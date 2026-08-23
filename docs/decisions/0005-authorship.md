# 0005 — Authorship across rewriting

Decision 0002 gave every revision `author` and `when`, describing the work, and
`revised-by` and `revised`, describing the revision. It left open whether the
first pair should be *copied* into every later revision of a change or *read*
from the change's earliest revision.

They are copied. This document records why, what a copied fact can and cannot
be trusted to mean, and where that leaves the code.

## Reading fails exactly when rewriting has happened

The case against copying is redundancy: the same two lines repeated in every
revision of a change, and nothing enforcing that the repetitions agree.

The case for it is that the alternative does not work. Decision 0001 made
supersession an edge recorded on the *successor*, precisely so that rewriting
stays legible when the superseded revision is absent — and `History::superseded`
documents that absence as ordinary rather than incomplete. A rule that reads
authorship from a change's first revision therefore fails whenever that first
revision has been dropped, which is to say whenever the history has been
rewritten and pruned. It is a lookup that works until the moment it is needed.

Copying also keeps a revision a *whole* document. A file that states who did
the work and when needs no repository, no index, and no other file to be read
by a person — which is the property decisions 0002 and 0004 keep spending lines
to protect.

## A copied fact is a claim, not evidence

`author` is written by whoever writes the bytes. When a reviewer amends someone
else's change, they compose a file asserting a fact about a third party:

```
author Adam Harris <adam@example.com>
when 2025-08-19T09:02:40-06:00
revised-by Rowan Vale <rowan@example.org>
revised 2025-08-20T08:14:33+02:00
```

Nothing in the format verifies the first two lines. They are as trustworthy as
the person who wrote the file, and no more — the same warning decision 0001
attached to change IDs, for the same reason: **authorship must never be a
security boundary.** What makes this honest rather than alarming is that the
alternative is not better. A tool that derived authorship from a local
identity would be asserting the same unverified claim with less of the
reasoning visible. Verifiable authorship needs signatures, which is a later
decision and a different mechanism.

Two consequences follow, and both are deliberately permissive:

- **Divergent revisions of one change may disagree about `author`.** Divergence
  is legitimate (decision 0001), so disagreement about who did the work is a
  thing a person is shown, not an error. Consistency across a change is a
  convention writers keep, not an invariant the model enforces.
- **Nothing checks that `revised` is later than `when`.** No timestamp
  participates in identity, causality, or ordering, so a nonsensical pair
  misleads a reader and cannot mislead the model. Rejecting it would give
  timestamps a semantic weight the format has spent three documents denying
  them.

## Squashing can lose an author

Supersession may cross change IDs — that is what squashing one change into
another does, and `ChangeState::Abandoned` is the state the absorbed change is
left in.

The successor is a revision of the absorbing change, so its `author` describes
*that* change's work. The absorbed change's authorship survives only in its own
revisions, which are now superseded and may legitimately be absent. Squashing
can therefore erase the record that someone contributed.

This is recorded rather than fixed. Fixing it means a header naming co-authors
carried forward through supersession, which is a real feature with real design
(how many, how deduplicated, what happens on repeated squashes) and no user
yet. Until then, `x-co-authored-by` is exactly the advisory space decision 0004
provides, and a tool that squashes should write it.

## Where these facts live in the code

Authorship is a per-revision fact that the causal core never reads. Nothing in
`heads`, `missing_parents`, `superseded`, or `change_state` consults `author`,
`when`, `revised-by`, or `revised`, and after this decision nothing ever will —
copying forward means resolution never needs a lookup.

So the code splits along the same line the format does:

- **`format::RevisionDocument`** owns every header, the verbatim body, and the
  bytes the digest covers. It is what a `.rev` file parses to and what a writer
  emits.
- **`core::Revision`** stays what it is: the causal facts, and nothing that
  does not participate in causality or convergence.

The obvious objection is that a `log` needs the graph and the authorship at
once, and a core that holds only causal facts forces every renderer to consult
a side table. The store answers it. Decision 0003 makes the store the
authority — a directory of documents — so the store holds
`RevisionDocument`s keyed by digest, and a `core::History` is a *projection* of
them for graph questions. There is no side table because the documents were
never the side; the graph is the derived thing, which is the same relationship
decision 0003 gives `cache/`.

The alternative — growing `core::Revision` until it holds every header — was
rejected for two reasons. It puts timestamps inside a model whose first line of
documentation says no timestamp participates in identity or causality, and it
sets the precedent that each format decision widens the causal core, which
trees and signatures would then continue.

## Consequences

- `author` and `when` are required in every revision, root or not, and are
  copied verbatim across amend, rebase, and reword.
- `revised-by` and `revised` describe the revision. 0002 requires `revised`
  wherever `supersedes` appears; `revised-by` is written only when it differs
  from `author`, since a fact equal to another fact is a second spelling of it.
- A future `co-authored-by` is anticipated but not reserved: under decision
  0004's growth rule, adding it later costs nothing but forbids removing it.
- `src/format/` is owed as a module distinct from `src/core/`, and the store
  from decision 0003 holds documents rather than revisions.

## Resolved questions

1. **Whether `when` should be the moment work began or the moment it was
   recorded.** Answered by [0010](0010-writer.md): it is the moment the change
   was first recorded, copied forward through amendments.

## Deferred

2. **Whether an author is a free-text line or a structured identity.**
   `Name <address>` is a convention here, unparsed, which keeps the format out
   of the identity business until signatures force it in. Decision
   [0028](0028-accepting-by-path.md) keeps it deferred until a real key
   authority and trust boundary say what structure is needed.
