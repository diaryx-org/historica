# Loro evaluation

Loro is a strong candidate to learn from and possibly use at runtime. It
provides operation-based CRDTs, version vectors, causal frontiers, branching,
time travel, and efficient data structures.

It is not currently Historica's persistence foundation.

## The boundary

Loro's stable synchronization API exports and imports a binary operation log.
Its JSON representation describes materialized document state, not enough
history to recreate operation identities, dependencies, and concurrent edits.
The internal encoding and operation-log crates expose more machinery, but are
explicitly unstable implementation details.

Consequently, persisting only readable Historica documents while treating a
Loro document as authoritative would leave no supported way to recreate that
same Loro history after deleting its binary export. Replaying visible edits as
new local Loro operations would mint different operation IDs and can produce
different conflict behavior.

## Acceptable future uses

Loro may still be useful if one of these boundaries becomes concrete:

1. **Disposable materialization.** Historica's readable operations are the
   authority, and a Loro document is a cache that can be rebuilt exactly through
   a stable structured-operation import API.
2. **Leaf-document collaboration.** A versioned file uses Loro internally, but
   has a complete readable operation representation defined and tested by
   Historica.
3. **Selected data structures.** We adopt independently usable, stable Loro
   types or algorithms whose semantics do not depend on its binary operation
   log.
4. **Upstream support.** Loro gains a stable structured export/import format
   carrying all operation IDs and causal metadata.

Until one of those is true, depending on Loro would make its binary encoding a
practical part of Historica's recovery contract, contrary to the project's
central rule.
