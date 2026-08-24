Comparison to other version control systems

| | Historica | Git / Hg | Jujutsu | Pijul / Darcs | Fossil | Automerge / Loro |
|---|---|---|---|---|---|---|
| Stored artifact | text ops + payloads | binary snapshots | snapshots | patches | SQLite | binary CRDT log |
| Readable without the tool | **yes** | no | no | partly | no | no |
| Merge is deterministic across implementations | **yes** | no | no | yes | no | yes |
| Merge preserves author runs (no interleaving) | **yes (Fugue)** | no | no | partly | — | yes (Fugue/RGA) |
| Conflicts stored in history | no (recomputed) | no | **yes** | yes | no | n/a |
| Stable change ID across rewrites | yes | no | **yes** | patch hash | no | n/a |
| CRDT metadata on disk | **none** | n/a | n/a | yes (graph) | n/a | grows forever |
| Redaction preserving structure | **yes (`forget`)** | no (rewrites all hashes) | no | no | `shun` | no |
| Remote / transport | **none** | yes | yes | yes | yes | yes |
| Rename detection at diff | **recorded, not inferred** | heuristic | heuristic | recorded | heuristic | n/a |
| Line attribution (`blame`) | **read from the operations** | re-diffed per commit | re-diffed per commit | patch-derived | re-diffed per commit | n/a |
| A merge's kept lines keep their author | **yes** | no | no | yes | no | n/a |
| Checkout to a past revision | **no** (`update` reaches heads, by decision) | yes | yes | yes | yes | n/a
| File modes | one bit, `executable` | one bit | one bit | one bit | one bit | n/a