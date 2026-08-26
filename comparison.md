# Comparison to other version control systems

Historica prioritizes readability and maintainability by hand.
This means it has different tradeoffs compared to other version-control systems.

**No index, no configuration**
There are only two sources of truth:
the `*.ops.txt` and `*.rev.txt` files in the history,
and the actual files in your workspace.
Rather, at execution time,
Historica does a tree-walk through the operation/revision files.

**Library-first**
Historica is designed to be embedded in apps.
It shys away from process-spawning and large dependencies.
The Historica CLI is WASI-compatible (except for `fetch`).

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

## Command by command comparison to Git

### Reading a repository

| Git | Historica | Not the same thing because |
|---|---|---|
| `git status` | `historica status` | nothing is remembered between commands, so the answer is derived from the folder and the store every time (0015) |
| `git log` | `historica log` | the filters compose, and `--limit` counts what they left |
| `git log --format=…`, `--porcelain` | `historica log --fields` | one shape rather than a template language, and it carries no author and no message: `show` already prints the document those live in, byte for byte, so restating them would be a second answer that could disagree with the first (0064) |
| `git log <a>..<b>` | `historica log <a>..<b>` | the same meaning, computed as one ancestry taken out of another rather than walked, so two revisions the graph left concurrent are as well defined a range as two along a chain (0063) |
| `git log --follow -- <path>` | `historica log --path <path>` | the file is followed by identity, not by resemblance of name, so a rename is not a break in it (0008) |
| `git show <rev>` | `historica show <target>` | `show` prints the stored document, byte for byte. The *rendering* of what a revision did is `diff <target>` |
| `git show <rev> -- <path>` | `historica show <target> <path>` | prints the operation document — the deletes and inserts as they are stored |
| `git ls-tree -r <rev>` | `historica files <target>` | each entry carries the file's identifier as well as its path |
| `git show <rev>:<path>` | `historica cat <target> <path>` | — |
| `git diff` | `historica diff` | a rename between two revisions is *stated*, because the store recorded it; one in the folder is a drop and an add, because the folder cannot see it |
| `git blame` | `historica blame` | read from the operations rather than re-diffed, so a line keeps its author through a rename and through a merge that did not touch it |
| `git branch --list`, `git tag --list` | `historica names` | one kind of name, not two |
| `cat .gitignore` | `historica skip` | — |
| `git fsck` | `historica check` | reports every fault rather than stopping at the first, and exits non-zero only when the store cannot be trusted |
| — | `historica arrange` | Git has no filenames to arrange; Historica's are presentation, and this renames them to readable ones where they sit (0003) |

### Writing a repository

| Git | Historica | Not the same thing because |
|---|---|---|
| `git init` | `historica init [<dir>]` | the store is a visible `history/` directory beside the work (0006) |
| `git config user.email …` | `historica identity <author>` | said once, for every repository, and never kept beside the history (0010) |
| `git add <path>` | — | there is no index. A path on `record` narrows what is *surveyed*, and nothing is remembered past the end of the command |
| `git commit -a -m …` | `historica record -m …` | — |
| `git commit -m … <paths>` | `historica record <paths> -m …` | the files left out are not compared with the tree at all, so this records an observed state as much as the unrestricted command does (0039) |
| `git commit --amend` | `historica amend` | the rewrite is *recorded* as supersession rather than hidden, and the original stands until `prune` (0001, 0013) |
| `git rebase -i` + `reword` | `historica amend <target> -m <message>` | a revision work stands on takes a message and nothing else, and what stood on it is carried onto the new one verbatim — same operation documents, so the store gains none (0059) |
| `git mv <old> <new>` | `historica record --move <old>=<new>` | a rename is the one fact a person has to state, because the folder cannot show it (0011) |
| `git rm <path>` | delete the file, then `historica record` | — |
| `git merge <branch>` | `historica merge [<target>…]` | with no argument it takes every head. Nothing conflicted is ever recorded — two heads already *are* the conflict (0012) |
| `git checkout <branch>`, `git switch` | `historica update [<target>]` | reaches heads only. See below |
| `git restore <path>`, `git checkout -- <path>` | `historica update` | all or nothing: a folder half-holding a head is worse than a folder that plainly is not there yet (0030) |
| `git reset --hard` | `historica update` | bytes no revision records are never overwritten and never deleted |
| `git branch <name>`, `git tag <name>` | `historica name <bookmark> <target>` | one command, because a bookmark that moves and a bookmark that is pinned differ by `--revision`, not by kind (0062) |
| `git rebase --onto` | `historica carry [<target>] [--onto <destination>]` | restates work against a different parent. Without `--onto` that parent is a rewrite the store already holds, and nothing is stamped or minted, so two replicas repairing one history write the same bytes; with it a person decided, so the revision named is stamped and the stack above it derives from that (0010, 0059) |
| `git gc --prune=now` | `historica prune` | local, manual, and deliberately the undo history: it deletes superseded revisions nothing stands on, and prints every file (0013) |
| `echo … >> .gitignore` | `historica skip [--private] <path>…` | a rule has an axis saying whether it travels (0051) |

### Sharing

| Git | Historica | Not the same thing because |
|---|---|---|
| `git clone <dir>` | `historica export <dir>` here, `historica receive <dir>` there | export *assembles* a copy rather than mirroring the store: bookmarks and the cache stay behind, private rules do not travel, and nothing unrecorded or skipped can (0042, 0052) |
| `git push` | `historica export <dir>`, then `historica offer <dir> > offer.txt` | there is nothing at the far end to talk to. Publishing is writing a directory out and letting an ordinary file server hand it back |
| `git fetch <remote>` | `historica fetch <url>` | takes the manifest's URL, verifies every arriving file against its digest before believing it, adds history, and stops (0048) |
| `git pull` | `historica fetch <url>`, then `historica update` | the fetch and the folder's catch-up are two commands because they are two decisions |
| `git remote add …` | — | there are no remotes. Nothing is configured, so nothing is stale |
| `git bundle create` | `historica export <dir>` | compressing it is `tar`'s job |
| `git archive` | `historica export <dir> --files-only` | writes the folder and no history under it, for looking at a revision rather than working on one |

### Rewriting and redaction

| Git | Historica | Not the same thing because |
|---|---|---|
| `git revert <rev>` | — | undo the edit and `record` it, which is what the history should say happened |
| `git filter-repo`, BFG | `historica forget <target> <path> --lines <a>..<b>` | destroys those lines everywhere history quotes them and preserves their arithmetic, so everything downstream still materialises and merges. Every other hash in the history is untouched (0014) |
| `git reflog` | superseded revisions, until `historica prune` | the undo history is in the readable files rather than in a local log the format does not know about |
| — | `historica abandon <target> -m <why>` | supersedes a revision, and everything standing on it, with a tombstone that says why (0013) |
| `git rebase --onto <parent> <target>` (to drop one commit) | `historica abandon <target> --only -m <why>` | supersedes the one revision and carries what stood on it onto the tombstone, so the work above survives the work beneath it (0059) |

### Git commands with no counterpart, and why

`git stash` — nothing is remembered between commands (0011).
A folder holding work you are not ready to record is already the thing `stash` produces,
and `update` will not touch it, because it never overwrites or deletes bytes no revision records.

`git clean` — the same rule from the other side.
There is no command to remove unrecorded files because no command is permitted to.

`git cherry-pick` — not built.
`carry` is the narrow case that is decided:
restating work against a rewrite of its own parent,
where nothing has to be minted and both replicas write the same bytes.

`git bisect`, `git grep`, `git notes`, `git submodule`, `git worktree` — not
built, and none of them is refused on principle. `export --files-only` is the
part of `worktree` that exists today, and it is also the part of `bisect` that
exists: `log <a>..<b> --fields` says which revisions to search, in a shape a
script can cut a column out of, and `export --files-only` stands each one in a
directory of its own — so the loop is a shell script rather than a command that
would have to remember where it had got to (0063, 0064).

`git checkout <old-rev>` — refused on principle, and the one row above worth
dwelling on. The folder is only ever given a *head*: decision 0030 settled that
`update` names a position at the front of history and never one behind it, so
the detached state 0011 said would one day be necessary never is. To look at an
old revision, read it — `cat`, `files`, `show`, or `export --files-only` into a
directory of its own. To *work* from one, the honest record is a rewrite, and
`abandon` and `carry` are how that is written down.
