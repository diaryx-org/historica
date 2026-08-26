# 0071 — A name with structure in it

`set_bookmark` refused a name containing `/`, and the message said why: *a
bookmark is one filename*. That was true of the implementation and had never
been argued. 0021 gave a bookmark file its `.txt`, 0024 gave bookmarks their
third key and refused a name spelled as an identifier, 0062 gave them the
travel axis. None of them was asked whether a name may have structure in it.

It is asked now because `feature/x` is not exotic. Across the 25 git
repositories on this machine, 6 of 36 local branches have a slash in them, and
the names are `claude/<slug>` — what Claude Code calls a branch unless told
otherwise — and the `feat/` and `fix/` that fall out of Conventional Commits,
which this repository's own subjects already use. It is the default output of
two tools already in the loop, and historica-git reports every one of them as a
name that did not cross.

## The deadline is the tag, not the feature

Deferring this is not neutral, and the reason is the one 0016 recorded when it
nested `revisions/`:

> the fact that a flat reader fails *quietly* is the reason it belongs in a
> document rather than in a comment.

`check_names` skipped any entry that was not a file, and `name_files` listed
one level. So a store with `names/feature/x.txt` in it did not fail — it read
as a store with one fewer bookmark, reported nothing, and `check` called it
healthy. A 1.0 that shipped that behaviour would not merely lack hierarchical
names; every deployed copy of it would be a reader that silently drops them,
which is 0069's foreclosure argument arriving in the one directory where a
filename is data rather than presentation.

That asymmetry is also the answer to "why not just decide it later". Later
costs a format version. Now costs a walk.

## The decision

**A bookmark's name is its path below `names/`, without `.txt`.**
`names/main.txt` is `main`, and `names/feature/x.txt` is `feature/x`. The name
is spelled with `/` whatever the machine spells a path with, because a store
carries one spelling of a name and a copy made on another platform is the same
store.

**The grammar is 0018's, read rather than restated.** A name is a path:
relative, no empty component, no `.` or `..`, no leading or trailing space, no
control character, NFC. `store::check_name` delegates to `format::check_path`
for all of it and adds one refusal of its own — a backslash, ungated by
platform for the reason `PLATFORM_NAMES` is ungated: a name that is one
directory on one machine and two on another is a bookmark that changes shape
when its store is copied.

**Two of those refusals are load-bearing rather than tidy.** A bookmark file's
path *is* its name, and a name arrives over transport from a store this one did
not write. `..` and a leading `/` are what stop a manifest line from choosing
where in this store to put bytes. That guard used to be spelled `!name
.contains('/')` in `fetch::named_by` — flatness was doing security work as a
side effect, and the replacement has to do it on purpose. `set_bookmark` is the
one door into `names/`, every ingress goes through it, and it asks.

**`feature` and `feature/x` may both be bookmarks.** `names/feature.txt` beside
`names/feature/` is two files with two names, and a filesystem holds both
without complaint. Git forbids the pair because a loose ref is a file where the
directory would go; historica has no such collision and no reason to borrow the
prohibition.

**0024's rule stays at the writer, not in the grammar.** A name spelled as a
full identifier is a name this format *can* hold and a writer declines to
write. Refusing it in `check_name` would make the reader drop a file somebody
put in `names/` by hand, which is a store quietly holding one fewer bookmark
than its own directory shows — the failure this document exists to close.
`set_bookmark` states it, where the refusal reaches the person doing it.

**The walk is the loader's.** `check` and `open` call one function, for 0016's
reason: a `check` that recursed differently from the loader is how a store
passes a check it should not. A `.txt` file whose path is not a name this
format could write is `ForeignFile` — said out loud rather than skipped — and a
symbolic link under `names/` is `Unfollowed`, as it already is everywhere else.

**A removal takes its empty directories with it.** `remove_name` tidies
upwards until `remove_directory` refuses, stopping at `names/`, which is
`arrange`'s pattern exactly. An empty `names/feature/` in a published copy says
a `feature/` bookmark is there when none is.

## What this leaves open

- **Case-insensitive filesystems** get one more way for two names to collide,
  as `feature/x` and `Feature/x`. Flat names already had that shape of problem
  and the store still has no answer to it; nesting widens it rather than
  introducing it.
- **A depth limit.** There is none, for the reason 0016's walk has none: a tree
  of real directories cannot contain itself, and the walk follows no link.
- **Whether `names` should display a tree.** It prints a name per line, which
  stays right until somebody has enough of them to want otherwise.
