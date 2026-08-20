# 0011 — The working copy

Decision 0008 deferred "the working directory: checkout, status, and how a
contested path is shown to a person". Decision 0010 decided what a writer
supplies and handed the same list on, because a writer has to be *given*
something before it can supply anything: a set of files, a parent to record
against, and the facts about the file set that cannot be observed.

This decides that much and no more. Checkout and status remain deferred; what
follows is what `historica record` needs and nothing that only a nicer front
end would want.

## The decision

- **The working copy is the directory holding the store.** Everything beside
  `history/` is tracked, except what `history/skipped` names.
- **The parent is the store's head.** One head needs no argument; several
  require `--onto`, and so does deliberately working somewhere older.
- **One record covers every changed tracked file.** There is no index.
- **A rename is stated; everything else is observed.** `--move old=new` is the
  one fact a person supplies, and it performs the rename if they have not.

And the rule underneath all four:

> Nothing is remembered between commands. The working copy is the folder as it
> stands and the store as it stands; there is no third thing that can disagree
> with either.

That rule is why there is no index, no tracked-file list, no pending-rename
file, and no stored position. Each of those is a place work can hide, and this
project has spent nine decisions keeping the number of places a person must
look at one.

## The folder is the working copy

Decision 0006 already defines the folder: discovery walks up from the working
directory looking for `history/`, and the directory holding it is the
repository root. Everything beneath that root is tracked, `history/` excepted.

There is no `add`. A journal is a folder of prose, and asking permission per
file is friction that buys nothing — the person who made the file is the person
recording it, a second later. More to the point, a list of tracked files would
have to live somewhere, and wherever that is becomes a third source of truth: a
file present in the folder, absent from the list, and therefore absent from
history, with nothing on screen to say so.

The cost is that a file appears in history because it appeared in the folder.
That is what `history/skipped` is for, and why it is refused rather than
guessed at when it cannot do its job.

## `history/skipped`

The file is named for what it holds. It lists what history does not take.

```console
$ cat history/skipped
skip target/
skip .DS_Store
skip-suffix .tmp
```

It is the grammar every readable file here uses: a key, one space, a value to
the end of the line. Two keys:

- `skip` — a path relative to the root. A value ending in `/` names a directory
  and everything beneath it; a value that does not is one exact path.
- `skip-suffix` — a trailing string, matched against the last path component.

**No glob language, no negation, no per-directory files.** Gitignore's pattern
syntax is a language with precedence rules, and the part people get wrong is
never the pattern — it is which of five files won. Here one line means one
thing and the file is in one place. A future key adding globs costs nothing to
introduce, because it is a new key and not a new meaning for an old one.

An unknown key is an error. This is the one place where 0002's argument —
refusing is friendlier than lying — has a sharper edge than usual: a reader
that ignored `skip-glob` because it had not heard of it would record files
somebody asked it not to, into a history that is append-only. Refusing to
record is recoverable. Recording is not.

The file lives in the store because what a repository skips is a fact about the
repository, not about the person — the opposite of 0010's identity, which lives
with the person for the same reason read backwards. It is therefore mutable and
synced, which puts it in `names/`'s company as part of the conflict surface,
and `check` reads it as it reads a bookmark: a malformed line is an error
naming the file.

**A rule that matches a file already in the tree is refused.** Adding
`skip drafts/` for a directory history already holds would otherwise make those
files vanish from the folder's point of view, and the next record would spell
that as `drop` — a line asking for privacy, silently deleting history's copy of
what it names. The message says which file, and says that removing a file from
the tree is what deleting it does. History holds what it holds.

## The parent is the head

The store has no notion of where a person is standing, and this decision adds
none. `record` takes the head; if the store has more than one, it refuses and
asks for `--onto <target>`, which takes the same targets every other command
does. An empty store records a root revision with no parent.

The alternative was a per-machine file — `history/at`, one line, never synced.
It is rejected for now rather than forever. `names/` cannot hold a position,
because bookmarks sync and 0003 calls them the entire conflict surface, so two
machines would overwrite each other's sense of where each was standing; and
`cache/` cannot, because it is defined as deletable without loss. A position
would therefore be a fourth kind of file in a layout that has three, and the
thing that forces it does not exist yet. **When checkout arrives** — when
something other than a head can be in the folder — the file becomes necessary,
and that is the decision that should introduce it.

Recording advances a bookmark that named the parent's change, because 0006 made
`change` bookmarks the kind that follow work. A bookmark spelled `revision` is
the exact pin that must not move, and does not.

## What one record covers

Every tracked file whose state differs from the parent's, in one revision.
`--dry-run` prints that set and writes nothing.

```console
$ historica record --dry-run
added   2026-08-20.md
edited  2026-08-19.md
moved   notes.md -> docs/notes.md
dropped scratch.md
```

Each of the four comes from comparing the folder with the tree at the parent:

| The world | The fact | Where it comes from |
| --- | --- | --- |
| Present, not in the tree | `add` | a file ID minted as 0010 mints |
| In the tree, absent | `drop` | observed |
| `--move old=new` | `move` | stated |
| Content differs | `edit` | `diff` against the parent's state (0009) |

Minting a file identifier is 0010's rule word for word, which is 0008's
position already: "0001's argument for minting rather than deriving it applies
here word for word". 0010 says `change`; this says the same of `file`, and
neither is a security boundary.

There is no index. An index is a second place work can hide, and 0007 already
makes every operation a permanent event — a person who wants one topic per
revision gets it by recording more often, not by curating a buffer.

A record that would state nothing is refused. 0009 says a file that did not
change names no document; a revision that changed no file, added none, and
moved none is that fact at the level above, and recording it would put a node
in the graph that means nothing.

Documents are written before the revision that names them: operations first,
then the revision. An interrupted record therefore leaves operation documents
nothing points at, which `check` already reports as a note, rather than a
revision naming a document that is not there, which it reports as an error.

## A rename is the only fact that must be said

0008 minted file identifiers precisely so that a rename would not have to be
recovered by matching content, and refused that heuristic in the same breath as
0002 and 0007 refused theirs. A person therefore has to say it, and `--move`
is where.

It accepts the world in either state:

- old path present, new path absent — `record` performs the rename, then
  records it;
- rename already done by hand — `record` records it;
- both present, or neither — refused, naming both paths.

So the flag works whether a person reached for `mv` first or not, which is the
only way a flag like this survives contact with how people actually work. A
file that was renamed *and* edited states both facts, `move` and `edit`, which
is what `tests/corpus/tree/revisions/03-move.rev` already spells.

Everything else is observed, because absence is a fact rather than a guess. A
file deleted from the folder is `drop`ped; there is no `--drop`, and `record`
never deletes anything a person did not delete.

## What the format cannot hold

Three kinds of file cannot be recorded, and each is refused by name with the
line that fixes it — `skip <path>` in `history/skipped`.

- **Content that is not UTF-8.** 0007's items are lines of text, and 0008's
  binary shape has no implementation.
- **Symlinks.** Nothing in the format spells one, and following it would record
  a copy of somebody else's file under this name.
- **Anything the filesystem offers that is not a regular file**: devices,
  sockets, and the rest.

They are refused rather than skipped silently, on one argument: a person who
believes a file is in history and finds later that it is not has lost work, and
the difference between the two outcomes is one error message. A mode is not
refused, because 0008 already decided that a mode is noise in a tool for prose;
an empty directory is not refused either, because 0008 decided a directory
exists exactly when a file's path names it, so an empty one is nothing to
record rather than something to reject.

## The message

`-m` takes it. With no `-m`, `$VISUAL` then `$EDITOR` opens on an empty file,
and what the person leaves is the message. An empty message is allowed, because
0002 says so: "nobody should be made to describe work before they are allowed
to record it".

**The template is empty, and nothing is stripped.** Git's editor template is
comment lines beginning with `#`, removed before the commit is written — which
here would eat the first line of every journal entry that opens with a Markdown
heading. 0002 says the body is never parsed, trimmed, re-wrapped, or escaped,
and a writer that stripped lines on the way in would be doing all four to a
format that promises none of them. What a person types is what the file holds,
trailing spaces included.

`record` prints the change ID and digest of what it wrote, and says when the
message was empty — 0006's `arrange` falls back to a change ID for the filename
in that case, and a person should hear about it before the folder does.

## What this writer does not do

Three refusals, in the library's own words, exactly as `files` and `cat`
already refuse:

- **Amending.** 0010 decided what a rewrite says; restating a descendant's
  operations against a parent whose content changed is transforming operations
  against operations, which is 0007's merge under another name and is not
  wired into the store.
- **Recording where the ancestry holds a merge.** `Store::content` walks
  single-parent edges, so the parent state cannot be materialised there yet.
- **Recording a merge.** Same reason from the other side: the merged content is
  what a person would be editing, and nothing can produce it yet.

None of these needs a decision. All three become possible the moment `merge`
is wired into the store, which is the work the README already names as owed.

## Rejected alternatives

**An index.** Above: a second place work can hide, in a project whose whole
argument is that there is one place to look.

**An explicit `add`, with a tracked-file list.** The list is a third source of
truth, and the failure it produces is silent: a file in the folder, absent from
history, with nothing on screen saying which.

**Gitignore syntax.** Above. The complexity is not in the patterns.

**A stored position now.** Above: rejected until checkout needs it, not on its
merits.

**Inferring a rename by content similarity.** Refused by 0008 as the heuristic
that identifiers exist to avoid.

**Skipping unrecordable files with a warning.** A warning scrolls past. The
person finds out when they need the file.

**`--drop`.** Deletion is observed, and a flag that deleted a person's file to
match its own record would be the one destructive thing in the tool.

## Consequences

- `src/` gains the writer 0010 owes and a working-copy module beside it: the
  comparison that produces the four facts, and the reader for
  `history/skipped`.
- `historica record [-m <message>] [--onto <target>] [--move <old>=<new>]
  [--dry-run]` is the command. `history/skipped` is a fifth entry in the
  store's layout, parsed by the store and reported by `check` on the terms a
  bookmark is.
- The tests owed are the ones that would catch a writer being clever: a
  rename recorded as `move` and not as `drop` plus `add`; a rename plus an edit
  in one revision; a record that would state nothing being refused; a file that
  is not UTF-8 refusing by name; a `skip` rule matching a tracked file being
  refused; and a message that begins with `#` surviving byte for byte.
- 0008's working-directory deferral is half answered. Checkout and status are
  the other half and stay deferred.

## Deferred

**Checkout and status**, and with them the stored position this decision
declines to invent.

**Binary content**, which 0008 shaped and nothing implements.

**Two paths differing only in case or normalisation**, which is 0008's second
open question and arrives here as a real one: the folder is what the filesystem
says it is, and a filesystem that folds case will hand this writer one file
where the tree holds two. `check` already calls that a note. What `record`
should do about it needs the case in front of it.
