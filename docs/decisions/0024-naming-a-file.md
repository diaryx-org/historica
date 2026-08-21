# 0024 — Naming a file

`historica files` prints a file identifier beside every path, and nothing in
this tool accepts one. Decision 0008 minted those twenty-four characters so that
a rename would keep everything recorded against the file rather than against the
path — and then left the identifier where only the format can reach it. A person
who wants "this file, whatever it is called now" has to spell it as a path,
which is the one name 0008 established is not the file's.

This document gives the identifier a spelling on the command line, and gives it
the same thing 0006 gave a change: a one-line file holding a name for it.

## The decision

- **A file identifier is spelled `file:<identifier>` where a path is expected.**
  `cat`, `show`, and everything else path-addressed take it, and it may be
  abbreviated to any unambiguous prefix, exactly as a change ID may.
- **`path:<path>` is the mirror escape**, for the file whose path begins
  `file:` and would otherwise be read as a spelling.
- **A file bookmark is a third key in `names/`.** `file <identifier>`, one line,
  in `history/names/<name>.txt`, beside the `change` and `revision` bookmarks
  0006 specified and under 0021's `.txt` rule.
- **`historica name <bookmark> <target> <path>` writes one**, taking the third
  argument `show` already takes and meaning by it what `show` means: this
  revision, and one file in it.
- **A bookmark name is usable wherever an identifier is** — after `file:`, and
  in `--at`.
- **A bookmark whose name is itself a full identifier is refused**, since the
  name would shadow the thing it is spelled like.

Nothing in the format changes. No header is added, no document's bytes move, the
corpus is untouched, and the version stays where 0017 put it. This is a decision
about what a person may type and about a file that only the front end reads.

## Why the path position could not simply absorb it

Decision 0001 spent a section on one argument position accepting two kinds of
name, and the trick was a disjoint alphabet: `k`–`z` for a change ID, `0`–`9`
and `a`–`f` for a digest, so neither can be read as the other. A file identifier
is spelled exactly as a change ID is — 0008 says so, and gives the reason: one
alphabet to learn.

The trick does not reach the path position, and the reason is worth stating
because it is not about alphabets at all. Both of 0001's spellings name things
*the tool minted*. A path is a value **a person chose**, and 0008 settled that a
path is any valid UTF-8 without control characters — which includes
`kxryzmorwlvtnsqpkzmuprys`. A file may be called that. A file may be called
anything. So no alphabet, however disjoint, can partition a space that already
contains everything.

The front end had a bare identifier in the path position anyway, since before
either half of this was thought about: `cat <target> <path>` parsed the argument
as an identifier first, and fell through to the path only when the parse failed
or the tree held no such file. That is the ambiguity above with a precedence
rule bolted on, and the precedence runs the wrong way — a file actually named
like an identifier becomes unreachable the moment some other file's identifier
is spelled the same, and which file `cat` prints depends on a value nobody can
see. It is retired here.

The existing target position keeps its rule, because there the argument really
is one of three minted names and 0001's alphabets really do separate them.

## The spelling is `file:`, and not `id:`

A prefix is the only shape available: a flag would make `cat --file <id>
<target>` a second grammar for the same command, and a sigil is a character
somebody's filename already has.

`id:` was the obvious candidate and is the wrong word. There are three
identifiers in this repository — a revision ID, a change ID, and a file
identifier — and 0001 exists because conflating the first two was the original
mistake. A prefix that says "an identifier follows" says nothing about which,
in the one tool where that distinction is load-bearing.

`file:` is the format's own word. The revision document spells these lines
`add <file> <path>`, `move <file> <path>`, `drop <file>`, and
`edit <file> <digest>`; the command that prints them is `files`; the bookmark
line this decision adds is `file <identifier>`. The command line therefore uses
the key the store's own files use, with a colon where those have a space,
because a shell argument is one word. A person who has read the store already
knows this word, which is the whole of the argument.

## `path:`, for the file this makes unreachable

A path may begin `file:`, so introducing the prefix takes one filename out of
reach of `cat` — which is exactly the failure this decision opened by refusing.
`path:` closes it: the rest of the argument is a path, literally, with one
prefix stripped and nothing else interpreted. `path:file:notes.md` names the
file called `file:notes.md`, and `path:path:x` names the file called `path:x`.

Nobody will type it. It is here because the alternative is a grammar with a hole
in it that the person who falls into it cannot climb out of, and because two
lines of code is a small price for being able to say that every file in a
repository can be named.

## A prefix is abbreviated against what `files` printed

`file:kx` resolves over the file set at the revision named, and not over every
identifier the history has ever held. Two reasons, and they agree.

The identifiers in scope are the ones `historica files <target>` prints, so the
prefix a person can see is the prefix that resolves, and the ambiguity they are
told about is one they can look at. And the alternative is worse than it sounds:
a file dropped four years ago would keep collecting prefixes forever, so the
number of characters needed to name a file that exists would grow with the
number that do not.

The cost is that the same prefix may name different files at different
revisions. That is true of digests too, and for the same reason — an
abbreviation is a convenience over a set, and the set is stated in the argument
before it.

## A file bookmark is 0006's bookmark, with one fewer choice

0006 gave a bookmark exactly one line and two keys: `change`, which follows the
work through every rewrite, and `revision`, which pins bytes that must not move.
The choice existed because those are genuinely two behaviours.

A file identifier has one. It is minted once, survives rename by construction,
and 0023 established that it survives amendment too — an amendment keeps the
identifier its predecessor minted, because the same file in the same place is
not a different file. There is nothing for a second key to mean, so there is no
second key and no flag.

```console
$ cat history/names/main.txt
change qpvuntsmwlrkzxonmvtplsyq
$ cat history/names/entry.txt
file lqxstvnmpkwyzrolvtsqnkxm
```

They live in one directory because a name is a name. Two directories would mean
one word could mean two things depending on where a reader looked, `names` would
have to say which anyway, and 0006's observation that `names/` holds the only
mutable files in a store — and is therefore the store's entire conflict surface
— is a reason to have one such directory rather than two.

`check` gains nothing structural: a bookmark is still one line with one key and
one identity in the matching alphabet, and a `file` line naming an identifier
no revision mentions is the dangling-bookmark note 0006 already wrote down, for
the reason it already gave. The name may be ahead of the sync.

## The command is `name`, with the argument `show` already takes

`show <target> [<path>]` means *this revision, and optionally the one file in
it*. `name <bookmark> <target> [<path>]` now means the same thing by the same
argument: with two arguments it points a bookmark at the work, with three it
points one at a file, resolved at the revision named.

A sibling command was the alternative — `name-file`, or `bookmark --file`. It
would be a second command whose whole difference is which of two things the
argument names, and this front end has one of those already: 0023 rejected
`record --amend` because a flag that changes what a command *does* is a flag
worth misreading. A third positional argument does not change what `name` does.
It writes a bookmark either way; the argument says what the bookmark is for.

`--revision` with a path is refused rather than ignored, since a file bookmark
has nothing to pin: it is the paragraph above, said in an error message.

## What this is for: an identifier that comes from somewhere else

The case that made this urgent is not a person typing `file:kx`.

An external system — prov, whose identifiers are NOID: digits and consonants —
wants to refer to a file in a Historica repository and be right about it after
every rename. The tempting arrangement is for that system to supply the
identifier, so that both sides hold one name for one file.

It cannot, twice over.

**The alphabet.** A NOID contains digits. 0001's disjoint alphabets are what let
one argument position accept a change ID or a digest without ambiguity, and they
hold because the two alphabets do not intersect. A third spelling containing
`0`–`9` intersects the digest alphabet immediately: `3t9x` is not a digest and
not a change ID, and a shorter one that happened to be all digits would be read
as a digest prefix. The property is not a convenience; it is what makes a person
able to look at a name and know what kind of name it is.

**The minting rule.** 0008 refused a derived file identifier for 0001's reason,
word for word: a derived identifier changes when the thing is rewritten. An
identifier supplied by another system is not derived, but it is not minted here
either, and it makes that system's availability a precondition for recording —
which is a worse dependency than either decision was willing to take on.

So the join is a **file bookmark whose name is the external identifier**. A
bookmark name is a string; it has no alphabet to collide with and nothing about
it is parsed. The external system holds its own identifier, this store holds a
one-line file mapping that identifier to the file it means, and
`historica cat head file:<noid>` answers with the file's current content
whatever it has been renamed to since.

That is the intended integration path, and it needs nothing from this format
that this decision does not already give it. The one constraint to state is that
a bookmark's name is a filename, so it must be a single path component — an
external identifier carrying `/` has to be spelled without it, or held under a
name that maps to it.

## The refusal that keeps the two apart

A bookmark whose name is itself a full identifier — twenty-four characters of
`k`–`z` — is refused when it is written.

Every place a bookmark may be typed looks it up before parsing anything, because
a name somebody chose beats a spelling the tool reserved; `target` says so
already about a bookmark called `ba5e`. That precedence is right and it is what
makes an identifier-shaped name a trap: `file:lqxstvnmpkwyzrolvtsqnkxm` would
stop naming the file it spells the moment somebody bookmarked that word, and
nothing would say so. Refusing at the point of writing costs a person nothing —
they were about to give a file a name, and its identifier is not one.

The refusal covers a change bookmark on the same terms, since a change ID and a
file identifier are one spelling and the trap is one trap. A four-character
`ba5e` is untouched: an abbreviation is not an identifier, and a bookmark
winning over a digest prefix is 0001's own answer.

## Consequences

- `store` gains `Name::File`, parsed from and written as `file <identifier>`,
  and `set_name` gains the refusal above. `check` learns the third key and
  reports a `file` bookmark naming an identifier no revision mentions as the
  dangling-bookmark note it already has.
- `cli/target` gains the `file:` and `path:` spellings in one function, which
  `cat` and `show` already share, and loses the bare-identifier fallback.
- `record --at <file>=<path>` accepts a bookmark where it accepted an
  identifier. It takes no prefix there: `--at` names a file against a survey
  rather than against a revision, so there is no stated set to abbreviate over,
  and an abbreviation whose meaning depended on what the folder happened to
  contain would be the same fault this document opened with.
- `names` prints all three kinds, each distinguished by the key its own file
  holds. A file bookmark resolves to the path that file has at the current
  heads, which is the answer a person is looking for and the one thing the
  bookmark deliberately does not record.
- A caller upgrading finds `cat <target> <identifier>` no longer resolves. It is
  a spelling that only ever worked by ambiguity, and the fix is one prefix.
- Nothing in the format grows, and the corpus grows nothing. If naming a file
  ever seems to want a header, that is evidence against this design rather than
  an extension of it.

## Rejected alternatives

**A flag: `cat --file <identifier> <target>`.** Two grammars for one command,
and the one that is typed less often is the one that has to be remembered. The
prefix keeps the argument in the position it was already in.

**A sigil: `@kx` or `:kx`.** Shorter, and it says nothing. `@` is a character a
filename may have and a reader has to be taught; `file:` is a word already in
the store, in the format, and in the name of the command that prints it.

**Resolving a bare identifier where no file matches the path.** The fallback
that exists today, tidied. It leaves the meaning of an argument depending on
what the repository contains, which is the property 0002 and 0008 each refused
in another form: two replicas must not disagree about what a name says.

**Letting a file bookmark carry a revision as well as a file.** 0006 refused the
two-line bookmark and the reasons carry over unchanged, with one more on top: a
file identifier does not move, so the second line would be stale by design and
would mean nothing on the day it disagreed.

**A separate `files/` directory of bookmarks.** Above: one name, one place.

**Accepting an external identifier as a file identifier.** Above: it breaks
0001's alphabets and 0008's minting rule, and buys nothing a bookmark does not
buy.

## Deferred

**A bookmark that names a path rather than a file.** Occasionally what somebody
means is "whatever is at `notes/today.md`", which is not what this records and
should not be spelled the same way. It needs a fourth key or nothing, and
nothing has asked for it.

**Showing bookmarks in `files`.** `names` lists them; putting them in a second
place is presentation work that can wait for evidence that the first place is
not where people look.

**Deleting a bookmark.** There is no command for it in this repository and this
decision does not add one: a bookmark is a file, and removing it is `rm`. Worth
revisiting when `names` has enough in it that a person stops wanting to look.

## Open questions

1. **Whether a file bookmark should follow a file across a `drop` and a fresh
   `add`.** It does not, and cannot: 0008 says a resurrection is a new file with
   a new identifier. The bookmark then names something history holds and the
   tree does not, which is reported where it is used rather than being silently
   repointed.
2. **What a file bookmark means at a revision that predates the file.** It
   resolves to an identifier the tree at that revision does not hold, and the
   refusal names both. Whether that should instead be silence is a question
   about how often a person addresses an old revision by a name they made for a
   new one.
