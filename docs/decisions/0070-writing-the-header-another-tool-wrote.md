# 0070 — Writing the header another tool wrote

0065 decided what a *reader* does with a key that has a dot in it: parse it,
hash it, sort it last, carry it across an amendment, never interpret it. The
parser has done that since. Nothing decided who puts one there.

The answer was nobody. `record` filled `extensions` with an empty map and
`Recording` had no field a caller could state one through, so the only dotted
header any store could hold was one written by hand into a `.rev` file. The
room 0065 made was room no tool could reach.

## What wants it

historica-git converts a git repository into a history and back. Decision 0004
over there makes the git commit a function of the revision — tree, parents,
author line, message, and a committer restated from the author rather than read
from the clock — so the round trip is an identity rather than a filing
cabinet: import a repository, write it back, and `git rev-list --all` matches.

It matches for a repository historica can hold entirely, and the exceptions are
exactly the git facts this format has no word for: a committer distinct from
the author, an `encoding`, a signature stripped before hashing. Pointed at
historica-git's own repository, every commit is signed and so no commit
round-trips. A repository whose commits are signed cannot be written back
without rewriting everyone's history, which makes the missing field the gate on
driving git with historica at all.

`git.committer` and `git.signature` close that, and they close it *because* of
the property 0065 already granted them: they are in the canonical bytes, so the
revision's identity covers them, and 0023 carries them across an amendment, so
a rewrite does not silently drop the fact that made the commit what it was. A
field beside the store, or a note in a sidecar, would have neither. Both are now
carried, and every one of historica-git's own signed commits verifies against
the repository written back from the history.

The third did not cross, and the reason is the useful half of the example.
historica-git's 0005 declined `git.encoding`, because an encoding is a claim
*about* the message rather than a fact beside it, and import has already
re-encoded the message to UTF-8 by the time it records — a document is UTF-8.
Carrying the declaration without the bytes it describes would file a commit
that says it is Latin-1 and is not. So a header holds what travels *with* the
revision without contradicting it, and a fact that describes bytes historica
has already changed is not one of those. That is a limit on what this field is
for, and it is worth knowing before somebody reaches for it as a place to put
anything git said.

## The decision

**A recording states the headers another tool wants on it.**
`Recording.extensions` is a map keyed by the whole spelling, dot and all, and
`record` writes it into the document. Empty is the ordinary case and what the
CLI passes, since historica records on its own behalf and has no fact it lacks
a word for.

**The writer checks the key, rather than trusting the caller.** 0065 made the
tool boundary the parser's business precisely so that `x-<tool>-<fact>`
convention could become a checked rule; a writer exempt from it would file a
document historica's own parser refuses by name, which is a store holding bytes
nothing can read back. So `format::check_extension` states the rule for a
writer — lowercase letters, hyphens and dots, a dot with something on both
sides of it, and at least one dot, since a key without one is this format's own
to define — together with 0002's three rules for any header value. `record`
asks before it plans, so a refusal has not already filed an operation document
on its way to saying no, and `record::check_extensions` is public for a front
end that performs a rename before it walks the folder.

The parser and the writer share one predicate for the characters, so the two
ends cannot drift. What they do not share is the dot: the parser must accept a
dotless key, because every header this format defines is one.

**An amendment carries and states nothing of its own.** 0023 already
carried `extensions` forward, and that stays the whole of it: `Amendment` gets
no field. The reason is 0023's own — an amendment restates what its predecessor
said, and a writer that cannot read a header must not drop it — and the reason
not to add the field now is that nothing has yet had to. A tool that rewrites a
revision *and* has to restate its own header is a real case, but the invalidated
`git.signature` is not it: a rewritten commit's signature is not stale, it is
wrong, and what to do about that is a question about signatures rather than
about amendment. When something needs to restate, the field goes on `Amendment`
and the choice is per key, not all-or-nothing.

**A tombstone writes none.** 0013's tombstone records nothing about the work it
supersedes, and a header some other tool hung on that work is about the work.
`abandon` writes an empty map for the same reason it writes no tree facts.

## What this leaves open

- **No CLI spelling.** There is no `--header` flag, because the person at the
  terminal is recording on historica's behalf and a tool driving the library is
  not. A flag would also need an answer for what `status` and `show` display,
  which is a question about presentation that nothing is asking yet.
- **Restating on amendment**, above: the field, when something needs it.
- **Nothing enumerates who is using a key.** 0065 refused a registry, and this
  changes none of that argument. Two tools that both spell themselves `git` are
  two tools with one name, which is a fact about their names.
