# 0063 — A range of revisions

Every command that reads the graph names one position. `log <target>` is that
revision and everything behind it, `show` and `cat` are that revision alone,
and 0001 spent a section on the argument position all three share:

> change IDs are spelled in `k`–`z` and digests in hex, so one command-line
> argument position can accept either without ambiguity

What has no spelling is the second most common question a person asks of a
history, which is not "what is behind this" but "what does this have that
that one does not". It comes up whenever two positions are compared: what a
fetch brought, what a branch of work added, what a release note has to cover,
which revisions a search has to walk. Today each of those is answered by
printing two logs and reading the difference by eye.

That last one is why this is being decided now rather than filed under
convenience. Asked whether `bisect` should be a command, the answer was that
the loop is a shell script anybody can write and read — except that the script
cannot compute the set it has to bisect. `Ancestry` is `pub(crate)` and there
is no spelling for the question, so the only way to get the revisions between
two positions out of this tool is to ask for two logs and subtract them in
`awk`. The missing thing is a query, and a driver command would have been a
worse answer to it: it would have carried state between commands, spawned
processes in a loop, and stood the folder at a revision 0030 refuses it.

## The decision

- **`log <from>..<to>` covers everything behind `to` that is not behind
  `from`.** Git's meaning for the same two dots, and deliberately so: this is
  a spelling millions of hands already have, and inventing a better one would
  be asking the world to learn a syntax in order to read a project whose
  premise is that it should not have to. 0037 made the same trade for the
  unified diff and gave the same reason.

- **It is a set subtraction over two ancestries, so it is defined for two
  revisions the graph left concurrent.** `ancestry(to)` minus
  `ancestry(from)`, and nothing about that asks the two ends to lie on one
  chain. Where they are concurrent, what comes back is the other side of the
  fork; where one is behind the other, the chain between them is the same
  answer with nothing on the other side. This is the one place the decision
  is *not* git's: git's `a..b` is also a subtraction, but git's history is a
  shape where people reason about it as a walk, and the walk and the
  subtraction come apart at merges. Here there is one definition and it is
  the honest one.

- **It goes in the argument position 0001 partitioned, and nothing else
  moves.** Neither alphabet contains a full stop — `k`–`z` and `0`–`9`,
  `a`–`f` — so the separator cuts a spelling no minted identifier could have
  been. There is no new flag, no second argument, and no other command
  learning the syntax: `show <a>..<b>` would be asking for a document that
  does not exist, and `diff` already spells the two-position question
  `--onto`.

- **A bookmark is looked up whole before the spelling is cut.** A store with
  a bookmark called `before..after` means the bookmark. This is not a new
  rule; it is the rule that already lets a bookmark called `head` beat the
  word the tool reserved, and 0022 permits the name — `names/` refuses `/`,
  `\`, and a full identifier, and a full stop is none of those. The cost is
  stated rather than hidden: a bookmark whose own name holds `..` can be
  named whole and cannot be one end of a range. That is the recoverable
  failure of the two, in 0045's terms, because the person who chose that name
  can rename it and nobody else's spelling changes.

- **Both ends are said outright.** No `a..` meaning the head and no `..b`
  meaning the root. `head` is four characters and a store may have several
  heads, so the elision would need the multi-head refusal `update` and
  `log --path` already carry, in order to save nothing worth saving. The
  refusal prints what to type.

- **`a...b` is refused by name.** Git's symmetric difference has no spelling
  here and no evidence anybody wants one. It is refused specifically rather
  than generically because the generic message would report that `.b` is not
  a bookmark and is spelled as neither a change ID nor a digest, which is
  true and would send a git-trained person hunting for a bookmark they never
  made.

- **An empty range is an answer, printed to stdout, exiting zero.** `to`
  holding nothing `from` does not is a fact about the history rather than a
  fault in the command, and it is a *different* fact from a store with
  nothing in it yet — which is why it does not reuse that sentence.

- **The filters compose with it, and `--path` is read at `to`.** A range says
  which revisions and a filter says which of those, so they compose the way
  the filters compose with each other. 0008 makes a path a fact read at one
  revision, and the revision a range names is its far end: the file a person
  typed the name of is the file it is now, not the file it was before the
  work being asked about happened to it.

## What is not here

**A range anywhere but `log`.** `blame` and `files` are about one position by
their nature. `diff` compares two and already spells it `--onto`, which is
the same question with a different answer shape and no reason to gain a
second syntax for it.

**`bisect`.** Above, and still not built. What this decision does is make the
shell script possible to write, which was the whole of the argument against
building the command.

**A machine-readable `log`.** The script a range now permits still has to
parse a rendering meant for eyes. That is the next thing somebody will want
and it is a decision of its own, because it is a promise about output nothing
currently makes. It is 0064's, and `log --fields` is what it decided.

## Consequences

- `target::Reach` is what one target argument resolves to, and
  `target::reach` is where the separator is cut. `target::resolve` is
  unchanged and still means one position, which every other command wants.
- `render::shown` takes the reach and `render::log` takes the set it
  produced, so the emptiness is decided where the person's own spellings are
  and the two callers stop computing the set twice.
- `tests/cli.rs` holds the cases that matter: the far end's own work, the
  other side of a fork, an empty range, the refusals, and a bookmark whose
  name holds the separator.
