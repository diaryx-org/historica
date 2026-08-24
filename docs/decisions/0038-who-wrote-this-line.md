# 0038 — Who wrote this line

0037 answered "what changed". The other question a person asks of a history
they did not write is "who wrote *this*, and why" — and the only way to ask it
here was `log`, which says what every revision did and leaves the reader to
find the one that touched the line in front of them.

Every tool has this command and every tool has to guess at it. Git's `blame`
runs a diff between each pair of adjacent commits and decides, by resemblance,
which line of the child is which line of the parent; the knobs it grew —
`-M`, `-C`, `-w`, `--ignore-rev` — all exist because that guess is wrong often
enough to need arguing with.

Historica does not have to guess, and has not had to since 0007. A revision
records the items it *inserted*, a merge records which items *survived* and
under whose names (0032), and `merge::Merged::origins` — the vector saying
which revision wrote each item — has been computed on every materialisation
since 0012 needed it to label the runs inside a contested span. `blame` is
that vector, printed.

## The decision

- **`blame [<target>] <path> [--lines <first>..<last>]`.** A rendering, like
  `diff` and for 0037's reason: nothing here is stored, nothing reads it back,
  and `show` remains the command that prints the authority. One argument is a
  target or a path by 0001's disjoint alphabets, exactly as `diff` reads it,
  and `--lines` is spelled the way `forget` already spells a span.

- **The attribution is read, not inferred.** `origins` comes from the
  operations themselves: an item is written once, by the revision whose
  document inserted it, and it carries that name for as long as it survives.
  Nothing is re-diffed to produce it, so the answer cannot move under a
  person — it does not depend on a matching algorithm, it does not change when
  a flag is passed, and two implementations of this format print the same
  names. There is no `-w` and no `--ignore-rev`, because there is no
  re-derivation for them to steer.

- **A line the store recorded as new is new, even where a person would call it
  moved.** `show`, for the revision that moved a line down a file, prints a
  `delete` and an `insert`; `diff` renders that as a removal and an arrival;
  and `blame` says the mover wrote it. All three are the same fact, and the
  fact is what was written down at the time. `-M` and `-C` exist in other
  tools to argue with that answer by resemblance, and declining them is 0037's
  rule one command later: what a person is shown and what the store holds are
  one answer computed once. What is bought with that guess is the two claims
  below, which no heuristic can offer at all.

- **A line keeps its author across a merge.** 0032's resolution keeps items
  *under their own names* rather than restating them, and `merge` crosses one
  by taking those names as stated. A merge therefore authors only the lines it
  actually typed — the resolution's `insert` pieces — and every line it kept
  is still attributed to the branch that wrote it. This is the property
  three-way merge cannot have: a conflict resolved by hand in git is a commit
  that appears to have written both sides.

- **A rename is not a question here.** 0008 hangs paths off file identifiers,
  so a file is one file for its whole life and its attribution reaches back
  through every path it has had. `--follow` is not an option because there is
  nothing to follow.

- **The column is the change ID.** 0001 makes the change the name that
  survives amendment and rebase, and the revision digest the name of one
  version of it. A person reading `blame` wants to ask `show` about what they
  find, and the change is the spelling that still resolves after the work has
  been revised.

- **With no target it is the folder, and an unrecorded line says so.** The
  right side of `diff` with no target is the folder, and this matches it. The
  lines history holds keep their author; the lines only the folder has are
  marked `(the folder)` and attributed to nobody, because attributing them
  would be attributing work that has not been recorded. Which lines those are
  comes from `crate::diff`'s decomposition — the one `record` would write and
  the one `diff` prints — so the two commands cannot disagree about what the
  folder has changed.

- **A file of bytes is refused.** 0017 gives it no lines, and there is nothing
  to attribute line by line.

- **A forgotten line still has an author.** 0014 destroys text and preserves
  shape, and the author of a line is shape: the row prints `\ forgotten` where
  the text was, beside the change that wrote it. A redaction is not an
  unpersoning.

## What is not here

**Colour**, deferred with 0037's, and for the same reason: it would be the
first output here to need a TTY check.

**Reverse blame** — "which revision deleted this line" — which is a real
question and a different command. `merge::quotes` already knows the answer,
because `forget` needs it, so this is unbuilt rather than undecided.

**Attributing a line to a person rather than to a revision.** The author
column is the name the revision recorded, and two spellings of one person are
two people here. Identity is 0005's, and it declines to be a directory.

## Consequences

- `cli::blame` is the new module. `cli::diff::laid` — the operations laid back
  over the parent as ` `, `-` and `+` lines — becomes shared rather than
  private, which is what keeps the folder's attribution and the folder's diff
  one answer.
- `render::abbreviations` and `render::CHANGE_FLOOR` become visible to the
  rest of the front end, so a change ID is abbreviated the same way wherever
  it is printed.
- `tests/blamecmd.rs` holds the claims that distinguish this from a
  resemblance: a line keeps its author through a rename and through a merge
  that did not touch it, and a moved line belongs to whoever moved it because
  that is what the operation document says.
