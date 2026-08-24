# 0037 — What changed

Every command that reads a store prints what the store holds. `show` prints a
document byte for byte, `cat` prints a file byte for byte, and 0003's rule is
why:

> The readable files are the authority.

What was missing is the question people actually ask most often, which is not
"what does this file say" but "what changed". `status` counted it — *edited 1*
— and `show` printed the operation document, which is a diff in the format's
own words and is unreadable to everything else. There was no way to see a
change.

## The decision

- **`diff` is a rendering, and says so.** Nothing here is stored, nothing reads
  it back, and `show` remains the command that prints the authority. That
  separation is the reason this can safely borrow a shape from elsewhere.

- **The shape is the unified diff.** Not because it is good — it is a format
  from 1990 with an off-by-one in its own header convention — but because
  `git apply`, every editor, every review tool and every person who has used
  version control already reads it. Inventing a better one would be asking the
  world to learn a format in order to read a project whose entire premise is
  that you should not have to.

- **`diff [<target>] [<path>] [--onto <target>]`**, with `--onto` naming the
  left side exactly as it does in `status` and `record`. With no target the
  right side is the folder; with one it is that revision, and the left side
  defaults to its parent — so `diff <target>` is "what that revision did",
  which is the question `log` leaves a person holding.

- **One argument is a target or a path, decided by 0001's disjoint alphabets.**
  A change ID is `k`–`z` and a digest is `0`–`9`, `a`–`f`, so `diff notes.md`
  is a path because nothing else could name it and `diff kxry` is a target
  because nothing else could — whether or not this store holds one. That is the
  alphabets doing the job they were chosen for rather than a guess between two
  readings, and `path:` is still there for the file whose name is spelled like
  a change.

- **A rename between two revisions is stated. A rename in the folder is not.**
  This is the decision that makes this command different from every other
  tool's, and it falls straight out of 0008: files carry identifiers and paths
  hang off them. So a revision-to-revision comparison pairs files *by
  identifier* — one file that moved and was edited in the same revision is one
  row, with `rename from`/`rename to` above its hunks, read rather than
  guessed. Every other system recovers this with a similarity heuristic and
  gets it wrong when a rename comes with a large edit; here there is nothing
  to recover.

  The folder is the opposite case and gets the opposite treatment. 0011 makes
  stating a rename the one thing a person has to do, because the folder holds
  paths and no identifiers. So a moved file there is a `deleted file` and a
  `new file`, exactly as `status` reports it. Rendering it as a rename would
  be inventing a fact that `record` would then decline to write down, and the
  two commands disagreeing about what happened is worse than the folder being
  honest about what it cannot see.

- **The hunks are `crate::diff`'s decomposition, not a second one.** What is
  shown and what `record` would state are one answer computed once. A tool
  whose preview disagreed with its commit would be a tool nobody could trust
  twice, and 0009 already made that decomposition the considered one.

- **A file of bytes says `binary files differ`.** 0017 gives it no lines, and a
  photograph written between two `@@` markers is a mess rather than an answer.

- **A merge is refused, naming the sides.** What a merge *did* depends on which
  parent you are asking about, and 0012's whole position is that a tool does
  not choose between two lines of work on a person's behalf. The refusal
  prints the two commands that would work, as every other refusal here does.

## What is not here

**Colour.** Every other command prints plain text, and this would be the first
to need a TTY check and a `--color` flag. It is the one output where colour
genuinely helps, so this is deferred rather than declined.

**A word-level or intra-line diff.** `similar` would do it, and it would be a
second decomposition beside the recorded one — which is exactly what the
"one answer computed once" rule above rules out. If it is ever wanted, it is a
rendering *of* the recorded operations rather than a fresh comparison.

**`diff` as a patch format anything reads back.** The output is a rendering.
Nothing in Historica parses it, and a future that wanted an exchange format
would want 0007's operation documents, which are already exact, already
readable, and already what the store holds.

## Consequences

- `cli::diff` is the new module, and `target::could_be_target` is the alphabet
  question 0001 implied and nothing had needed to ask out loud before.
- The folder comparison reports a mode difference (0034) as its own line
  naming the file, because a mode can be the whole of what changed and two
  bare `mode` lines between two other files' hunks would belong to neither.
- `tests/diffcmd.rs` holds the pair of tests that matter: a rename between two
  revisions is stated, and a rename in the folder is a drop and an add.
