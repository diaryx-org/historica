# 0009 — The run after a historica command

0008 deferred it by name, and said what it is worth:

> **The run around every historica command**, which is what makes colocation
> worth having and what detection will report through. Its own decision, and
> the next one.

Colocation gave a person one directory in which `git log`, `git blame` and an
editor's gutter are correct, but only as of the last time somebody typed a
`write`. What was missing is the *when*: what makes the projection in `.git/`
current after `historica record` has put something in the store.

Historica's decision 0074 is the trigger this was waiting for. A writing
command run with `--fields` prints `historica-wrote-1` and one pointer per
thing the store now holds or no longer holds, and prints the header with no
lines when it wrote nothing. Its 0053 and 0072 refuse dispatch out of
`historica` into the tools beside it, so nothing here can be made to run *by*
`record`. What can happen is that a wrapper reads the statement. The task
listed three questions for the wrapper to answer, and this answers them.

## The decision

- **The run is `write --wrote <statement>`, a flag rather than a command.**
  What it does is 0007's incremental write, onto a repository this tool
  already keeps, so it is `write`. 0008 refused a new verb for adopting a git
  commit for the same reason: one conversion under one condition does not need
  a second word to explain and a second path to test. The flag changes the
  trigger and the report, not the conversion. `-` is standard input, which is
  the ordinary case:

  ```sh
  historica record -m 'note' --fields | historica-git write --wrote -
  ```

- **The statement is a trigger, not a scope.** Any line at all brings the
  repository up to date with the whole store, through `to_repository`. Writing
  only the revisions named was the tempting reading, and it is wrong in two
  ways. A `name` or `unname` line means refs move, and which refs move is a
  question about every bookmark, not about the line. And git's state would come
  to depend on which commands happened to go through the wrapper, where the
  premise of 0004 is that a commit is a function of the store and nothing else.
  0007 already made the whole write cheap when little changed: a revision the
  repository holds is named by object ID and not sent again.

- **A statement with no lines does nothing, and costs reading standard
  input.** No store is opened, git is not started, and nothing is printed.
  This is what makes the run bearable on every command, and it is the one fact
  in 0074's format that the store cannot tell anybody afterwards. **No
  statement at all is the same.** A command that stopped before printing a
  header wrote nothing, and a usage error is the case; the command's own exit
  status says what went wrong, and the wrapper passes it on.

- **A statement this build does not read is refused whole, and nothing is
  written.** A header other than `historica-wrote-1`, or a line kind outside
  the four, is 0074's rule read from the receiving end: discard the statement
  rather than guess. The refusal says that `write` without `--wrote` brings the
  repository current, since the store is unaffected by the refusal and the
  ordinary write needs no statement. The parser is historica's, under 0053;
  this tool does not hold a second grammar.

- **A `revision` the store does not hold is refused.** The statement is then
  about another store — `historica -C elsewhere record` piped into a run here
  is the case — and bringing *this* repository up to date would be an answer
  to a question nobody asked. It is checked before anything is written. Names
  and `gone` lines are not checked, because a statement naming another store's
  bookmark that this store also has is indistinguishable from one about this
  store, and a check that cannot tell is not worth the read.

- **The run never makes a repository.** It keeps a projection current; making
  one is `colocate`'s, or a `write` somebody typed. A store with no repository
  beside it is refused, and the refusal names `colocate`. A wrapper on a
  machine where a store was never colocated would otherwise `git init` in a
  person's folder the first time they recorded.

- **With no directories, the store is found as historica finds it, and the
  repository is the same directory.** `Store::discover` walks up from where the
  wrapper runs, so `record` in a subdirectory is kept current like `record` at
  the root. Naming `<folder> <repository>` keeps the two-directory arrangement
  current too, for whoever wants that.

- **A ref git moved on its own is said in the same breath, and the run still
  succeeds.** 0008's detection is unchanged: the ref is not followed, and
  every other ref and commit is written. The run exits zero, because the
  historica command succeeded and git is a projection of it; a wrapper that
  failed here would make `record` look as if it had not recorded. What keeps
  the run and the detection from contradicting each other is that they are
  one report. The held-back refs are printed under *git is not where the store
  is*, the run says nothing about git being current, and 0008's rule leaves the
  index alone where HEAD is one of the held-back refs.

- **Held-back refs leave `uncarried` for a list of their own.** `Report`
  gains `held_back`, and a whole `write` prints it under the same heading. A
  ref git moved is not a fact git has no word for; it is a statement that git
  is not yet where the store is, which a person acts on with `import`. Mixed
  into `uncarried` it was a line among notes that are true on every run.

- **The run's report is three lines and no more.** What historica wrote,
  briefly, because `--fields` took the sentences the command would otherwise
  have printed for the person typing it. What git got: commits written, refs
  moved or deleted. And how many notes there are on what git cannot hold, with
  the `write` that lists them. The notes are not repeated: most of them are
  facts about the whole history, true on every run, and a run on every command
  that restated them would bury the one line in it that changes, which is
  whether git kept up. 0001's rule is kept by saying they exist and where.

- **An unborn HEAD is pointed at the branch the write chose.** A store with no
  bookmark, colocated, leaves HEAD on git's own default branch, which nobody
  has made. When a bookmark is named later and the run writes its branch, HEAD
  still names the unborn one, and `git status` reads every file as untracked
  although the branch is there. Where HEAD's branch does not exist before the
  write and was not written by it, the run points HEAD at the branch a first
  write would have chosen. An unborn HEAD holds nothing of anybody's, so this
  takes nothing from anybody, and without it the first `record` after naming a
  branch leaves git exactly as wrong as it was before.

## The wrapper

Nothing here can install itself in front of `historica`, so the wrapper is a
person's, and the README gives it for the shells a person has. It is a
function rather than an alias because three rules have to be in it:

- `--fields` goes only on the commands 0074 lists, with `squash` added since,
  because a command outside the list refuses the flag rather than printing an
  empty statement.
- `--dry-run` runs plain, because historica refuses it with `--fields`: a plan
  is not on disk.
- The pipeline fails when `historica` does. In sh, bash and zsh that is
  `set -o pipefail` in a subshell; in nushell, `pipefail` is on by default
  but a pipeline that ends a custom command loses its status, so the function
  ends with `null`.

Each was found by running the wrapper rather than by reading about it.

`historica git write --wrote -` also works, through historica's 0072
spelling, and changes nothing here: it is the same program by another name.

## Rejected alternatives

**Importing git's refs before every command, as jj does.** 0008 refused it
under the stance that historica owns the directory, and nothing here reopens
it. This run is a write *after* the fact.

**A hook in the store.** Historica's 0053 refuses executable hooks, and 0072
refuses dispatch out of `historica`. The pipe is the shape those leave.

**`historica-git run <historica arguments>`, which runs historica itself.**
It would hold the list of writing commands and the `--dry-run` rule in one
place rather than in each shell's function. It would also make `historica`
the binary a second runtime dependency, beside the `git` 0002 names as the
only one, and put historica's argument grammar inside this tool, where it
would be wrong the first time historica changed it. A function in a person's
shell is theirs to correct.

**Writing only what the statement names.** Above: refs are a question about
every bookmark, and git would come to depend on which commands went through
the wrapper.

**Running the write when the store changed, judged by reading it.** That is
the open 0074 exists to avoid, and a store that did not change is
indistinguishable from one nobody wrote to.

**Failing the run when a ref is held back.** The command it follows
succeeded. A non-zero exit would read as a failed `record`, and the person
would record again.

## Consequences

- `export::after` is the run as a library call, taking historica's
  `wrote::Statement`; the binary reads standard input, parses with historica's
  parser, and finds the store.
- `export::Error` gains `Elsewhere` and `Unprojected`.
- `export::Report` gains `held_back`, and a whole `write` prints it under its
  own heading rather than among what did not cross. A library caller that
  looked for a held-back ref in `uncarried` now finds it in `held_back`.
- The dependency moves to historica `1.0.0-rc.8`, since rc.2 cannot read a
  store the current `historica` writes: 0083 put a size on every file of bytes.
- The open task is closed.

## Deferred

- **The folder.** `update` and `merge` write the folder and not the store, so
  they have no statement, and 0074 deferred one. Neither changes the store,
  so neither changes what git should hold. Where `update` brings the folder to
  a head HEAD does not name, `git status` says the folder differs, as it does
  for any edit, and what would move HEAD to follow is its own decision.
- **A wrapper that cannot tell a writing command from a reading one.** The
  list in the function is historica's, copied. A command historica adds that
  takes `--fields` is missing from it until somebody adds it, and the failure
  is the old one: git falls behind until the next run. Historica could say
  which commands take the flag, and the wrapper could ask, if this becomes a
  nuisance.
