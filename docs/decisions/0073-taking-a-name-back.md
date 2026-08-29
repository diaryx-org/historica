# 0073 — Taking a name back

A bookmark is written by `Store::set_bookmark`, which 0071 calls *the one door
into `names/`*, and moved by `Store::set_name`, and stated at the command line
by `name`. There is no other direction. `Store::remove_name` exists and is
`pub(super)`, written for 0062's withdrawal — a published copy states the names
the origin shares, so a bookmark the origin deleted leaves the copy on the next
`export` — and a caller who is not that export cannot reach it.

So the only way to delete a bookmark is `rm history/names/main.txt`, and the
awkward part is that it works. A bookmark is a file, the loader reads the
directory, and a store missing one file is a store with one fewer bookmark. It
works in the way that makes a thing worth building a command for rather than in
the way that makes one unnecessary: the person gets no statement of what the
name pointed at, an open `Store` in the same process keeps the entry in its
map, 0071's empty `names/feature/` is left behind, and a path assembled by hand
is the one operation in this design where a mistake is spelled as a path
outside the store.

The asymmetry is the whole argument. Every other mutable thing here has both
directions — `record` and `abandon`, `skip` and the file a person deletes,
`export` adding a name and `export` withdrawing one. Bookmarks have the ingress
and not the egress, and no decision ever said they should.

## The decision

**`Store::remove_name` is public.** The same function, the same contract, one
fewer restriction. It takes the name, deletes the file, drops the entry, and
tidies 0071's directories upward to `names/`.

**One removal for both of 0062's axes.** There is no `remove_bookmark` beside
it, because the axis is a fact about a file that is going: `private` says what
an `export` does with a name, and a name that is not there is carried by
nothing. 0062's pairing of `set_name` with `set_bookmark` exists because a move
must not silently un-privatise; a deletion has no target to move and no axis to
preserve.

**A name already gone is not an error, and the return says which happened.**
`Ok(false)` is *there was no file*, which is what 0052's export needs — the
plan naming it was worked out from a listing rather than held under a lock —
and what any caller reconciling against a store somebody else is also writing
needs. `remove_skipped` answers the same way for the same reason.

**The command is `name --delete <bookmark>`, and not a word of its own.**
Deleting a bookmark is something done to a bookmark, and `name` is where a
person says what one is. A top-level `unname` would spend a word in the command
table on the smaller half of one verb's job, and the table is the first thing a
person reads. One bookmark per invocation: a deletion is deliberate, and a
command that took a list would take a typo along with the name that was meant.

**`--delete` refuses the flags that shape a target.** `--revision`, `--change`,
`--private` and `--shared` all say something about where a bookmark points or
who may see its name, and a bookmark that is going has nowhere to point and
nobody to be seen by. Stating one alongside `--delete` is a person who means
two different things, and the refusal names the flag they typed.

**A bookmark that is not there is an error at the command line.** The library
answers `false` and the command fails, and the difference is who is asking:
`Store::remove_name` is called by an export working from a plan, and `name
--delete` is typed by somebody who believes the name exists. A silent success
over a misspelling is how a person concludes they deleted a bookmark they still
have.

**What it prints is what the name pointed at.** `deleted feature/x, which was
change nwlxsqot… (private)` — because a deletion nobody meant is undone by
typing the bookmark back, and this is the line that says how.

## A deletion is local, and says so

`receive` takes every name the source states and the receiver lacks (0029,
0062). So a name deleted here comes straight back from the first replica that
still holds it, and the command says as much, in the shape 0062 already gives
`name --shared`: *a replica that still holds `feature/x` will bring it back on
the next receive.*

That is not a defect to be fixed by making deletion propagate. 0054 settled the
general form:

> Withdrawal is a merge rule: it says a name present here and absent there
> means *deleted* rather than *not yet arrived*, and that is a claim about a
> grammar historica has promised not to learn.

For `names/` the claim would have to be a tombstone — a file recording that a
name is gone, mutable, unioned, and permanent, in the one directory 0006 calls
*the entire conflict surface* of a store. It would also be the exact shape of
0062's deferred un-privatising problem, arriving in a place where the safe
direction is not obvious: a bookmark restored by a replica costs a person a
second `--delete`, where a bookmark deleted everywhere by a stale tombstone
costs them the label on work they may not be able to name again.

So deletion joins `prune` and `forget`'s local half: it is this store's, it
propagates through nothing, and the person who wants it everywhere says it
everywhere. What would justify a better answer is somebody doing it often
enough to be maintaining the difference by hand, which is 0051 and 0062's test
and not yet met.

## What a deletion does not take

Nothing recorded. The revisions the bookmark pointed at are where they were and
are reached by change ID or digest as they always were; `log` still lists them;
`prune` takes only a revision *superseded* by one this store keeps, and 0013 is
explicit that a head no bookmark names is *work whose author has not given it a
name, not garbage*. There is no path from deleting a label to collecting the
work under it, which is what makes this command cheap enough to have.

That is worth stating because git's `branch -d` guards against exactly the
opposite arrangement, where an unreferenced commit is a candidate for garbage
collection and a deleted branch can be the last reference. Historica's prune
rule was decided in 0013 without this command in mind, and it is what lets this
command skip the merged-ness check, the `-D` escalation, and the reflog that
exists to undo it.

`forget` is the other thing this is not: it destroys recorded content, and a
person deleting a bookmark to make work disappear has asked the wrong tool —
0062 says the same sentence about `private`.

## Rejected alternatives

**A compare-and-delete taking the `Bookmark` it expects.** It reads as
carefulness and buys nothing here: a bookmark file is one line, and a person
deleting `main` means `main`, not *`main` if it still points where I last
looked*. A caller who does want that reads `Store::bookmark` first, and holds
the same store the write goes through.

**Deleting many at once, or a subtree.** 0071 made `feature/x` a name, which
makes `name --delete feature/` a thing somebody will eventually type. It is
deferred rather than refused: a prefix deletion is the first operation here
whose blast radius depends on what the store holds rather than on what was
typed, and it wants a listing and a confirmation that no other command in this
tool currently has.

**An `unname` command.** Above: a word in the table for half of one verb.

**Leaving it to `rm`.** What the section above describes, and the state this
decision found: it works, it is undocumented, and it is the only operation in
the design whose spelling is a path.

## Consequences

- `Store::remove_name` is public, so the implementing commit carries a
  `Behavioural-change:` trailer — nothing existing behaves differently, and a
  method that was not callable now is.
- `name --delete <bookmark>` refuses `--revision`, `--change`, `--private`,
  `--shared`, a second bookmark, and a name the store does not hold; it prints
  what the bookmark pointed at, including 0062's axis, and the note that a
  replica will bring the name back.
- The usage text gains the form, and `docs/cli.md`'s `names` and `name` section
  gains the paragraph. `export`, `receive`, `offer`, `fetch` and `check` are
  untouched: this adds a caller to a function they already used.
