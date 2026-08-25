# 0055 — The folder an export wrote

0052 said the folder half of an incremental export was already built:

> The folder is `update`'s work, as it always was. `export_onto` already ends
> in `update::plan` and `update::apply`, and a non-empty folder catching up to
> a target is precisely 0030. Nothing here is new; the call site simply stops
> being able to assume the folder was empty.

That is true of every export that only adds, and false of every export that
withdraws — which is to say, false of exactly the runs 0052 exists for.

0030 will not write over a file whose bytes no revision records, and it asks
the question of the store as it stands. An incremental export changes the
store as it stands: a `forget` destroys the document the copy's folder was
materialised from, a `prune` and a moved target withdraw the revisions that
recorded it. So by the time `update::plan` is called, the bytes in the copy's
folder are unrecorded — and they are unrecorded *because this run destroyed
the record*. 0030 then reports them as "work nothing has recorded" and
refuses, which is a true sentence about a store and a false one about a
folder nobody has ever worked in.

The failure is not a refusal in the abstract. The store half has already
happened by then, so the copy ends with the new history and the old folder,
and the one command that would repair it refuses for the same reason. A
redaction that destroys the bytes in `history/` and leaves them in the file
beside it is 0014's promise broken in the place a `wget -r` reads first.

## The decision

- **An export replaces the folder it wrote, and refuses a folder somebody
  changed.** Where the destination's folder still holds exactly what the
  copy's own history last put there, every path in it is this export's own
  output and may be written over or removed without being asked about. Where
  it differs anywhere — an edited file, a mode set by hand, a stray at a
  tracked path — 0030's rule applies unchanged and the export refuses.

- **The question is asked before the run takes anything away.** That is the
  whole of the fix and the whole of the subtlety: "has anybody touched this
  folder" has an answer at the start of the run and no answer at the end,
  because the run is what removes the evidence. So it is settled against the
  copy as it arrives, and acted on afterwards.

- **It is asked only where something is being withdrawn or destroyed.** An
  addition-only publish leaves every record in place, so 0030 answers
  correctly on its own and there is nothing to ask. This costs one extra pass
  over the folder on the runs that were already paying for a pass over the
  copy, and nothing at all on the ordinary ones.

- **Nothing is waived for a destination that is not a copy this store made.**
  Every refusal 0052 states comes first — not a store, broken, unrelated,
  recorded in — so the folder question is only ever asked of a directory that
  has already been established as this store's own published copy.

## Why not simply trust the destination

The tempting shorter rule is that an export owns its destination outright, so
the folder is always replaceable. It is wrong for a reason 0042 makes plain: an
export *is* a repository, and a person may open the copy and work in it. The
existing tests do exactly that — a copy is `receive`d into and `update`d — and
`historica export ../journal` typed at a directory somebody has been editing
should not silently discard their afternoon. 0030's rule is the one that knows
the difference, and this decision keeps it for every case where it can still
tell.

The `undisturbed` check is the narrowest thing that distinguishes the two: it
is 0030's own plan, run against the copy's own head, and it says *settled* only
where the folder is byte-for-byte what the last export left. A person who has
touched anything gets the refusal they should get.

## Rejected alternatives

**Materialise the folder before the store changes.** The obvious ordering, and
it cannot work in either direction. Before the additions, the target's own
content may not be in the copy yet. After the additions but before complying
with forgetting, the copy holds the original *and* the stand-in at once —
which is the state `check` calls `Resurrected`, and materialising from it
would write the forgotten text into the folder and then destroy only the
store's copy of it. The exact failure this decision exists to prevent, arrived
at by trying to avoid it.

**Empty the folder and lay it out fresh.** `update::plan_into` already refuses
a non-empty directory, so the export would delete everything and rewrite it.
Correct, and it renames nothing but rewrites every byte on every publish —
which is the whole-store cost 0052 refused, and it breaks a fetch in flight
for files that never changed.

**Let the refusal stand and tell the publisher to delete the copy.** It makes
the answer to a `forget` "rebuild the published copy from scratch", which is
the operation 0052 exists to avoid, and it leaves the copy in the broken
intermediate state until they do.

**Do the folder half first and the store half after.** It moves the problem
rather than solving it: `update::plan` requires the target to be a current
head, and a target moving back to an ancestor is not one until the revisions
above it are withdrawn.

## Consequences

- `update` gains `Overwrite`, an internal two-valued question the planner
  already had implicitly, and `undisturbed`, which is 0030's plan run for its
  answer rather than for its writes. Both are `pub(crate)`: this is a rule
  about what one caller may do to a folder it owns, not a mode a person can
  ask for.
- `update::plan_at` is reachable inside the crate. Its head check is not
  waived — the export pays it at the end of the run instead, because the
  revisions that outrank the target are withdrawn by the same run — and
  nothing writes a position anywhere, which is the property 0030 was
  protecting.
- A published copy somebody has edited refuses to update, and says so in
  0030's words. That is the right answer and it is worth knowing that
  `historica status` in the copy is what explains it.
