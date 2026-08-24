# 0044 — What this copy has held

0022 fixed the bug it found and wrote down, plainly, the part it could not
fix:

> **The store still cannot be repaired.** The bytes are gone; no other copy
> exists; the revision names a digest nothing holds. `check` calls a missing
> payload a note, on the reasoning that transport has more to deliver — true
> when a payload is missing because a replica has not sent it yet, and false
> when it is missing because something overwrote it. Telling those apart needs
> a fact this format does not record.

0027 closed the question by keeping it a note and rewording it to name both
states. That was the right answer to the question as asked. The reasoning is
about *absence*, and absence genuinely cannot distinguish the two: a digest
this store does not hold looks the same whether it is still in flight or was
destroyed on Tuesday.

But the store is not the only thing in the room. The question is not what
absence can prove — it is whether anybody here saw the bytes before they went,
and this copy was present for its own history. A payload that `record` filed,
or that `receive` accepted, was held by this machine at a moment this machine
can remember. That is not a fact about the format, which is why the format
does not record it and should not. It is a fact about a copy, and `cache/` is
where facts about a copy live.

## The decision

- **A witness record at `history/cache/witnessed.txt`.** One digest per line,
  each a payload or operation document this copy has held. It carries the
  header `historica-witness-1`, for 0036's reason: a fixed name has no digest
  to check it against, so a file written by a version spelling it differently
  is discarded whole rather than half-understood.

- **It is written where the bytes passed through.** `record` witnesses what it
  filed, `receive` what it accepted, `check` what its walk found. Those are
  the three moments this copy demonstrably had the content, and none of them
  is a new read: each already knows the digest it is handling.

- **It changes a severity and never anything else.** Where `check` has already
  decided to report an absence, a witnessed digest makes that finding an error
  instead of a note — *this store held it and does not now* — and an
  unwitnessed one leaves the note exactly as 0027 worded it, because that
  wording describes exactly the state it is left describing. The witness never
  adds a finding, never removes one, and never reaches a finding `check` was
  not already going to make.

- **An absence the store accounts for is not one of those findings.** A
  forgetting document produces `Forgotten` and not `MissingPayload`, so the
  witness never reaches it. This is not an exception carved out for 0014; it
  falls out of the rule above. A copy that forgot something did hold those
  bytes — holding them is what let it destroy them — and if the witness were
  consulted one branch earlier it would call every honoured redaction a fault.

- **It is never believed about content.** 0035 removed invalidation as a
  question by hashing bytes before using them. A witness cannot be checked
  that way, because the bytes it speaks for are the ones that are gone. What
  makes that safe is not a proof but a ceiling: the only thing a witness can
  produce is a severity. A file an old version wrote, a person edited, or a
  disk half-flushed can raise a note that should have stayed a note, or fail
  to raise one that should have risen, and can do nothing else. No byte
  anybody reads depends on it.

- **It is a cache, with everything 0003 promises of one.** Deleting it loses
  no information — every error it raised falls back to the note that error
  already was, and `check --complete` is unmoved, since completeness was never
  about severity. What deleting it costs is the sharpening, until the next
  `check` walks the store and witnesses what is still there.

- **It does not travel.** `export` writes `cache/` for nobody (0042) and
  `receive` does not merge one. A replica that never held a payload has no
  business inheriting the claim that it did, and a witness file that crossed
  machines would say "destroyed here" about bytes that were only ever
  somewhere else.

## Why this is the fact that was missing

The failure 0022 describes leaves evidence, and the store already prints it.
0036 keys the catalogue by the digest of a file's own bytes, so a payload
overwritten in place does two things at once: it leaves the index under the
digest the revision names, and it enters the index under the intruder's. The
report that comes out says `MissingPayload` in one place and `UnnamedPayload`
in another, and nothing joins them, so a person reading a store mid-sync sees
two ordinary notes among many.

The witness is the join. It does not find anything the walk did not already
find; it supplies the one bit that decides which of two readings of the same
absence is the true one, and the reading it produces is the one a person can
act on. Twelve notes on a syncing store are not actionable and are not
supposed to be. One error saying this copy held a digest it can no longer
produce is a thing to go and do something about, and it is exactly the signal
a host application wants after a sync cycle — the thing 0022's postscript
said was needed and could not be built at the time.

## The list 0022 said would need adding to

0022 shipped five names and a prefix and predicted the list would rot. Adding
to it wants a criterion, or it grows by anecdote, and the incident supplies
one: **the names that matter are the ones a program writes into every
directory it touches, unprompted.** That is what made `.DS_Store` lethal and
it is what the five names and `._` have in common. It is also what most
plausible additions do not have.

`@eaDir` has it. A Synology NAS creates one inside every directory holding
indexed files, without being asked, which is Finder's behaviour under another
name. **It joins the list.**

The near misses are worth recording so the next person does not have to
re-derive them. Syncthing's `.stfolder` and `.stversions` are written once at
a sync root, not into every directory, so a payload collides with one only if
the sync root is an operation directory. `.Spotlight-V100`, `.Trashes` and
`$RECYCLE.BIN` are volume-root names with the same property. Word's `~$` and
LibreOffice's `.~lock.` land beside the document being opened, so they reach a
payload only when somebody opens a payload in that editor — a real risk, and a
smaller one than a program that writes unbidden. Random-suffix temporaries
like `.goutputstream-XXXXXX` are worth nothing on a blocklist at all, since
the name never repeats and no payload can be filed under one twice.

**The list is not gated by the platform it is running on**, and this is worth
saying out loud because gating it looks like tidiness. Three reasons it is
not:

- `naming` consults the list to decide what a payload is *filed* as. A gate
  would make the filing scheme a function of the machine, so one store
  recorded on Linux and on macOS would put one payload at two paths, and two
  replicas would disagree about a filename that 0019's collision rule assumes
  is a function of the store's contents.
- Stores travel, which is the premise of 0029 and 0042 entirely. A store
  recorded on Linux meets `@eaDir` when it is synced to the NAS, and the
  recording machine cannot know what folders a copy will pass through.
- The list is already cross-platform and unconditional. `Thumbs.db` and
  `desktop.ini` are Windows names carried on every macOS store today, and
  `.directory` is KDE's. `@eaDir` would be the one exception, for no reason
  the others do not share.

## What it costs

**A fact that cannot be verified, in a project that verifies everything.**
Every other file in the store is named by a digest of its own bytes, or is
checked against one, and this one is taken on trust. The ceiling above is what
makes it tolerable rather than a hole, and the ceiling is a real constraint on
where the witness may be consulted, not a description of where it currently
is: the moment anything reads a witness to decide what bytes are, this
document has been broken.

**A note that becomes an error may still be wrong about why.** A witnessed
payload can go missing because somebody deleted `history/` and restored an
older backup over it, or because a sync tool resolved a conflict by discarding
a file. The error says the store held it and no longer does, which is true in
every one of those cases and is the most a witness can say. It does not say
who.

**One more file that is written on the ordinary path.** `record` and `receive`
gain an append, and `check` gains a write at the end of a walk it was already
paying for. The append is small and unordered, so it costs a line per new
digest and no read.

## Rejected alternatives

**Recording it in the format.** A `held` header, or a manifest that travels.
This would make the fact durable and shared, and it would be wrong twice: it
is not true of the history, only of one copy of it, so it would either be
false on arrival or would have to be stripped on every send — and it would put
into the corpus a thing no reader materialising a file ever consults. 0003's
division holds. Facts about a copy are the copy's.

**Making a missing payload an error unconditionally.** The thing 0022
considered and 0027 refused. Every store between syncs would fail `check`,
which is the state a distributed history spends most of its life in, and an
error everybody learns to ignore is a note with worse manners.

**A timestamp per witness, so the error could say when.** More to store, more
to be wrong about, and 0043 has already been through what a modification time
is worth as evidence. The question the witness answers is a yes or no, and the
line that answers it should be a digest and nothing else.

**Hashing the witness file, so it could be checked.** A digest of a file that
is appended to on every command is a digest rewritten on every command, and
what it would protect is a file whose worst failure is a misfiled severity.
The header version is the right amount of scepticism for this file.

## Consequences

- `store` gains `witness`: a module that reads, appends to, and parses
  `cache/witnessed.txt`, on the pattern `store/catalogue.rs` and
  `working/catalogue.rs` already share.
- `Finding::severity` stops being a function of the finding alone.
  `MissingPayload` and `MissingOperations` become `Severity::Error` when the
  digest is witnessed, which means severity is asked with the witness in hand
  and `Report` carries the answer rather than recomputing it.
- The `Display` for both findings gains the second wording. A witnessed
  absence should not say "may not have arrived yet", since that is the reading
  the witness has just ruled out.
- `record`, `receive`, and `check` each witness. `check` does it last, so a
  walk that fails part way through has witnessed nothing rather than half of
  the store.
- `arrange` and `prune` do not witness. Neither introduces content, and a
  rename is not a sighting of anything new.
- `PLATFORM_NAMES` is six names, and its comment gains the criterion above so
  the next addition has a test to meet.
- `export` and `receive` are unchanged, which is the point: both already
  exclude `cache/`, and a decision that needed to edit them would be a
  decision that had put the fact in the wrong place.
- The corpus is unchanged. No document's bytes move, no name a reader parses
  changes, and a store written before today reads identically — it simply has
  witnessed nothing yet, which is the state the fallback is written for.

## Deferred

**Forgetting a file of bytes.** 0014 defers it, so `check`'s `bytes` branch
does not consult the forgetting index the way its `text` branch does, and it
does not need to. When whole-payload forgetting lands, that branch gains the
standing check its neighbour has, and the witness rule inherits the right
behaviour without being touched — because the rule is stated over the findings
`check` makes, not over the absences it sees. This is recorded here so that
the interaction is a thing somebody already thought about rather than a thing
somebody discovers.

**A witness for the folder.** The working copy has the same exposure and a
better answer available, since an unrecorded file that vanishes was never in
the store to begin with. 0043 has already named `check --folder` as where a
question about the folder's bytes would go.

**Saying who.** An error that named the writer that overwrote a payload would
be worth a great deal more than one that does not, and nothing in a folder of
files can know it. It would want the platform's own audit facilities, which
are not portable and are not this project's to wrap.
