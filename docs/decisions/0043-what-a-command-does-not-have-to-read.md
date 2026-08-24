# 0043 — What a command does not have to read

0036 removed the cost of *finding* a digest and left the cost of *taking* one
standing. Two of them, in fact, and this is both.

The first is the folder. `status` compares what the folder holds with what the
position records, and identity comes from content, so the comparison is a
comparison of bytes — which the recorder performed by reading every tracked
file, every time. A journal is cheap that way. A folder with a fifty-megabyte
photograph in it is not: three tenths of a second to be told nothing has
changed, on every command, for as long as the file exists, and proportionally
more for a folder full of pictures. Nothing about that cost is paid for
anything. The photograph has not moved since the last time it was hashed, and
the directory has been able to say so all along.

The second is the store. 0017 admitted it in one sentence:

> the implementation reads a payload whole to hash it and whole to write it.

A great many questions in this crate are *which digest is this file* — which
path holds a payload, whether a document is one `prune` may delete, whether a
payload is one `forget` destroys, what to call a file `arrange` is filing.
None of those wants the file. Every one of them read it whole, so that a
store of photographs held one photograph in memory per file examined and
threw it away again.

Both halves are the same shape, which is why they are one document: **a
command should not read what it does not need**, and both fixes are a
capability the filesystem may decline.

## The decision

- **A catalogue of the working folder lives at
  `history/cache/working.txt`.** One line per tracked path — the digest of
  that file's bytes, and the size and modification time the directory reported
  when those bytes were hashed. `<digest> <size> <modified> <path>`, the path
  last because a path is the one field that may hold a space, and the time as
  a whole number of nanoseconds either side of the Unix epoch. It carries the
  header `historica-working-1`, for 0036's reason: a fixed name has no digest
  to check it against, so a catalogue written by a version spelling it
  differently is discarded whole rather than half-understood.

- **It is believed per entry, on one condition: the directory still reports
  the size and the modification time the entry records.** 0036's catalogue is
  believed as a whole, because its question is *what does this directory
  hold*. This one's question is about each file separately, so a folder
  somebody has been working in comes back missing exactly the files they
  touched and keeps the rest. Everything it does not account for — a new path,
  a size that moved, a time that moved, a file it names that is gone — is read
  and hashed, exactly as before this existed.

- **An entry whose time is not strictly older than the catalogue's own write
  time is unverifiable, and its file is read.** This is the racy-mtime rule,
  and the next section is why it is here.

- **A lookup hashes what it reads before believing it.** 0036's rule, one
  level up. The catalogue says what a file hashed to and never what it holds
  now: a comparison that says *this differs* is followed by the read it was
  avoiding, and what that read finds is what the folder holds — so the answer
  comes from the file whatever the catalogue said, and the entry is corrected
  by the read it caused rather than costing that read on every command
  afterwards.

- **`Filesystem::stamp` is how a size and a time are asked for, and `None` is
  the load-bearing answer.** Decision 0025 kept metadata out of this trait and
  gave a good reason:

  > Identity comes from content (0003), so nothing here has ever asked a file
  > how big or how old it is, and a trait that offered it would invite a
  > future reader to depend on something two replicas can disagree about.

  The reason still holds and this does not break it, because **nothing here is
  ever an answer**. A stamp never says what a file holds; it only ever says
  whether an answer already worked out may be taken again. So the method is
  defaulted to `None` — 0034's shape, doing 0034's work — and a host whose
  folder is an iCloud document provider, a Swift object, or a `BTreeMap` takes
  the default, never writes a catalogue, and reads the folder on every command
  as it always did. It gets the same answers in the same words.

- **`Filesystem::read_in_pieces` is the same bargain for reading.** It hands a
  file's bytes to a reader in whatever runs it finds convenient, and `Ok(None)`
  is reserved for *this filesystem hands a file over whole* — in which case the
  caller falls back to `read`. `fs::digest_of` is the one function that uses
  it, over `format::Hasher`, so a caller that wanted a digest holds a buffer
  rather than a file. `Disk` reads in sixty-four-kilobyte pieces; nothing
  depends on the number, because the digest of a file is the digest of a file
  however it arrived.

- **The comparison happens at the digest, not at the bytes.** This is what
  makes the catalogue worth having. 0017's `bytes <file> <digest>` already
  *states* what a whole file holds, and 0031 makes every content document state
  the digest of the file it produces, so both sides of "has this changed" were
  already digests waiting to be compared. `record::survey` now asks
  `Working::digest` first and reads the file only when the two differ.

- **The catalogue is written once, where the folder has finished being
  asked.** A survey that rewrote it after every file would be quadratic in the
  size of the folder, which is 0036's argument about writers unchanged. What
  that costs is that a folder is described using the digests the *previous*
  command wrote down.

- **A folder that learned nothing writes nothing.** Two `status` runs in a row
  leave `cache/` byte for byte as the first one left it.

- **Every failure to read or write it is ignored.** 0035's rule, unchanged. A
  read-only folder, a full disk, and a `cache/` somebody deleted mid-command
  are all conditions under which describing a folder must still succeed.

## The racy-mtime rule

A modification time is not a version number. Every filesystem has a
granularity, and two writes inside one tick of it produce one time. So this is
possible: a file is hashed and catalogued under time *T*; before the clock
leaves *T*, a person's editor writes it again, to the same length; the
catalogue now records *T* and a digest of bytes that are no longer there, and
the directory will go on reporting *T* forever.

Git has had this exact problem since it had an index, and calls such an entry
*racily clean*. Its answer is a comparison against the index file's own
timestamp, and this takes it:

> An entry whose recorded time is not strictly older than the catalogue's own
> write time is unverifiable. Its file is read and hashed.

The catalogue's write time is the modification time of `working.txt` itself,
which is the one clock reading that comes from the same place every entry's
does — no clock is consulted, and nothing here would be allowed to consult one,
since 0010 makes a clock a thing a *writer* supplies and 0041 refuses to let a
name come from one.

What that leaves is the case where the second write also lands in the same tick
as the catalogue's own — and the command after that believes nothing about the
file either, because the entry is no longer strictly older than a catalogue
that has since been rewritten. Narrowing it further would need a clock the
folder does not have.

## Deleting it changes how long a command takes and nothing else

That is 0003's promise and it is the claim the tests are written against.
Delete `working.txt`, truncate it, hand it a header from another version, or
replace every digest in it with a digest of somebody else's bytes: every
command says exactly what it said before, having read the folder, which is
what it would have done anyway. `tests/cache.rs` does each of those and
compares the output; `tests/filesystem.rs` counts the reads, so *the file was
not opened again* is an assertion rather than a stopwatch, and drives the same
history over a filesystem that reports no stamp at all to show that the answers
do not move.

There is one thing believed unread, and 0036 has one too, so it is worth
stating in the same place rather than burying:

**A path the directory reports at the same size and the same time is taken to
hold the bytes it held.** Every check above is a check that this remains true —
the size, the time, the racy rule, and the hash of whatever any read of the
file turns up. What none of them can catch is a catalogue *forged* to be
internally consistent: an entry that names a digest the file does not have,
under a size and a time the file does have, and that happens to be exactly the
digest the store already records for that path. Only a person constructing that
file by hand produces it.

What it costs if it happens is bounded, and this is the difference from 0036's
exception. There, a wrong catalogue could make a reader treat an ordinary
document as a redaction, which is a claim about a *history*. Here the worst
case is that one command describes an edit as absent. The edit is still in the
folder, byte for byte; nothing has been recorded and nothing has been
destroyed; the next write to the file moves the time and ends it; and
`rm history/cache/working.txt` is a complete fix that loses nothing, because
there was never anything in it.

## What this is not

**Not an index.** 0011 refuses one and 0039 says why: an index holds a version
of a file that is in neither the folder nor the history, and records a state
that never existed. Nothing here holds content. Every line is a claim about a
file that is present, in the folder, exactly as the folder has it — and the
claim is checked against the directory before it is used. `record <path>...`
still restricts what is *observed* rather than staging anything, and nothing is
remembered between commands except how to avoid re-reading a file nobody has
written to.

**Not a reason to trust a clock.** Nothing in the format, in a filename, in a
merge, or in a comparison of revisions has gained a dependency on a
modification time. The one use is *may this digest be taken again*, and the
answer `no` is always available and always correct.

**Not `check`'s.** 0035 and 0036 keep that command away from every cached
answer, because it is the one caller that wants the work rather than the
result. `check` reads the store and has never read the folder, so there is
nothing here for it to decline — but the rule stands for the same reason, and
the store-side streaming below does not change what `check` reads or compares.

## Where a payload is no longer held

The streaming half touches every place a file was read whole purely to learn
which digest it is:

- `store::catalogue` reads a payload's digest without the payload. This is the
  one that matters most, because it is on the path of every command: a history
  with photographs in it catalogues `operations/` without loading one. A
  document is still read whole, because the catalogue has to parse it to learn
  what it forgets.
- `Store::scan_for_payload` is a search, and every file it examines but one is
  put down again. Only the file that answers is read.
- `prune` hashes three directories to decide what may go, and keeps none of it.
- `forget` finds the files whose bytes are a destroyed digest, and does not
  hold the bytes it is about to destroy in order to decide to destroy them.
- `receive` complies with a forgetting document by the same search.
- `arrange` asks each file what it is in order to decide what to call it.

`check` is deliberately not on the list. It compares the bytes of two files
claiming one digest and holds a text payload to UTF-8, so the bytes are what it
wants; it is also the command whose whole job is the work.

## What this costs

**A `stat` per tracked file on the walk.** The working walk already listed the
directory and asked each entry what kind it was; it now also asks for a size
and a time. That is what every other tool that keeps an index pays, and it is
paid in exchange for not opening the file.

**A file in `cache/` that grows with the folder.** One line per tracked path,
parsed on every command. 0036 deferred the same question about `operations.txt`
and the same answer applies: when the parse becomes the cost that the reads used
to be, the form that fixes it is one that can be read without parsing all of it,
which is a binary index, and 0003 permits one so long as deleting it loses
nothing.

**Two more methods on `Filesystem`.** 0025 counted nine and meant it, and this
is the second decision to add to that count — 0034 and 0040 were the first,
and all four are the same kind of method: defaulted, declinable, and incapable
of changing an answer. What keeps the count honest is that the nine are what an
implementation *must* provide, and that number has not moved.

**A survey that reads the folder in a different order.** The mode is now asked
for before the content rather than after, and a file the tree holds is settled
by digest before it is opened. Nothing observable changed, but the sequence of
calls a host's filesystem sees did.

## Rejected alternatives

**Validating the catalogue as a whole, the way 0036 does.** 0036 believes its
catalogue only when the set of paths it names is the set the directory holds,
which is right there because *its* question is about the directory. Applied
here it would throw away every entry the moment a person saved one file, which
is the state a working folder is in most of the time — and the folder is
exactly where the expensive files are.

**Putting the size and the time in the format.** A revision could state the
size of the file it recorded. It must not: 0003 puts identity in content, two
replicas would disagree about a modification time within seconds of each other,
and a format that stated a size would have a second answer to a question the
digest already answers. Everything here is in `cache/`, where deleting it is
correct.

**Hashing the working file lazily on a background thread.** Faster in the case
where a person runs two commands, and it makes a library that needs a runtime.

**Making `stamp` required rather than defaulted.** It would tax the exact
hosts 0025 exists for: a document provider that hands over opaque blobs would
have to invent a size and a time, and the invented ones would be believed. A
declined capability is a correct answer; a fabricated one is not.

**A single `Filesystem::digest` method instead of a streaming read.** It would
put this crate's hashing choice into the trait, so that an implementation could
answer with a digest of something it had not read, and a host would have to
know what SHA-256 is to implement a folder. `read_in_pieces` asks for bytes,
which is the only thing a folder has.

**Streaming `check` as well.** It compares the bytes of duplicates and decodes
text payloads, so it wants the file. Reading a payload twice — once to hash and
once to compare — would be slower, not faster.

## Consequences

- `fs::Stamp`, `Filesystem::stamp`, `Filesystem::read_in_pieces` and
  `fs::digest_of` are new and public. The two methods are defaulted, so every
  existing implementation compiles unchanged and behaves unchanged.
- `working` becomes a directory: `working/mod.rs` and `working/catalogue.rs`,
  mirroring `store/`.
- `Working` holds the folder's root and a cell of what it knows, and gains
  `digest`, `bytes_and_digest`, `text_and_digest` and `remember`. It is still
  `Debug` and `Clone` where its filesystem is.
- `record::survey` calls `Working::remember` once, at the end.
- `record::held_bytes` is gone. The whole-file comparison it existed for is now
  a comparison of the digest the tree states with the digest the folder has, so
  an unchanged photograph costs neither read.
- A file of bytes whose payload the store has not received no longer stops a
  survey where the folder holds those bytes: the tree states the digest, the
  folder hashes to it, and the file is unchanged. It was previously an error
  naming the undelivered payload.
- The measurement that motivated this: a folder holding one fifty-megabyte
  file, warm, on a machine whose SHA-256 is in hardware. `status` goes from
  44ms to 3ms, and the first run — the one that has to read — is unchanged.
  What is left is proportional to the number of tracked paths rather than to
  the number of bytes in them.

## Deferred

**`update`.** It reads every tracked file to compare it with what a head
records, and the comparison could start at a digest the same way. It differs
from `status` in that the files it finds a difference in are files it is about
to *write*, so the saving is confined to the ones it leaves alone — which is
most of them, and is worth measuring before it is built.

**Rename detection.** `record` holds the bytes of every added path so that a
file dropped in one place and added in another can be offered as a rename. Two
files match when their content matches, which is a digest question wearing a
map of `Vec<u8>` as a key. Nothing has measured it, because the folders where
it would show are folders somebody has just reorganised.

**A `check` for the folder.** Nothing reads the working folder without
trusting it, which is the standing 0035 gave `check` over the store. If the
believed-unread case above ever needs a command that ends it, that command is
`check --folder`, and it is a walk that hashes everything.
