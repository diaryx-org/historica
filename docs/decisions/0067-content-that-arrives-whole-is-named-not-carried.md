# 0067 — Content that arrives whole is named, not carried

0017 gave a payload its storage, its grammar and a format version, and ended by
naming what it had not paid for:

> **Large payloads.** The implementation reads a payload whole to hash it and
> whole to write it. Streaming, chunking, and not holding a video in memory are
> real work that a journal with photographs in it will not notice and a
> repository of build artefacts will.

0043 paid half of it from the other end. `Filesystem::read_in_pieces` and
`fs::digest_of` mean that *asking what a file hashes to* costs a buffer rather
than the file, and `record` uses that to settle an unchanged photograph without
opening either copy of it. What was left was every path that wanted the bytes
themselves, and there were more of them than the deferral implied — because the
type a payload was carried in went all the way up.

`Content::Whole(Vec<u8>)` is the sentence this decision is about. Materialising
a file of bytes read the payload, hashed it, and handed the caller a `Vec<u8>`;
`Content::bytes` then *cloned* it. `Change::Whole(Vec<u8>)` did the same on the
writing side, and because a survey is a map of every changed path, recording a
folder of twenty photographs held twenty photographs at once and then wrote
them. `diff` read the working copy whole and the stored payload whole in order
to print `binary files differ`. An `update` plan carried the bytes of every
file it was going to write, before it wrote the first.

None of that is a performance bug. It is one type stating something the format
does not: that what a revision says about a file of bytes is the bytes.

## What the format actually says

`bytes <file> <digest>`. That is the whole of it. A revision document names a
payload and never carries one, `operations/` holds the file, and 0017's own
argument for that arrangement is that the payload is `photo.png` — a file a
person opens in the tool they already use, whose only claim is its digest and
whose verification is `shasum -a 256`.

So the answer to "what does this file hold" is a name, and it was being
answered with a copy. Every caller that had the copy was doing one of two
things with it: comparing it against another copy, or writing it somewhere.
The first is a comparison of digests that was materialising two files to make
it. The second is a copy from one file to another that was going through a
buffer the size of the larger.

## The decision

- **`Content::Whole` carries the payload's digest**, and `Change::Whole` with
  it. A `Content` says what the revision document says. Asking a store to
  materialise a photograph now costs a tree lookup, reads nothing, and answers
  for a store that has not been delivered the bytes at all — which is a better
  answer than the old refusal, because whether the bytes are here is a
  different question with its own spelling.

- **`Content::bytes` is retired, and `Content::digest` replaces it.**
  `State::digest` already takes a line file's digest without building the
  string, and a payload names its own, so both sides of every comparison are
  arithmetic. A method handing back bytes could not survive this honestly: for
  a file of bytes it would have to reach into the store, read a file, and hash
  it before believing it — a store's work, at a store's cost, behind a
  signature promising neither. The bytes are asked of the store, by the two
  spellings below.

- **`Store::payload_file` is the primitive**, and it is what keeps the promise
  0017 made. It finds the file a digest names and hashes it *in pieces* before
  answering, so a payload is verified before anything is handed over and no
  buffer is spent doing it. `Store::payload_in_pieces` and
  `Store::copy_payload_to` are built on it and inherit that order: the file is
  hashed, and only then are its bytes fed to a caller or copied to a
  destination. What that costs is a second pass over the file, which is a read
  and never an allocation, and it is what makes `historica cat photo.png` a
  pipe that cannot emit content failing the one claim a payload makes.
  `Store::payload` stays, returning every byte, for the callers that mean to
  hold the whole thing.

- **`Filesystem::write_in_pieces` mirrors `read_in_pieces`**, defaulted to
  `Ok(None)` on the same convention and with the same warning: an
  implementation answering it must not have called `feed`, because the caller
  then buffers the pieces and calls `write`, and a partial write followed by a
  whole one leaves a file with a prefix of itself in front. It promises
  `write`'s landing — the destination holds the complete old file or the
  complete new one — and one thing beyond it: **an error out of `feed` leaves
  the destination exactly as it stood**. That sentence is what a verified
  streamed copy is built on, since the only way to refuse bytes that turn out
  to hash wrongly is to refuse them after the last of them has arrived.

- **A streamed payload write hashes as it writes and lands only if it
  matched.** `Store::insert_payload_in_pieces` is given the digest first —
  which it needs anyway, because that is what decides whether the store already
  holds these bytes and the write can be skipped entirely — and refuses at the
  last piece otherwise, reporting `StoreError::PayloadMismatch`. `record`,
  `receive`, `export` and `fetch` all write through it now.
  `insert_payload_at` keeps its signature and is this with the bytes in hand.

- **`record` streams each changed file out of the folder as it files it.** The
  survey states a digest, and `file_content` copies from the working copy at
  the moment the payload is written, hashing on the way past — so a folder of
  twenty photographs is one buffer, once, and a photograph that changed
  underneath the record is `PayloadMismatch` rather than bytes filed under a
  name that lies about them. The sniff that decides a new file's kind is one
  streaming pass too, accumulating the bytes only while the file might still be
  text and dropping them the instant it settles otherwise. Every format worth
  streaming settles it early: a PNG's signature carries a NUL in its first
  dozen bytes and a JPEG's first three are not UTF-8 at all.

- **A `text` payload keeps its bytes.** 0007's items are lines and the recorder
  is about to name every one of them, so a file of lines is in memory because
  the format needs it there, not because nobody thought about it. The split
  this decision makes is exactly 0017's split, and it is not an accident that
  the kind which cannot be streamed is the kind whose content the format
  actually reads.

- **The `update` plan names a payload and streams it at apply.** `Written` has
  two arms for 0017's two kinds: lines carried with the bytes they replace, and
  a payload named with the digest of what it replaces. `update::apply` takes
  the store, and lays a photograph down straight from the store's own file.

## What `update` gives up, and it is a window rather than a rule

0025's per-file promise is that a file which changed between the plan looking
and the apply acting is left alone and reported, and 0043 gave the filesystem
the chance to make the look and the write one operation. `Filesystem::write_if`
takes the bytes to expect; a streamed write has no bytes to hand it, because
having them is the thing being avoided. So a payload's guard is a digest, and
the destination is hashed and then written — two steps, with exactly the window
the trait's own default has always had for every filesystem that does not
implement `write_if`.

That is the honest price and it is worth saying plainly rather than burying:
for a file of bytes, `Disk` no longer narrows the race window that decision
0025 narrowed. A file of lines is untouched and still goes through `write_if`.
What is not given up is the rule — a drifted path is still left exactly as it
stands and still reported — and what is gained is that laying out a repository
of video no longer needs as much memory as the largest file in it.

A conditional streamed write is spellable, and it would want a filesystem that
can check a destination and take a stream in one operation. Nothing this crate
runs on offers one, so it is not invented here.

## The scratch a crash can leave

`Disk` stages a streamed write in a temporary sibling and renames it over the
destination, which is `write`'s atomic replacement done by hand because the
bytes are not all present at once. Every failure path removes the temporary.
A crash *between* the create and the rename does not, and the file it leaves is
in `operations/`, where 0017's rule is that everything which is not a `*.ops`
document is a payload.

So a machine that lost power mid-record can leave a file `check` reports as a
payload nothing names. That is a note rather than an error, and it is the same
note an interrupted `record` has always earned — 0017 chose content-first
writing precisely so that an interruption leaves content nothing points at
rather than a revision pointing at nothing. The temporary is dot-prefixed and
suffixed `.partial` so that a person who meets one can see it is not theirs.

## Consequences

- `Content::Whole(RevisionId)`, `Content::digest`, `Content::lines`,
  `Content::payload`. `Content::bytes` is gone, and so is the read
  `content_at` performed for a file of bytes — the `MissingPayload` refusal for
  a `bytes` file moves to whatever asks for the bytes, and stays exactly where
  it was for the `text` payload a creation replays from.
- `Store::absent_payload` is where that refusal moved to, and it is the seam
  with 0066, which landed alongside this. An absence still arriving and an
  absence somebody made are different answers, and losing the one place that
  told them apart would have scattered the distinction across every caller
  that wants bytes. So there is still one place; it is just no longer the
  method that answers what a revision said.
- `Change::Whole(RevisionId)`, and `file_content` takes the working copy.
  `RecordError::NoPathForContent` is the refusal for a plan that states whole
  content and no path to read it from, which nothing produces and which is an
  error rather than a `debug_assert` because the alternative is writing a
  revision naming bytes nobody has.
- `Working::sniff` is the streaming kind-and-digest read, and
  `Working::reread_digest` is `Working::digest` worked out afresh in pieces
  rather than answered from `cache/working.txt`. `Working::bytes_and_digest`
  survives for the callers that want a file of lines.
- `renames` matches by digest. 0015's rule is byte equality and this is byte
  equality, asked of the number the format already keeps for exactly that
  purpose — and it is the change that stops a survey holding every added
  file's content to look for a rename among them.
- `update::Write` carries a `Written` rather than `bytes` and `replaces`;
  `Stood::File` and `Remove::held` carry a digest; `update::apply` takes the
  store. `RecordedBytes::holds` compares digests, which is 0030's overwrite
  question asked without materialising either side.
- `Source::get_in_pieces` is defaulted to `get`, so every implementor keeps
  compiling and keeps answering — the default *is* streaming, in runs of one.
  A fetch feeds the pieces straight into the store's file. **Resumption is not
  in it**: nothing carries an offset, a feed that stops halfway fails the whole
  request, and the answer is to ask again. That is affordable precisely because
  nothing partial is ever written, which is the same property that makes a
  tampered manifest cost a wasted request and nothing else.
- `scan_for_payload` returns a path. It was already hashing each candidate in
  pieces to find the one that answered, and then reading that one whole to
  return it; the hash was the verification, so the read was the answer to a
  question already answered.
- `write_once_from_pieces` is `write_once` for a file nobody is holding. The
  exclusive create is not available — the bytes arrive over time — so the look
  and the write are two steps, and what makes that safe is what makes it safe
  everywhere else in this store: the name is the digest, so two writers racing
  to file one payload write the same bytes, and a writer that finds the name
  taken hashes it rather than trusting it and reports `ContentMismatch` for a
  file that is not those bytes.
- `historica cat` and `historica show` print a payload straight from the
  store's file; `historica record --merge` lays a contested attachment down the
  same way; `historica diff` compares by digest on both sides and reads the
  working copy only where it is going to print lines from it.

## What is resident now

Counted as *copies of a file's content held at once*, which is a property of
the code rather than a measurement:

| command                       | before          | after |
|-------------------------------|-----------------|-------|
| `record` of *n* changed files | *n* payloads    | none  |
| `update` / materialise        | every payload   | none  |
| `diff` of one binary file     | two copies      | none  |
| `fetch` of one payload        | one copy        | none  |
| `cat` of a payload            | two copies      | none  |

"None" means a fixed buffer whose size the filesystem chose — 64 KiB for
`Disk` — and never a quantity the file decides. A filesystem that takes the
default for either streaming method is exactly where it was before, which is
0043's rule for a declined capability: it costs time, and never an answer.

A file of lines is unchanged in every row, and deliberately so.

## Rejected alternatives

**A parallel streaming API beside the buffering one.** `payload_streamed`
alongside `payload`, `Content::Whole` still holding bytes, nothing breaking.
Rejected because the buffering one would stay the obvious call and the type
would keep saying the thing that is not true. Nothing is published yet, so a
breaking change costs a recompile now and would cost a major version forever.

**Sniffing a new file's kind by its first piece alone.** Read 64 KiB, decide,
and never look at the rest. It is what every other tool does and it would make
the sniff a fixed cost. Rejected because 0017 put the kind on the file's
identity, permanently, and a rule that reads part of a file to decide something
irrevocable about all of it is the kind of rule that is right until the day a
UTF-8 file has a NUL in its second megabyte. Reading the whole file costs a
pass and buys an answer about the whole file.

**Keeping the bytes for the drift guard so that `write_if` still applies.**
It preserves 0025's narrow window exactly. Rejected because it preserves it by
holding the file, which is the thing this decision is for, and because the
window it narrows is one every filesystem taking the trait default already has.

**Compressing or packing, again.** 0017 rejected it and the reason is
unchanged: a store whose files need a tool to read is the thing this project
exists not to build. Streaming does not touch that promise — `shasum -a 256`
still prints what the revision names — which is why it is the version of this
work that could be done.

## Deferred

**Resumption.** A fetch that loses a connection halfway through a large payload
starts that payload again. The shape is an offset in `Source::get_in_pieces`
and a partial file somewhere `check` will not read as a payload, and the second
half of that is the real work — 0003's directory has one place for content and
0017 was explicit that a payload's identity is the digest of the whole of it.
`cache/` is where a partial download would go, and what it would owe is an
account of what it holds that a reader may not believe without hashing.

**A payload whose bytes never touch this machine.** Everything above still
copies each payload into `operations/`, which is right for a store and wrong
for the one case a person will eventually ask about: a folder of video already
sitting on a disk, recorded without a second copy of it. That is a question
about whether a store may name a file it does not hold, which is a question
about what `check` means, and it is not this one.

**`check` hashing every payload.** It is the command that does the work rather
than takes the result, and it now does that work in pieces like everything
else — but it still reads every payload in the store on every run, which is a
cost that grows with the store and answers a question about a set of files that
are immutable. Whether that answer may ever be remembered is 0035's territory
and 0036's, and neither of them was arguing about a video.
