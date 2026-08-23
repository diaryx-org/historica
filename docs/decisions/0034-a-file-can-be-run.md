# 0034 — A file can be run

0008 left this out and said exactly why:

> **Modes, symlinks, and an executable bit.** Not represented, and not for a
> good reason so much as a narrow one: this is a tool for prose and journals,
> where a mode is noise, and a mode is a fact about a file that
> `mode <file> <value>` could carry later without disturbing anything. A
> repository of shell scripts would notice before a repository of entries did.

The narrow reason has held up. The part that has not is what happens to
somebody who is not the repository of entries. Recording a file that is
executable and then running `update` gives it back readable and not
executable, with nothing printed and nothing to `check`. That is not a fact
the format declines to represent. It is a fact the tool observes, drops on the
floor, and then overwrites — and the file it overwrites is a person's, in
their own folder, which is the one place decision 0030 promises to touch
nothing it was not told to.

So the choice is not "model modes or stay small". It is "model this one bit,
or stop destroying it". A tool that cannot represent an executable file should
refuse it or leave it alone. This one wrote over it.

## The decision

- **`mode <file> <value>` is a tree fact**, stated by the revision that
  changes it, exactly as `move` states a path that changed. Two values parse:
  `executable` and `plain`.
- **A file with no `mode` line anywhere in its history is plain.** Every store
  written before this one therefore reads as it always did, and says the same
  thing it always meant.
- **The bit is not fixed at `add`.** A file's *kind* is, under 0017, because
  lines and bytes are different things to store. A mode is not what a file is;
  it is a fact about it that changes, and `chmod +x` is a thing people do to
  files they already have.
- **It applies to both kinds.** A compiled program is `bytes` and is exactly
  the file most likely to want this.
- **This is `historica-v4`.** A document claims it only when it carries a
  `mode` line, so a store that never marks anything executable never becomes
  version 4 and goes on being readable by every version 3 reader — 0004's rule
  doing the work it was written for.
- **A filesystem that cannot see the bit may not record it changing.**
  `Filesystem::executable` returns `Option<bool>`, and `None` means *this
  filesystem does not model an executable bit*. A recorder that gets `None`
  states no `mode` line and leaves the recorded value standing.
- **Concurrent modes resolve by digest, and are reported.** 0008's rule for
  two concurrent `move`s, unchanged and for the same reason: it is
  deterministic, it depends on nothing a clock said, and a person is told what
  was decided by rule rather than by agreement.

## One bit, not a mode

`mode` is the header 0008 named, and the value it carries is a word rather
than a number. What that gives up is every other thing a POSIX mode holds:
the read and write bits, the group and other bits, setuid, sticky.

Giving them up is the point.

**A umask is not history.** The read and write bits of a file in a person's
folder are a fact about that person's machine and that person's account.
Recording them means a file checked out on another machine gets the first
machine's answer, and a file recorded on a system with a different umask
records a difference nobody made. Git carries exactly one bit for exactly this
reason, after carrying more and regretting it.

**Setuid in a version-control system is a loaded gun.** A format that can say
"this file, when written into a folder, becomes setuid root" is a format whose
merge algorithm is a privilege-escalation surface. Nothing here is worth that.

**The executable bit is the one that is about the file.** Whether a thing is a
program is a property of the thing, not of who is holding it. It survives
being mailed, copied, and checked out somewhere else, and it is the one bit
whose loss makes a repository stop working.

## The filesystem question

Decision 0025 made the folder something asked for rather than assumed, and the
trait is the whole of what Historica may ask. Modes need two more questions
than it had, and the second is the interesting one:

```rust
fn executable(&self, path: &Path) -> io::Result<Option<bool>>;
fn set_executable(&self, path: &Path, executable: bool) -> io::Result<()>;
```

`None` rather than `false` is what keeps this safe. A filesystem that cannot
observe the bit — Windows, an in-memory map, a document provider handing over
opaque blobs — would otherwise report every file as plain, and the next record
would state `mode <file> plain` for every executable file in the history. A
person's two machines would then take turns flipping the bit off and on, each
recording a change the other had to undo, forever.

Git solves this with `core.fileMode`, which is configuration a person has to
know exists and has to set correctly on each machine. Here it is a property of
the filesystem implementation, answered by the implementation, and a host that
does not answer gets the safe behaviour without being asked. Both methods have
default implementations — `Ok(None)` and `Ok(())` — so a filesystem that does
not model modes says so by saying nothing, and every implementation written
before this decision keeps compiling and behaves correctly.

`Disk` answers on Unix and returns `None` on Windows. That is not a Windows
limitation being papered over; it is a Windows filesystem accurately reporting
that it has no such bit.

## What a person sees

- **`status` and `record`** report a mode change as `mode`, beside `edited`,
  because a revision that states nothing else still states something and a
  fact `record` writes that `status` never mentioned would be the thing
  decision 0015 exists to prevent.
- **`update`** sets the bit to what the tree says, on a file it writes and on
  a file already holding the right bytes with the wrong bit. It prints the
  ones it changed. This is inside 0030's promise rather than an exception to
  it: the mode of a recorded file is recorded, and a folder that half-holds a
  head is what that decision refuses.
- **`log`** counts a mode change under the tree facts it already counts.

## What this costs

**A fifth version.** The version ladder exists to be climbed and this is the
climb it was built for: a store gains version 4 the moment it first records an
executable file and not before, older readers refuse only the stores that
actually use it, and every document written yesterday parses today.

**One more thing a merge can contest.** The rule is `move`'s, so there is no
new principle, no new metadata, and nothing written down that a merge did not
already write.

**Two more trait methods**, which takes `Filesystem` from nine to eleven.
0025's count was never the promise — the promise was that the trait asks for
nothing it does not need and requires nothing of its implementor. Both new
methods have defaults, so the surface an implementor must actually write is
unchanged at nine.

## Rejected alternatives

**Numbers, as git spells them.** `100755` and `100644` are a file format's
internal constant leaking into a document meant to be read. `executable` is
what the line means, and the format has said `text` and `bytes` rather than
`0` and `1` since 0017.

**An advisory `x-mode` header.** 0002 gives `x-` headers to things a reader
may ignore. A reader that ignores this one writes a file that will not run,
which is the failure this decision exists to fix. An executable bit is not
advisory to the person whose build just broke.

**Leave it out, and refuse an executable file.** Honest, and much worse. A
folder of prose with one `deploy.sh` in it would become unrecordable, and the
refusal would be for a property of the file the person may not have chosen.

**Leave it out, and print a warning.** A warning on every record of every
executable file, for a fact the format could simply carry. Warnings that
cannot be acted on are noise, and this one could be acted on only by deleting
the bit.

**Full POSIX modes behind a flag.** Two formats, two merge rules, and a
question — "which mode does the merge of a 755 and a 644 have" — with no good
answer. The bit that matters has one.

## Consequences

- `Version::V4`, claimed by a document with a `mode` line and by nothing else.
  `Store::raise_version` moves the store's marker the first time one is
  written, which is the machinery 0017 built and 0026 ordered.
- `tree::Entry` carries `executable`, defaulting to false, and `tree::apply`
  refuses a `mode` naming a file the tree does not hold — the error every
  other tree fact already gets.
- `TreeContest::Mode` joins `TreeContest::Path` and the rest.
- The recorder observes the bit through the filesystem, compares it with the
  tree, and states the difference. A new file that is executable states `add`
  and `mode` together; nothing else may.
- `history/format.txt` gains the line and its two values, because a person
  hand-writing a revision document is the reader that file exists for.

## Deferred

**Symlinks.** Still refused by name in the working copy, and still the right
answer for now. A symlink is not a mode: it is a fourth kind of thing a tree
entry can point at, beside lines and bytes, and it brings a target that is
itself a path with its own escaping and its own security questions. It
deserves its own decision, or none.

**Empty directories.** Unchanged by this. 0008 is right that a directory
exists exactly when a file's path names it.

**A `check` note for a store that states modes on a filesystem that cannot
hold them.** The materialising command is where this bites, and `update`
already prints what it set. A store carried to Windows states modes nothing
there can apply, which is a true fact about Windows rather than a fault in the
store.
