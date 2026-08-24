# Historica

Historica is an experiment in readable, convergent version control.

The repository format follows one non-negotiable rule:

> The readable files are the authority.

A person must be able to inspect the history, understand its relationships, and
recover stored content without decoding an opaque database or binary operation
log. Binary indexes and snapshots may eventually exist as disposable caches,
but deleting every cache must lose neither information nor meaning.

## Current scope

The `core` module models the smallest collaboration-safe history:

- immutable revisions, each naming both the digest of its own bytes and the
  change it is a version of;
- explicit causal parents, named by digest, so history is a Merkle DAG;
- explicit supersession, so rewriting a change is recorded rather than hidden;
- a history that merges by set union;
- deterministic head discovery, over parents and over supersession alike;
- resolution of a change to its current revision, including the legitimate
  states of divergence and abandonment;
- rejection of two revisions with disagreeing bytes claiming one digest.

The `format` module reads and writes the revision document those revisions are
stored as. It parses strictly — one byte sequence per set of facts, so that
hashing the file is as trustworthy as hashing a canonical model would be — and
refuses anything else with an error naming the line and the fix. Writing a
parsed document reproduces its bytes exactly, and a revision's ID is the
SHA-256 that `shasum -a 256` already prints for the file.

`tests/corpus/revisions/` is the specification, executed. Seven hand-written
files are a real five-change history containing a merge, an amendment by a
reviewer, and the rewrite that amendment forced; nine more are invalid, each
for one stated reason that `tests/corpus.rs` holds the parser to.

The same module reads and writes the operation document, which is what one
revision did to one file: a list of deletes and inserts against the state at
that revision's parents, positions counted into the parent rather than into
the document being built. It is as strict as the revision document and for the
same reason — operations ascend, never overlap, and never state one fact twice,
so one byte sequence parses per edit and the digest can cover the file. Items
are lines, so an item may hold a carriage return that the format's own lines
may not, and a file whose last line has no terminator says so in one place.

`tests/corpus/tree/` is a history of two files with a rename in it, and the
first corpus where the revisions and the operation documents describe one
history together rather than narrating the same one separately.

`tests/corpus/operations/` is that half of the specification. The numbered
files are the edits the numbered revisions made to one file, with a gap at 04
because a merge that changes nothing about a file names no operation document;
three more pin the rules that no revision happened to exercise, and seventeen
invalid ones are each refused for their own stated reason by
`tests/operations.rs`. `states/` is that file as it stands at each revision,
hand-written, which is what the replayer is held to.

Content that no operation produced is decision 0017, and it is where the
format's version stops being a formality. A **payload** is a file of bytes in
the store carrying no format of its own: `text <file> <digest>` names the lines
a file is created with, `bytes <file> <digest>` names the whole content of a
file that has no lines, and both are stored beside the documents they are not.
So a created file is *itself* in the store rather than a second copy with `+`
down the left margin, and a photograph is a photograph. A file is lines or
bytes for its whole life, fixed when it is added. Retiring `add` with `edit` —
which counted an edit's positions into a file that did not exist yet — is what
makes this `historica-v1`, and 0004's rule that a reader's vocabulary only
grows is why every version 0 document still parses exactly as it did.

`tests/corpus/whole/` is that executed: two revisions that file a photograph
and the entry it belongs to, where the entry's first content is the entry and
the second revision's `edit` counts its positions into what that payload
produced. Six invalid files pin the grammar, each refused for its own stated
reason by `tests/whole.rs`.

The `replay` module materialises a file from what was done to it. It does the
linear case, which decision 0007 says costs nothing: positions are stated
against the parent, so applying them is arithmetic rather than interpretation,
and a chain of documents from the root produces the file byte for byte. It is
also where a `delete` line's redundancy is spent — a document whose recorded
items disagree with the parent it claims to edit is refused there, rather than
absorbed into a merge, and so is a result that would leave a line without a
terminator anywhere but at the end.

The `merge` module is the one decision 0007 spent itself on: concurrent
branches merge by replaying their event graph, and the structure that resolves
concurrency is built during that walk and thrown away at the end, so nothing a
merge needs is ever written down. An item's name is derived — item *i* of
revision *R* is `(R, i)`, and *R* is a digest of readable bytes — and ties are
broken by that name, never by a timestamp. Runs written by one author stay
whole, which is the guarantee Fugue was chosen for. A merge returns the content
and the spans where concurrent work met, so a tool can decline to record an
automatic merge and show a person both versions instead.

The `tree` module is the file set, specified by 0008. A revision records what
it did to it — `add`, `move`, `drop`, `edit`, and 0017's `text` and `bytes` —
as headers in the revision document, and the tree at a revision is what
replaying those facts produces. Files carry identifiers and paths hang off
them, so a rename keeps everything recorded against the file and no heuristic
has to recover the connection later. There are no directories: one exists
exactly when a file's path names it. An entry also says what it points at: an
operation chain, or one payload whole, decided when the file was added and
never again, so an `edit` addressed to a photograph is refused by name.

An entry also carries a mode, which decision 0034 makes the one POSIX bit this
format has an opinion about. `mode <file> executable` and `mode <file> plain`
are tree facts stated by the revision that changes them, as `move` states a
path that changed, and a file no `mode` line has ever named is plain — so
every store written before this says what it always meant. The rest of a mode
is deliberately absent: a umask is a fact about a machine rather than about a
history, and a format that could say `setuid` would have a merge algorithm
with a privilege question in it. Two concurrent modes resolve by digest and
are reported, which is 0008's rule for two concurrent `move`s unchanged. A
filesystem with no such bit answers `None` rather than `false`, and a recorder
that gets `None` states nothing and leaves the recorded value standing — which
is what stops two machines flipping the bit at each other forever, without
anybody having to know a configuration flag exists.

The `diff` module is the writing half, specified by 0009. Given the file at a
revision's parent and the file as it stands, it records what the revision did:
line matching from `similar`, configured to histogram and to no deadline, and
then Historica's own rules — maximal runs, a replacement anchored at the removed
run's start, and a result that parses whatever the matcher hands over. A file
that did not change names no document at all. `tests/corpus/diffs/` holds a
before, an after, and the document recorded for the pair, for the choices a
property test cannot see; `examples/matchers.rs` is the measurement decision
0009 chose the matcher on.

The `record` module is the writer 0010 and 0011 specify, and `working` is what
it is given: the folder beside the store, everything in it tracked except what
`history/skipped.txt` names — and a rule there covering a file the tree already
holds is refused, because the walk would stop offering the path and the next
record would spell a request for privacy as a deletion of the file it names. A change ID is 96 bits from the operating system, an
author comes from a person's own configuration and is never guessed, and the
time is the clock in the offset the platform reports. Everything else is
observed by comparing the folder with the tree at the parent — including a
deletion, which is a fact rather than a heuristic, and including which kind of
file a new one is: valid UTF-8 with no NUL is lines, and everything else is
bytes. That last rule is the tool's rather than the format's, because a
recorder is allowed signals a format may not use. Only a rename has to be
stated, with `--move`, which performs it if the person has not.

The `fs` module is the folder itself, asked for rather than assumed. Everything
that persists anything goes through `fs::Filesystem` — nine methods, no
metadata beyond what a directory entry is, and nothing that follows a symbolic
link — and `fs::Disk` is that trait over `std::fs`, behind the default `disk`
feature. `Store<F = Disk>` and `Working<F = Disk>` carry it as a type
parameter, so the trait itself requires nothing at all: not `Send`, not `Sync`,
not `Debug`. A store over a filesystem that has those has them, and one over a
Swift object or a `JsValue` — neither of which is `Send` — is welcome without
anyone writing `unsafe impl`. Dynamic dispatch stays available rather than
mandatory, since a smart pointer to a filesystem is one:
`Store<Arc<dyn Filesystem>>` is the store that chose at run time. Nothing at a
call site moved — `Store::open(root)` and every `&Store` signature mean
`Store<Disk>` as they always did. Turning the feature off leaves a library that
names `std::fs` nowhere, which is what lets a host holding its documents
through a document provider — iCloud, a security-scoped bookmark, an Android
content URI — use this without a path the operating system will open.
`tests/filesystem.rs` records a history, reopens it, checks it, and prunes it
inside two `BTreeMap`s; decision 0025 is the argument.

The `store` module is that format as a folder. It loads a `history/` directory
by reading files and never their names — revisions and operation documents alike,
so renaming every file in a store changes no identity and breaks no reference — which is what lets a store be
hand-arranged into something a file browser can narrate. `operations/` holds
two kinds of file on the rule `revisions/` already keeps: only a name ending
`.ops.txt` is a document there, and every other file is a payload — so an
ordinary `.ops` file in the repository keeps its own name — found by its digest
and not
read at all until something wants its bytes, so a history with photographs in
it does not cost a full hash to run `log`. The writer names each file the way a
person reads it — decision 0019 — appends only, and never overwrites; a
digest-named store stays legal everywhere and the loader cannot tell the
difference. `check` reads a store
without loading it and separates errors, which mean the store contradicts
itself, from notes, which never fail: an undelivered parent, an undelivered
operation document or payload, a payload nothing names, a duplicate, or a sync
tool's conflicted copy is a legitimate state and is reported as one — and a
file the operating system wrote into the folder is not reported at all, because
a note on every machine whose file browser has been near the store is a note
that means nothing. A `text`
payload that is not UTF-8 is an error, because no operation document could ever
quote a line of it. It also replays: every revision on a
linear chain is held to the file set it names and every `-` line to the parent
it claims to have edited, which is the error 0007 asked for and 0008 unblocked.
A store can materialise a file — `tree` and `content` at a revision — and
refuses a history with a merge in it rather than ordering it arbitrarily.

What that costs is decision 0036. Identity coming from content is what left the
store no way to find a digest but to open every file in `operations/` and hash
it, so a `cat` that a cache could answer in one read still paid fifteen
thousand opens first. A **catalogue** in `cache/` says where each digest is,
and it is believed on one condition — that the set of paths it names is the set
the directory holds, which a walk checks without opening anything. Everything
it does not account for is read. A lookup still hashes what it finds before
believing it, and a catalogue that cannot answer costs a pass over the
directory rather than an answer, so deleting it, truncating it or filling it
with lies changes how long a command takes and nothing else. `check` builds its
own by reading, because it is the command that wants the work.

The `historica` binary is the front end decision 0006 said was owed. `init`,
`check`, and `arrange` are the three commands it names; `log`, `show`, `files`,
`cat`, and `names` read a store and render it; `status` reads the folder beside
it and says how the two differ; `update` makes the folder hold a head, writing
what the store records, removing what it does not, and touching nothing
unrecorded — decision 0030, which is also where checkout-to-the-past is
declined and the stored position it would need is refused for good; `record`
writes one and `amend` rewrites one,
`skip` writes the rule saying what recording does not take, and `identity` says
who is writing. `diff` is what changed — the folder against the
position, or what a revision did — and decision 0037 makes it the one command
that renders rather than prints, in the unified shape every other tool already
reads. What separates it from every other tool's is 0008: two revisions carry
file identifiers, so a rename between them is *stated*, with the edit that
came with it underneath, where a similarity heuristic would have guessed and
missed. The folder gets the opposite treatment for the opposite reason — it
holds paths and no identifiers, so a rename there is a drop and an add until
somebody says `--move`, and rendering it as a rename would invent a fact
`record` would decline to write down. The hunks are `crate::diff`'s own
decomposition rather than a second one, so what a person is shown and what
recording would state are one answer. `--color` is `auto`, which is a terminal
and nothing else and which `NO_COLOR` settles; decorated, the ± lines carry the
changed words inside them in inverse video, which is a decoration of lines
`crate::diff` has already chosen rather than a second opinion about them.
Undecorated, every escape is the empty string, so a pipe gets the bytes it got
before there was a flag. `blame` is the same trick applied to the
other question — who wrote each line — and decision 0038 makes it the one
command every other tool has to guess at and this one does not. A revision
records the items it *inserted* and a merge records which items it *kept* and
under whose names, so `merge::Merged::origins` has said which revision wrote
each item since 0012 needed it to label a contested span, and the command is
that vector printed. A line therefore keeps its author through a rename, since
0008 makes a file one file for its whole life, and through a merge, since
0032's resolution keeps items under their own names rather than restating
them — so a merge authors only the lines somebody typed into it, which is
exactly what a three-way merge cannot say. `name` writes a bookmark, and takes the third argument `show`
takes: with a path it names the file at that path rather than the work, so
`history/names/` holds `file` lines beside `change` and `revision` ones and
`cat <target> file:<bookmark>` is that file wherever it has since been moved to.
What `log` prints is narrowed by `--limit`, `--author`, `--grep`, `--since`,
`--until`, and `--path`; they compose, and `--limit` counts what the rest left
rather than what they were given. `--path` is where 0008 pays: the path is read
once, at one revision, and what the log follows is the *file* it named — so a
rename is not a break in a file's history and no heuristic is asked to guess
that it was one. A time bound is read in each revision's own offset, since
0002 leaves no shared instant here to compare against, and a bare `YYYY-MM-DD`
is that whole day there. Nothing there decides anything
the library has not — `files` and `cat` refuse a merge in the library's own
words rather than choosing an order, and `show` prints the stored file byte for
byte, because the readable file is the authority and a rendering of it is not.
`arrange` is the library's rather than the front end's — decision 0025 — so a
host that syncs a store gets the readable folder for the same reason a person
does; `store::arrangement` is the plan and `store::arrange` carries it out, on
the pairing `prunable`/`prune` already has.
The naming scheme is `naming`, and both the writer and `arrange` use it, which
is what makes them agree: revisions are `YYYY-MM-DD summary.rev.txt`, so the
file a person double-clicks opens in the editor they already have, and each
revision's operation documents and payloads sit under a directory of the same
name, at the path they had — as real directories, so a revision's folder is the
subtree of the repository that revision touched and `notes/photo.png` inside it
opens as a picture. Its rule to keep is that two replicas must produce one set
of filenames, so a collision resolves by change ID and then by digest, never by
a counter, which would depend on what else was in the directory. `arrange` is
what applies that scheme to a store that does not have it — one written by an
older version, by another tool, or by hand — and on a store this version wrote
it does nothing. It is deliberately not a lint: a name that differs is usually
a person filing their own history, which `check` has no business calling a
fault, and every fault `check` does report it finds in content. The loader
walks both directories to any depth and never follows a symbolic link, which is
what lets a person file a history however they please.

The `tree` module also merges. Decision 0008's rules for concurrent tree facts
are here rather than in prose now: a `drop` concurrent with an edit or a move
loses and is reported, two concurrent `move`s resolve to the lower digest, two
concurrent `drop`s agree, and two files claiming one path both keep their
identities, because a name invented by a merge is content nobody wrote. What
is concurrent with what is decided by ancestry, computed for the length of the
call and thrown away with everything else a merge builds.

The store walks that graph. `tree` and `content` at a revision materialise
across merges, `merged_tree` and `merged_content` return what was contested
along with the answer, and both take several heads as readily as one — which
is what recording a merge will ask of them. `check` walks each head's whole
ancestry rather than stopping at the first merge, so a concurrent history is
held to the same standard a linear one is.

The `conflict` module is the view a person edits. Decision 0012 keeps nothing
conflicted in the format — two heads already are the conflict, and 0007's walk
recomputes it from the same files on every machine — so a contested span is
rendered into the working copy between marker lines, with each run inside it
labelled by the revision that wrote it. `historica merge` writes that view and
prints the command that records it. What it joins is what is named and every
head that is not, so divergence — the state the command exists for — needs no
argument at all, and the command it prints back names every head it joined
rather than only the ones a person typed. `record --merge` recomputes the merge,
refuses while any line the renderer wrote still stands in a contested file, and
otherwise diffs the folder against *the merge result*, so what it records is
exactly the resolution. Detection is per line and scoped to a merge record,
which is why this repository can hold a decision document full of marker lines
and record it without complaint.

Two files claiming one path is the other thing a merge cannot resolve on its
own, and there the command printed carries the `--at` that settles it — naming
the path the merge wrote each file to, so following it records the folder as it
stands, and any other path may be typed in its place. The file written beside
the one that keeps the path is named for the reason rather than by a counter,
with the marker in front of the extension so it still opens in the editor that
would have opened it, and with no character on it that a Windows filesystem
would refuse.

A file of bytes takes the same route through all of it and stops at the merge:
0008 makes two concurrent `bytes` a divergence to report, and there is nothing
to render between marker lines in a JPEG, so `merge` names the contested path,
prints the command that fetches each side, and leaves the folder alone. For
that one case the tool cannot tell a resolution from an oversight, which is
said out loud rather than papered over.

The rewriting half starts at the tip, which is decision 0023. `amend` writes a
revision superseding the head: the change, the author, and the moment the work
was first recorded are copied, `revised` is the clock now because a person
asked for this, and everything the folder says is worked out again by the
survey `record` already does — including the identifiers the amended revision
minted, kept by path, so the same file in the same place does not become a
different file every time the work is rewritten. The rename it recorded is
inherited, because a recomputation cannot observe one. A revision something
stands on is refused, and so is one something has already replaced, and the
superseded revision stays exactly where it was, because with no operation log
here it is the whole of the undo. The position a command works from becomes
the head *nothing has rewritten*, which is decision 0001's rendering question
answered at the moment it first has an answer that matters.

`abandon` is decision 0013's other tip-first command: a tombstone of a newly
minted change supersedes a head, or a run ending at one, records nothing, and
carries the one message this format requires — the reason is the only thing
it has. The content falls out of the ancestry, so nothing is undone. `prune`
is the same decision's disk half: it deletes exactly a revision document that
is superseded and orphaned and a content document nothing kept names, prints
every file, and refuses a store `check` calls broken. It is local, manual,
not secrecy, and the undo history, all four of which 0013 says in as many
words.

For the sentence a person cannot rotate, decision 0014 is `forget`: destroy
the payload, preserve the shape. A forgetting document names the digest whose
bytes were destroyed, states the same operations at the same positions with
the same counts, and stands a `\ forgotten` marker where each destroyed item
stood — so a redacted history materialises and merges byte for byte outside
the forgotten runs. An item forgotten once is forgotten everywhere it is
quoted, the deletes that quoted it back included, and two redactions union to
the more thorough one in either arrival order. What forgetting cannot hide it
says out loud: shape, position, paths, and the revision around it all stay.
A store that has forgotten something can prove its structure and not its
content — the `shasum` claim above becomes conditional at that moment, and
only then — and a store that has forgotten nothing is unaffected, which is
nearly all of them.

What is still owed of the rewriting half is everything that needs a
descendant reparented: amending a revision that has one, abandoning it, and
moving a change somewhere new are one piece of work — transforming operations
against operations — and none of it is built.
The ordering rule is held to convergence and to non-interleaving by property
tests over every walk order of each graph they generate, and by the
conformance suite 0007 asks for: an independent reference implementation of
the other architecture — a live per-replica Fugue tree, placement computed at
the source, messages instead of replay — that the event-graph merge is held
to agree with, step by step, across randomised histories.

## Installing

historica is published to [crates.io](https://crates.io/crates/historica), so
the command line below is a `cargo install` away:

```console
cargo install historica
```

The library is the same crate — `historica = "0.1"` in a `Cargo.toml` — because
the binary decides nothing the library has not, and every answer the commands
give is one a caller can ask for directly. It builds on stable Rust 1.88 or
newer, which is the floor the `msrv` job holds it to, and it is MIT or
Apache-2.0 at the reader's choice: [`LICENSE-MIT`](LICENSE-MIT) and
[`LICENSE-APACHE`](LICENSE-APACHE).

Version 0.1 is an experiment rather than a promise. What the format guarantees
is decision 0004's rule — a reader's vocabulary only ever grows, so a document
written today still parses — and the Rust API carries no such rule yet.

## The command line

```console
$ historica init .
made a store at /home/adam/journal/history
$ historica log
nwlxsqot  4cf00b8c  (head)
    Adam Harris <adam@example.com>  2025-08-21T22:05:00-06:00
    dropped 1
    Withdraw the entry, keeping what it taught

mzvwutkl  d56419e5
    Adam Harris <adam@example.com>  2025-08-20T08:14:33-06:00
    moved 1  edited 1
    File the README under docs, and say what it covers

kxryzmor  55874ae7
    Adam Harris <adam@example.com>  2025-08-19T09:02:40-06:00
    edited 1
    Say why a path is not an identity

qpvuntsm  f23cda95
    Adam Harris <adam@example.com>  2025-08-19T00:47:11-06:00
    added 2
    Start a journal
$ historica files nwlxsqot
docs/README.md  swtlmnkqvzyrxopwstlnmkqv
$ historica cat nwlxsqot docs/README.md
# Notes

A journal kept in Historica, and the notes that came with it.
$ historica name main nwlxsqot
main -> change nwlxsqotvkzmuprysltnwxqk
$ historica name readme nwlxsqot docs/README.md
readme -> file swtlmnkqvzyrxopwstlnmkqv
$ historica cat nwlxsqot file:readme
# Notes

A journal kept in Historica, and the notes that came with it.
$ ls history/revisions
'2025-08-19 Start a journal.rev.txt'
'2025-08-19 Say why a path is not an identity.rev.txt'
'2025-08-20 File the README under docs, and say what it covers.rev.txt'
'2025-08-21 Withdraw the entry, keeping what it taught.rev.txt'
$ historica arrange
/home/adam/journal/history/revisions: 0 renamed, 4 already arranged
$ historica check
/home/adam/journal/history: nothing to report
```

A target is a bookmark, a change ID, or a revision digest, and the last two may
be abbreviated to any unambiguous prefix — decision 0001's disjoint alphabets
are what let one argument position accept either. The position beside it names a
file, and there the alphabet trick does not reach: a path is a value a person
chose rather than a name the tool minted, and a file may legitimately be called
`kxryzmorwlvtnsqpkzmuprys`. So a file identifier is spelled `file:` and a
bookmark can hold one — decision 0024 — abbreviating to any prefix unique among
the files at that revision, and `path:` says the rest is a path for the file
whose own name begins `file:`. `historica help` lists the rest. `check` exits non-zero only when the store cannot be trusted, so it can
be run in anger; a duplicate, an undelivered parent, or a sync tool's
conflicted copy is a note, and notes never fail.

What those notes leave a person to work out is what they cost, and the cost is
not the count: one undelivered payload under the root makes every file after it
unreadable, while ten in a branch nothing stands on cost nothing. So `check`
says the consequence as well as the symptom — which heads this store holds the
history of and cannot produce — and `check --complete` is the caller who wants
that to fail, being a sync that should have finished or a backup about to be
trusted. It is still not an error: the store contradicts nothing, and the
readable files are simply not all here yet.

A refusal that turns on a person having to choose a head says which heads those
are in the terms they would recognise — the change, any bookmark, who wrote it,
when, and what it says — because a digest is the one thing about a revision
that says nothing about which line of work it is.

## Decisions

Choices that constrain later work are written down as they are made.

- [`docs/decisions/0001-identity.md`](docs/decisions/0001-identity.md) — why
  every node carries both a derived revision ID and an assigned change ID.
- [`docs/decisions/0002-revision-document.md`](docs/decisions/0002-revision-document.md)
  — the readable revision document, and why its digest covers the file rather
  than a re-serialised model. Examples live in
  [`tests/corpus/revisions`](tests/corpus/revisions).
- [`docs/decisions/0003-store.md`](docs/decisions/0003-store.md) — the store:
  identity comes from content, filenames are presentation.
- [`docs/decisions/0004-parser-contract.md`](docs/decisions/0004-parser-contract.md)
  — strict reading, the `historica-v0` preamble, and why a reader's
  vocabulary can only ever grow.
- [`docs/decisions/0005-authorship.md`](docs/decisions/0005-authorship.md) —
  authorship is copied into every revision of a change, and is a claim rather
  than evidence.
- [`docs/decisions/0006-store-questions.md`](docs/decisions/0006-store-questions.md)
  — one-line bookmarks, a visible `history/` root, and what `check` treats as
  an error rather than a note.
- [`docs/decisions/0007-content-and-merge.md`](docs/decisions/0007-content-and-merge.md)
  — a revision records what it did rather than what a file is, and concurrent
  edits merge by replay rather than by three-way heuristic. Examples live in
  [`tests/corpus/operations`](tests/corpus/operations).
- [`docs/decisions/0008-tree.md`](docs/decisions/0008-tree.md) — files carry
  identifiers and paths hang off them, there are no directories, and a revision
  records what it did to the file set rather than what the file set is.
- [`docs/decisions/0009-diff.md`](docs/decisions/0009-diff.md) — how operations
  are recorded from an edited file, why the matcher is a dependency where the
  merge rule could never be, and the replacement anchoring 0007 left ambiguous.
- [`docs/decisions/0010-writer.md`](docs/decisions/0010-writer.md) — the three
  facts a writer supplies and nothing can derive: 96 bits from the operating
  system, an author stated in a person's own configuration rather than guessed
  or kept beside the history, and the clock at the moment of recording. A
  rewrite the tool performs on its own behalf copies all three, so two replicas
  that rebase one change write one file.
- [`docs/decisions/0011-working-copy.md`](docs/decisions/0011-working-copy.md)
  — the folder beside the store is the working copy, `history/skipped.txt` says
  what it does not take, the parent is the head, and a rename is the one fact
  a person has to state. Nothing is remembered between commands.
- [`docs/decisions/0012-conflicts.md`](docs/decisions/0012-conflicts.md) —
  nothing conflicted is ever recorded, because two heads already are the
  conflict; contested spans are rendered into the working copy with markers a
  merge record refuses to accept, and a contested path is stated on the command
  line rather than invented.
- [`docs/decisions/0013-abandoning-and-pruning.md`](docs/decisions/0013-abandoning-and-pruning.md)
  — abandoning is a tombstone superseding the work, which is the state 0001
  already had a name for; pruning deletes superseded documents nothing names as
  a parent, is local, manual, and is the undo history.
- [`docs/decisions/0014-forgetting.md`](docs/decisions/0014-forgetting.md) —
  redaction that keeps a history working: a forgetting document destroys an
  operation document's payload and preserves its arithmetic, so everything
  downstream still materialises and merges; forgetting converges by union, an
  item is forgotten wherever it is quoted, and what survives is shape,
  authorship, and paths.
- [`docs/decisions/0015-status.md`](docs/decisions/0015-status.md) — what
  status shows and what it is allowed to know: a comparison derived from the
  folder and the store with nothing remembered between commands, the survey
  the plan is derived from, and a refusal reported rather than raised.
- [`docs/decisions/0016-the-store-a-person-reads.md`](docs/decisions/0016-the-store-a-person-reads.md)
  — the folder a person browses: operation documents filed under the revision
  that names them, a walk that recurses to any depth and never follows a
  symbolic link, and the command that writes a `skip` rule.
- [`docs/decisions/0017-content-that-arrives-whole.md`](docs/decisions/0017-content-that-arrives-whole.md)
  — content no operation produced: a payload is a file of bytes named by its
  digest, stored beside the documents it is not one of, so a created file is
  itself in the store rather than a second copy with `+` down the left margin
  and an image is an image. `text` and `bytes` say which, a file's kind is
  fixed when it is added, and retiring `add` with `edit` is what makes this
  `historica-v1`.
- [`docs/decisions/0018-a-path-is-a-path.md`](docs/decisions/0018-a-path-is-a-path.md)
  — a path is filed as a path: real directories for real components, nothing
  clipped, and no character standing in for `/`. 0016 nested the revision and
  then spent the length it bought on a homoglyph nobody can type; this spends
  it on the filesystem's own separator, so a revision's folder is the subtree
  that revision touched.
- [`docs/decisions/0019-the-name-a-store-is-written-with.md`](docs/decisions/0019-the-name-a-store-is-written-with.md)
  — `record` writes the readable name rather than a digest a command has to be
  run to replace, so the folder 0003 promised is the one a person gets. What a
  writer cannot know is what another replica wrote this morning, so a collision
  it cannot see degrades to the conflicted copy `check` already understands.
  `arrange` becomes the command that applies the scheme to a store that does
  not have it, and is deliberately not a lint: a name that differs is usually
  a person filing their own history.
- [`docs/decisions/0020-a-document-says-it-is-text.md`](docs/decisions/0020-a-document-says-it-is-text.md)
  — documents are written `.rev.txt` and `.ops.txt`, so the file a person
  double-clicks opens in the editor they already have. The older suffixes are
  read forever, because a store that quietly stopped having documents in it is
  the worst failure available; the cost is that a payload still has to avoid
  both.
- [`docs/decisions/0021-the-store-explains-itself.md`](docs/decisions/0021-the-store-explains-itself.md)
  — the marker becomes `historica.txt` and carries a note saying what the
  folder is and that nothing in it needs Historica to read; `skipped` and the
  bookmarks follow the documents into `.txt`. The older suffixes stop being
  read, which retires the payload rule in the form that bit: an actual `.ops`
  file keeps its own name. It is the last decision that gets to break a store,
  because it is the last one written while none exists that its author did not
  write.
- [`docs/decisions/0022-names-the-store-cannot-own.md`](docs/decisions/0022-names-the-store-cannot-own.md)
  — recording `.DS_Store` and then opening the store in Finder destroyed the
  payload, because Finder writes a `.DS_Store` into every folder it displays.
  A payload is never filed under a name the store does not own, a file with
  such a name inside the store is somebody else's rather than content, and
  `init` writes a `skipped.txt` that keeps them out of a history that is
  append-only.
- [`docs/decisions/0023-what-an-amendment-keeps.md`](docs/decisions/0023-what-an-amendment-keeps.md)
  — the head, rewritten: the change, the author, and the moment the work was
  first recorded are copied, `revised` is stamped because amending is an act a
  person performs, and every tree fact is worked out again from the folder —
  keeping the file identifiers the amended revision minted, because the same
  file in the same place is not a different file. A revision something stands
  on is refused, since reparenting a descendant is 0007's merge under another
  name; and the position becomes the head nothing has rewritten, which is the
  rendering question 0001 left to whoever needed an answer.
- [`docs/decisions/0024-naming-a-file.md`](docs/decisions/0024-naming-a-file.md)
  — a file identifier is spelled `file:` where a path is expected, because
  0001's disjoint alphabets cannot partition a position that already holds
  every string a person may name a file; and a bookmark gains a third key,
  `file`, beside 0006's `change` and `revision`. That is the join an outside
  system gets: its own identifier cannot be Historica's, since digits would
  break the alphabets and 0008 mints rather than derives, but it can be the
  *name* of a bookmark, because a name is only ever a string.
- [`docs/decisions/0034-a-file-can-be-run.md`](docs/decisions/0034-a-file-can-be-run.md)
  — the executable bit, which 0008 left out for a narrow reason and `update`
  then destroyed: a file recorded runnable came back plain, silently, in
  somebody's own folder. `mode <file> <value>` carries one bit and spells it
  as a word; a filesystem that cannot see the bit says so rather than
  reporting `false`, which is what makes a store safe to carry between a Mac
  and a Windows machine without configuration; and it is `historica-v4`,
  claimed only by the documents that use it.
- [`docs/decisions/0036-where-a-digest-is.md`](docs/decisions/0036-where-a-digest-is.md)
  — identity coming from content is what left the store reading every file in
  `operations/` to find one digest, which 0035's cache could not help with
  because reaching the cache meant paying it first. A catalogue in `cache/`
  says where each digest is, believed only while the paths it names are the
  paths the directory holds, and a lookup still hashes what it reads. A
  catalogue that is missing, stale or wrong costs a pass over the directory
  and never an answer, which is 0003's promise; what a reader believes
  unread is which documents forget something, and `check` is excluded for
  exactly that reason.
- [`docs/decisions/0037-what-changed.md`](docs/decisions/0037-what-changed.md)
  — `diff`, and the one place this tool renders rather than prints. The shape
  is borrowed because the world already reads it, the hunks are the
  decomposition `record` would write rather than a second one, and the
  difference from every other tool's diff is 0008: a rename between two
  revisions is a fact rather than a resemblance, while a rename in the folder
  is not a fact at all and is not rendered as one.
- [`docs/decisions/0038-who-wrote-this-line.md`](docs/decisions/0038-who-wrote-this-line.md)
  — `blame`, and the vector 0012 already computed. Attribution is read out of
  the operations rather than recovered from the bytes, so there is nothing for
  `-w` or `--ignore-rev` to steer and no similarity threshold to argue with; a
  line keeps its author through a rename (0008) and through a merge that kept
  it (0032), and a line the store recorded as new is new even where a person
  would call it moved. With no target the folder is the right side, as in
  0037, and a line only the folder has is marked rather than attributed.
- [`docs/loro.md`](docs/loro.md) — the initial Loro evaluation, and the
  conditions that would reverse it.

## Development

CI is a program rather than a YAML file. Every job the workflow runs is one
entry in `xtask/src/main.rs`, and `cargo xtask ci` runs all of them locally, in
the same order, against the same commands:

```console
cargo xtask            # what the jobs are
cargo xtask ci         # all of them: fmt, clippy, test, msrv
cargo xtask clippy     # or one
```

Which is to say the underlying commands are still the underlying commands:

```console
cargo fmt --all --check
cargo clippy --workspace --all-targets -- -D warnings
cargo test
```

The corpus checks with tools that are already installed, which is the claim the
format exists to make:

```console
cd tests/corpus/revisions && shasum -a 256 -c MANIFEST
cd tests/corpus/operations && shasum -a 256 -c MANIFEST
cd tests/corpus/diffs && shasum -a 256 -c MANIFEST
cd tests/corpus/tree && shasum -a 256 -c MANIFEST
cd tests/corpus/whole && shasum -a 256 -c MANIFEST
cd tests/corpus/modes && shasum -a 256 -c MANIFEST
```

### Releasing

A release is a tag, the GitHub release cut from it, and a `cargo publish` run by
hand. `cargo xtask release` does the mechanical half — bump the version,
regenerate the changelog's unreleased region into a section under the new
version, commit both, tag — and stops there:

```console
cargo xtask changelog --write   # refresh the unreleased region
cargo xtask release minor       # bump, cut, commit, tag — locally
cargo xtask release minor --push
```

Without `--push` nothing leaves the machine, and the command prints the two
pushes it did not run. `.github/workflows/release.yml` is what the tag starts,
and it asks `cargo xtask release-notes` for the body rather than keeping its own
copy of the notes.

What the tag does not do is publish. crates.io is a separate `cargo publish` a
person runs, deliberately, because it is the only step here that cannot be taken
back: a GitHub release can be deleted and cut again, and a version number on
crates.io can never be reused, even after a yank.

The changelog's generated region needs [git-cliff]; `nix profile install
nixpkgs#git-cliff` or `cargo install git-cliff`. Its **Behavioural changes**
section is built from `Behavioural-change:` trailers on the commits themselves —
[`docs/CHANGELOG.md`](docs/CHANGELOG.md) says how to write one.

[git-cliff]: https://git-cliff.org
