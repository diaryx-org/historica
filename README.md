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

Content that no operation produced is decision 0017. A **payload** is a file
of bytes in the store carrying no format of its own: `text <file> <digest>`
names the lines a file is created with, `bytes <file> <digest>` names the
whole content of a file that has no lines, and both are stored beside the
documents they are not. So a created file is *itself* in the store rather
than a second copy with `+` down the left margin, and a photograph is a
photograph. A file is lines or bytes for its whole life, fixed when it is
added — which is what retired `add` with `edit`, the early spelling that
counted an edit's positions into a file that did not exist yet.

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
operation chain, one payload whole, or 0040's link, decided when the file was
added and never again, so an `edit` addressed to a photograph is refused by
name.

A link is a third kind of file, and it carries a target where the other two
carry content. Decision 0040 gives that target two spellings and lets the
recorder choose between them by resolution: a link to a file *in this history*
— `current -> 2026/august.md` — is recorded as `link <file> file:<file>`, a
reference to a thing the store knows by identity, so renaming the target leaves
it pointing at the same file and every other tool's symlink dangles silently.
A link to something *outside* — `config -> /etc/myapp` — is not a reference to
anything the store knows, so the honest record is the string, and it is
recorded verbatim. Resolution is lexical and against the tree, never against
the filesystem: the target is joined to the link's own directory, `.` and `..`
are folded as text, and the result is looked up in the tree the revision
states. Nothing follows anything, which is what makes writing links down safe —
a link pointing at `/` does not make the walk enumerate the machine. `update`
materialises each spelling as itself, a reference as the relative path to
where the target sits *now*; a folder that cannot hold links refuses by name
rather than writing a plain file holding the target. And a revision may not
drop a file while a `file:` link still names it: the recorder satisfies that
by restating such a link verbatim in the same revision, so the dangling link a
person actually has is recorded as the dangling string it actually is.

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
`history/skipped/` names — and a rule there covering a file the tree already
holds is refused, because the walk would stop offering the path and the next
record would spell a request for privacy as a deletion of the file it names.
A rule is four keys on two axes (0045, 0051): `skip <path>` and `skip <path>/`
name a file and a directory, `skip-name <name>` and `skip-name <name>/` match
one path component at any depth with `*` standing for any run of characters
in it, and `private` and `private-name` say the same things while keeping
their own text out of an `export`. A change ID is 96 bits from the operating system, an
author comes from a person's own configuration and is never guessed, and the
time is the clock in the offset the platform reports. Everything else is
observed by comparing the folder with the tree at the parent — including a
deletion, which is a fact rather than a heuristic, and including which kind of
file a new one is: valid UTF-8 with no NUL is lines, and everything else is
bytes. That last rule is the tool's rather than the format's, because a
recorder is allowed signals a format may not use. Only a rename has to be
stated, with `--move`, which performs it if the person has not.

A record can be told to look at some of the folder rather than all of it —
decision 0039, `record <path>...`, where a directory means the files under it.
What it narrows is what is *observed*: the paths left out are compared with
nothing, so nothing is recorded about them, they stay in the folder, and
`status` goes on listing every one of them. That is the whole difference
between this and an index, which holds a version of a file that is in neither
the folder nor the history and records a state that never existed. A named
path the folder no longer holds records the deletion, because absence is still
a fact; a path nothing answers to is refused, and so is a `--move` with one end
outside the restriction, since a restriction that spelled half a rename would
record the other half as a file appearing out of nowhere. A merge takes no
paths at all: 0032 has it state what every contested file is, and half of that
is a revision meaning something other than what it says.

The `fs` module is the folder itself, asked for rather than assumed. Everything
that persists anything goes through `fs::Filesystem` — nine methods an
implementation must provide, nothing that follows a symbolic link, and a
handful of defaulted ones on top that a folder may decline without losing
anything: whether a file can be run (0034), where a link points (0040), and
decision 0043's two, a size and a modification time, and a file handed over in
pieces rather than whole. Declining any of them is answering `None`, and the
consequence of `None` is always that a command reads what it would have read
anyway. `fs::Disk` is that trait over `std::fs`, behind the default `disk`
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

Decision 0043 is the same argument twice more. The folder gets a catalogue of
its own — `cache/working.txt`, a digest per tracked path with the size and the
modification time the directory reported when it was taken — believed per entry
while both numbers still stand, so `status` on a folder with a photograph in it
compares the digest 0017 already states with a digest nobody had to re-read the
photograph for. A file modified twice inside one tick of the filesystem's clock
is what git calls racily clean, and the guard is git's: an entry whose time is
not strictly older than the catalogue's own is unverifiable and its file is
read. A size and a time are what 0025 kept out of `Filesystem` on the grounds
that identity comes from content, and they are allowed back on the condition
that keeps the grounds intact — nothing here is ever an answer, only ever
whether an answer already worked out may be taken again, so a folder that
reports neither reads every file on every command and says exactly the same
things about it. The other half is that a payload read purely to be hashed is
no longer held: `prune`, `forget`, `receive`, `arrange`, the payload search,
and the catalogue itself take a digest in pieces, so a store of photographs
costs a buffer rather than a photograph. `check` is excluded from both, for the
reason it is excluded from everything in `cache/`.

What was left after both is the directory every command reads before it does
anything at all, which is decision 0058. Opening a store walks `revisions/` and
performs one read and one parse per file — a revision document holds the whole
of the graph, so `names` opened six hundred files to print four lines. The
bytes were never the cost: six hundred documents are 688 KB, which is a fifth
of a millisecond out of one file and nine milliseconds out of six hundred, or a
hundred and eleven from a cold page cache. So `cache/revisions.txt` holds those
documents verbatim, each behind a line stating its digest, its size, the
modification time the directory reported, and its path. Bytes rather than
facts, because a cache of parsed facts would be a second grammar for the
revision document and would have to be *believed*, where bytes can be hashed —
three tenths of a millisecond for the whole file, and the cheapest way there is
to make a cache incapable of inventing a history. An entry is taken when its
bytes hash to the digest it claims, when the directory still reports the size
and time it recorded, and when that time is strictly older than the file
holding it, which is 0043's racy rule unchanged; anything else is a document
this store opens. Nothing derived is written down — the heads, the ancestry and
the supersession are computed on every command exactly as before — so this is
where the documents come from rather than an index of what they say. What was
left after that was the parse, and decision 0061 is the answer that needed no
cache at all: a document's graph facts — `change`, `parent`, `supersedes` — are
the first three ranks of a key order the parser already enforces, so the
revision is a *prefix* of the document and the author, the moment and the whole
of the tree were being read by every command for almost none of them. Reading
the revision walks the same lines and holds them to the same rules about a
document's shape; what it sheds is the interpreting and the allocating, which
is two thirds of what a parse is — 9.3 µs a document against 3.1 on a store of
twenty files. So opening reads the
revision and holds the bytes, everything refusable without interpreting a value
is still refused there, and what a document *did* is parsed at the moment
something asks. Behind that sat a larger cost the measuring turned up: the
projection every command builds reached the graph through `to_revision`, whose
`id` is the digest of the document rewritten, so asking a store for its shape
re-serialised and re-hashed every document in it to arrive at the name each was
already filed under. A store now holds each revision beside the digest it was
read from. Alternating the binaries call by call: on six hundred revisions over
twenty files `status` falls from 48 ms to 27 and `names` from 14 to 11, and on
twenty-five hundred `status` from 201 to 112 and `names` from 50 to 34. What is
paid for it is `files` and `cat` at a head, which want the tree of every
revision they reach and so read a document twice — 13% to 20% more. What is
left largest is the one stamp per document that opening
performs, which is the hand-edit rule 0058 paid for deliberately, and it is
0061's deferral rather than its decision.

The `historica` binary is the front end decision 0006 said was owed. `init`,
`check`, and `arrange` are the three commands it names; `log`, `show`, `files`,
`cat`, and `names` read a store and render it; `status` reads the folder beside
it and says how the two differ; `update` makes the folder hold a head, writing
what the store records, removing what it does not, and touching nothing
unrecorded — decision 0030, which is also where checkout-to-the-past is
declined and the stored position it would need is refused for good. That
decision's one deferral is `update::plan_into`, which lays the tree at any
revision out in a directory holding nothing: the same plan and the same apply,
so a payload, a link and a mode arrive as themselves, with the head rule
replaced by the emptiness rule. It has no command, because what wanted it is a
caller building a working tree of its own — `Working::read` takes any root and
`record` takes the working copy as an argument, so a tool can lay a revision
out, let a person work in it, and record against that revision without the
folder beside the store ever moving. `receive`
combines another local store with this one, and `export <dir>` is the journey
in the other direction — a fresh repository written somewhere else, holding
the folder as one revision has it and the ancestry that leads there, which is
decision 0042 and the half 0029 said was missing. Nothing unrecorded and
nothing a `skip` rule names can appear in a copy that is assembled rather than
mirrored, and compressing the result is tar's job. The rules themselves do
travel — decision 0051, so a copy's first `record` does not offer to record
the recipient's build output — and the copy says how many private rules stayed
behind. So do the bookmarks, on the same argument, which is decision 0062: an
export is a replica and `receive` is its pull, so a name withheld comes
straight back the moment the copy meets its origin, and an exclusion binding
only where it is useless is a gap rather than a protection. What travels is
every bookmark not marked `private` whose target the copy holds — the second
test being `check`'s own, so that an export never opens a copy on a finding
its origin did not have — and a name that is a disclosure gets the axis
`skip` already has: a second line, `private`, since `fix-acme-layoffs` states
in its own filename the fact `private clients/acme-layoffs/` exists to
withhold. `export --files-only` is that command with the store left out —
decision 0060 — because a copy's ancestry is most of what it costs: exporting
the three-hundredth revision of a six-hundred-revision store writes 14 MB, of
which 13 is `history/`. It writes the same folder the full copy would, from
the same target through the same materialisation and the same travelling
rules, so the two agree byte for byte; what it does not write is anything to
record into, which is why it is for looking at a revision rather than working
on one, and why the directory it is given has to be empty. `record`
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
`history/names/` holds `file` lines beside `change` and `revision` ones, over
an optional second line saying `private` (0062), and
`cat <target> file:<bookmark>` is that file wherever it has since been moved to.
What `log` prints is narrowed by `--limit`, `--author`, `--grep`, `--since`,
`--until`, and `--path`; they compose, and `--limit` counts what the rest left
rather than what they were given. `--path` is where 0008 pays: the path is read
once, at one revision, and what the log follows is the *file* it named — so a
rename is not a break in a file's history and no heuristic is asked to guess
that it was one. A time bound is read in each revision's own offset, since
0002 leaves no shared instant here to compare against, and a bare `YYYY-MM-DD`
is that whole day there. `log <from>..<to>` narrows which revisions are on
offer in the first place, to everything behind `to` that is not behind `from`
(0063) — a subtraction of two ancestries, so it says the other side of a fork
as readily as the stretch along a chain, and the filters compose with it as
they compose with each other. `--fields` prints that same listing for something
that is not a person (0064): a `historica-log-1` header, then
`<digest> <change> <when> <marks|-> <parent>...` a line, spelled whole,
single-spaced and unescaped because no field there can hold a space. What it
leaves out is what a person wrote — `show` prints the document those live in,
byte for byte, so a listing that restated them would be a second answer that
could disagree with the first. Nothing there decides anything
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
opens as a picture. Both of those are filed under the revision's own year and
month — decision 0041 — so a journal kept for a decade is a hundred and twenty
folders rather than one listing of thousands, which is the thing a person
scrolls rather than opens; the filename keeps the whole date, so a file
separated from its folder still says when it is from. The month is read from
the revision's `when` as spelled, in the offset the author experienced, since
no part of a name may come from the clock the machine happens to have. Its rule
to keep is that two replicas must produce one set of filenames, so a collision
resolves by change ID and then by digest, never by a counter, which would
depend on what else was in the directory — and the month is the directory that
rule is now applied inside, which changes nothing about it. `arrange` is
what applies that scheme to a store that does not have it — one written by an
older version, by another tool, or by hand — and on a store this version wrote
it does nothing. What it will not do unasked is move a revision document out of
a folder somebody put it in: it renames one where it sits, because a revision
is one file with nothing for a directory to group, so a folder around one is a
statement. `arrange --refile` is the one that applies the month to those too,
and is how a flat store catches up. `operations/` is filed by the revision's
stem under both, since the directory there says which revision and which path
rather than anything a person chose. None of it is a lint: a name that differs
is usually a person filing their own history, which `check` has no business
calling a fault, and every fault `check` does report it finds in content. The
loader walks both directories to any depth and never follows a symbolic link,
which is what lets a person file a history however they please.

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

The rewriting half's wall — restating a descendant's operations against a
parent whose content moved is 0007's merge under another name — is decision
0059, walked through rather than around: `carry` restates work standing on a
rewritten revision against the rewrite, which is the state transport can
deliver and `check`'s note describes. Everything that describes the work is
copied and `revised` comes from the rewrite that caused it, so nothing is
stamped or minted and two replicas repairing one history write byte-identical
files. A file the rewrite did not touch is carried verbatim, naming the same
operation documents; one it did touch is restated through 0007's merge, the
delta between the two bases replaying concurrently with the descendant's own
operations — and where the two meet, the carry refuses whole, because
resolving concurrent work is a person's. What is still owed on top of the
primitive is the inline acts: amending or abandoning a revision that has a
descendant, and moving a change somewhere new, each a spelling question 0059
leaves open now that the machinery beneath all three is built.
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

The library is the same crate — `historica = "1.0"` in a `Cargo.toml` —
because the binary decides nothing the library has not, and every answer the
commands give is one a caller can ask for directly. It builds on stable Rust
1.88 or newer, which is the floor the `msrv` job holds it to, and it is MIT or
Apache-2.0 at the reader's choice: [`LICENSE-MIT`](LICENSE-MIT) and
[`LICENSE-APACHE`](LICENSE-APACHE).

### What 1.0 promises

Two things, and they are not the same promise.

The **format** promises what decision 0047 spells on line one. A document
headed `historica` parses under the grammar this version reads, and 0004's
rule holds inside it: a reader's vocabulary only ever grows, so a document
written today still parses. A format that cannot keep that takes a new
spelling — `historica-2` — rather than a number, and the pre-1.0 spellings
`historica-v0` through `historica-v5` are refused by name and never reused.
This is the promise that would be expensive to retract, which is why it is the
one 1.0 was cut for.

The **Rust API** promises ordinary semver, which before 1.0 it did not: a
change a caller would have to edit their own code for takes a 2.0, and the
smaller differences are written down as `Behavioural-change:` trailers, which
[`docs/CHANGELOG.md`](docs/CHANGELOG.md) collects under each release. That API
is also the whole of the plugin surface, by decision 0053: a tool built on
historica is an ordinary crate depending on it, and a fact the API does not
expose is a change to historica rather than a hole opened from outside.

Three things are outside both. `history/cache/` is disposable by decision 0003
and its contents are nobody's interface — deleting it changes how long a
command takes and nothing else. The exact wording a command prints is not an
API, though what it has to say is, since a person reads it and 0021 makes that
a design constraint. And `xtask` is this repository's CI rather than a
published thing, which is what `publish = false` says.

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
2025-08
$ ls history/revisions/2025-08
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
[`docs/decisions/index.md`](docs/decisions/index.md) lists every one of them
with a paragraph on what it decided and why, and
[`docs/loro.md`](docs/loro.md) is the initial Loro evaluation and the
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

The conformance suite searches randomly from a seed, and `cargo test` runs it
at a fixed one so that two runs are the same run. `cargo xtask test` rotates it
and echoes what it chose, so that CI looks somewhere new each time and a red run
can still be made red again:

```console
HISTORICA_CONFORMANCE_SEED=0x0007c04f0000f00d cargo test --test conformance
```

A failure prints that line for you, along with the failing round shrunk to the
fewest replicas and actions that still reproduce it.

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
