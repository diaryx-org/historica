# The command line

`historica help` prints what every command takes, and is the authority on
that. This document is the other half: why each command is the shape it is.
Each section names the decision that argued it, and
[`docs/decisions/index.md`](decisions/index.md) is the full list.

The binary decides nothing the library has not. Every answer a command gives
is one a caller can ask for directly, and where the library refuses — a merge
it will not order arbitrarily, a head it will not choose between — the command
refuses in the library's own words rather than picking for you.

## Targets and paths

A target is `head`, a bookmark, a change ID, or a revision digest, and the last
two may be abbreviated to any unambiguous prefix. Decision
[0001](decisions/0001-identity.md) gives changes and digests disjoint
alphabets, which is what lets one argument position accept either without a
flag saying which was meant.

The position beside it names a file, and there the alphabet trick does not
reach: a path is a value a person chose rather than a name the tool minted, and
a file may legitimately be called `kxryzmorwlvtnsqpkzmuprys`. So a file
identifier is spelled `file:`, a bookmark can hold one
([0024](decisions/0024-naming-a-file.md)) abbreviating to any prefix unique
among the files at that revision, and `path:` says the rest is a path for the
file whose own name begins `file:`.

## Reading a store

### `log`

The history, newest first, narrowed by `--limit`, `--author`, `--grep`,
`--since`, `--until`, and `--path`. They compose, and `--limit` counts what the
rest left rather than what they were given.

`--path` is where [0008](decisions/0008-tree.md) pays: the path is read once,
at one revision, and what the log follows is the *file* it named — so a rename
is not a break in a file's history and no heuristic is asked to guess that it
was one.

A time bound is read in each revision's own offset, since
[0002](decisions/0002-revision-document.md) leaves no shared instant here to
compare against, and a bare `YYYY-MM-DD` is that whole day there.

`log <from>..<to>` narrows which revisions are on offer in the first place, to
everything behind `to` that is not behind `from`
([0063](decisions/0063-a-range-of-revisions.md)) — a subtraction of two
ancestries, so it says the other side of a fork as readily as the stretch along
a chain, and the filters compose with it as they compose with each other.

`--fields` prints that same listing for something that is not a person
([0064](decisions/0064-a-listing-for-something-that-is-not-a-person.md)): a
`historica-log-1` header, then `<digest> <change> <when> <marks|-> <parent>...`
a line, spelled whole, single-spaced and unescaped because no field there can
hold a space. What it leaves out is what a person wrote — `show` prints the
document those live in, byte for byte, so a listing that restated them would be
a second answer that could disagree with the first.

### `show`

One document as stored, byte for byte, because the readable file is the
authority and a rendering of it is not.

### `files` and `cat`

The file set at a revision, and one file's content there. Both refuse a history
with a merge in it rather than ordering it arbitrarily — the library's refusal,
in the library's words.

### `status`

Reads the folder beside the store and says how the two differ.

### `diff`

What changed — the folder against the position, or what a revision did.
Decision [0037](decisions/0037-what-changed.md) makes it the one command that
renders rather than prints, in the unified shape every other tool already
reads.

What separates it from every other tool's is [0008](decisions/0008-tree.md):
two revisions carry file identifiers, so a rename between them is *stated*,
with the edit that came with it underneath, where a similarity heuristic would
have guessed and missed. The folder gets the opposite treatment for the
opposite reason — it holds paths and no identifiers, so a rename there is a
drop and an add until somebody says `--move`, and rendering it as a rename
would invent a fact `record` would decline to write down.

The hunks are `crate::diff`'s own decomposition rather than a second one, so
what a person is shown and what recording would state are one answer.

`--color` is `auto`, which is a terminal and nothing else and which `NO_COLOR`
settles; decorated, the ± lines carry the changed words inside them in inverse
video, which is a decoration of lines `crate::diff` has already chosen rather
than a second opinion about them. Undecorated, every escape is the empty
string, so a pipe gets the bytes it got before there was a flag.

### `blame`

The same trick applied to the other question — who wrote each line — and
decision [0038](decisions/0038-who-wrote-this-line.md) makes it the one command
every other tool has to guess at and this one does not.

A revision records the items it *inserted* and a merge records which items it
*kept* and under whose names, so `merge::Merged::origins` has said which
revision wrote each item since [0012](decisions/0012-conflicts.md) needed it to
label a contested span, and the command is that vector printed.

A line therefore keeps its author through a rename, since
[0008](decisions/0008-tree.md) makes a file one file for its whole life, and
through a merge, since
[0032](decisions/0032-a-merge-states-its-resolution.md)'s resolution keeps
items under their own names rather than restating them — so a merge authors
only the lines somebody typed into it, which is exactly what a three-way merge
cannot say.

### `names` and `name`

`name` writes a bookmark, and takes the third argument `show` takes: with a
path it names the file at that path rather than the work, so `history/names/`
holds `file` lines beside `change` and `revision` ones, and
`cat <target> file:<bookmark>` is that file wherever it has since been moved
to ([0024](decisions/0024-naming-a-file.md)).

A bookmark carries a second line saying `private`
([0062](decisions/0062-two-axes-for-a-bookmark.md)), because
`fix-acme-layoffs` states in its own filename the fact
`private clients/acme-layoffs/` exists to withhold.

### `skip`

Writes the rule saying what recording does not take. A rule is four keys on two
axes ([0045](decisions/0045-one-rule-to-a-file.md),
[0051](decisions/0051-two-axes-for-a-rule.md)): `skip <path>` and
`skip <path>/` name a file and a directory, `skip-name <name>` and
`skip-name <name>/` match one path component at any depth with `*` standing for
any run of characters in it, and `private` and `private-name` say the same
things while keeping their own text out of an `export`.

A rule covering a file the tree already holds is refused, because the walk
would stop offering the path and the next record would spell a request for
privacy as a deletion of the file it names.

## Writing a store

### `record`

The writer [0010](decisions/0010-writer.md) and
[0011](decisions/0011-working-copy.md) specify. The folder beside the store is
what it is given: everything in it tracked except what `history/skipped/`
names.

A change ID is 96 bits from the operating system, an author comes from a
person's own configuration and is never guessed, and the time is the clock in
the offset the platform reports. Everything else is observed by comparing the
folder with the tree at the parent — including a deletion, which is a fact
rather than a heuristic, and including which kind of file a new one is: valid
UTF-8 with no NUL is lines, and everything else is bytes. That last rule is the
tool's rather than the format's, because a recorder is allowed signals a format
may not use — and being the tool's is what makes it overrulable: `--bytes
<path>` and `--lines <path>` say which kind a file being added is, for the
paths where a person knows better than the sniff. A lockfile or a minified
bundle is text nobody wants line-merged; a file of UTF-8 holding a NUL is lines
the sniff cannot tell from a photograph. The format's own rule is not
overrulable, so `--lines` on bytes that are not UTF-8 is refused: an item is
text. And since a kind is fixed when a file is added, stating one for a file
the history already holds is refused too, naming the `drop` and `add` that
would change it. Only a rename has to be stated, with `--move`, which performs
it if the person has not.

`record <path>...` looks at some of the folder rather than all of it —
decision [0039](decisions/0039-recording-some-of-the-folder.md), where a
directory means the files under it. What it narrows is what is *observed*: the
paths left out are compared with nothing, so nothing is recorded about them,
they stay in the folder, and `status` goes on listing every one of them. That
is the whole difference between this and an index, which holds a version of a
file that is in neither the folder nor the history and records a state that
never existed.

A named path the folder no longer holds records the deletion, because absence
is still a fact; a path nothing answers to is refused, and so is a `--move`
with one end outside the restriction, since a restriction that spelled half a
rename would record the other half as a file appearing out of nowhere.

A merge takes no paths at all:
[0032](decisions/0032-a-merge-states-its-resolution.md) has it state what every
contested file is, and half of that is a revision meaning something other than
what it says.

### `merge` and `record --merge`

Decision [0012](decisions/0012-conflicts.md) keeps nothing conflicted in the
format — two heads already are the conflict, and
[0007](decisions/0007-content-and-merge.md)'s walk recomputes it from the same
files on every machine — so a contested span is rendered into the working copy
between marker lines, with each run inside it labelled by the revision that
wrote it.

`historica merge` writes that view and prints the command that records it. What
it joins is what is named and every head that is not, so divergence — the state
the command exists for — needs no argument at all, and the command it prints
back names every head it joined rather than only the ones a person typed.

`record --merge` recomputes the merge, refuses while any line the renderer
wrote still stands in a contested file, and otherwise diffs the folder against
*the merge result*, so what it records is exactly the resolution. Detection is
per line and scoped to a merge record, which is why this repository can hold a
decision document full of marker lines and record it without complaint.

Two files claiming one path is the other thing a merge cannot resolve on its
own, and there the command printed carries the `--at` that settles it — naming
the path the merge wrote each file to, so following it records the folder as it
stands, and any other path may be typed in its place. The file written beside
the one that keeps the path is named for the reason rather than by a counter,
with the marker in front of the extension so it still opens in the editor that
would have opened it, and with no character on it that a Windows filesystem
would refuse.

A file of bytes takes the same route and stops at the merge:
[0008](decisions/0008-tree.md) makes two concurrent `bytes` a divergence to
report, and there is nothing to render between marker lines in a JPEG, so
`merge` names the contested path, prints the command that fetches each side,
and leaves the folder alone. For that one case the tool cannot tell a
resolution from an oversight, which is said out loud rather than papered over.

### `update`

Makes the folder hold a head, writing what the store records, removing what it
does not, and touching nothing unrecorded — decision
[0030](decisions/0030-the-folder-catches-up.md), which is also where
checkout-to-the-past is declined and the stored position it would need is
refused for good.

That decision's one deferral is `update::plan_into`, which lays the tree at any
revision out in a directory holding nothing: the same plan and the same apply,
so a payload, a link and a mode arrive as themselves, with the head rule
replaced by the emptiness rule. It has no command, because what wanted it is a
caller building a working tree of its own — `Working::read` takes any root and
`record` takes the working copy as an argument, so a tool can lay a revision
out, let a person work in it, and record against that revision without the
folder beside the store ever moving.

### `amend`

The rewriting half starts at the tip, which is decision
[0023](decisions/0023-what-an-amendment-keeps.md). `amend` writes a revision
superseding the head: the change, the author, and the moment the work was first
recorded are copied, `revised` is the clock now because a person asked for
this, and everything the folder says is worked out again by the survey `record`
already does — including the identifiers the amended revision minted, kept by
path, so the same file in the same place does not become a different file every
time the work is rewritten. The rename it recorded is inherited, because a
recomputation cannot observe one.

A revision something has already replaced is refused, and the superseded
revision stays exactly where it was, because with no operation log here it is
the whole of the undo. The position a command works from becomes the head
*nothing has rewritten*, which is decision
[0001](decisions/0001-identity.md)'s rendering question answered at the moment
it first has an answer that matters.

A revision something *stands on* takes a message and nothing else, which is
decision [0059](decisions/0059-carrying-a-descendant-across.md)'s reword. The
folder states the head's content and can state no other, so surveying it
against a middle revision's parents would squash the whole stack into that
revision — a different act wearing this one's flag. So `amend <target> -m` is
what a middle revision takes, `--move` is refused there by name, and a bare
`amend <target>` refuses with the flag that works: the store explains itself
down to the spelling. Everything the reworded revision stated it states
again, so what stood on it is carried onto the new message verbatim — the
same operation documents, named again, and the store gains none. Content-
editing the middle waits on 0030's working forward from the past, where it
has always lived.

### `abandon`

Decision [0013](decisions/0013-abandoning-and-pruning.md)'s other tip-first
command: a tombstone of a newly minted change supersedes a head, or a run
ending at one, records nothing, and carries the one message this format
requires — the reason is the only thing it has. The content falls out of the
ancestry, so nothing is undone.

`--only` abandons the one revision and carries what stood on it onto the
tombstone, which is decision
[0059](decisions/0059-carrying-a-descendant-across.md). The unflagged sentence
is untouched — *this revision and everything standing on it* — because a
person who learned it would otherwise destroy or preserve the wrong work on
the strength of a silent change. What `--only` costs is that the descendants'
base genuinely moved: the abandoned work left the ancestry, so files it
touched are restated, and a descendant that edited what it introduced is a
contested span. The refusal names the work still standing on what is being
abandoned, which is the fact a person wants before they mean it, and the
store is left as it was found.

### `carry`

The rewriting half's wall — restating a descendant's operations against a
parent whose content moved is [0007](decisions/0007-content-and-merge.md)'s
merge under another name — is decision
[0059](decisions/0059-carrying-a-descendant-across.md), walked through rather
than around.

`carry` restates work standing on a rewritten revision against the rewrite,
which is the state transport can deliver and `check`'s note describes.
Everything that describes the work is copied and `revised` comes from the
rewrite that caused it, so nothing is stamped or minted and two replicas
repairing one history write byte-identical files. A file the rewrite did not
touch is carried verbatim, naming the same operation documents; one it did
touch is restated through 0007's merge, the delta between the two bases
replaying concurrently with the descendant's own operations — and where the two
meet, the carry refuses whole, because resolving concurrent work is a person's.

`--onto <destination>` is the same restating with a person deciding where.
It is one command rather than two because there is no second primitive in it:
same machinery, same refusals, and only the provenance differs — which is the
pair of rows 0010 already wrote. Without `--onto` a rewrite the store holds
decided and everything derives; with it a person did, so the revision named
takes a reading of the clock and the stack above it derives from *that*, so it
converges exactly as a repair's does. A destination among what would move is
refused, since the result would stand on a revision the act supersedes; so are
a merge, whose parents' agreement would have to be worked out afresh, and a
revision already standing where it was asked to stand.

There is no `move` command, because `--move <old>=<new>` already means
renaming a file and one word cannot mean both. There is no `rebase` either:
it is another tool's word for a guarantee this does not make, that one leaves
markers in a folder for a person to fix where this refuses whole.

### `prune`

[0013](decisions/0013-abandoning-and-pruning.md)'s disk half: it deletes
exactly a revision document that is superseded and orphaned and a content
document nothing kept names, prints every file, and refuses a store `check`
calls broken. It is local, manual, not secrecy, and the undo history, all four
of which 0013 says in as many words.

### `forget`

For the sentence a person cannot rotate, decision
[0014](decisions/0014-forgetting.md) is `forget`: destroy the payload, preserve
the shape. A forgetting document names the digest whose bytes were destroyed,
states the same operations at the same positions with the same counts, and
stands a `\ forgotten` marker where each destroyed item stood — so a redacted
history materialises and merges byte for byte outside the forgotten runs.

An item forgotten once is forgotten everywhere it is quoted, the deletes that
quoted it back included, and two redactions union to the more thorough one in
either arrival order. What forgetting cannot hide it says out loud: shape,
position, paths, and the revision around it all stay. A store that has
forgotten something can prove its structure and not its content — the `shasum`
claim the README makes becomes conditional at that moment, and only then — and
a store that has forgotten nothing is unaffected, which is nearly all of them.

A file of bytes is forgotten **without `--lines`**, because it has none to
name: decision [0066](decisions/0066-forgetting-a-payload.md) destroys the
payload whole and leaves a document of two headers where it sat, saying which
digest went and how many bytes it held. Which spelling a path takes is not a
choice — a file's kind was fixed when it was added — so asking for the other
one is refused, by name, with the one that would have worked. Two things a
person should hear before running it: a file of bytes is replaced whole, so
each version of it is its own payload and is forgotten on its own; and a
forgotten payload cannot materialise at all, so `update` refuses the file
until a revision records the `drop` that says it is gone.

### `identity`

Says who is writing. An author comes from a person's own configuration and is
never guessed ([0005](decisions/0005-authorship.md)).

## Moving a store

### `receive`

Combines another local store with this one.

### `export`

The journey in the other direction — a fresh repository written somewhere else,
holding the folder as one revision has it and the ancestry that leads there,
which is decision [0042](decisions/0042-a-copy-to-take-away.md) and the half
[0029](decisions/0029-receiving-another-store.md) said was missing.

Nothing unrecorded and nothing a `skip` rule names can appear in a copy that is
assembled rather than mirrored, and compressing the result is tar's job.

The rules themselves do travel — decision
[0051](decisions/0051-two-axes-for-a-rule.md), so a copy's first `record` does
not offer to record the recipient's build output — and the copy says how many
private rules stayed behind. So do the bookmarks, on the same argument, which
is decision [0062](decisions/0062-two-axes-for-a-bookmark.md): an export is a
replica and `receive` is its pull, so a name withheld comes straight back the
moment the copy meets its origin, and an exclusion binding only where it is
useless is a gap rather than a protection. What travels is every bookmark not
marked `private` whose target the copy holds — the second test being `check`'s
own, so that an export never opens a copy on a finding its origin did not have.

`export --files-only` is that command with the store left out — decision
[0060](decisions/0060-the-copy-without-the-history.md) — because a copy's
ancestry is most of what it costs: exporting the three-hundredth revision of a
six-hundred-revision store writes 14 MB, of which 13 is `history/`. It writes
the same folder the full copy would, from the same target through the same
materialisation and the same travelling rules, so the two agree byte for byte;
what it does not write is anything to record into, which is why it is for
looking at a revision rather than working on one, and why the directory it is
given has to be empty.

### `offer` and `fetch`

`offer` lists the transferable files of a published copy for a reader that
cannot list the directory it is fetching from — decision
[0056](decisions/0056-listing-what-it-cannot-read.md). It writes nothing;
redirect it beside the copy, as `offer.txt`, after the `export` that made it.

`fetch` takes what a published copy holds and this store lacks, adding history
and stopping — `update` is the folder's catch-up. Decision
[0048](decisions/0048-asking-for-what-is-missing.md) puts the transport in the
binary rather than the library: the library does the whole of the algorithm
through a `Source` that answers one question, and what the binary adds is that
question over HTTP.

It is behind a feature, and decision
[0057](decisions/0057-the-stack-a-fetch-rides-on.md) argues the stack: linking
the platform's own HTTP puts a fetch on the TLS roots, the proxy configuration
and the security updates the machine already maintains, where shelling out to
`curl` would put it on whatever binary of that name happens to be first on
`PATH`. A build without the feature is a CLI without a `fetch`, which is what a
`wasm32-wasip1` build is.

## Keeping a store readable

### `init`, `check`, `arrange`

The three commands decision [0006](decisions/0006-store-questions.md) named.

`check` reads a store without loading it and separates errors, which mean the
store contradicts itself, from notes, which never fail. It exits non-zero only
when the store cannot be trusted, so it can be run in anger; a duplicate, an
undelivered parent, or a sync tool's conflicted copy is a note.

What those notes leave a person to work out is what they cost, and the cost is
not the count: one undelivered payload under the root makes every file after it
unreadable, while ten in a branch nothing stands on cost nothing. So `check`
says the consequence as well as the symptom — which heads this store holds the
history of and cannot produce — and `check --complete` is the caller who wants
that to fail, being a sync that should have finished or a backup about to be
trusted. It is still not an error: the store contradicts nothing, and the
readable files are simply not all here yet.

`arrange` is the library's rather than the front end's — decision
[0025](decisions/0025-the-folder-is-asked-for.md) — so a host that syncs a
store gets the readable folder for the same reason a person does.

The naming scheme is `crate::naming`, and both the writer and `arrange` use it,
which is what makes them agree: revisions are `YYYY-MM-DD summary.rev.txt`
([0019](decisions/0019-the-name-a-store-is-written-with.md)), so the file a
person double-clicks opens in the editor they already have, and each revision's
operation documents and payloads sit under a directory of the same name, at the
path they had — as real directories, so a revision's folder is the subtree of
the repository that revision touched and `notes/photo.png` inside it opens as a
picture.

Both are filed under the revision's own year and month — decision
[0041](decisions/0041-where-a-revision-is-filed.md) — so a journal kept for a
decade is a hundred and twenty folders rather than one listing of thousands.
The filename keeps the whole date, so a file separated from its folder still
says when it is from. The month is read from the revision's `when` as spelled,
in the offset the author experienced, since no part of a name may come from the
clock the machine happens to have. Two replicas must produce one set of
filenames, so a collision resolves by change ID and then by digest, never by a
counter, which would depend on what else was in the directory.

`arrange` applies that scheme to a store that does not have it — one written by
an older version, by another tool, or by hand — and on a store this version
wrote it does nothing. What it will not do unasked is move a revision document
out of a folder somebody put it in: it renames one where it sits, because a
revision is one file with nothing for a directory to group, so a folder around
one is a statement. `arrange --refile` applies the month to those too, and is
how a flat store catches up.

None of it is a lint: a name that differs is usually a person filing their own
history, which `check` has no business calling a fault, and every fault `check`
does report it finds in content.

## What a refusal says

A refusal that turns on a person having to choose a head says which heads those
are in the terms they would recognise — the change, any bookmark, who wrote it,
when, and what it says — because a digest is the one thing about a revision
that says nothing about which line of work it is.
