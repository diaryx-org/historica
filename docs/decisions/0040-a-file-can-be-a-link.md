# 0040 — A file can be a link

0034 deferred this in one paragraph and named the shape of the answer:

> **Symlinks.** Still refused by name in the working copy, and still the right
> answer for now. A symlink is not a mode: it is a fourth kind of thing a tree
> entry can point at, beside lines and bytes, and it brings a target that is
> itself a path with its own escaping and its own security questions. It
> deserves its own decision, or none.

What has not held up is the blast radius of the refusal. `record` surveys the
whole folder, so one symlink anywhere in it refused the whole record — a
folder of prose with one `current -> 2026/august.md` in it was unrecordable,
and the refusal named a file the person may not remember making. Decision 0039
narrowed that to the paths a person names, which turns the refusal from a wall
into a pothole. This decision removes it: a link is a thing a folder holds,
and a tool that surveys folders should be able to write it down.

There are two kinds of link, and every other tool records them as one. A link
to a file *in this history* — `current -> 2026/august.md` — is a reference to
a thing the store knows by identity, and a path is 0008's least favourite way
to spell an identity: rename the target and git's symlink dangles, silently,
because what was recorded was a spelling rather than the fact. A link to
something *outside* — `config -> /etc/myapp`, a target on one machine — is
not a reference to anything the store knows; it is a string a person chose,
and the honest record is the string. This decision records each as what it
is.

## The decision

- **A link is a third kind of file, fixed at `add`.** 0017 fixed a file as
  lines or bytes for its whole life because they are different things to
  store. A link is a third different thing: no content to diff, no lines to
  merge, a target instead of either. Replacing a link with a real file is
  `drop` and `add` — it is a different thing, and pretending otherwise would
  give `edit` a case where the parent it counts positions into is a path to
  somewhere else.
- **`link <file ID> <target>` is a tree fact**, stated by the revision that
  adds the file — where `text` or `bytes` would have stated content — and
  restated by any revision that changes the target, exactly as `move`
  restates a path that changed. The target is the rest of the line. No
  operation documents, no payloads: one line of text lives where one-line
  facts live.
- **The target has two spellings, and the recorder chooses by resolution.**
  A target that resolves to a file in the tree is recorded as that file:
  `link <file ID> file:<file ID>` — 0024's spelling, in the format itself,
  for the same reason it exists in the CLI: a position that holds every
  string a person may name needs a prefix no digest or path is. Everything
  else — a target that escapes the folder, resolves to nothing tracked, or
  is absolute — is recorded verbatim: `link <file ID> <the string>`.
- **Resolution is lexical, against the tree, never against the
  filesystem.** The observed target is joined to the link's own directory,
  `.` and `..` are folded as text, the result takes 0033's NFC — it is now
  claiming to be a store path — and is looked up in the tree this revision
  states, so a target added by the same record resolves. Nothing follows
  anything: a chain of links resolves one hop, to the link entry that path
  names, which is itself a file with an identity. What lexical folding gets
  wrong — a `..` walked through a directory that is itself a symlink on
  some machine — is exactly the machine-dependence that makes such a target
  *outside* this history, and it is recorded verbatim, correctly.
- **An absolute target is recorded verbatim even when it lands inside.** A
  person who spelled `/home/adam/journal/notes.txt` said something about a
  machine, and rewriting it into a reference changes what the folder said.
  Portability is offered to the links that were already portable.
- **`update` materialises each spelling as itself.** A `file:` target
  becomes the relative path from the link's directory to the target's
  *current* path, in the host's own separators — so the link follows its
  target through every rename, which is the point — and a verbatim target
  becomes exactly its bytes. The round trip is stable: recording what
  `update` wrote resolves to the same identity, or the same string, and
  states nothing.
- **Concurrent targets resolve by lower digest, and are reported** —
  `move`'s rule, over the stated line whichever spelling it holds. A `drop`
  of the link concurrent with a retarget loses, as a drop does against an
  edit. And a rename of the *target* concurrent with anything at all is no
  contest: the reference is to the identity, so there is nothing to
  disagree about — the case every path-spelled symlink gets wrong, gone by
  construction.
- **This is `historica-v5`**, claimed only by a document carrying a `link`
  line, so a store with no links stays readable by every version 4 reader.
- **A filesystem that cannot see links may not record one changing.** Two
  methods join `Filesystem`, both defaulted:

  ```rust
  fn link_target(&self, path: &Path) -> io::Result<Option<String>>;
  fn set_link(&self, path: &Path, target: &str) -> io::Result<()>;
  ```

  `Ok(None)` from the default means *this filesystem does not model links*,
  and a recorder that gets `None` states nothing and leaves the recorded
  target standing — 0034's rule, doing the same work: two machines, one
  blind to the fact, must not take turns rewriting it.

## When the target is dropped

A reference is the one fact that can be made false by a fact about a
different file, so it gets the one rule this format has for that shape,
stated rather than discovered:

- **A revision may not drop a file while a `file:` link still names it.**
  `tree::apply` refuses it as it refuses an `edit` naming a file the tree
  does not hold. The recorder satisfies the rule without anyone's help: the
  survey sees the target's path resolve to nothing tracked, and restates the
  link verbatim — the spelling the folder holds at that moment — in the same
  revision as the `drop`. The dangling link a person actually has on disk is
  therefore recorded, as the dangling string it actually is.
- **A `drop` concurrent with a `file:` link naming it loses, and is
  reported** — the rule a drop already obeys against an edit, for the same
  reason: destruction yields to reference, and a person is told.

## What is never followed

The trait's standing rule — nothing follows a symbolic link — is not
relaxed; it is what makes this safe to build. The walk *reads* a link it
meets, with `link_target`, and never walks through it, so a link pointing at
`/` does not make the survey enumerate the machine. Resolution is a string
operation against the tree. `update` *writes* a link, with `set_link`, and
never opens what it points at, so a received store may say
`link kx.. ../../etc/passwd` and the only consequence is an honest symlink,
pointing where symlinks are allowed to point. Every write `update` performs
addresses the entry itself, never the entry's referent — the atomic-rename
path of 0026 included: a link is removed and remade, not written through.

## A host with no links

`update` on a filesystem whose `set_link` is the default refuses, naming the
links it cannot make and the reason. It does not write a plain file holding
the target — that invents content no revision stated, which git's
`core.symlinks=false` does and then explains forever — and it does not skip
them silently, because a folder that half-holds a head is what 0030 refuses.

## Refused at record, by name

A verbatim target that is not UTF-8 (this store is UTF-8 text), one holding
a newline (a header is a line), and one that itself begins `file:` (the one
string the two spellings cannot share a column with). All three are
vanishingly rare, all three name the file and the fix, and the third is
cheaper than an escaping scheme every reader would carry forever.

## Rejected alternatives

**A mode.** 0034 already said why not: a link is not a fact about a file, it
is a different kind of thing for an entry to point at.

**One spelling — always the path.** Every other tool's answer, and the
dangling symlink after every rename is its price. The store knows the
identity; recording the spelling instead is recording the shadow.

**One spelling — always resolve, and refuse what does not.** A folder with
`config -> /etc/myapp` in it becomes unrecordable, for a link that is doing
its job. The outside exists; the format should be able to say so.

**A payload holding the target.** A digest and a second file to store one
line the revision document carries itself.

**A kind that can change.** Git allows a path to alternate between file and
symlink and every tool downstream carries a case for it. Here the honest
spelling is cheap: `drop` the link, `add` the file, both facts recorded
against the things they are about.

## Consequences

- `Version::V5`, claimed by a `link` line and nothing else, raised by 0017's
  machinery.
- `tree::Entry` gains the third kind, holding `Reference(FileId)` or
  `Verbatim(String)`. `edit`, `text`, `bytes`, and `mode` addressed to a
  link are refused by name; `link` addressed to a non-link is too; a link
  has no executable bit to state. `drop` gains the dangling-reference
  refusal above.
- `TreeContest` gains the target contest and the drop-versus-reference
  contest, resolved and reported like their precedents.
- The recorder observes a new symlink as `add` + `link`, a retargeted one as
  `link` alone, a kind change as `drop` + `add`, and performs resolution at
  survey time — including the automatic verbatim restatement beside a
  `drop`.
- `status` and `diff` render a target change as what it is — one line,
  before and after, in whichever spelling is recorded; `diff` renders a
  `file:` target by the path it resolves to at that revision, beside the
  identity, since a person reads paths. `cat` on a link prints an error
  naming the target: there are no bytes, and inventing some would be a
  rendering.
- `history/format.txt` gains the line and both spellings, because a person
  hand-writing a revision document is the reader that file exists for.

## Deferred

**Hard links, sockets, and devices.** Not files, not history, not here.

**A `check` note for verbatim targets that escape the folder.** A true fact,
but a note on every `../` would mostly name build systems doing ordinary
things. If it earns its place it earns it later.

**Re-resolution on later records.** A verbatim link whose target later
*becomes* tracked stays verbatim until the link itself changes — the
recorder states facts on change, and silently upgrading a spelling is a
change nobody made. A person who wants the reference retargets the link,
or asks a future command to do exactly that, out loud.

## Since

The rule above says the recorder chooses by resolution, and left unsaid
what it resolves. It resolves what changed, and nothing else.

Materialisation runs at the parent before anything is looked up: the
recorded target, spelled the way `update` spells it, from where the link
sat. A folder holding exactly that string is a folder nobody edited, and
the recorded target stands — no `link` line, no fact, the same silence
0034 gives a mode on a machine that cannot see one. Resolution, and the
demotion to verbatim it can end in, happen only for a string that
genuinely differs from what was written there.

The case this was missing is the one the reference exists for. A record
that `--move`s the *target* leaves the link on disk spelling the old path,
because `mv` has never rewritten the links pointing at what it moved. That
old path resolves to nothing in the new tree, so resolving it recorded a
retarget onto a dead string — nobody's edit, stated as a fact, undoing
rename survival at the exact moment it was earning its keep. Nothing about
the tree asked for that: the reference is still true after the move, since
the file is still there, at a new path. The revision now states nothing
about the link, and the folder is briefly stale until `update` writes the
new spelling and prints the line — 0030's job, and the same answer it
gives a file whose bytes are right and whose mode is wrong.

The comparison is one comparison, so a verbatim target gets it too, which
is what makes the deferral above a rule rather than an omission: a
verbatim link whose target becomes tracked is a string nobody touched, and
is left alone by the same line of code that leaves a reference alone.

**The drop restatement takes precedence.** An unchanged string is an
unchanged fact only while the fact is one the resulting tree can hold.
Where the record drops the file a `file:` link names, "When the target is
dropped" is unweakened: the reference is about to be false, the folder's
string is restated verbatim in the same revision as the `drop`, and no
amount of not touching the link exempts it.
