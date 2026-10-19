# 0086 — A copy chooses its heads

[0029](0029-receiving-another-store.md) made several heads ordinary: "a receive
can create multiple heads. That is ordinary graph history; the existing merge
command decides whether to join them." That sentence was written for one
person's replicas meeting each other, and there it is right. It stops being
right the first time a store receives somebody else's work: a contributor's
line, an assistant's change set, a stranger's suggested fix. That work becomes
a head the moment it arrives, and three things follow from it being one.

- `record` and `update` stop knowing which head is the person's, and refuse
  until they are told ([0011](0011-working-copy.md),
  [0030](0030-the-folder-catches-up.md)). Receiving a suggestion breaks the
  ordinary path of the person who received it.
- `merge` joins "what is named, and every head that is not"
  (`cli/src/cli/record.rs`, the command as built). A bare
  merge accepts every contribution in the store, whether or not anyone read
  it.
- Accepting *part* of a contribution has no spelling. [0059](0059-carrying-a-descendant-across.md)
  deferred "duplicating a change", which is what cherry-pick would mean here,
  on the grounds that "wanting it is undemonstrated in a journal". A forge, and
  Diaryx's change sets, demonstrate it.

These are one problem, not three. The store knows which revisions exist and
how they stand on each other. It does not know, and cannot know, which of them
this copy *stands on*, because that is not a fact about history. It is a
choice made by whoever holds the copy, and a different holder of the same
bytes may choose differently.

## The decision

- **A tip is a fact about the store; a head is a fact about the copy.** A
  *tip* is a current revision that no current revision stands on. Tips are
  computed from the revisions alone, travel with them, and are what an offer
  lists. A *head* is a tip of the part of history this copy follows.
  Everything that asks "which line is the person's" (`record`, `update`,
  `merge`, `status` and every read that defaults to "the latest") asks about
  heads.
- **What a copy follows is a rule, not a record.** A rule is something that
  can be asked of one revision: does this copy follow it? Following a revision
  follows everything it stands on, so the followed part of history is closed
  under ancestry, and its heads are the followed revisions that nothing
  followed stands on. Nothing is stored. Heads are derived from the store and
  the rule every time they are asked for, so 0030's sentence holds: the
  folder as it stands and the store as it stands, and no third thing that can
  disagree with either.
- **The embedder supplies the rule.** The library takes it as a parameter
  wherever it asks for heads. Diaryx follows what a writer of the document
  signed. A forge follows what a maintainer's key vouched for, through
  historica-minisign. The CLI follows writers, as argued below.
- **A tip the rule does not follow is held.** Held work is shown, by
  `log`, `status` and the refusal that lists heads, as held and with its
  author and message, so a person can see what is waiting. It is never
  swept into anything.
- **Taking is the only way held work joins a head.** To take is
  `historica carry <held> --onto <head>`, 0059's human move, unchanged. It
  restates the work against the head, copies `change`, `author` and `when`,
  stamps `revised` and `revised-by` from the person taking it, and names the
  held revision on `supersedes`. The revision it writes stands on a head and is
  the copy's own, so it is followed, and it is the new head.
- **A supersession counts only when the copy follows the revision that states
  it.** A held revision that supersedes a followed one does not make the
  followed one stop being current, for this copy. This is what makes heads
  safe to derive from a store that strangers can write into, and is argued
  below.
- **`merge` joins heads.** Its targets must be heads. A held target is
  refused, and the refusal names the take. A bare merge joins every head,
  which is now every line the copy follows and nothing else, and 0029's
  sentence goes back to meaning what it was written to mean.

## Tips, and the revision that vanished

The current computation is "every revision nothing names as a parent, minus
every revision something supersedes" (`History::heads`, then
`current_heads` in `cli/src/cli/target.rs` and again in `src/update.rs`). It
subtracts the superseded *after* finding the childless, and that order loses
work as soon as a take is partial.

Take the tip `C` of a held line `A-B-C`, leaving `A` and `B` where they are.
`C'` stands on the head and supersedes `C`, so `C` drops out. `B` was never
childless, because `C` stands on it, so `B` was never in the set to begin
with. The untaken work is in the store, current, and in no list of anything.

Finding the childless among the *current* revisions fixes it: `C` is not
current, so nothing current stands on `B`, and `B` is a tip, held, exactly
what it is. Amending and squashing reach the same answers under either order,
because each leaves the superseded revision's parent with a current child,
the amendment or the squash. Abandoning supersedes nothing, since its
tombstone is a child. That is why the difference went unnoticed until now.

One case does change, and the change is the rule working. Move a revision off
its parent onto an unrelated line, `carry X --onto Y` where `X` stood on `P`
and nothing else does, and `P` is now a tip. Under the old order it vanished.
`P`'s work is in no line anyone stands on. The person may have meant to leave
it, and showing it costs them an `abandon`. Hiding it would cost the work
itself, with nothing in any list to say so. The same move with `P` among `Y`'s
ancestors changes nothing, because then `P` has a current child on the way
to `Y`. This is a `Behavioural-change:` on the commit that
builds it.

The fallback in both copies of `current_heads`, which returns every childless
revision when subtracting the superseded leaves nothing, is not needed under
the new order. A store whose revisions are all superseded has no current
revision, and one with any current revision has a current tip. Both copies
become one function in the library.

[0001](0001-identity.md) deferred "whether head discovery hides superseded
revisions", keeping the core "a pure graph question". This keeps the core
exactly that. `History` answers tips, and the rule that turns them into heads
lives in the layer that has a copy.

## Taking, whole and in part

Every take is 0059's carry with a person deciding, so the acts below are not
new commands. They are the one command aimed at different revisions.

- **The whole line** is a take of its first revision. 0059's move carries
  everything standing on the moved revision after it, so `A`, `B` and `C`
  arrive as `A'`, `B'` and `C'` on the head. Where nothing moved under them,
  the carry is verbatim and only the revision documents are rewritten.
- **A prefix** has no spelling of its own yet. Taking `A` writes `C'` as
  well, and `C'` is the taker's, so it is followed and it is the head. To
  keep only `A'` and `B'`, the taker then abandons `C'`. A spelling that
  writes only the prefix is the open question below.
- **One change from the middle or the top** is a take of that revision
  alone. It is restated through 0007's merge against the head: the delta
  from its old base to the head replays concurrently with its own
  operations, so it brings its own work and nothing from the revisions it
  stood on. A contested span refuses the whole take, as every carry does.

Taking keeps the change ID, and that is why it supersedes rather than
duplicating. "Is change `hx` in this line?" stays a question with an answer,
and on the contributor's side the supersession is what tells their copy that
the work was taken.

A take is a person's decision and reads the clock, so two people taking the
same held revision write two revisions of one change. That is 0001's
divergence, legitimate and shown. It is the same thing two people amending one
change would produce, and nothing new to teach.

## What the contributor's copy sees

The contributor receives the copy their work was taken into. What happens next
depends on their rule, and in both cases it is the right thing.

- **If they follow the copy that took it**, `A'` supersedes `A` for them. Any
  of their work standing on `A` that was not taken now stands on a
  superseded revision, which is the state `check` already notes and plain
  `historica carry` already repairs. The repair derives everything, so two
  contributors repairing one store write the same bytes. What the taker
  left behind lands on the taker's line, ready to be offered again.
- **If they do not**, `A'` is held for them, and supersedes nothing. Their
  own line is untouched until they take the taker's work or follow it.

## Why a supersession must be followed to count

Without this rule, the decision would hand any writer a way to hide someone
else's work. A change ID cannot be verified (0001: "any author can write a
revision claiming any change ID"), and neither can a `supersedes` line. A
revision superseding the maintainer's head, received from anywhere, would
make that head stop being current. The maintainer's line would disappear from
`record`'s and `update`'s view, with the stranger's revision held and the
maintainer's own work in no list. That is possible today, in any store that
receives from a stranger, and it is quiet.

Under the rule, a supersession is an act of the line that states it. It
takes effect in a copy that follows that line, and in no other. That is
also why taking works at all: the take is followed, so its supersession of
the held work counts, and the held work leaves the list of held tips.

Among held work, supersession counts as it always has. A contributor who
amends their offered change has written a successor to it, and the list of
held tips shows the successor. Nobody's line is hidden by that, because no
held revision is anybody's head.

## The rule, and what it is not

A rule is asked one question per revision and must be closed under ancestry,
which the library makes true rather than trusting the embedder to: the
followed set is the ancestry of every revision the rule accepts. A rule that
accepts a revision standing on unaccepted work has accepted that work too.
This is the same reading historica-minisign already gives a claim, which
"covers its whole ancestry".

A rule is not a permission. Historica still has none. A held revision is in the
store, readable by `log`, `show` and `cat`, and travels on in every export.
The rule decides only what this copy stands on, which is the one question
nobody but the copy's holder can answer. Whether the rule's answer is
*evidence*, a signature checked against keys this copy trusts, or a
convenience, an author's name that anyone could have typed, is the
embedder's to say, and 0005's warning about authorship applies to every rule
built on it.

## The CLI's rule: writers

The library cannot have a default the embedders share, because Diaryx's rule
and a forge's are different. The CLI needs one, and it follows writers.

- **A revision's writer** is its `revised-by`, and its `author` when it has
  none ([0002](0002-revision-document.md), [0005](0005-authorship.md)). That
  is the name of whoever wrote these bytes, not whoever began the change, so a
  take is the taker's and a contributor's amendment of their own offer is
  theirs.
- **The copy follows its own identity**, the author `record` would write in
  this folder ([0010](0010-writer.md)), with `HISTORICA_AUTHOR` and the
  per-directory blocks of the identity file applied exactly as `record`
  applies them. The block that names that author may also list `follow`
  lines, one name each, for the other people whose work this copy stands on
  without being asked: a second device under another name, a co-author. The
  file never travels, so this choice stays the copy's.
- **Everything else is held.**
- **With no identity configured, every tip is a head.** That is today's
  behaviour with the vanished-revision fix, and it is the CLI's
  `Following::Everything`. A person who has not said who they are cannot be
  told apart from anyone else, and nothing they receive is held from them.
- **`record --onto <held>` is refused**, and the refusal names the take.
  Recording onto held work would make it the ancestry of the person's own
  revision, which is the unrewritten join that merging held work is rejected
  for below.

Its cost is stated here so that nobody mistakes it. A name is a claim, not
evidence (0005). A stranger who writes the person's own name as `author` is
followed, and their revision is a head like any other. What this rule
protects against is sweeping in what one did not mean to, and it protects
against no one who will type a name. Protection against bad faith is a key:
historica-minisign's rule follows what keys in `trust/` vouched for, and is
the rule a forge and anyone receiving from strangers should use. Keys stay
out of the core CLI ([0046](0046-who-vouches-for-a-revision.md)).

Three rules were available. *Everything* is kept as the fallback above, and
*keys* is historica-minisign's. *Authors*, a file of its own or a fifth key in [0051](0051-two-axes-for-a-rule.md)'s closed set, became the
identity file the person already has, so the rule asks them to configure
nothing new.

## Rejected alternatives

**A stored set of followed heads.** A file in `cache/`, written when
`record` makes a head and when a person accepts one. It is simple, and it is
0030's third thing exactly: a position, under another name, that can
disagree with the store. A copy restored from backup or synced by a tool
would follow what the file says rather than what the store holds. 0044 shows
the kind of fact `cache/` may hold safely, one whose worst failure is a
misfiled severity. Which line a person records on is not that kind of fact.

**Heads under bookmarks.** A bare merge that skips a head under someone
else's bookmark. Bookmarks travel (0062), so the contributor's bookmark would
decide what the maintainer's merge skips, and a contributor who leaves their
work unnamed would have it swept in. It moves the choice to the wrong party.

**Duplicating instead of superseding.** 0059's deferred act, cherry-pick with
a fresh change ID and no `supersedes`. It leaves the held work standing as a
held tip after it has been taken, and it severs the change ID, the one link
by which either side can tell that the work arrived. It stays deferred, now
without a use.

**Merging held work.** Letting `merge` name a held tip, as it names a head.
A merge revision would stand on the held line, so the contributor's revisions
would enter the followed ancestry unrewritten, under the contributor's name
and without the taker's. Taking restates the work as the taker's act and
leaves the contributor as its author. That is the distinction a reviewer
needs, and a merge cannot draw it.

**Receive holding, by a flag.** `receive --hold` for strangers and plain
`receive` for one's own replicas. Which work was received how is not in the
store, so this needs the stored set above, and it puts the choice at the
moment of transport, before anyone has read what arrived.

## Open question

**Taking a prefix without writing the rest.** `carry <first> --onto <head>`
carries the whole line, and a prefix is then an `abandon` of the remainder's
take. A `<first>..<last>` target, 0063's range, would say it in one act. The
carry planner already moves a line; stopping it early is the open part.

## Deferred

**Declining held work.** `abandon` writes a tombstone that travels, which
would end the contributor's line in their own copy as well as hiding it here.
Declining is a fact about the copy that declines, as Diaryx already treats
it (pedantic's `Dismissed`). Until historica has a spelling for it, held work
stays held, and an embedder hides what it has declined.

**Trying held work in the folder.** `update` gives the folder only heads
(0030), so a held line cannot be put there to be built or run. Taking it into
a scratch copy is the spelling today. Whether the folder may hold a held tip
without reopening 0030 is its own question.

**Taking a merge.** 0059's carry refuses to move a merge revision, so a held
line with a merge in it is taken around the merge or not at all.

## Consequences

- `History` gains `tips`, computed over current revisions. `History::heads`
  stays the pure graph question, every revision nothing names as a parent,
  superseded ones included, and is renamed `childless` so that no caller
  mistakes it for this document's heads. The offer an export writes keeps
  asking it, because a listing answers relatedness rather than rendering
  (`Store::offer`), so the offer's bytes do not change. `check`'s rule
  coverage and `skip`'s keep asking it too: a path held by any revision is a
  path a rule cannot cover.
- `src/following.rs` holds the rule's trait, the closure under ancestry, the
  supersession that counts, and the one `heads` the library and CLI share.
  `update::plan`, `carry`, `merge` and every target resolution take a rule.
  `Following::Everything` is the rule that reproduces today's answers.
- Heads cost nothing until they are asked for. `receive` does not consult the
  rule. Heads are found by walking down from the tips and stopping at the
  first followed revision on each path, so only unfollowed revisions are read
  in full, through the lazy parse, and 0061's fast causal read stays the path
  everything else takes. `core::Revision` is not widened with authorship
  until a measurement asks for it.
- The identity file gains the `follow` key, and `Identities` answers the
  followed names for a directory beside the author it already answers.
- The CLI's `current_heads`, `the_head` and `read_at`, and `src/update.rs`'s
  copy of `current_heads`, become calls to that one function.
- Rendering marks held tips as held, beside heads, in `log` and in every
  refusal that lists heads.
- 0001, 0029 and 0059 gain a `## Since` naming this document: 0001's head
  discovery deferral is answered, 0029's multiple heads are qualified to the
  lines a copy follows, and 0059's duplicating a change keeps its deferral
  for the reason above.
- Tests worth naming: a partial take leaves the untaken revisions as one held
  tip; a stranger's revision superseding the head leaves the head current and
  the stranger's revision held; a contributor who follows the taker, running
  plain `carry`, writes the same bytes as a second contributor doing the same;
  a bare merge in a store holding a received contribution joins nothing it
  did not join before; and under `Following::Everything` every existing test
  passes unchanged.
