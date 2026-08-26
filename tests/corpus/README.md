# The corpus

The specification, executed. Every file here is hand-written rather than
generated, and each directory is read by one test that holds the parser, the
replayer, or the writer to it. A change to the format that this corpus does not
mention is a change nobody argued for.

Every directory has a `MANIFEST`, which is the claim the format exists to
make — that the tools already on the machine can check it:

```console
cd tests/corpus/revisions && shasum -a 256 -c MANIFEST
```

An `invalid/` directory holds files that must be refused, one per stated
reason, and the filename is the reason. A test that accepted one of them would
be a reader guessing at what it was leaving out, which decision
[0004](../../docs/decisions/0004-parser-contract.md) forbids.

| Directory | Read by | What it pins |
|---|---|---|
| [`revisions/`](revisions) | [`corpus.rs`](../corpus.rs) | the revision document |
| [`operations/`](operations) | [`operations.rs`](../operations.rs) | the operation document, and replay |
| [`tree/`](tree) | [`tree.rs`](../tree.rs) | a rename, told by two document kinds at once |
| [`whole/`](whole) | [`whole.rs`](../whole.rs) | payloads — content no operation produced |
| [`links/`](links) | [`links.rs`](../links.rs) | a file that is a link |
| [`modes/`](modes) | [`modes.rs`](../modes.rs) | the executable bit |
| [`merged/`](merged) | [`resolution.rs`](../resolution.rs) | what a merge records as its resolution |
| [`diffs/`](diffs) | [`diff.rs`](../diff.rs) | the choices the writer makes |

## `revisions/`

Seven files are a real five-change history containing a merge, an amendment by
a reviewer, and the rewrite that amendment forced. Nine more are invalid, each
for one stated reason. Decision
[0002](../../docs/decisions/0002-revision-document.md) is the argument.

## `operations/`

The other half of the same history. The numbered files are the edits the
numbered revisions made to one file, with a gap at `04` because a merge that
changes nothing about a file names no operation document. Four more pin rules
no revision happened to exercise — a carriage return inside an item, a file
whose last line has no terminator, a stated result, and items quoted verbatim —
and nineteen invalid ones are each refused for their own reason.

`states/` is that file as it stands at each revision, hand-written, which is
what the replayer is held to. Decision
[0007](../../docs/decisions/0007-content-and-merge.md) is the argument.

## `tree/`

A history of two files with a rename in it, and the first corpus where the
revisions and the operation documents describe one history together rather than
narrating the same one separately. Decision
[0008](../../docs/decisions/0008-tree.md) is the argument.

## `whole/`

Two revisions that file a photograph and the entry it belongs to, where the
entry's first content is the entry and the second revision's `edit` counts its
positions into what that payload produced. Five invalid files pin the grammar.
Decision [0017](../../docs/decisions/0017-content-that-arrives-whole.md) is the
argument.

`forgotten/` is that photograph destroyed: the document of two headers that
stands where the payload sat, and five invalid ones — a `length` with nothing
to forget, the two headers out of order, a `result`, a padded count, and a
body under a document that can have none. Dropping the stand-in in and
deleting the payload is what a replica receives, so the test assembles the
store by hand rather than running the command. Decision
[0066](../../docs/decisions/0066-forgetting-a-payload.md) is the argument.

## `links/`

Four revisions covering both spellings a link has — a reference to a file this
history knows, and a verbatim string for anything outside it — and the rule
that a revision may not drop a file a `file:` link still names. Seven invalid
files pin the rest. Decision
[0040](../../docs/decisions/0040-a-file-can-be-a-link.md) is the argument.

## `modes/`

Three revisions that make a file runnable and then plain again, and three
invalid files. Decision [0034](../../docs/decisions/0034-a-file-can-be-run.md)
is the argument.

## `merged/`

Five revisions forking and rejoining, with `states/` again as the hand-written
answer at each. What is pinned here is the resolution a merge *states* — which
items it kept and under whose names — rather than the content alone. Nine
invalid files pin the grammar of a `keep`. Decision
[0032](../../docs/decisions/0032-a-merge-states-its-resolution.md) is the
argument.

## `diffs/`

Four cases, each a `parent.txt`, a `child.txt`, and the `recorded.ops.txt` the
writer must produce for the pair: a replacement's anchor, a line that survives
between two changes, and a final newline gained and lost. These are the choices
a property test cannot see. Decision
[0009](../../docs/decisions/0009-diff.md) is the argument, and
[`examples/matchers.rs`](../../examples/matchers.rs) is the measurement it chose
the matcher on.
