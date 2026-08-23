# Changelog

What has changed in historica, release by release, for someone deciding whether
to move to a newer one.

Two halves, written two different ways.

The bulleted groups below — **Added**, **Fixed**, **Changed**, and a
**Behavioural changes** section under them — are **generated** from the commit
log by `cargo xtask changelog --write`, which reads `.config/cliff.toml`.
Anything inside a `git-cliff:begin` / `git-cliff:end` pair is rewritten on every
run, so an edit made there is an edit thrown away.

Everything else is handwritten and stays: this prose, and any intro a release
needs under its own heading, below the end marker where regeneration cannot
reach it.

**Behavioural changes** are collected from `Behavioural-change:` trailers on the
commits themselves, not from their subjects — because "would a reader who
upgrades without editing a line of their own code observe a difference" is a
judgment about the change that no subject can carry. Write one trailer per
observable difference, as prose someone can act on:

```
add(store): write `.rev.txt` and `.ops.txt`, and read the older names forever

Behavioural-change: A revision file is written as `.rev.txt`. Stores written
  before this keep their old suffixes and are still read; nothing has to be
  migrated.
```

historica has not been released. The first `## vX.Y.Z` heading below covers
every commit since the beginning, including the thirty-five written before the
repository adopted conventional commits. Those have been triaged, in
`.config/cliff.toml` rather than here: each subject is mapped to the type and
scope it would have carried, so seventeen of them group with everything written
after them and the eighteen that only revised a decision document or a
`.gitignore` drop out the way `docs:` and `chore:` always do. Nothing was
rewritten to achieve it.

Anything still off-convention lands under **Uncategorised**, deliberately
visible, to be triaged into its real group before the tag is cut.

## Unreleased

<!-- git-cliff:begin — generated; edits here are overwritten -->

### Added

- **fs** — ask for the folder rather than assume std::fs ([`a86a2f5`](https://github.com/diaryx-org/historica/commit/a86a2f56ec91956ab39636ba4936c3ed2267f27e))
- **store** — arrange is the library's, not the front end's ([`7a74def`](https://github.com/diaryx-org/historica/commit/7a74def782e768f23203489206fe8ebd2a57cd29))
- comparison to other VCS ([`46eb876`](https://github.com/diaryx-org/historica/commit/46eb8768b516d34282bb697eb7fcd7f9c5389b7a))
- **update** — the folder catches up to a head ([`a824e5f`](https://github.com/diaryx-org/historica/commit/a824e5fbb27474d56a904bef2ad03b85c7be3db2))
- **format** — an operation document states its result ([`26f2e6e`](https://github.com/diaryx-org/historica/commit/26f2e6ec2825c3cfb8082436814c1b48220e5e9e))
- **format** — the resolution document, 0032's grammar ([`3ad606e`](https://github.com/diaryx-org/historica/commit/3ad606ea2294264cbfa157d1e233d74393e43d0b))
- **store** — materialise a file by following its resolutions ([`804a6a9`](https://github.com/diaryx-org/historica/commit/804a6a93f55071aeab732fc89c909ec7ccad263e))
- **record** — a merge writes the resolution it read both sides for ([`9320286`](https://github.com/diaryx-org/historica/commit/9320286266e8cc21938a1c91e8da75c915cdcb45))
- **check** — hold a merge to what it owes a resolution for ([`16c6b43`](https://github.com/diaryx-org/historica/commit/16c6b43320718b5a44897e5aa5673180edad40ed))
- **store** — a store carries the format it is written in ([`cb55fc3`](https://github.com/diaryx-org/historica/commit/cb55fc3d0db83470b2d067522941ad97ec592c39))
- **format** — one spelling for a path ([`2c73a76`](https://github.com/diaryx-org/historica/commit/2c73a76aebfdf54cc8e54368ce366ede0eca7999))
- **check** — say which heads a store holds the history of and cannot produce ([`32e85d9`](https://github.com/diaryx-org/historica/commit/32e85d91102e01b547f807893952f131bcecb32c))
- **format** — a file can be run ([`0318e4d`](https://github.com/diaryx-org/historica/commit/0318e4d46607c67b3f81fdcdd814bb08b9872d78))

### Fixed

- **merge** — anchor to the next element in the traversal, tombstones included ([`03dae53`](https://github.com/diaryx-org/historica/commit/03dae53908009565eb5ccaefa36bf35981943fb6))
- **cli** — merge joins the heads it was not told about ([`4c57101`](https://github.com/diaryx-org/historica/commit/4c57101685334f6a00c22e68a313b8c2ab3502d5))

### Changed

- **store** — carry the digest out of the ancestry walk ([`203fcb5`](https://github.com/diaryx-org/historica/commit/203fcb5647fb79582528931a8fffd0e94753e486))
- **merge,tree** — store an ancestry, not a set per revision ([`9c9da52`](https://github.com/diaryx-org/historica/commit/9c9da52683f7d3682c6711dfd04522602f4a31ef))
- **merge** — apply a chain arithmetically instead of building the tree ([`5959505`](https://github.com/diaryx-org/historica/commit/5959505ad6ec7dcc2595406244f87f50b54f0807))

### Uncategorised — triage before release

- replace mutable files atomically ([`f2b42c8`](https://github.com/diaryx-org/historica/commit/f2b42c8553f5436d5d6cf82855bdb2ee54f3bc5d))
- require acceptance for contested attachments ([`8545421`](https://github.com/diaryx-org/historica/commit/8545421f5589c7bbd27a6ccb40e88fb7a65525a7))
- Add content-aware local store receive ([`55e346d`](https://github.com/diaryx-org/historica/commit/55e346d7d26f7fc5c04302344d5f9222bc8b0ef4))
- load resolution documents beside operation documents ([`0c675af`](https://github.com/diaryx-org/historica/commit/0c675af9eb787eba4efc5d723807b42a54999ed1))
- cross a resolution in the event-graph walk ([`1889a0e`](https://github.com/diaryx-org/historica/commit/1889a0ecfe2a79700f0e59025142b6218b58b235))

### Behavioural changes

- `historica::store::walk` takes the filesystem as its first
  argument. Every other function keeps its signature; pass
  `&historica::fs::Disk` to get what it did before.

- `historica::working::Working` no longer implements
  `Default`. It holds the filesystem it was read from, and there is no default
  one to hold when `disk` is off.

- `historica::record`'s `record`, `plan`, `amend`, `abandon`
  and `survey` now require the store and the working copy to be over one
  filesystem type. Decision 0011 already says the working copy is the folder
  next to the store; this is that, checked.

- building with `--no-default-features` drops `Store::init`,
  `open`, `check`, `discover`, `Working::read`, `record::author_for` and the
  `historica` binary. Use the `_on` constructors and supply a `Filesystem`.

- `arrange` prints each directory's renames before the names
  it left as duplicates, rather than interleaving them in walk order. The
  lines, the counts and the summary are otherwise as they were.

- `Store::reachable` and `Store::reachable_from` return
`Vec<(RevisionId, &RevisionDocument)>` rather than `Vec<&RevisionDocument>`.
The digest of each document now comes back beside it, because the store
already knows it and recomputing it costs a re-serialisation. A caller that
only wants the documents can add `.into_iter().map(|(_, document)| document)`;
a caller that was calling `RevisionDocument::id` on each result should drop
that call and take the first element of the pair instead.

- merge output changes wherever an insertion's left
neighbour held a tombstoned right child. Linear histories now always
read back exactly as recorded (previously misordered on ~half of all
digests); merges of concurrent histories may order differently than the
same merge computed by an earlier build, and a merge recorded by one is
unaffected, since a recorded merge is a revision, not a recomputation.

- Every document `record`, `amend`, and
  `record --merge` writes now claims `historica-v3` and carries a
  `result` line, and a store's header rises to v3 on the first record
  after upgrading. Readers built before this refuse such a store at the
  gate. Documents written earlier still read exactly as they did.

- `merge::Event`'s `operations` field is replaced by
`stated`, which carries the digest naming the document beside the
document itself; build one with `Event::nothing`, `Event::operations`,
or `Event::resolution`. `MergeError` gains `UnknownReference`, for a
`keep` naming an item its author's view does not hold.

- `Store::content` at a merge recorded under version
3 follows the revision's resolution instead of running the event-graph
walk, and reports `MaterialiseError::Content` where a `keep` names a
document this store does not hold or a run longer than that document
has items. `Store::minted` is new: the items one document mints, in
document order, which is the run a `keep` counts into.

- `record --merge` writes a resolution document for
every file its parents' states differ about, including files that
merged cleanly — before this, such a file was recorded as a delta
against the algorithmic merge, or not recorded at all. `Change` gains
a `Resolution` variant and `RecordError` gains `EmptiedByMerge`.

- a revision document naming a path that is not in
normal form C is refused at load, which no store this tool wrote can
contain. A folder holding two names that differ only in normalisation
is now recorded as one file rather than two; `check` cannot see the
case, and the deliberate version of it is what decision 0033 accepts
losing. `historica` gains a dependency on `unicode-normalization`.

- `historica merge` with no arguments joins every
  standing head, and with one argument joins it with every head not
  named. It refused both before. A store with one head and nothing named
  still refuses, with a message that says which situation it is in.

- The `historica record --merge ...` line that `merge`
  prints now names every head the merge joined, not only the ones typed
  on the `merge` command line. Scripts parsing that line get more
  `--merge` flags than they did.

- Refusals that ask for a head — `status` and `record`
  with several heads, `cat head`, `update` — print several lines per
  head instead of one, carrying the change ID, author, time, and message
  summary. Anything matching those refusals line by line will need to
  look again.

- `historica check` prints one further line when the
  store cannot produce one of its heads, after the error and note
  summary, and one note per such head. Its exit code is unchanged: notes
  still never fail.

- `historica check --complete` is new, and exits
  non-zero when any head's history is not all here. Ordinary `check`
  answers whether the store contradicts itself; this answers whether
  delivery has finished.

- `store::Report` gains `is_complete` and `incomplete`,
  and `store::Finding` gains an `Incomplete` variant. The enum is
  `#[non_exhaustive]`, so matches on it already carry a wildcard arm.

- A revision may state the mode of a file it names, as
  `executable` or `plain`, and a document that does claims `historica-v4`. A
  store gains that version the first time one is written and not before, so a
  history that never marks anything executable is still read by every reader
  published for version 3.

- `record` states a mode change it observes, `status` and
  `log` report it as `mode`, and `update` sets the bit on files it writes and
  on files already holding the right bytes with the wrong bit — printing each
  one. An executable file recorded before this upgrade is still recorded as
  plain; the first record after it states the change.

- `Filesystem` gains `executable` and `set_executable`, both
  with default implementations that model no mode, so existing implementors
  keep compiling and keep behaving correctly. A host that can see the bit
  should override them.

- `tree::Entry` gains `mode`, `tree::TreeContest` gains
  `Mode`, `format::RevisionDocument` gains `modes`, and `format::Mode` is new.
  Code constructing an `Entry` or a `RevisionDocument` by hand needs the new
  field.

- A store marker of `historica-v4` is now read rather than
  refused. `historica-v5` is what a reader that knows less than this one says
  it cannot read.

<!-- git-cliff:end -->

## v0.2.0 — 2026-08-21

### Added

- **core** — a causal history that merges by union ([`8f18d50`](https://github.com/diaryx-org/historica/commit/8f18d50c7bd556feb36204367a92e924e6aa4dfe))
- **core** — give every revision two identities ([`3af91e2`](https://github.com/diaryx-org/historica/commit/3af91e2e84431736a721aec196b558ff750a67f8))
- **format** — read and write the revision document ([`05f6959`](https://github.com/diaryx-org/historica/commit/05f69592420f11ae7b0dc8810545be3ecd3c1f9f))
- **store** — read and write the store ([`625311d`](https://github.com/diaryx-org/historica/commit/625311d4531a3480db41f024e6b11c83856d70e0))
- **format** — read and write the operation document ([`711aa15`](https://github.com/diaryx-org/historica/commit/711aa15d7636cef01cdcf26ac68a2e806fdb5125))
- **replay** — replay a linear history into the file it produced ([`b75a464`](https://github.com/diaryx-org/historica/commit/b75a464374ae75b50ea181ba6565b67272259f71))
- **diff** — record operations from an edited file ([`f28a49d`](https://github.com/diaryx-org/historica/commit/f28a49d13b06860df01494d530a5bc8308d9649c))
- **tree** — read a tree, and replay one ([`fb4f0ab`](https://github.com/diaryx-org/historica/commit/fb4f0ab1873bfae83b04d93e8deffec2d82e0da1))
- **store** — hold a store to the files it says it holds ([`4585343`](https://github.com/diaryx-org/historica/commit/4585343581cd19a48ecf9f8982db0a8a44d94130))
- **merge** — merge concurrent branches by walking their event graph ([`52cac80`](https://github.com/diaryx-org/historica/commit/52cac80a7a3b524b913c371c4e37aef076d2845d))
- **cli** — read a store from the command line ([`efe9cc8`](https://github.com/diaryx-org/historica/commit/efe9cc86c2041d7145021e2e6922329ee92fec85))
- **record** — record a revision from the folder beside the store ([`07da45e`](https://github.com/diaryx-org/historica/commit/07da45e52af3b63b4f409622577b1f35cd8ac636))
- **store** — materialise a history that has a merge in it ([`fc479e8`](https://github.com/diaryx-org/historica/commit/fc479e8e4d42fe2bed64ec3b4378470e6e5a6384))
- **conflict** — merge two lines of work, and record the resolution ([`0da71ad`](https://github.com/diaryx-org/historica/commit/0da71add957bcc5204728cb4e97b2d8ba1096853))
- **cli** — show how the folder differs from what is recorded ([`2e5d231`](https://github.com/diaryx-org/historica/commit/2e5d231b4db39afe2442c55a1686e7f7d7637112))
- **arrange** — file a history where a person can find it, and say what it skips ([`6ce4ab9`](https://github.com/diaryx-org/historica/commit/6ce4ab9925f4680bbe0a0961cfa94efb402f7bec))
- **format** — content that arrives whole, and the version that costs ([`44e4c38`](https://github.com/diaryx-org/historica/commit/44e4c383675d8d95ab0b2542dcb5e8e39beb53fc))
- **arrange** — file a path as a path, in directories ([`94f4c3c`](https://github.com/diaryx-org/historica/commit/94f4c3cd84ab0fef495162d85852f6512655b54d))
- **record** — write the name a person reads, rather than one arrange replaces ([`61f304f`](https://github.com/diaryx-org/historica/commit/61f304f5e5b6be79affe9213d069624864f33fd7))
- **store** — write `.rev.txt` and `.ops.txt`, and read the older names forever ([`3602a46`](https://github.com/diaryx-org/historica/commit/3602a46ccccea64cd7640d2f38d6a90bbef42635))
- **store** — the store explains itself, and one suffix per kind ([`9a66edb`](https://github.com/diaryx-org/historica/commit/9a66edbcd139177914b5885cb90138b07ae5474c))
- **record** — the head can be rewritten, and only the head ([`c85cddb`](https://github.com/diaryx-org/historica/commit/c85cddb41974a5610c3d202df491d7180ef3f241))
- **cli** — the identifier a file keeps is one a person can type ([`0ffabaf`](https://github.com/diaryx-org/historica/commit/0ffabafc57d5dff2dc96fd15d3dea9995f01d359))
- **record** — work can be abandoned, and a store pruned of what it replaced ([`658e626`](https://github.com/diaryx-org/historica/commit/658e62601dbec80b9fd6c01f057162b78606b1ef))
- **format** — forgetting destroys an item's payload and preserves its shape ([`2ec258b`](https://github.com/diaryx-org/historica/commit/2ec258bb23fb09b22757e43378754580c91ec7d5))

### Fixed

- **naming** — a payload never carries the extension that says "document" ([`4afb03a`](https://github.com/diaryx-org/historica/commit/4afb03a080497a7e94483d6072dc20b0740541c8))
- **store** — a payload is never filed where a file browser will write ([`36cf54a`](https://github.com/diaryx-org/historica/commit/36cf54a40e26b4478981e34133a7b0871d7e6976))
- **format** — a document claims the lowest version that expresses it ([`2c400ec`](https://github.com/diaryx-org/historica/commit/2c400ec30770d8484c443f9fdc87eb8a1c70d4d4))

### Changed

- **store** — keep the error a caller returns small ([`a1fa06d`](https://github.com/diaryx-org/historica/commit/a1fa06d494cf98d0395325112a5a8e2c162cc059))
- **core** — read a hex pair as a pair, rather than as a slice of two ([`e4b47b9`](https://github.com/diaryx-org/historica/commit/e4b47b973eabe686ab94bcc151ec4ec2d371d1ba))

### Behavioural changes

- `record` now refuses a path two files claim that `--at`
has not settled, with `RecordError::Contested`, rather than diffing the
working-copy file against whichever file a map happened to keep. This can
only arise after a merge, and the old behaviour recorded work against the
wrong file rather than saying so.

- `record` and `status` now refuse a `skip` rule covering a
path the tree holds, naming the files and the deletion that is how a file
leaves a tree; the old behaviour recorded the rule's effect as a `drop`.

- `arrange` moves operation documents into a directory per
revision, where it previously left them under digest names; a reader that does
not walk `operations/` recursively will not find them.

- `historica init` writes `historica-v1`, and recording
into an existing version 0 store rewrites its header, because the header states
the highest document version the store holds and is therefore the gate a reader
too old for it is refused at. `record` no longer refuses a file that is not
UTF-8 text; it stores it whole. A revision that adds a file with content now
names a payload rather than an operation document, so `show <rev> <path>`
prints the file rather than a document for such a revision, and its refusal for
a file the revision said nothing about now reads "said nothing about" rather
than "did not edit".

- an arranged store's `operations/` directory has a
different shape. `arrange` re-files an existing arranged store on the next run
-- `2026-08-20 Say more/src⁄cli⁄mod.rs.ops` becomes
`2026-08-20 Say more/src/cli/mod.rs.ops` -- which is renames only, so no
identity moves and no reference dangles. Names are no longer clipped, so a deep
path that previously produced a name ending in `…` now produces the whole
path, and a store whose paths exceed what a platform allows for a whole path
reports an I/O error naming the file instead of arranging it.

- `record` writes readable filenames rather than digests, so
a new store's `history/` folder reads as dated revisions and a subtree per
revision without `arrange` being run. Existing stores are unaffected until
they are arranged, and digest names stay legal everywhere -- nothing reads a
name. `arrange` on a store written by this version reports "0 renamed".

- a payload whose path's last component ends in `.ops` is
filed as `<name>.ops <digest>` rather than `<name>.ops`. A store written by
the previous version holds such a payload under a name that makes it
unreadable; `arrange` re-files it, and until then `Store::open` refuses the
store with the parse error the misnamed file produces.

- `record` and `arrange` write `.rev.txt` and
`.ops.txt`. Stores written under the older suffixes load unchanged and are
re-filed by `arrange`; the corpus keeps the older names deliberately, as the
standing test that they still read.

- a store written before this commit does not load. The
marker is now `historica.txt` rather than `historica`, `history/skipped`
is `history/skipped.txt`, a bookmark file is `names/<name>.txt`, and
`.rev` and `.ops` are no longer read as documents. Nothing is deployed and
every store that exists was written by the author this week, which is the only
reason this is allowed; once one exists that its author did not write, the
accepted set is append-only forever.

- `init` writes `history/skipped.txt` where it previously
left the file absent, so a fresh store skips `.DS_Store`, `Thumbs.db` and
`desktop.ini` until a person deletes those lines. `check` no longer reports
a file the platform wrote as a foreign file.

- the head a command works from is now the head no revision
supersedes, rather than every head the parent graph has. `record`, `status`,
`merge`, and the `head` target used to refuse a store holding a rewritten
revision with "this store has 2 heads"; they resolve to the revision that did
the rewriting instead. A store with no `supersedes` line in it is unaffected,
and `log` still shows a superseded head, marked. Separately, `--move` reads
its old path against where the revision being written has the file rather than
against the tree its parents hold: the same set of paths for `record` except
where an earlier `--move` or `--at` in the same command has already moved
something.

- a bare file identifier in the path position no longer
resolves. `cat <target> <identifier>` and `show <target> <identifier>` used to
try the argument as an identifier first and fall through to the path, which made
a file named like an identifier unreachable and made which file was printed
depend on a value nobody can see; the spelling is now `file:<identifier>`, and a
bare argument is always a path. Separately, `Store::set_name` refuses a bookmark
name spelled as a full identifier — twenty-four characters of `k`–`z` — since
every position looks a bookmark up before parsing anything and such a name would
shadow the identifier it spells. An abbreviation is untouched.

- new documents and store headers say `historica-v2`, so
a store written by this version is refused by older readers at the gate.

- materialising a redacted file renders `\ forgotten`
lines where destroyed items stood; a store that has forgotten nothing is
byte-for-byte unchanged.

- supersedes the previous commit's version claim — new
stores and documents say `historica-v1` again, and only a store that has
forgotten something says `historica-v2`.

