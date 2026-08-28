# Changelog

What has changed in historica, release by release, for someone deciding whether
to move to a newer one.

Two halves, written two different ways.

The bulleted groups below — **Added**, **Fixed**, **Changed**, and a
**Behavioural changes** section under them — are **generated** from the commit
log by `dx changelog --write`, which reads one shared `cliff.toml` — the same
file, and the same style, in every repository here.
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

historica is published to [crates.io](https://crates.io/crates/historica). Its
first release, v0.1.0, went up without a tag behind it, and the tag list is what
`release changelog` reads to decide which sections this file owes — so
v0.2.0 is the oldest heading below, and it covers every commit since the
beginning rather than only the day between the two.

Those commits include the thirty-five written before the repository adopted
conventional commits. They were triaged once, when v0.2.0's section was written:
each subject was read for the type and scope it would have carried, so seventeen
of them group with everything written after them and the eighteen that only
revised a decision document or a `.gitignore` drop out the way `docs:` and
`chore:` always do. Nothing was rewritten to achieve it, and the result is the
section below rather than a table of subjects in the cliff config — regeneration
never reaches a released section, so a per-commit mapping there would have been
carried for the life of the repository to reproduce bytes that already exist.

Anything still off-convention lands under **Uncategorised**, deliberately
visible, to be triaged into its real group before the tag is cut.

## Unreleased

<!-- git-cliff:begin — generated; edits here are overwritten -->

### Changed

- **release** — read the shared cliff config, not a local copy ([`621a87e`](https://github.com/diaryx-org/historica/commit/621a87ef6191edb6ac2dba29895c9f97afa1abc4))

### Behavioural changes

- releasing this repository needs diaryx-org/devtools on PATH
  for its git-cliff config as well as for `release` itself. Nothing in the tree
  configures git-cliff any more.

<!-- git-cliff:end -->

## v1.0.0-rc.1 — 2026-08-27

### Breaking

- **format** — one spelling for the format ([`422ff71`](https://github.com/diaryx-org/historica/commit/422ff71bdc6598b93782fc8ac8eceec48c0ed613))
- **fs** — land Disk::write through fs-transaction, retiring atomic-write-file ([`6644b4b`](https://github.com/diaryx-org/historica/commit/6644b4b1d96c2d315ff0b33af39f0612d08564d2))
- **format** — say whose header it is with a dot, not an `x-` ([`e10a5c3`](https://github.com/diaryx-org/historica/commit/e10a5c374c29e74aa40a4dddefccfab16bb1fef3))
- **store** — name a payload rather than carry it, and stream both ways ([`d105349`](https://github.com/diaryx-org/historica/commit/d105349f493944a45a94d945595809f110d78651))
- **forget** — destroy a payload whole, and say how much went ([`4614660`](https://github.com/diaryx-org/historica/commit/4614660a238787cc3c1564eab57d5d857d0b360f))
- **record** — say which kind a file being added is, where the sniff would guess ([`e405664`](https://github.com/diaryx-org/historica/commit/e405664bc2ab8698065da853deeb6ba1522c1b84))
- **cli** — the command line is its own package ([`8d99c0d`](https://github.com/diaryx-org/historica/commit/8d99c0d6b887ac40a812ffd5961aaff478100066))
- **store** — a place for a store to say it was written by a newer Historica ([`94f5fee`](https://github.com/diaryx-org/historica/commit/94f5fee3a08e62e8f5cbe661c6351baacc08f71d))
- **record** — a rewrite carries the work standing on it ([`1184af6`](https://github.com/diaryx-org/historica/commit/1184af6fc97c5cc9c1880cf53fe44de6d2e75bff))
- **api** — room to add a field to what a command hands back ([`d459573`](https://github.com/diaryx-org/historica/commit/d4595736d2015b2e8048ccaf36a953858dbc665f))
- **record** — a recording can state another tool's header ([`107d729`](https://github.com/diaryx-org/historica/commit/107d7297f40ca1274bff80f78d6ad1bf6c21d053))
- **store** — a bookmark's name is its path below names/ ([`af6846c`](https://github.com/diaryx-org/historica/commit/af6846ce45e545a22781835480d381f74a449327))

### Added

- **fs** — ask for the folder rather than assume std::fs ([`a86a2f5`](https://github.com/diaryx-org/historica/commit/a86a2f56ec91956ab39636ba4936c3ed2267f27e))
- **store** — arrange is the library's, not the front end's ([`7a74def`](https://github.com/diaryx-org/historica/commit/7a74def782e768f23203489206fe8ebd2a57cd29))
- **record** — require acceptance for contested attachments ([`8545421`](https://github.com/diaryx-org/historica/commit/8545421f5589c7bbd27a6ccb40e88fb7a65525a7))
- **store** — receive another store, by content rather than by filename ([`55e346d`](https://github.com/diaryx-org/historica/commit/55e346d7d26f7fc5c04302344d5f9222bc8b0ef4))
- comparison to other VCS ([`46eb876`](https://github.com/diaryx-org/historica/commit/46eb8768b516d34282bb697eb7fcd7f9c5389b7a))
- **update** — the folder catches up to a head ([`a824e5f`](https://github.com/diaryx-org/historica/commit/a824e5fbb27474d56a904bef2ad03b85c7be3db2))
- **format** — an operation document states its result ([`26f2e6e`](https://github.com/diaryx-org/historica/commit/26f2e6ec2825c3cfb8082436814c1b48220e5e9e))
- **format** — the resolution document, 0032's grammar ([`3ad606e`](https://github.com/diaryx-org/historica/commit/3ad606ea2294264cbfa157d1e233d74393e43d0b))
- **store** — load resolution documents beside operation documents ([`0c675af`](https://github.com/diaryx-org/historica/commit/0c675af9eb787eba4efc5d723807b42a54999ed1))
- **merge** — cross a resolution in the event-graph walk ([`1889a0e`](https://github.com/diaryx-org/historica/commit/1889a0ecfe2a79700f0e59025142b6218b58b235))
- **store** — materialise a file by following its resolutions ([`804a6a9`](https://github.com/diaryx-org/historica/commit/804a6a93f55071aeab732fc89c909ec7ccad263e))
- **record** — a merge writes the resolution it read both sides for ([`9320286`](https://github.com/diaryx-org/historica/commit/9320286266e8cc21938a1c91e8da75c915cdcb45))
- **check** — hold a merge to what it owes a resolution for ([`16c6b43`](https://github.com/diaryx-org/historica/commit/16c6b43320718b5a44897e5aa5673180edad40ed))
- **store** — a store carries the format it is written in ([`cb55fc3`](https://github.com/diaryx-org/historica/commit/cb55fc3d0db83470b2d067522941ad97ec592c39))
- **format** — one spelling for a path ([`2c73a76`](https://github.com/diaryx-org/historica/commit/2c73a76aebfdf54cc8e54368ce366ede0eca7999))
- **check** — say which heads a store holds the history of and cannot produce ([`32e85d9`](https://github.com/diaryx-org/historica/commit/32e85d91102e01b547f807893952f131bcecb32c))
- **format** — a file can be run ([`0318e4d`](https://github.com/diaryx-org/historica/commit/0318e4d46607c67b3f81fdcdd814bb08b9872d78))
- **store** — keep a file a walk materialised, in cache/ ([`ae509e3`](https://github.com/diaryx-org/historica/commit/ae509e350d06a6e2206973d410b27317262d6b2c))
- **xtask** — time the reading commands on a store built to order ([`7de53a2`](https://github.com/diaryx-org/historica/commit/7de53a25a85a6769f32907a85b15ee45d64d9767))
- **cli** — `diff`, where a rename is a fact rather than a resemblance ([`a190130`](https://github.com/diaryx-org/historica/commit/a190130884639ee7c0ee9a2e8362c43b2a6a150d))
- **cli** — `blame`, where the author of a line is read rather than guessed ([`7ce2441`](https://github.com/diaryx-org/historica/commit/7ce2441677dada3ffde537ba9a643bb13561ffae))
- **cli** — colour for `diff`, and the words that changed inside a line ([`0d85a89`](https://github.com/diaryx-org/historica/commit/0d85a891d20aecc672da9de76cdefb3325c93e8b))
- **cli** — `log` narrowed, where a path follows the file rather than the name ([`21c6725`](https://github.com/diaryx-org/historica/commit/21c6725fcb8be5668e3a4037dbef52ddb6f4382b))
- **record** — name the paths, where the rest is unlooked at rather than unchanged ([`b9e90c0`](https://github.com/diaryx-org/historica/commit/b9e90c02d095345c5f079e61a32ffd37150e2d90))
- **store** — file a revision under its month, where a folder is opened rather than scrolled ([`c0b1168`](https://github.com/diaryx-org/historica/commit/c0b11681471e1d9705c6e8940df2e048ae879ff7))
- **cli** — `export`, where the copy is assembled rather than mirrored ([`17b3f19`](https://github.com/diaryx-org/historica/commit/17b3f19262e9933657f5012a53e70e8220768c75))
- **format** — a file can be a link ([`54c69b2`](https://github.com/diaryx-org/historica/commit/54c69b2ab19585d7f1374681ad7e4ee03deab58b))
- **store** — `arrange --refile`, where the month is asked for rather than imposed ([`698bd8a`](https://github.com/diaryx-org/historica/commit/698bd8a1a8b8bdb80aa82a2e03970506da9a8f83))
- **fs** — let a folder stamp a file, and hand one over in pieces ([`48f2482`](https://github.com/diaryx-org/historica/commit/48f24822028bc4ea55c16a0f61bd6e2ef5a36d01))
- **store** — skipped/, one rule to a file ([`34a81f8`](https://github.com/diaryx-org/historica/commit/34a81f86f30c07ea21f158d9c9790642bb39cd24))
- **check** — note the work a rewrite did not reach ([`342ac5f`](https://github.com/diaryx-org/historica/commit/342ac5fd96aee7cb11d52f35e9abf7cbba504a7c))
- **update** — lay a revision out in a directory that holds nothing ([`b2c6fb0`](https://github.com/diaryx-org/historica/commit/b2c6fb05b5988a956bbaa8bde33cf46e060adc31))
- **store** — ask what a digest is, not which grammar you hoped for ([`ad8ac7e`](https://github.com/diaryx-org/historica/commit/ad8ac7ee98f68c63daa3f343596ecba775004a97))
- **format** — a resolution can forget what it minted ([`cfc6763`](https://github.com/diaryx-org/historica/commit/cfc676320905b5e928672bb6694145c5df072505))
- **skipped** — give a rule two axes, and close the key set ([`5d582c8`](https://github.com/diaryx-org/historica/commit/5d582c8259687374e432377e02b44a0326587fb2))
- **store** — let a reserved directory declare how it travels ([`440f901`](https://github.com/diaryx-org/historica/commit/440f901cadbd849885882fd9b271c093c991bb87))
- **store** — export onto the copy this store already made ([`a0570a0`](https://github.com/diaryx-org/historica/commit/a0570a091cd7711d38bfbf71c9e44a6931b03756))
- **store** — offer, the listing a directory has no way to give ([`6b72cec`](https://github.com/diaryx-org/historica/commit/6b72cec758d00348c8b3dda6b9a8ca1fbf338a62))
- **store** — fetch, taking what is missing from a directory nothing can list ([`9026896`](https://github.com/diaryx-org/historica/commit/9026896989c84000fee4626ec960bb66db35adf5))
- **cli** — fetch, over the stack the platform already maintains ([`12a49ea`](https://github.com/diaryx-org/historica/commit/12a49eaab5a04af1beb5c89a775923dd68f9e67c))
- **store** — keep the revision documents, so that opening costs one read ([`ab2ae9e`](https://github.com/diaryx-org/historica/commit/ab2ae9ec9c5dd8c5506ccfaa615b96b51d88c927))
- **record** — carry, finishing the rewrite transport delivered half of ([`5c44586`](https://github.com/diaryx-org/historica/commit/5c44586361ad0403dcba85ea616cd8ab503e430e))
- **export** — --files-only, the folder without the history under it ([`b83bc41`](https://github.com/diaryx-org/historica/commit/b83bc416a11c4734bd1b4d50a981508785bd8881))
- **names** — a bookmark travels, and a second line keeps one back ([`f00a314`](https://github.com/diaryx-org/historica/commit/f00a3145c0460c9e1d88f61e1974cace47a8ffcf))
- **fs** — barrier every Disk::create_new before anything can name it ([`659b659`](https://github.com/diaryx-org/historica/commit/659b659c7070c2320b8dca74ebe339458d7e30ce))
- **fs** — offer update's per-file guard to the filesystem as write_if ([`0a3bdb2`](https://github.com/diaryx-org/historica/commit/0a3bdb2a98dacbe5abff98ca350f963249d28ddc))
- **cli** — let log take a range of revisions ([`84c4767`](https://github.com/diaryx-org/historica/commit/84c476773843e2ce34f286a8b66dbd54b77a843e))
- **cli** — give log a reading for something that is not a person ([`535656e`](https://github.com/diaryx-org/historica/commit/535656ee058a55e1f1b212e6e609f74157980caf))
- **diff** — a file of bytes names both payloads and both lengths ([`3bd0673`](https://github.com/diaryx-org/historica/commit/3bd067358916652a1fbc305fa85efe2569164cad))

### Fixed

- **fs** — replace mutable files atomically ([`f2b42c8`](https://github.com/diaryx-org/historica/commit/f2b42c8553f5436d5d6cf82855bdb2ee54f3bc5d))
- **merge** — anchor to the next element in the traversal, tombstones included ([`03dae53`](https://github.com/diaryx-org/historica/commit/03dae53908009565eb5ccaefa36bf35981943fb6))
- **cli** — merge joins the heads it was not told about ([`4c57101`](https://github.com/diaryx-org/historica/commit/4c57101685334f6a00c22e68a313b8c2ab3502d5))
- **cli** — print a merge command that settles the path it says is claimed ([`57086c3`](https://github.com/diaryx-org/historica/commit/57086c3ce627b64ebaf8724e7d6e302ca6ded8c8))
- **record** — a link nobody touched is a link nobody retargeted ([`2ab9962`](https://github.com/diaryx-org/historica/commit/2ab9962fdc831a975cfbc7b42fb7ae99b4598fb3))
- **store** — add @eaDir to the names the store cannot own ([`4db3b94`](https://github.com/diaryx-org/historica/commit/4db3b94adb0c5bab400a6e221f2c4298694e8e09))
- **show** — print the resolution a merge states ([`8cd293c`](https://github.com/diaryx-org/historica/commit/8cd293c9abcee8055a2e04cb108a53357ff50c42))
- **receive** — carry the resolution documents a merge names ([`861d943`](https://github.com/diaryx-org/historica/commit/861d9437b180bc550d68d84581641687f3012e65))
- **forget** — say why it cannot reach into a resolution ([`5f74c3b`](https://github.com/diaryx-org/historica/commit/5f74c3b45f124a46da3b9bb8b5a55e7fccbeca1e))
- **tests** — say who the cache tests are, rather than borrowing it ([`71f88b0`](https://github.com/diaryx-org/historica/commit/71f88b00064f92ce972d53551a323e543ef0ddb7))
- **merge** — a keep of a name two concurrent revisions share lands once per element ([`8e538b3`](https://github.com/diaryx-org/historica/commit/8e538b3ad505e8524a508ea25711132f210c8b05))
- **log** — refuse a document it cannot read, rather than printing a history without it ([`9e2918b`](https://github.com/diaryx-org/historica/commit/9e2918b593f894b72d093508cb790b0d7927a90c))
- **fs** — close set_link's window where the path names nothing ([`79e0e7c`](https://github.com/diaryx-org/historica/commit/79e0e7c857a5facb3fa35c0b323eef10818550b6))
- **naming** — a stem gives up everything a filesystem reserves ([`c4b0748`](https://github.com/diaryx-org/historica/commit/c4b074872373f545b30e1ae3f367ecac0a299426))

### Changed

- **store** — carry the digest out of the ancestry walk ([`203fcb5`](https://github.com/diaryx-org/historica/commit/203fcb5647fb79582528931a8fffd0e94753e486))
- **merge,tree** — store an ancestry, not a set per revision ([`9c9da52`](https://github.com/diaryx-org/historica/commit/9c9da52683f7d3682c6711dfd04522602f4a31ef))
- **merge** — apply a chain arithmetically instead of building the tree ([`5959505`](https://github.com/diaryx-org/historica/commit/5959505ad6ec7dcc2595406244f87f50b54f0807))
- **store** — read operations/ on first need, not at open ([`ce87443`](https://github.com/diaryx-org/historica/commit/ce8744311635bfe8e95add20896eca90f026a729))
- **replay** — move a file through a replay step instead of copying it ([`fb55a07`](https://github.com/diaryx-org/historica/commit/fb55a07b0f5e7cd6ae7803945d9c1a1e0f6691ab))
- **store** — say where a digest is, instead of hashing the directory to find it ([`6c6b06e`](https://github.com/diaryx-org/historica/commit/6c6b06e7d8a67cf2e3717e42b28063a8cc909336))
- **store** — hash a payload in pieces rather than holding it whole ([`f89db41`](https://github.com/diaryx-org/historica/commit/f89db4146f12c57b33e61d8cab03b298818e70b0))
- **working** — catalogue what the folder hashed to, so a photograph is not read twice ([`e14a9e0`](https://github.com/diaryx-org/historica/commit/e14a9e0a722cae9fa8b32366274592e49d4d5b3f))
- **check** — replay a chain forward rather than walking it ([`dc80af4`](https://github.com/diaryx-org/historica/commit/dc80af4864f8267d9850f834f305b861654d1980))
- **store** — take the catalogue without walking the directory ([`2a77605`](https://github.com/diaryx-org/historica/commit/2a7760590b4c180de86b23cf2e8f2b567af1927e))
- **store** — read the revision, and leave the rest of the document alone ([`f145783`](https://github.com/diaryx-org/historica/commit/f145783ad002cd90766e3ab3a4491a016094884f))
- **format** — name a revision by the digest its reader already has ([`c196552`](https://github.com/diaryx-org/historica/commit/c1965525537e04a93cac53676f575bd9de704a9b))
- **xtask** — cut releases with the shared tooling, not a sixth copy ([`ffd7911`](https://github.com/diaryx-org/historica/commit/ffd7911c0b49917d1cb8da5ea75f7304b9e1b65b))

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

- `Store::open` and `Store::open_on` no longer read
  `operations/`, so a store holding an unparsable operation or resolution
  document now opens. The `StoreError::Unparsable` it used to fail with,
  naming the same file, is raised by the first call that needs what that
  document says. A caller that opened a store as a validity check should
  use `Store::check`, which reports every fault in the folder at once and
  is unchanged.

- `Store::operation`, `Store::operations`,
  `Store::resolution`, `Store::resolutions`, `Store::forgetting` and
  `Store::effective_operation` now return `Result<_, StoreError>`, since
  each may have to read `operations/` first. The success values are what
  they were.

- `MaterialiseError` gains `UnreadableOperations`,
  carrying what the store said when that directory would not read or parse.
  The enum is `#[non_exhaustive]`, so a matching caller already has a
  wildcard arm.

- A store now gains files under `history/cache/`, named by
  digest, when a command materialises a file whose history was long enough
  to be worth keeping. Nothing references them, `check` ignores them, and
  deleting the directory loses nothing but time. `forget` and `prune` now
  delete every entry, which is what keeps forgetting's promise true.

- `cat <revision> <path>` at a single revision now answers
  by decision 0032's stated rule rather than by merging the reachable
  history. The two agree wherever the rule reaches, and where it does not —
  every merge recorded before version 3 — it still falls back to the merge,
  so no store reads differently. It is now the same code path `update`
  writes files from, which is what makes them unable to disagree.

- `historica merge` now prints `--at "<file>=<path>"` pairs
in the command it suggests whenever two files claim one path, where it
previously printed a command that `record` refused. A script matching the
printed command exactly will see the new arguments. The file written beside
the contested path is now named `notes (historica abcd1234).md` rather than
`notes.md (historica: abcd1234)`; nothing reads that name back, but a script
that matched the old spelling will not match the new one.

- `Store::operation`, `Store::resolution` and

- a store whose `operations/` holds one unparsable document
no longer refuses every content question. `Store::content` answers for every
file whose own history does not name that document, and the parse failure is
reported by `Store::operations`, `Store::resolutions` and `check` as before. A
caller relying on the coarser refusal will now get answers where it got an
error.

- reading a store writes `history/cache/operations.txt`.
Stores on read-only media are unaffected — every failure to write it is
ignored — but a tool watching the store directory for changes will see it
appear and be rewritten whenever `operations/` gains or loses a file.

- `historica record` accepts paths, and with any named it
  compares only those with the tree. With none, it surveys the whole folder
  exactly as before. For callers of the library, `Recording` carries a new
  `only` field and `record::survey` takes a `&Restriction` argument;
  `Restriction::Everything` is what both meant until now.

- A revision recorded by this version is written to
`revisions/YYYY-MM/<date> <summary>.rev.txt` and its content to
`operations/YYYY-MM/<date> <summary>/...`, rather than directly under
`revisions/` and `operations/`. The filename itself is unchanged. Anything
scripting against store paths with a one-level glob — `revisions/*.rev.txt`,
`ls history/operations` — must walk instead. Identity is unaffected: a
filename is presentation, no digest or reference moves, and a store written
by an older version loads exactly as before. Running `arrange` once files an
existing store into the new layout, and reports every move; `arrange` on a
store this version wrote does nothing. `arrange` also no longer keeps a
revision in a directory a person filed it into by hand — it files it under
its month like every other — which is a change for anyone who arranged a
store that way and then ran the command.

- The walk no longer refuses a symbolic link, so a folder
  holding one now records where it used to stop. Every link in such a folder is
  recorded the first time it is surveyed, `status` lists them as `added`, and a
  `skip` rule written to work around the old refusal keeps working and now keeps
  a link out that would otherwise be recorded. A link whose target is not UTF-8
  is still refused, by name.

- A revision may state where a link points, as
  `link <file ID> <target>`, and a document that does claims `historica-v5`. A
  store gains that version the first time one is written and not before, so a
  history with no links in it is still read by every reader published for
  version 4.

- `Filesystem` gains `link_target` and `set_link`, both
  defaulted, so existing implementors keep compiling. `Ok(None)` from
  `link_target` is reserved for a filesystem that models no links at all — an
  implementation that models them answers with a target or with an error, never
  with `None` — and `update` refuses by name on a filesystem that answers
  `None` rather than writing a plain file holding the target. The forwarding
  implementations for `&T`, `Arc<T>`, `Rc<T>` and `Box<T>` now also forward
  `executable` and `set_executable`, which they did not: a wrapped `Disk`
  previously reported no executable bit at all.

- `tree::Kind` gains `Link` and `tree::Entry` gains `target`;
  `tree::TreeContest` gains `Target` and `Referenced`; `tree::TreeError` gains
  `Dangling`; `format::RevisionDocument` gains `links`; `format::LinkTarget`,
  `format::check_link_target` and `update::materialise` are new. Code
  constructing an `Entry` or a `RevisionDocument` by hand needs the new field,
  and code matching on `Kind` needs the new arm.

- `store::content_at` and `content_at_heads` refuse a link
  with the new `MaterialiseError::IsALink` rather than producing bytes, and
  `cat` and `blame` refuse one by name. `update::Remove` gains `link`,
  `update::Update` gains `links`, and `update::Applied` gains `linked`.

- A store marker of `historica-v5` is now read rather than
  refused. `historica-v6` is what a reader that knows less than this one says it
  cannot read.

- A record that moves a file some `file:` link points at no
  longer states a `link` line for that link. It previously restated the link
  verbatim, as the now-dead path the folder still spelled, which silently turned
  a reference into a string and left the link dangling after the next rename.
  The revision is now smaller by that line, `status` and `record` no longer list
  the link, and `update` afterwards rewrites the stale symlink to the target's
  new path and prints it. A verbatim link whose target has since become tracked
  likewise stays verbatim while its string is unchanged, as 0040 said it should.
  A deliberate retarget, and the verbatim restatement owed when a record drops
  the target, are unchanged.

- `arrange` files a revision document under `YYYY-MM/` only
when asked, with the new `arrange --refile`. Plain `arrange` renames a revision
where it sits, including one sitting flat in `revisions/`, which is what it did
before this release and what anyone who filed a store by hand relies on. So a
flat store is no longer migrated by running `arrange` — it is migrated by
running `arrange --refile` once, after which both spellings of the command move
nothing. What is new since the last release is the writer: a revision recorded
by this version is written to `revisions/YYYY-MM/<date> <summary>.rev.txt` and
its content to `operations/YYYY-MM/<date> <summary>/...`, so anything scripting
against store paths with a one-level glob must walk instead. `operations/` is
filed under the month by either spelling of `arrange`, since its directories
are named by the revision rather than chosen by a person. Identity is
unaffected throughout: a filename is presentation, no digest or reference
moves, and a store written by any version loads as before. In library terms,

- `Filesystem` gains `stamp` and `read_in_pieces`, both
  defaulted, so existing implementors keep compiling and keep behaving
  identically. `Ok(None)` from either means "this filesystem does not report
  that", and the only consequence is that a command reads what it would have
  read anyway — nothing about correctness may turn on either method answering
  `Some`. An implementation that answers `Ok(None)` from `read_in_pieces` must
  have called the reader no times, since the caller then asks for the file
  whole.

- `fs::Stamp` and `fs::digest_of` are new and public.

- `history/cache/working.txt` is a new file, written by
  `status`, `record`, `amend` and `diff`. It holds no content and states
  nothing about the history: one line per tracked path, saying what that file
  hashed to and the size and time the directory reported for it. Deleting it is
  always safe and always correct — every command then reads the folder, which
  is what it did before this existed, and writes the file again. It is not
  copied by `export` and is not `check`'s business.

- A file of bytes whose payload the store has not received no
  longer stops `status` or `record` where the folder holds those bytes. The
  tree states the digest, the folder hashes to it, and the file is unchanged;
  it previously failed with an error naming the undelivered payload.

- `Working` gains `digest`, `bytes_and_digest`,
  `text_and_digest` and `remember`, and `record::survey` calls `remember` once
  when it is done. A caller driving `survey` directly needs nothing new;
  a caller that built its own comparison out of `Working::bytes` still can.

- a payload whose file is named `@eaDir` is now filed
  under `@eaDir <digest>` rather than under its own name, and a file
  called `@eaDir` inside `history/operations/` is no longer indexed as a
  payload or reported by `check`. A store written before this that holds
  a payload legitimately named `@eaDir` at its own name stops being able
  to produce it; `arrange` refiles it. No document's bytes change.

- `history/skipped.txt` is no longer read; rules live
in `history/skipped/`, one file each, and `check` reports a leftover
`skipped.txt`. `skip` with no argument prints rules with their files
instead of the file's bytes, `receive` reports "received N rules" instead
of "received skipped.txt", and the skipped-file receive conflict no
longer exists.

- every document and store header is written with the
preamble `historica`; the numbered `historica-v0`..`historica-v5`
preambles are refused by name, so a store written by a 0.x release is no
longer readable — there is no migration, and nothing was ever published
that wrote one. `RevisionDocument`, `OperationDocument`, and
`ResolutionDocument` lose their `version` field, `Version` is gone from
the public API along with `Store::version`, `ExportPlan::version`, and
the version line in `export`'s output.

- `check` emits a new note, `StandsOnSuperseded`, where a
  store holds both a supersession and a live descendant of the superseded
  revision. It never fails, so `check`'s exit status is unchanged, and
  `Finding` is `#[non_exhaustive]`, so the new variant breaks no match.
  `merge` prints one line per such head before its other output.

- `historica::store::Body` is public, and `Store` gains
  `body` and `bodies`. Nothing existing changed shape.

- `show <merge> <path>` prints the resolution document
  instead of failing with "which this store does not hold yet". The
  undelivered-document message itself now says "content document" rather
  than "operation document", since either grammar can be the thing that is
  missing.

- `receive` transfers resolution documents, so a store
  that received a merge from an earlier version is missing documents and
  should receive again — the second run now copies what the first left
  behind. Its counts print as "content documents" rather than "operation
  documents", and count both grammars. `ReceivePlan::operations` is
  `ReceivePlan::documents` and `Received::operations` is
  `Received::documents`.

- `forget` refuses a span including lines minted by a
  resolution with a message naming that limit, instead of reporting the
  resolution as undelivered. `ForgetError::MintedByResolution` is a new
  variant of an already `#[non_exhaustive]` enum.

- `check` states a chain's contradiction in the
replayer's words rather than the merge walk's — "the document deletes `x`
at position 1, where the parent holds `y`" where it used to describe the
same fault as a walk that could not place an item. The finding, its
severity and the exit code are unchanged.

- `forget` redacts lines a merge minted, where it
  refused before, and follows a forgotten line to the copy a resolution
  made of it when the person moved that run while resolving. A store
  redacted with an earlier version may still hold such a copy in
  plaintext; forgetting the span again reaches it.

- `ResolutionDocument::result` is `Option<RevisionId>`
  and the struct gains `forgets`. A resolution this tool writes still
  always states a result; a forgetting one must not.

- `Forgotten::writes` holds `store::Body` rather than
  `OperationDocument`, since a stand-in is written in the grammar of
  what it stands in for. `ForgetError::MintedByResolution` is gone, the
  refusal it named having become a capability.

- `merge::Quoted` gains `text` and `dropped_by`, the
  latter naming revisions that removed an item without quoting it, which
  is how a resolution drops one.

- `Rule` is no longer three flat variants. It is a
 `scope` beside a `private` flag, and the scope is the new `Scope`
 enum — `Path`, `Under`, `Name` and `NameUnder`, the last two holding
 the new `Pattern` type. Construct with `Rule::shared(scope)` or
 `Rule::private(scope)`. Rule equality includes the flag, so a private
 rule and its shared twin are two rules to `Skipped::stated`, to
 `receive`'s union, and to `skip`'s already-held check.

- `skip-suffix` is refused by name. A store holding
 one stops every command with an error naming `skip-name *<ending>`,
 and `check` reports it with the exact replacement line. The `skip
 --suffix` flag is refused in the same way, pointing at `--name`.

- `export` now writes every shared rule into the
 copy's `history/skipped/`, where it previously wrote none. `Exported`
 and `ExportPlan` gain a count of the rules carried and a count of the
 private rules withheld, and `export` prints both.

- `export` now carries `history/claims/` into the
 copy — every file in it, whole, rather than the subset naming
 exported revisions. `ExportPlan` gains `reserved()`, `Exported` gains
 a `reserved` count, and `export` prints "carried N files another tool
 wrote". A store with no such directory exports exactly as before.

- `receive` now unions `history/claims/` from the
 source, add-only: a filename the receiving store already holds is
 left untouched and never read, and only names it lacks are written.
 `ReceivePlan` gains `reserved()` and counts toward `is_empty()`,
 `Received` gains a `reserved` count, and both `receive` and its dry
 run print what they would take.

- `history/trust/` is stated as never crossing a
 store boundary, which is what both commands already did by accident
 and now do by rule. A directory at the store root that nothing
 reserved is likewise left alone in both directions.

- `store::Travel`, `store::RESERVED_DIRS` and
 `store::travel` are new, and are how a tool asks what historica
 promises about a directory it reserved.

- `export` no longer refuses a destination holding a
 copy of this store. Where `<dir>` holds a related store that passes
 `check`, it is updated in place — files written, left, or withdrawn —
 rather than refused with `Occupied`. A destination that is empty,
 absent, or holds something else behaves exactly as before.

- an update export destroys bytes in the destination.
 A `forget`, a `prune`, a target moved off a branch, and a rule the
 origin stopped sharing all remove files from the copy's `history/`,
 and the copy's folder is rewritten to the target. Callers who pointed
 `export` at a copy expecting a refusal now get a rewrite.

- `Exported`'s `revisions`, `documents`, `payloads`,
 `forgetting` and `reserved` count what this run *wrote* rather than
 what the plan named. For a fresh copy the numbers are unchanged; for
 one being updated they are the difference. `Exported` gains
 `withdrawn`, `destroyed` and `updated`.

- `ExportError` gains `BrokenCopy`, `Unrelated` and
 `Recorded`, and `Occupied`'s message now says the destination holds
 something that is not a copy of this store. It is `#[non_exhaustive]`,
 so a caller matching on it already had a wildcard arm.

- `ExportPlan` gains `updating()`, `withdraws()`,
 `destroys()` and `writes()`, and `Store::export_plan_onto` is the
 planning entry point that knows about the destination — including
 every refusal, so a dry run refuses where the real thing would.
 `export_plan` is unchanged and still describes a fresh copy.

- `historica export` prints "withdrew N files",
 "destroyed N forgotten originals", and "updated the copy of X at Y" in
 place of "made a copy" where it updated one; `--dry-run` names each
 file it would withdraw, as `prune` and `forget` do.

- `historica`'s default features now include `http`,
  which links the platform's native HTTP stack — objc2 and friends on
  Apple, libcurl on Linux, the windows crate on Windows. A packager or a
  downstream crate that does not want them builds with
  `--no-default-features --features disk`, which loses the `fetch`
  command and nothing else.

- Opening a store now writes `history/cache/revisions.txt`,
  where before it only ever read `cache/`. That directory is derived and
  disposable by decision 0003 and its contents are nobody's interface, so no
  answer changes — but a caller that watched `cache/` for writes or counted
  the files in it will see the difference. Deleting the file, truncating it
  or filling it with lies changes how long a command takes and nothing else.

- merging across a recorded resolution that keeps one
(document, ordinal) name more than once — possible only where concurrent
revisions recorded byte-identical documents — now keeps one element per
occurrence instead of folding them all onto the first element in view
order, so such merges gain the items earlier versions dropped and read
them where the resolution placed them. A resolution keeping a name more
often than the author's view holds elements under it is now refused with

- `export` accepts `--files-only`, and `Store` gains
  `export_files`, `export_files_onto` and `export_files_plan_onto`. Nothing
  an existing caller does changes: without the flag `export` writes the
  repository it always did, and the folder half of that copy is unchanged
  in both directions.

- `Store::get` returns `Result<Option<&RevisionDocument>,
 StoreError>` and `Store::iter` yields `Result<(&RevisionId,
 &RevisionDocument), StoreError>`, because a parse deferred is a parse that
 can fail where it used to have failed at `Store::open`. A caller wanting a
 graph fact should take the new infallible `Store::revision`,
 `Store::revisions` or `Store::holds` instead; one wanting every document
 whole should take the new `Store::documents`. A revision document that is
 well-formed but states a value the format refuses — a `when` that is not
 RFC 3339, a path 0008 rejects, a file ID outside its alphabet, a `mode` or
 `link` that parses as neither spelling, or two tree facts contradicting
 each other about one file — now opens without error and is refused at the
 moment something asks what that revision did. `check` is unchanged: it
 reads every document whole and reports every fault at once.

- `Store::names` now maps to the new `Bookmark` rather
  than to `Name`, and `MutableConflict::Name`'s `here` and `there` are
  `Bookmark`s; `Store::name` still answers with the target alone, and
  `Store::bookmark` is the new one that answers both halves.
  `Finding::MalformedBookmark` and `StoreError::MalformedName` gain a
  `because`, and `MalformedName` is a struct with a private field rather
  than a unit. `Name::parse` takes the one target line rather than a
  bookmark file's whole text, and no longer accepts a trailing newline —
  `Bookmark::parse` reads the file. `OfferKind` gains `Name`, which older
  fetchers discard on 0056's standing rule for an unknown kind. A bookmark
  file carrying a second line is refused by any earlier historica, which
  refuses the whole store; that is 0006's strict parser rather than
  anything new here, and it is why nothing writes a second line unless
  somebody asks for one. `export` now writes and withdraws the copy's
  `names/`, so a bookmark made in a published copy that the origin does not
  state is removed on the next export, where before it was left alone.

- `Disk::write` now flushes the destination's parent
directory durably (fsync; F_FULLFSYNC on Apple) after the rename, where it
previously synced only the staged file — a mutable-file write is durable
when the call returns, at the cost of one directory flush per write. The
staging sibling is now named `.<name>.fstx-tmp` beside the destination
instead of atomic-write-file's `.atomic-write-file-*` names; a crash can
leave one behind, and it claims no store name either way.

- `Disk::create_new` now issues ordering flushes (the
file and its directory; F_BARRIERFSYNC on Apple, fsync elsewhere) where it
previously issued none — store writes gain crash ordering at the cost of
two barriers per document, and a crash can no longer leave a bookmark or
revision naming bytes that did not survive with it.

- replacing an entry with a symbolic link is now atomic —
no observer, concurrent or post-crash, sees the path absent mid-replacement.
A failed attempt can leave a `.<name>.fstx-tmp` sibling behind instead of
having already removed the destination.

- a guarded create judges absence by the entry rather
than by a read: a directory or a dangling symbolic link that raced into
a path the plan meant to create a file at now lands in `Applied.left`
("it changed underneath the update") where it previously aborted the
whole update with an I/O error (the directory) or was written over (the
dangling link).

- over `Disk`, a file named `.fstx-journal` sitting
beside a write's destination now refuses that write with an I/O error,
read as a stale fs-transaction journal awaiting recovery. No historica
operation writes one — a guarded write takes the journal-free fast
path — so only a file something else left there can trigger it.

- a revision document holding an `x-` header no longer
parses — `x-review-url` is now an unknown header with no dot in it, and
is refused by name at its line, with `<tool>.x-review-url` named in the
message as the spelling that would be ignorable. A document holding
`diaryx.review-url` parses where it was previously refused, and such a
key reaches `RevisionDocument::extensions` whole, as `x-` keys did.

- `ParseErrorKind::MalformedKey` now also covers a dot
with nothing on one side of it (`.a`, `a.`, `a..b`), where the key
alphabet previously admitted no dot at all and any dotted key was
malformed for the alphabet.

- A revision whose message holds `\ : * ? " < > |`, or
 whose summary ends in a full stop, is now written under a stem spelling
 those as a space or dropping them. A store arranged by an earlier
 version has stems this scheme spells differently; `arrange` applies the
 new one, which is 0019's first case. Nothing reads these names, so no
 digest, target, or bookmark moves.

- `diff` on a file of bytes prints `binary files
  differ: `<digest>` <n> bytes -> <digest> <n> bytes` where it printed
  `binary files differ`. Each digest is abbreviated to twelve characters,
  and a side that is not there — a new or deleted file — prints as
  nothing, leaving the `->` with one side. Anything reading that line as
  a fixed string sees a longer one; nothing in historica parses it.

- `Content::Whole` holds a `RevisionId` naming the
payload rather than the payload's bytes, and `Content::bytes` is gone.

- `Store::content_at` and `content_at_heads` no longer
read a payload, so a file of bytes materialises in a store that has not
been delivered the bytes, and `MaterialiseError::MissingPayload` and
`Unreadable` no longer arise from that arm. Whether the bytes are here is
now `Store::payload_file`, asked by whatever wants them; the same refusals
are unchanged for the `text` payload a creation replays from.

- `record::Change::Whole` holds a `RevisionId`, and the
recorder reads the working file again when it files the payload rather than
holding it from the survey. A file rewritten between the survey and the
write is `StoreError::PayloadMismatch` and nothing is filed, where before
the bytes read at survey time were written whatever the folder then held.

- `update::apply` takes the store as its first argument,

- writing a file of bytes into the folder no longer goes
through `Filesystem::write_if`. The destination is hashed and then written,
so a backend with a conditional write of its own no longer narrows the race
window for that file — the window is the trait default's, and the outcome
for a path that drifted is unchanged: nothing written, and `left` reports
it. A file of lines is untouched.

- `Filesystem` gains `write_in_pieces`, defaulted to
`Ok(None)`, meaning this filesystem takes a file whole. An implementation
answering `Ok(None)` must not have called `feed`, on `read_in_pieces`'

- `store::fetch::Source` gains `get_in_pieces`, defaulted
to `get`, so an existing implementor is unaffected. `Ok(false)` is `get`'s
`None`. A payload the store already holds is no longer requested from the
source at all, where it was previously fetched and then discarded by the
insert's own dedup.

- `StoreError::PayloadMismatch` is new — a payload fed in
pieces that did not hash to what it was promised, with nothing written.

- `historica cat` of a file whose payload this store has
not been delivered now says so in `cat`'s own words, naming the path and
the content digest, where it previously reported the store's materialise
refusal.

- `historica diff` prints the byte count of a file of
bytes only where the filesystem reports one; on `Disk` it always does, so
the line is unchanged there. A side whose length could not be learned
prints its digest alone.

- `working::Working` gains `sniff` (kind and digest in
one streaming pass), `reread_digest` (the digest worked out afresh rather
than answered from `cache/working.txt`), and `on_disk` (a path in the
folder's own spelling, whether or not the walk found it).

- `record::RecordError` gains `NoPathForContent`, for a
plan stating whole content and no path to read it from. Nothing this crate
produces states one.

- `historica forget <target> <path>` with no `--lines`
now forgets a file of bytes whole, where the whole command previously
refused any file that was not lines and treated a missing `--lines` as a
usage error. `--lines` on a file of bytes, and no span on a file of
lines, are each refused by name with the spelling that would have worked.

- `store::Forgetting` states an `Extent` — `Lines
{ first, last }` or `Whole` — in place of its `first` and `last` fields,
so a caller constructing one states which of the two acts it means.

- `Store::content_at` and `content_at_heads` answer a
forgotten payload with the new `MaterialiseError::ForgottenPayload`,
naming the stand-in and the destroyed length, where they answered
`MissingPayload` before. `MissingPayload` now means only that transport
has more to deliver, which is what its message always said.

- `check` reports a `bytes` payload with a stand-in as
`Forgotten` rather than `MissingPayload`, and a store holding both the
payload and a document forgetting it as `Resurrected`. Both are notes, as
they are for the other grammars, so no store's report gains an error.

- `store::Body` gains a `Forgotten` variant, so an
exhaustive match over it needs a third arm; `Body::write` is new, and is
what most such matches wanted.

- a file in `operations/` whose header block carries a
`length` line is now read as decision 0066's grammar and held to its
strictness, where it was previously read as an operation document and
refused as unparsable.

- `record::survey` takes a seventh argument, a `&Kinds`,
  and `record::Recording` gains a `kinds` field. `Kinds::default()` is
  what every existing caller wants: it is the sniff, unchanged.

- `amend` no longer re-sniffs the kind of a file its
  predecessor added. Where the folder's bytes have since crossed the
  UTF-8-and-no-NUL boundary, the amendment keeps the recorded kind
  instead of silently swapping it, and refuses if the file was recorded
  as lines and is no longer UTF-8.

- `cargo install historica` no longer installs anything.
  The command line is `cargo install historica-cli`, and the program it
  puts on the PATH is still called `historica`.

- The `http` feature no longer exists on the `historica`
  package. A caller who named it — `features = ["http"]` — gets an error
  from cargo rather than a silent no-op, and should drop it: no line of
  the library ever read it.

- `historica`'s default features are now `["disk"]` alone,
  so depending on the library no longer builds or links a platform HTTP
  stack. A caller who wanted the transport wanted the command line.

- A store header whose second line is neither blank nor absent
  is now refused, where it was previously ignored. Every store `init` writes is
  unaffected: it states nothing between the format line and the blank line under
  it, and this release writes no header there. What is reached is a hand-made
  store whose note begins on the second line, which `HEADER_NOTE` had invited by
  saying a person may write what they like below the first line. The error
  carries the fix, per 0004: put a blank line above the note. Published 0.1.0
  and 0.2.0 stores are unaffected, since 0047 already refuses them at the
  preamble.

- `StoreError::UnknownLayout` and `Finding::UnknownLayout` are
  new variants, the second at `Severity::Error`. Both enums are
  `#[non_exhaustive]`, so a match on either already had a wildcard arm; what a
  caller gains is being able to tell "this reader lacks the format" from "this
  reader lacks the layout", which are different sentences to the person holding
  the store.

- `historica amend <target>` no longer refuses a revision
  work stands on. With `-m` it rewords that revision and carries everything
  above it onto the new message; without `-m` it still refuses, but now naming
  the reword and the flag that performs it rather than saying the act is not
  built. A caller parsing the old "not built yet" text will not find it.
  `--move` against such a revision is refused by name.

- `historica abandon <target>` is unchanged — it still
  supersedes the named revision and everything standing on it. The new
  `--only` abandons the one revision and carries the rest onto the tombstone.

- `historica carry` gains `--onto <destination>`, which
  restates the named work against a parent a person chose. Unlike every other
  carry it stamps `revised` from the clock, so it does not converge across
  replicas; the stack carried above it does.

- The library signatures moved. `carry::plan` and
  `carry::carry` take a `carry::Carrying` rather than `Option<&RevisionId>`;
  `record::abandonment_plan` takes an `only: bool`; `record::Abandoning` gains
  `only`; and `record::Amended` and `record::Abandoned` gain the `carried`
  plan. `record::RecordError` gains `RewordWantsMessage`, `RewordOnly` and
  `Carry`, and `carry::CarryError` gains `MovingAMerge`, `MovingARoot`,
  `AlreadyThere` and `MovingOntoItself` — both are `#[non_exhaustive]`.

- The types the library returns are `#[non_exhaustive]`.
  A caller that built one with a struct literal, or matched one without a
  `..`, has to stop; reading their fields is unchanged. The types a caller
  supplies are deliberately not among them — `Recording`, `Amendment`,
  `Abandoning`, `Forgetting`, `RevisionDocument`, `OperationDocument`,
  `ResolutionDocument`, `fs::Entry` and `fs::Stamp` are still built by
  literal, and a field added to one of those is still a major version.

- `OfferError` and `ReceiveError` are `#[non_exhaustive]`,
  as every other error enum in the crate already was. A `match` over
  either now needs a `_` arm.

- `record::Recording` gains an `extensions` field, so a
  caller that constructs one by literal must add it — `BTreeMap::new()`
  is what every recording made on historica's own behalf passes, and what
  the CLI passes. A recording that states headers records them into the
  revision document, which means the revision's ID covers them.

- `record` now refuses a stated header whose key this
  format could define — one with no dot in it — with
  `RecordError::UnusableHeader`, naming the key and the fix. Nothing could
  state one before, so no existing caller can meet this.

- A bookmark's name may now have `/` in it, and the
  name is the whole path below `names/` rather than the filename. A
  store written by this release can hold `names/feature/x.txt`; a
  reader older than it lists that store's bookmarks without that one
  and reports nothing wrong, so a store holding nested names wants
  readers at this version or later.

- `StoreError::UnusableName` gains a `because` field
  carrying the sentence that says which rule the name broke, so a
  `match` naming its fields needs updating. The refusals themselves are
  wider than before in one direction — `/` is allowed — and narrower in
  several others: an empty component, `.`, `..`, a leading or trailing
  space, a control character and a name not in Unicode normal form C
  were all accepted before and are refused now.

- `check` walks `names/` recursively and reports what
  it finds there that is not a bookmark: a `.txt` file whose path is
  not a name this format could write is `ForeignFile`, and a symbolic
  link is `Unfollowed`. Both were skipped silently before.

- Removing a bookmark now removes the directories its
  name emptied, up to `names/` and no further, so an export that
  withdraws the last name under a directory leaves no empty one behind.

- `cargo xtask version`, `bump`, `changelog`, `release`, and
  `release-notes` no longer exist. Each now exits non-zero naming its
  replacement — `release <command>`, from diaryx-org/devtools, which must be on
  PATH. `cargo xtask ci`, `bench`, and the individual CI jobs are unchanged.


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

