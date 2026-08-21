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

historica has not been released. The first `## vX.Y.Z` heading below will cover
every commit since the beginning, including the stretch before the repository
adopted conventional commits — those land under **Uncategorised**, deliberately
visible, to be triaged into their real groups before the tag is cut.

## Unreleased

<!-- git-cliff:begin — generated; edits here are overwritten -->

### Added

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

- **core** — read a hex pair as a pair, rather than as a slice of two ([`e4b47b9`](https://github.com/diaryx-org/historica/commit/e4b47b973eabe686ab94bcc151ec4ec2d371d1ba))

### Uncategorised — triage before release

- Initial commit ([`8f18d50`](https://github.com/diaryx-org/historica/commit/8f18d50c7bd556feb36204367a92e924e6aa4dfe))
- Give every revision two identities ([`3af91e2`](https://github.com/diaryx-org/historica/commit/3af91e2e84431736a721aec196b558ff750a67f8))
- Propose the readable revision document ([`24fdaf3`](https://github.com/diaryx-org/historica/commit/24fdaf36cfffd43f3326b10ff41e6c254189982e))
- Free revision identity from the filename ([`67ffb96`](https://github.com/diaryx-org/historica/commit/67ffb9600cebb60de4c1b49243e4e69b177b564c))
- Answer the questions the format left open ([`211a91f`](https://github.com/diaryx-org/historica/commit/211a91febc0710c3257f664b3724f48fccbb6dbe))
- Spell the version as a preamble and shorten the change ID ([`e73d4f9`](https://github.com/diaryx-org/historica/commit/e73d4f945e4c69b1867c288e4f333505fa30f394))
- Reconcile the earlier decisions with content and merge ([`58c1cc0`](https://github.com/diaryx-org/historica/commit/58c1cc0503fe620b8e6f3277e50278caa12f0ce8))
- Require the blank line in an operation document ([`a6b4f70`](https://github.com/diaryx-org/historica/commit/a6b4f70de690fb476e6ab74db3cdbc2b4edf51d6))
- Read and write the revision document ([`05f6959`](https://github.com/diaryx-org/historica/commit/05f69592420f11ae7b0dc8810545be3ecd3c1f9f))
- Read and write the store ([`625311d`](https://github.com/diaryx-org/historica/commit/625311d4531a3480db41f024e6b11c83856d70e0))
- Read and write the operation document ([`711aa15`](https://github.com/diaryx-org/historica/commit/711aa15d7636cef01cdcf26ac68a2e806fdb5125))
- Replay a linear history into the file it produced ([`b75a464`](https://github.com/diaryx-org/historica/commit/b75a464374ae75b50ea181ba6565b67272259f71))
- Decide how operations are recorded from an edited file ([`e58d981`](https://github.com/diaryx-org/historica/commit/e58d981b817ccdb4f1248f2ca31f1714469103cb))
- Record operations from an edited file ([`f28a49d`](https://github.com/diaryx-org/historica/commit/f28a49d13b06860df01494d530a5bc8308d9649c))
- Decide the tree: files, paths, existence, and rename ([`747745b`](https://github.com/diaryx-org/historica/commit/747745bb9ed32adbf9ec5468a70b4d71b2b43f68))
- Read a tree, and replay one ([`fb4f0ab`](https://github.com/diaryx-org/historica/commit/fb4f0ab1873bfae83b04d93e8deffec2d82e0da1))
- Hold a store to the files it says it holds ([`4585343`](https://github.com/diaryx-org/historica/commit/4585343581cd19a48ecf9f8982db0a8a44d94130))
- Merge concurrent branches by walking their event graph ([`52cac80`](https://github.com/diaryx-org/historica/commit/52cac80a7a3b524b913c371c4e37aef076d2845d))
- Read a store from the command line ([`efe9cc8`](https://github.com/diaryx-org/historica/commit/efe9cc86c2041d7145021e2e6922329ee92fec85))
- Decide where a change ID, an author, and a time come from ([`85882f4`](https://github.com/diaryx-org/historica/commit/85882f40b12c4a09be4dbe9614abf3916ca74955))
- Close the writer's open questions ([`d884ba7`](https://github.com/diaryx-org/historica/commit/d884ba7c241922f8de1bbb259a5016e81bb20877))
- Decide what a writer is given ([`d12a506`](https://github.com/diaryx-org/historica/commit/d12a506a4d711577ecc07f8fc8fc9504046edb69))
- Decide how a conflict is shown and how a resolution is recorded ([`caa042b`](https://github.com/diaryx-org/historica/commit/caa042be08c455005805d145a5ea10e6e9636512))
- Decide how work is thrown away and how a store is pruned ([`164ba71`](https://github.com/diaryx-org/historica/commit/164ba71b033608a7930a625703827cfab8523b11))
- Record a revision from the folder beside the store ([`07da45e`](https://github.com/diaryx-org/historica/commit/07da45e52af3b63b4f409622577b1f35cd8ac636))
- Materialise a history that has a merge in it ([`fc479e8`](https://github.com/diaryx-org/historica/commit/fc479e8e4d42fe2bed64ec3b4378470e6e5a6384))
- Keep the error a caller returns small ([`a1fa06d`](https://github.com/diaryx-org/historica/commit/a1fa06d494cf98d0395325112a5a8e2c162cc059))
- Merge two lines of work, and record the resolution ([`0da71ad`](https://github.com/diaryx-org/historica/commit/0da71add957bcc5204728cb4e97b2d8ba1096853))
- Update .gitignore ([`60c0338`](https://github.com/diaryx-org/historica/commit/60c033862e3c501632327be58801d32e58c0b218))
- Update .gitignore ([`807a38a`](https://github.com/diaryx-org/historica/commit/807a38ac50038801b61344a33c3eaa9c7805d957))
- Decide what forgetting means under sync ([`b537721`](https://github.com/diaryx-org/historica/commit/b5377217cb74a3a3d8490213fded8286a5654074))
- Decide what status shows and what it is allowed to know ([`af28baf`](https://github.com/diaryx-org/historica/commit/af28baf1300353016f269b230b68004c1bab941d))
- Show how the folder differs from what is recorded ([`2e5d231`](https://github.com/diaryx-org/historica/commit/2e5d231b4db39afe2442c55a1686e7f7d7637112))
- Decide how a store reads to the person browsing it ([`77ab56d`](https://github.com/diaryx-org/historica/commit/77ab56dace8e9302cf79671dd3d7440578b44cb8))
- File a history where a person can find it, and say what it skips ([`6ce4ab9`](https://github.com/diaryx-org/historica/commit/6ce4ab9925f4680bbe0a0961cfa94efb402f7bec))

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

<!-- git-cliff:end -->
