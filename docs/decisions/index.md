# Decisions

Choices that constrain later work are written down as they are made. Each
document argues its case, states the decision, and says what it leaves open;
a later one that overturns part of an earlier one says so by number. They are
listed here in the order they were written, which is the order the arguments
depend on each other in.

- [0001 — Two identities: revisions and changes](0001-identity.md)
  Why every node carries both a derived revision ID and an assigned change ID.

- [0002 — The revision document](0002-revision-document.md)
  The readable revision document, and why its digest covers the file rather
  than a re-serialised model. Examples live in
  [`tests/corpus/revisions`](../../tests/corpus/revisions).

- [0003 — The store: content is identity, names are presentation](0003-store.md)
  The store: identity comes from content, filenames are presentation.

- [0004 — The parser's contract](0004-parser-contract.md)
  Strict reading, the preamble, and why a reader refuses what it does not know
  rather than guessing. Its numbered-version machinery is 0047's now: the
  format has one spelling, `historica`.

- [0005 — Authorship across rewriting](0005-authorship.md)
  Authorship is copied into every revision of a change, and is a claim rather
  than evidence.

- [0006 — Bookmarks, the store root, and what `check` says](0006-store-questions.md)
  One-line bookmarks, a visible `history/` root, and what `check` treats as an
  error rather than a note.

- [0007 — Content: what a revision changes, and how two of them merge](0007-content-and-merge.md)
  A revision records what it did rather than what a file is, and concurrent
  edits merge by replay rather than by three-way heuristic. Examples live in
  [`tests/corpus/operations`](../../tests/corpus/operations).

- [0008 — The tree: files, paths, existence, and rename](0008-tree.md)
  Files carry identifiers and paths hang off them, there are no directories,
  and a revision records what it did to the file set rather than what the file
  set is.

- [0009 — Recording operations from an edited file](0009-diff.md)
  How operations are recorded from an edited file, why the matcher is a
  dependency where the merge rule could never be, and the replacement
  anchoring 0007 left ambiguous.

- [0010 — What a writer must supply](0010-writer.md)
  The three facts a writer supplies and nothing can derive: 96 bits from the
  operating system, an author stated in a person's own configuration rather
  than guessed or kept beside the history, and the clock at the moment of
  recording. A rewrite the tool performs on its own behalf copies all three,
  so two replicas that rebase one change write one file.

- [0011 — The working copy](0011-working-copy.md)
  The folder beside the store is the working copy, `history/skipped/` says
  what it does not take, the parent is the head, and a rename is the one fact
  a person has to state. Nothing is remembered between commands.

- [0012 — Showing a conflict, and recording its resolution](0012-conflicts.md)
  Nothing conflicted is ever recorded, because two heads already are the
  conflict; contested spans are rendered into the working copy with markers a
  merge record refuses to accept, and a contested path is stated on the
  command line rather than invented.

- [0013 — Abandoning work, and pruning a store](0013-abandoning-and-pruning.md)
  Abandoning is a tombstone superseding the work, which is the state 0001
  already had a name for; pruning deletes superseded documents nothing names
  as a parent, is local, manual, and is the undo history.

- [0014 — Forgetting](0014-forgetting.md)
  Redaction that keeps a history working: a forgetting document destroys an
  operation document's payload and preserves its arithmetic, so everything
  downstream still materialises and merges; forgetting converges by union, an
  item is forgotten wherever it is quoted, and what survives is shape,
  authorship, and paths.

- [0015 — Status](0015-status.md)
  What status shows and what it is allowed to know: a comparison derived from
  the folder and the store with nothing remembered between commands, the
  survey the plan is derived from, and a refusal reported rather than raised.

- [0016 — The store a person reads by hand](0016-the-store-a-person-reads.md)
  The folder a person browses: operation documents filed under the revision
  that names them, a walk that recurses to any depth and never follows a
  symbolic link, and the command that writes a `skip` rule.

- [0017 — Content that arrives whole](0017-content-that-arrives-whole.md)
  Content no operation produced: a payload is a file of bytes named by its
  digest, stored beside the documents it is not one of, so a created file is
  itself in the store rather than a second copy with `+` down the left margin
  and an image is an image. `text` and `bytes` say which, a file's kind is
  fixed when it is added, and `add` with `edit` — the early spelling of a
  creation — is retired.

- [0018 — A path is a path](0018-a-path-is-a-path.md)
  A path is filed as a path: real directories for real components, nothing
  clipped, and no character standing in for `/`. 0016 nested the revision and
  then spent the length it bought on a homoglyph nobody can type; this spends
  it on the filesystem's own separator, so a revision's folder is the subtree
  that revision touched.

- [0019 — The name a store is written with](0019-the-name-a-store-is-written-with.md)
  `record` writes the readable name rather than a digest a command has to be
  run to replace, so the folder 0003 promised is the one a person gets. What a
  writer cannot know is what another replica wrote this morning, so a
  collision it cannot see degrades to the conflicted copy `check` already
  understands. `arrange` becomes the command that applies the scheme to a
  store that does not have it, and is deliberately not a lint: a name that
  differs is usually a person filing their own history.

- [0020 — A document says it is text](0020-a-document-says-it-is-text.md)
  Documents are written `.rev.txt` and `.ops.txt`, so the file a person
  double-clicks opens in the editor they already have. The older suffixes are
  read forever, because a store that quietly stopped having documents in it is
  the worst failure available; the cost is that a payload still has to avoid
  both.

- [0021 — The store explains itself, while strictness is still free](0021-the-store-explains-itself.md)
  The marker becomes `historica.txt` and carries a note saying what the folder
  is and that nothing in it needs Historica to read; `skipped` and the
  bookmarks follow the documents into `.txt`. The older suffixes stop being
  read, which retires the payload rule in the form that bit: an actual `.ops`
  file keeps its own name. It is the last decision that gets to break a store,
  because it is the last one written while none exists that its author did not
  write.

- [0022 — Names the store cannot own](0022-names-the-store-cannot-own.md)
  Recording `.DS_Store` and then opening the store in Finder destroyed the
  payload, because Finder writes a `.DS_Store` into every folder it displays.
  A payload is never filed under a name the store does not own, a file with
  such a name inside the store is somebody else's rather than content, and
  `init` writes a note in `skipped/` explaining the rule that keeps them out
  of a history that is append-only.

- [0023 — What an amendment keeps](0023-what-an-amendment-keeps.md)
  The head, rewritten: the change, the author, and the moment the work was
  first recorded are copied, `revised` is stamped because amending is an act a
  person performs, and every tree fact is worked out again from the folder —
  keeping the file identifiers the amended revision minted, because the same
  file in the same place is not a different file. A revision something stands
  on is refused, since reparenting a descendant is 0007's merge under another
  name; and the position becomes the head nothing has rewritten, which is the
  rendering question 0001 left to whoever needed an answer.

- [0024 — Naming a file](0024-naming-a-file.md)
  A file identifier is spelled `file:` where a path is expected, because
  0001's disjoint alphabets cannot partition a position that already holds
  every string a person may name a file; and a bookmark gains a third key,
  `file`, beside 0006's `change` and `revision`. That is the join an outside
  system gets: its own identifier cannot be Historica's, since digits would
  break the alphabets and 0008 mints rather than derives, but it can be the
  *name* of a bookmark, because a name is only ever a string.

- [0025 — The folder is asked for](0025-the-folder-is-asked-for.md)
  The format's claim on a folder stands; the assumption that the folder is the
  one the operating system is handing this process was never argued for. The
  library reaches it through `historica::fs::Filesystem`, `Store<F = Disk>`
  and `Working<F = Disk>` carry it as a type parameter with the bound on the
  `impl` blocks, and `Disk` is that trait over `std::fs` behind the default
  `disk` feature. The short constructors still mean `Disk`, so an embedding
  host supplies its own folder and nothing else in the design moves.

- [0026 — A mutable file changes all at once](0026-atomic-mutable-files.md)
  `create_new` gave the immutable files the one concurrency property they
  need, and the mutable ones — the marker, the bookmarks, the rules — did not
  have the matching one: `write` truncated, so a reader in between met an
  empty bookmark or half a rule. `Filesystem::write` becomes atomic
  replacement, and a reader sees the complete old value or the complete new
  one and never a prefix of either. The contract is one file rather than a
  transaction. A conflict between two people stays real; what stops leaking is
  the interval in which one writer writes.

- [0027 — The small questions close together](0027-closing-the-small-questions.md)
  The questions the earlier decisions accumulated, closed where closing them
  needs no new format. Canonical history records facts rather than
  diagnostics: no `normalize` for a recorded revision, contested regions are
  derived and never recorded, and previews are presentation. Explicit intent
  wins where inference cannot; a valid store and a representable folder are
  different questions; defaults belong to whoever knows the folder rather than
  to the library; the store's prose belongs to its reader; and a file bookmark
  keeps naming one identity.

- [0028 — Accepting bytes is a statement about a path](0028-accepting-by-path.md)
  `record --accept <path>`, for the case text does not have: a contested byte
  payload has no marker lines a recorder can find, so recording must not
  mistake whatever bytes are in the folder for a resolution somebody examined.
  Every contested byte path must be accepted and every acceptance must be
  necessary — a stale or unneeded one is refused rather than ignored — and an
  acceptance takes the bytes already in the folder rather than choosing a
  parent. The same review traces the deferred large features to one missing
  thing: Historica has replicas in its model and no remote in its interface.

- [0029 — Receiving another store](0029-receiving-another-store.md)
  `receive <dir>` is a one-way union of another local store into this one —
  the content-aware operation plain copying stops being once both copies have
  changed, and not a transport or a persistent remote. The source is never
  written, documents are compared by digest rather than filename, the working
  folders are outside the operation, both stores must pass `check`, and
  relatedness is the default with `--join-unrelated` to seed. Immutable
  content is written before the revisions naming it, so an interrupted receive
  leaves unreachable content rather than a revision pointing at nothing.

- [0030 — The folder catches up](0030-the-folder-catches-up.md)
  `update [<target>]`, 0008's last deferred word, decided on its own rather
  than as a side effect: the folder is only ever given a head, so the position
  0011 said would one day be necessary never is. Files the target records are
  written byte for byte what `cat` prints, files it does not record are
  removed where history holds their bytes, and everything else is left alone.
  Bytes no revision records are never overwritten and never deleted, and where
  such a file sits at a path the target holds the whole update refuses and
  names it — all or nothing, because a folder half-holding a head is worse
  than a folder that plainly is not there yet.

- [0031 — A document states its result](0031-a-document-states-its-result.md)
  The first half of the pair that makes a person with an editor and `shasum`
  able to verify as well as read. An operation document states `result
  <digest>` — the SHA-256 of the file its operations produce — mandatorily,
  because an optional header would be two spellings for one edit; replay
  refuses a state that does not hash to it, so two implementations that drift
  apart find out where it happened. A forgetting document states no result and
  is forbidden one: a digest of destroyed content is an oracle anybody who can
  guess the sentence can confirm, so verification is suspended wherever
  forgottenness reaches.

- [0032 — A merge states its resolution](0032-a-merge-states-its-resolution.md)
  The deeper half, and the one place "readable without the tool" was quietly
  untrue: a recorded merge's content was a delta against the algorithmic merge
  result, so everything downstream of a merge materialised only through a
  correct Fugue implementation, forever, in every language. A merge revision
  now names a resolution document for every file its parents disagree about —
  `keep <digest> <first> <count>` takes a run of items from a document that
  exists, a bare `insert` mints new ones, and the assembled sequence is the
  file. A resolution never restates content that has an identity, so merging
  across a recorded merge stays ordinary, and the event-graph merge demotes to
  proposing the draft a person edits and records.

- [0033 — One spelling for a path](0033-one-spelling-for-a-path.md)
  The two halves 0008 left together have different answers. Case is genuinely
  two names a person may deliberately have, and nothing here touches it.
  Normalisation is not: `café.md` composed and `café.md` decomposed are one
  name whose bytes depend on the filesystem, the editor and the decade. So a
  path in a document is in normal form C and `check_path` refuses anything
  else, a path arriving from outside is normalised on the way in, and the
  folder keeps the spelling the folder has — a composed twin laid beside a
  decomposed original being the exact failure the decision exists to prevent.

- [0034 — A file can be run](0034-a-file-can-be-run.md)
  The executable bit, which 0008 left out for a narrow reason and `update`
  then destroyed: a file recorded runnable came back plain, silently, in
  somebody's own folder. `mode <file> <value>` carries one bit and spells it
  as a word; a filesystem that cannot see the bit says so rather than
  reporting `false`, which is what makes a store safe to carry between a Mac
  and a Windows machine without configuration.

- [0035 — The cache is a file already named](0035-the-cache-is-a-file-already-named.md)
  `cache/` gets its first occupant, and the invalidation problem that kept it
  empty turns out not to arise. An entry is a file named by the SHA-256 of its
  own bytes holding some file's content at some revision, found by a digest
  0031 already made every document state, so the cache supplies only
  digest-to-bytes and invents nothing. Bytes are hashed before they are
  believed, so there is no state in which a stale entry is returned and only
  one in which it is ignored; and an entry is written under the digest found
  rather than the digest stated, which files a state carrying forgetting
  markers where nothing will ever ask for it.

- [0036 — Where a digest is](0036-where-a-digest-is.md)
  Identity coming from content is what left the store reading every file in
  `operations/` to find one digest, which 0035's cache could not help with
  because reaching the cache meant paying it first. A catalogue in `cache/`
  says where each digest is, believed only while the paths it names are the
  paths the directory holds, and a lookup still hashes what it reads. A
  catalogue that is missing, stale or wrong costs a pass over the directory
  and never an answer, which is 0003's promise; what a reader believes unread
  is which documents forget something, and `check` is excluded for exactly
  that reason.

- [0037 — What changed](0037-what-changed.md)
  `diff`, and the one place this tool renders rather than prints. The shape is
  borrowed because the world already reads it, the hunks are the decomposition
  `record` would write rather than a second one, and the difference from every
  other tool's diff is 0008: a rename between two revisions is a fact rather
  than a resemblance, while a rename in the folder is not a fact at all and is
  not rendered as one.

- [0038 — Who wrote this line](0038-who-wrote-this-line.md)
  `blame`, and the vector 0012 already computed. Attribution is read out of
  the operations rather than recovered from the bytes, so there is nothing for
  `-w` or `--ignore-rev` to steer and no similarity threshold to argue with; a
  line keeps its author through a rename (0008) and through a merge that kept
  it (0032), and a line the store recorded as new is new even where a person
  would call it moved. With no target the folder is the right side, as in
  0037, and a line only the folder has is marked rather than attributed.

- [0039 — Recording some of the folder](0039-recording-some-of-the-folder.md)
  `record <path>...`, which restricts what a record observes without inventing
  the index 0011 refused: the unnamed paths are not compared with anything,
  nothing is remembered past the command, and every fact recorded is still one
  the folder stated. A restriction may not spell half a rename, and a merge,
  which states what every contested file is, takes no paths at all.

- [0040 — A file can be a link](0040-a-file-can-be-a-link.md)
  A symlink, which the walk used to refuse and now writes down. There are two
  kinds of link and every other tool records them as one: a link to a file in
  this history is a reference to something the store knows by identity, and a
  path is 0008's least favourite way to spell an identity, so it is recorded
  as `file:<file ID>` and follows its target through every rename. A link to
  something outside is a string a person chose, and the honest record is the
  string. Resolution is lexical and against the tree, so nothing is ever
  followed and a received store saying `link kx.. ../../etc/passwd` produces
  an honest symlink and nothing else. The one cross-file rule this format has
  lives here too: a revision may not drop a file while a `file:` link still
  names it, and the recorder satisfies it by restating that link as the string
  the folder holds.

- [0041 — Where a revision is filed](0041-where-a-revision-is-filed.md)
  The flat directories 0016 chose, answered where 0003 deferred it: a store
  kept the way a journal is kept passes ten thousand entries without ever
  having been large, and a listing of five thousand is not a folder anybody
  opens. A revision is filed under its own year and month, read from `when` as
  spelled so every replica files alike, and the filename keeps the whole date.
  `arrange --refile` is the migration; plain `arrange` renames a revision
  where it sits, because 0016's "a name that differs is usually a person
  filing their own history" is as true of the command with hands as of
  `check`. Nothing in the loader changes, because it never read a name.

- [0042 — A copy to take away](0042-a-copy-to-take-away.md)
  `export <dir> [<target>]`, the sending half 0029 named by saying what it is
  not. No directory on disk holds the bytes a stranger should be given: the
  folder carries unrecorded edits and every file a `skip` rule exists to keep
  private, and `history/` carries bookmarks, rules, and a cache that are the
  exporter's. So the command *builds* that directory — the folder as the
  target has it, and the target's ancestry closed over the documents and
  payloads it names and every forgetting document touching any of it, since
  0014 always travels. The result is an ordinary store whose pull is
  `receive`, so clone and pull turn out to have been one design. Ancestry
  closes over parents and nothing else: a `supersedes` line may name a digest
  the copy does not hold, which is what 0001 has said all along — the
  successor carries the evidence.

- [0043 — What a command does not have to read](0043-what-a-command-does-not-have-to-read.md)
  The folder gets 0036's catalogue, and a payload stops being held to be
  hashed. `cache/working.txt` says what each tracked path hashed to, believed
  per entry while the directory still reports the size and the time it was
  taken at, and refused for any entry not strictly older than the catalogue
  itself — git's racily-clean rule, for git's reason. The size and the time
  0025 kept out of `Filesystem` come back as a declinable capability, because
  nothing here is ever an answer: a folder that reports neither reads every
  file and says the same things. And `fs::digest_of` streams, so the six
  places that read a file whole purely to learn which digest it is now hold a
  buffer instead. Deleting `cache/working.txt` changes how long a command
  takes and nothing else.

- [0044 — What this copy has held](0044-what-this-copy-has-held.md)
  0022 could not tell a payload still in transit from one something
  overwrote, because absence cannot. This copy can: it was present for its own
  history. `cache/witnessed.txt` holds a digest per line for every payload and
  document `record` filed, `receive` accepted, or `check` walked past, and a
  witnessed absence is an error where an unwitnessed one stays the note 0027
  worded. It is consulted only where `check` already decided to report
  something, so a forgetting document still reads as `Forgotten`; it produces
  a severity and never a byte, which is what makes a fact nothing can verify
  safe to keep; and it is a cache, so deleting it drops every error back to
  the note it was. It does not travel, because a replica that never held a
  payload should not inherit the claim that it did. The same document gives
  `PLATFORM_NAMES` the criterion 0022 said it would need — a name a program
  writes into every directory it touches, unprompted — adds `@eaDir` on it,
  and says why the list is not gated by the platform running it.

- [0045 — One rule to a file](0045-one-rule-to-a-file.md)
  `skipped.txt` becomes `skipped/`, one rule to a file. What the file held was
  always a set — `skips` is `any(covers)`, with no order, no duplicates and no
  negation — and only the container was a sequence, which is the thing two
  writers cannot both append to. So two replicas each adding a rule stop being
  a conflict `receive` refuses over, and two `skip` commands on one machine
  stop being a read-modify-write, because adding a rule is `create_new`. The
  label mirrors the path and the content is the rule, since `skip docs/drafts/`
  holds a character no filename does; 0018's collision suffix and 0022's
  platform names apply unchanged. Removal has no tombstone and a later receive
  may resurrect a rule, which is the recoverable half of 0011's asymmetry and
  loud besides, since `record` already refuses over a rule covering a tracked
  file, and `check` names the rule file to delete where one arrives that way.
  The old `skipped.txt` is not read, not converted, and reported by `check`,
  which is the whole of the migration a library this young owes anybody.

- [0046 — Who vouches for a revision](0046-who-vouches-for-a-revision.md)
  The digest machinery answers whether these are the bytes and is silent on
  whose word they are, and the answer is more readable files rather than a
  signature spliced into the hashed object. A claim is a document vouching for
  a revision's digest — which pins its whole ancestry — signed with minisign,
  detached, in `history/claims/`, verified by a separate tool with two
  commands and no Historica. Claims union freely because a claim is a fact;
  the trust policy in `history/trust/` never crosses a store boundary, because
  trust is an opinion and authority must not flow from the party it exists to
  judge. Historica's whole contribution is tolerance, stated: a root directory
  it does not name belongs to whichever tool wrote it.

- [0047 — One spelling for the format](0047-one-spelling-for-the-format.md)
  The numbered preambles retire. `historica-v0` through `historica-v5`
  recorded the order this format was designed in, not a compatibility level
  anyone shipped a reader for, so 1.0 flattens them to the one spelling
  `historica` and the grammar under it is the union the versions were
  converging on. The gate 0004 built is unchanged in kind — any other spelling
  on line one is refused, the pre-1.0 spellings by name — and a future
  incompatible format takes a new spelling rather than a number. No migration,
  because nothing was published and re-preambling a content-addressed store is
  a rewrite no command should pretend otherwise about.

- [0048 — Asking for what is missing](0048-asking-for-what-is-missing.md)
  The incremental half 0042 deferred, which turns out not to be a set
  difference: a fetcher already knows its own half, and what a URL cannot do
  is say what it holds. `historica offer` prints that listing — kind, digest,
  what the entry forgets, and the path, with the heads above it — and
  `historica fetch <url>` asks for what it lacks, verifying every arriving
  file against the digest before believing it. The convention is one sentence:
  `offer.txt` at a root, paths relative to it, nothing a plain web server does
  not already do. `check` on the source is the rule that cannot survive a URL,
  and what replaces it is stated rather than assumed. `export` and an archive
  stay the clone; this is the pull.

- [0049 — What a lookup does not prove](0049-what-a-lookup-does-not-prove.md)
  0036 believed its catalogue only while the paths it names are the paths the
  directory holds, and that condition is a directory walk every content
  command paid for. A hit never needed it: the reader goes to the path, reads
  it, and hashes it before believing a byte, so a catalogue that is wrong can
  only fail to find bytes. So a reader takes the catalogue without walking,
  and an absence — a claim about every file in the directory, which no hash
  can check — still pays the pass. A writer walks once per command, because
  "does the store already hold these bytes" is an absence too, and answering
  it from a catalogue three documents behind would file a second copy of each.

- [0050 — Forgetting a merge's own text](0050-forgetting-a-merges-own-text.md)
  0032 gave `operations/` a second grammar and 0014's stand-in was written in
  the first, so the one kind of text a merge states that exists nowhere else
  was the one kind that could not be redacted. A resolution may now forget in
  its own grammar: a `forgets` header, every `keep` stated exactly and every
  `insert` at its own length, and `\ forgotten` where a destroyed item's text
  stood. A `keep` is never redacted — it carries a reference and no text, and
  the items it keeps are forgotten in the document that wrote them, which is
  what preserving shape was always for. A forgetting resolution states no
  `result`, for 0031's reason, and redactions union as they always did.

- [0051 — Two axes for a rule](0051-two-axes-for-a-rule.md)
  0042 called rules the exporter's and 0045 called them a fact about the
  repository, and both cannot hold: `receive` unions them and `export` drops
  them, so a copy reaches a collaborator without the `skip target/` that would
  keep their build output out of it, while the privacy that buys is undone by
  the first receive from an origin. So a rule has a second axis. A `skip` rule
  travels and `private <path>` does not, spelled as a key rather than a bit on
  a rule, because a bit has to merge and a key cannot disagree with itself —
  and where both spellings cover one path, that is a contradiction `check`
  names at error rather than a tie-break the union has to invent. Travel being
  orthogonal makes the keys a cross product, so the matching side is settled
  too: `skip-name <name>`, one path component in which `*` matches any run of
  characters, subsumes `skip-suffix` and reaches the `draft-*.md` that prefix
  and suffix together cannot. The danger in a glob was never the star but the
  separator, and a value holding no `/` has no dialect to quarrel over. Four
  keys, and the set closes. The ceiling is stated outright: an export carries
  operation documents verbatim, so no rule can filter recorded content without
  costing the copy its replica identity, and `private` is a rule about a rule.

- [0052 — The copy a stranger fetches from](0052-the-copy-a-stranger-fetches-from.md)
  0048 left the root `offer.txt` sits at to a convention, and its one example
  read as an instruction to publish the store — which 0042 spent a whole
  decision refusing, and which HTTP makes worse: a file server hands out any
  path asked for, so not listing `skipped/` withholds nothing from anybody
  willing to type one. The thing at the URL is an export with the manifest
  beside it, `fetch <url>` takes the manifest's URL and every path resolves
  against the manifest's own directory, and `export <dir>` updates an export
  it already made where the destination is related and passes `check`. A copy
  holding a revision the origin lacks is refused, naming `receive`: export
  assembles and does not merge.

- [0053 — Room for another tool](0053-room-for-another-tool.md)
  0046 reserved `claims/` and `trust/` for a tool outside historica and
  promised tolerance for the rest, which is enough while nothing moves and
  silent the moment a store crosses a boundary. So a reservation declares how
  the directory travels, and transport acts on the class rather than on which
  tool wrote it: `travels-and-unions` for immutable digest-named files, which
  `export` carries and `receive` unions add-only; `local-only` for a directory
  that never crosses in either direction; `derived` for one that is nobody's,
  which is what `cache/` has always been. An unreserved directory is
  `local-only`, because leaving something behind is the recoverable way to be
  wrong. `claims/` travels whole rather than filtered to the exported
  ancestry, since the filter needs a grammar 0046 refused historica, and since
  a claim covers everything its revision descends from — so the claim worth
  having is usually the one over a later head the filter would drop. The
  second half is the rest of the plugin surface: a side tool is an ordinary
  crate against the published API, an extension point historica must call
  arrives as a trait, and subprocess dispatch and in-store executable hooks
  are refused — an embedding host cannot exec, and a store that travels must
  not be a thing that runs.

- [0054 — A union does not withdraw](0054-a-union-does-not-withdraw.md)
  0053 said `export` carries a travelling directory whole, which was complete
  while an export crossed the boundary exactly once; 0052 made it something
  that happens repeatedly onto one destination, and the rest of that export is
  a diff that withdraws. A travelling reserved directory unions in both
  directions and at every run: `export` carries what the copy lacks, with
  `create_new`, and withdraws nothing. The class is the reason rather than the
  tool, because withdrawal is a merge rule — it reads a name present here and
  absent there as *deleted* rather than *not yet arrived* — and that is a
  grammar transport has promised not to learn. Everything this format
  destroys, it destroys because a document says so.

- [0055 — The folder an export wrote](0055-the-folder-an-export-wrote.md)
  An incremental export that withdraws destroys the record its own copy's
  folder was materialised from, so by the time `update::plan` runs the bytes
  in that folder are unrecorded and 0030 refuses — a true sentence about a
  store and a false one about a folder nobody has ever worked in. So an export
  replaces the folder it wrote and refuses a folder somebody changed, and the
  question is settled against the copy as it arrives and acted on afterwards,
  because "has anybody touched this" has an answer at the start of the run and
  none at the end. It is asked only where something is being withdrawn, and
  nothing 0052 refuses is waived to ask it.

- [0056 — Listing what it cannot read](0056-listing-what-it-cannot-read.md)
  0048's three kinds have no word for a rule file or for a file of a
  travelling reserved directory, and 0052 made both arrive in every published
  copy — so the first manifest written against a published export named
  neither, and a fetcher built a replica nothing vouched for, silently. `rule`
  names one file of `skipped/`, the shared ones only, since historica owns
  that grammar and 0051 gave a rule an axis saying whether it travels.
  `reserved` names one file historica carries and cannot read — one word
  however many directories are ever reserved, saying what the file is to
  historica rather than whose it is. The path is the address and is enough to
  file the bytes by, which is what makes the directory union wherever it
  lands.

- [0057 — The stack a fetch rides on](0057-the-stack-a-fetch-rides-on.md)
  0048 put the transport behind a one-method source and named no
  implementation, but `historica fetch` has to be some particular program
  making some particular request — which decides what certificate roots it
  trusts and who ships the fix when that stack has a hole in it. Exec'ing
  `curl` is refused out loud: what that trusts is whichever file is first on
  `PATH` at the moment of the request. The binary links the platform's own
  HTTP stack through `nyquest` — WinRT, NSURLSession, libcurl — so a fetch
  rides the system's TLS roots, proxy configuration and update cadence, none
  of which this repository has to ship or be late with. Versions are pinned
  exactly because nyquest is early, and it is behind an `http` feature that is
  on by default, so `--no-default-features --features disk` builds every other
  command with no transport compiled in.

- [0058 — What a command does not have to open](0058-what-a-command-does-not-have-to-open.md)
  0036 removed the cost of finding a digest and 0043 the cost of taking one;
  neither touched the directory every command reads first. Opening a store
  performs one read and one parse per file in `revisions/`, and since a
  revision document holds the whole of the graph, no command escapes it —
  `names` opened six hundred files to print four lines. The bytes were never
  the cost, the opens were. So `cache/revisions.txt` holds every revision
  document verbatim, behind a line stating its digest, size, modification time
  and path. Bytes rather than facts: a cache of parsed facts would be a second
  grammar kept in step by hand and would have to be believed, where bytes can
  be hashed for three tenths of a millisecond — the cheapest way to make a
  cache incapable of inventing a history. An entry is taken only while its
  bytes hash to the digest it claims, the directory reports the size and time
  it recorded, and that time is strictly older than the file holding it, which
  is 0043's racy rule unchanged. The stamps are what a store of immutable
  files could be argued not to need, and they are here because the readable
  files are the authority: a cache believed on immutability alone would go on
  printing what a hand-edited document used to say. Nothing derived is written
  down, so it is a cheaper way to reach the documents rather than an index of
  the graph, and `check` opens everything itself.

- [0059 — Carrying a descendant across](0059-carrying-a-descendant-across.md)
  The wall three decisions stopped at — restating a descendant's operations
  against a parent whose content moved is 0007's merge under another name —
  walked through by running that merge under that name. `carry` restates a
  revision standing on a rewritten one against the rewrite: what describes
  the work is copied, `revised` comes from the cause per 0010's
  carried-along row, a file whose base did not move names the same operation
  documents, and one whose base did is restated by replaying the delta
  between the bases concurrently with the descendant's own operations —
  refusing whole where they meet, because contested regions are a person's.
  Nothing is stamped or minted, so two replicas repairing one history write
  byte-identical files, and `check`'s note now names the command. The plain
  re-diff 0023's `## Since` sketched is corrected on the way: taken
  literally it would revert the rewrite wherever the descendant was silent.
  The inline acts — amend and abandon above a descendant, and moving a
  change — wait on the spelling questions the decision leaves open.

- [0060 — The copy without the history](0060-the-copy-without-the-history.md)
  0042 and 0052 both build a repository, which is the right default and not
  always what was wanted: exporting the three-hundredth revision of a
  six-hundred-revision store writes 14 MB, of which 13 is `history/`. Somebody
  reading what a file said last month wants the other one. `export` already
  reached the past — it accepts any target, not only a head — so what was
  missing was a way to decline the ancestry, not a capability. It arrives as
  `--files-only` rather than a command of its own, because a second command
  would duplicate the target resolution, the materialisation, the rule
  filtering and the printing to do strictly less, and because every name for
  it describes a tool this is not. What that costs is admitted: no other flag
  here changes what its command produces, and this one turns a repository into
  a directory. The folder is the one a whole export writes, filtered by the
  same travelling rules and pinned byte-identical by the tests; the
  destination must be empty, because 0052's update-in-place needs the copy's
  own history to say what the last run put there; and a broken store still
  refuses, because a copy of a fault is two faults.

- [0061 — What a command does not have to parse](0061-what-a-command-does-not-have-to-parse.md)
  0058 left the parse as the largest cost of opening a store and called that
  the honest place for it, since a cache that removed it would be a cache that
  had to be believed. True of a cache, false of the parse: what a graph
  question needs is `core::Revision`, and every field of it is a header of
  rank 0 to 2 or the verbatim message, so the author, the moment and the whole
  tree were being parsed by every command for almost none of them. The reading
  walks the same lines and holds them to the same rules about a document's
  shape; what it sheds is the interpreting and the allocating, two thirds of
  what a parse is — 9.30 µs a document on a store of twenty files against 3.11
  for the revision alone. `format::revision` reads that much and
  defers the rest to whatever asks, refusing at open everything refusable
  without reading a value, so what moves later is the meaning of a timestamp
  or a path and never the shape of the document. Behind it was a larger cost
  the measuring turned up: `Store::history` reached the graph through
  `to_revision`, whose `id` is `digest(&self.write())`, so asking a store for
  its shape re-serialised and re-hashed every document in it to arrive at the
  name each was already filed under — 7.3 ms a call on six hundred revisions,
  and `log` makes three. A store now holds each revision beside the digest it
  was read from. Nothing is written down and nothing believed: the settled
  half of the argument is that a cache of facts cannot be checked more cheaply
  than by parsing, because 0002's digest covers the whole file and leaves
  nothing smaller to check a part against. Over three stores, alternating the
  binaries call by call: `status` 48 ms to 27 and `names` 14 to 11 on six
  hundred revisions over twenty files, `status` 201 to 112 and `names` 50 to 34
  on twenty-five hundred, and `files` and `cat` at a head paying 13% to 20%
  more, since they are what wants every tree. Two earlier tables are recorded
  there as superseded, along with the way each was wrong. What is left largest
  is the per-document stamp, measured here and deferred to its own decision.

- [0062 — Two axes for a bookmark](0062-two-axes-for-a-bookmark.md)
  0042 left bookmarks behind on the same sentence 0051 took apart for rules,
  and the argument transfers whole: an export is a replica and `receive` is
  its pull, so a copy that meets its origin unions the withheld names straight
  back — an exclusion that binds only where it is useless. The half 0042 got
  right transfers too, since `fix-acme-layoffs` states in its own filename
  what `private clients/acme-layoffs/` exists to withhold. So a shared
  bookmark travels, and `private` is a second line the file may carry. The
  marker is a line rather than a sixth key because 0024 already proved the
  pointing vocabulary open, and the cross product 0051 could afford this one
  cannot; 0006 refused a second line that could *disagree* with the first,
  which a travel axis cannot. It is a field rather than a key because 0051's
  refusal turns on `skipped/` being a set — `names/` is a map with a
  disagreement rule since 0006, so the target conflicts as it always did and
  the axis joins toward private, reaching a person's other machines by the
  transport that already runs. A bookmark pointing past the export stays
  behind whatever its axis, on the rule that an export never manufactures a
  finding the origin did not have. Reverses one sentence of 0052 and the test
  named for it: a copy holds no record of which of its bookmarks an export
  wrote, so the update is all or nothing, and withdrawing nothing would leave a
  name in a world-readable directory after the origin made it private. `offer` gains a `name` kind and `fetch`
  takes only names it lacks, so a publisher moving `main` costs a fetcher
  nothing. The ceiling is stated outright: the revisions are in the copy, so
  `private` withholds the label and nothing else. Declines the store-layout
  gate a third time, and says why that is the document's least defensible
  sentence.

- [0063 — A range of revisions](0063-a-range-of-revisions.md)
  `log <from>..<to>`: everything behind `to` that is not behind `from`, as a
  subtraction of two ancestries rather than a walk, so it is defined for two
  revisions the graph left concurrent. Git's spelling, for 0037's reason.
  Goes in the argument position 0001 partitioned, where neither alphabet
  holds a full stop; a bookmark is looked up whole first, on the rule that
  already lets one beat `head`. Both ends are said outright, `a...b` is
  refused by name, and an empty range is an answer rather than a fault. What
  prompted it is that `bisect` was declined as a command and the shell script
  standing in for it could not compute the set it had to bisect.

- [0064 — A listing for something that is not a person](0064-a-listing-for-something-that-is-not-a-person.md)
  `log --fields`, paying 0063's deferral. Most of a history is machine-readable
  already, because 0003 makes the files the authority and `show` prints one
  byte for byte — so what this adds is only what no single document holds:
  which revisions, in what order, and what the graph found about them. A
  numbered header on 0048's reason, then `<digest> <change> <when> <marks|->
  <parent>...` — spelled whole, because an abbreviation is a fact about the
  store rather than about the revision; single-spaced and unescaped, because
  choosing these fields and no others leaves nothing that can hold a space.
  Author and message are not restated, on 0037's refusal of a second answer.
  Nothing to show is a header with no lines under it.

- [0065 — The header another tool wrote](0065-the-header-another-tool-wrote.md)
  The mark on an ignorable header is re-spelled: a key with a dot in it is some
  other tool's, `diaryx.review-url`, and a key without one is this format's to
  define. 0004's answer to RFC 6648 is untouched — it was about permanence, and
  the complaint was about reading, since `x-` was the one abbreviation in a
  grammar that spells out `supersedes`. A word in that place attaches to the
  fact instead of the header, and a registry of recognised keys cannot help the
  reader the rule exists for: the old one, whose list cannot hold a key added
  after it shipped.

- [0066 — Forgetting a payload](0066-forgetting-a-payload.md)
  The case 0014 deferred and 0017 designed without building: a file of bytes
  destroyed whole, with a document of two headers — `forgets` and `length` —
  standing where the payload sat. The deferred case turns out to be the easy
  one, because a payload has no items, no grammar and no chain, so there is no
  shape to preserve and the stand-in is a statement rather than a
  reconstruction. `length` is the only shape there is and is kept, which also
  makes two replicas' redactions one file. A third grammar in `operations/`,
  dispatched on a header rather than on an empty body, and no format version,
  since 0004 charges only for retiring a spelling. Content addressing does
  0014's walk in advance — one destruction reaches every quote — while each
  version of the file stays its own payload, which the command says out loud.
  A forgotten payload cannot materialise at all, and no placeholder is
  invented for it; `check` calls the absence forgotten rather than missing,
  which is the branch 0044 wrote down and waited for.

- [0067 — Content that arrives whole is named, not carried](0067-content-that-arrives-whole-is-named-not-carried.md)
  0017's last deferral, and it turned out not to be about size. What a revision
  says about a file of bytes is `bytes <file> <digest>`, and the type that
  carried the answer said the bytes instead — so materialising cloned a
  photograph, a survey held every changed one at once, and an `update` plan
  carried the whole folder before writing any of it. `Content::Whole` and
  `Change::Whole` name the payload now, `Content::bytes` becomes
  `Content::digest` because every caller was comparing rather than reading, and
  the bytes are asked of the store in pieces — verified before a byte is handed
  over, because the file is found by hashing it. `write_in_pieces` mirrors
  0043's `read_in_pieces` on the same declined-capability terms, and its one
  extra promise — a refusal at the last piece leaves the destination as it
  stood — is what lets a copy hash as it goes and land only if it matched. What
  is paid is 0025's narrowed window, for a file of bytes and no other, since a
  conditional write cannot be handed bytes nobody is holding.

- [0068 — The package a caller pays for](0068-the-package-a-caller-pays-for.md)
  0025 and 0057 both said the front end was the front end, and the manifest
  disagreed: `disk` and `http` were default features of one crate, so
  `historica = "1.0"` compiled a platform HTTP stack in order to build
  `src/cli/fetch.rs`, which the caller had no way to call. One line
  (`default-features = false`) was the escape and historica-git had not found
  it. Two packages instead — `historica` the library with `disk` alone, and
  `historica-cli` with the commands, nyquest and `http` — settled at 1.0
  because default features are semver and the correction would otherwise be a
  2.0. The program is still called `historica`; what changes is that installing
  it is `cargo install historica-cli`, which is the cost, taken knowingly.

- [0069 — A place to say a store is newer](0069-a-place-to-say-a-store-is-newer.md)
  0045, 0051 and 0062 each wanted a store-layout gate and each deferred it;
  0051 said a third should build it and 0062, the third, called its own
  declining indefensible. This is the fourth and still does not build it —
  what it notices is that 1.0 would not merely lack the gate but *foreclose*
  it, since `check_header` takes the first line and discards the rest, 0046
  hands every unclaimed root name to another tool, and `check` never
  enumerates the root, leaving nowhere a shipped 1.0 reader would ever see a
  warning. So the space is reserved and nothing else: `historica.txt` is read
  as a document's shape — preamble, headers to the first blank line, then the
  note — and that header block is closed and empty, so a line in it refuses
  the store and names a newer Historica as its writer. The block can be there
  because the file is not hashed; it could never be in a document, since a
  line added to one renames it.

- [0070 — Writing the header another tool wrote](0070-writing-the-header-another-tool-wrote.md)
  0065 said what a reader does with a dotted key and left nobody able to write
  one: `record` filled `extensions` with an empty map, so the room 0065 made
  was room no tool could reach. `Recording.extensions` is the way in, wanted by
  historica-git, whose round trip back to git is exact except for the facts
  this format has no word for — a committer distinct from the author, a
  stripped signature — and they belong in a header rather than beside the store
  because 0065 already puts them in the canonical bytes and 0023 already
  carries them across an amendment. The encoding git also states did not cross,
  and says what the field is not for: a claim *about* a message historica has
  already re-encoded would file a commit that contradicts itself. The writer checks the key
  rather than trusting the caller, since a dotless one would file a document
  historica's own parser refuses. `Amendment` gets no field: carrying forward
  stays the whole of it until something has to restate.

- [0071 — A name with structure in it](0071-a-name-with-structure-in-it.md)
  `set_bookmark` refused a `/` and no decision had ever argued the flatness —
  0021 gave the `.txt`, 0024 the identifier clash, 0062 the travel axis, none
  of them the slash. A bookmark's name is now its whole path below `names/`,
  so `names/feature/x.txt` is `feature/x`, and the grammar is 0018's read
  rather than restated. The urgency is 0016's: `check` skipped a directory and
  the loader listed one level, so a nested store read as a store with fewer
  bookmarks and `check` called it healthy — a 1.0 shipping that would foreclose
  the fix, 0069's argument in the one directory where a filename is data. Two
  of 0018's refusals turn out to be load-bearing: flatness was doing the
  traversal guard at transport ingress as a side effect, and `..` and a leading
  `/` now do it on purpose.

- [0072 — A command this tool does not have](0072-a-command-this-tool-does-not-have.md)
  A word the command table does not hold is looked for on `PATH` as
  `historica-<word>` and run with the arguments as given, so `historica git
  import` is `historica-git import`. 0053 refused subprocess dispatch as a
  *plugin mechanism*, and that argument is about capability — a host with no
  `PATH` cannot extend through one — where this is about spelling, which a host
  with no command line was never using. Nothing is registered, authorised, or
  remembered: the mechanism is `PATH` and a naming convention. The word must be
  ASCII letters, digits and interior hyphens, because `Command::new` resolves a
  separator as a position rather than through `PATH`; `-C` becomes the child's
  directory; the child's code is this one's; a built-in wins and shadows
  silently. Behind a feature, off where `http` is, since a wasi guest has
  neither a `PATH` nor a process. Rejects a nushell-style registry — nu caches
  signatures it needs at parse time and this has none to cache — and rejects
  folding the side tools into the CLI, which either adds a release lockstep or
  spends the compiler-enforced boundary 0053's promise is made of.

- [0073 — Taking a name back](0073-taking-a-name-back.md)
  Bookmarks had an ingress and no egress: `set_bookmark` is 0071's one door in,
  `remove_name` was `pub(super)` for 0062's withdrawal alone, and the only way
  a person could delete one was `rm history/names/main.txt` — which works,
  silently, leaving 0071's empty directory and saying nothing about what the
  name pointed at. `Store::remove_name` is public and `name --delete
  <bookmark>` is the command, in `name` rather than a word of its own, one
  bookmark at a time, refusing the flags that shape a target because a bookmark
  that is going has nowhere to point. One removal for both of 0062's axes; a
  name already gone answers `false` to the library and fails at the command
  line, since the export works from a plan and the person believes the name
  exists. The deletion is local and says so — `receive` fills in every name the
  receiver lacks, and the tombstone that would change that is 0054's merge rule
  in the one directory 0006 calls the entire conflict surface. Nothing recorded
  goes: 0013 prunes only superseded work, which is what lets this skip git's
  merged-ness check and its reflog. Defers a prefix deletion, which 0071 made
  spellable and which is the first operation here whose blast radius depends on
  what the store holds.

Not a decision, but the evaluation one of them rests on:
[`docs/loro.md`](../loro.md) — the initial Loro evaluation, and the conditions
that would reverse it.
