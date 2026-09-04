//! `fetch`, exercised as decisions 0048, 0052, 0056 and 0057 describe it.
//!
//! The source here is always a directory on this machine, which is not a
//! concession to testing: decision 0048 puts the transport behind one method so
//! that a local directory is an honest implementation of it rather than a
//! special case, and everything these tests hold `fetch` to is true of a web
//! server for exactly the same reasons. Nothing in this file opens a socket.
//!
//! What is under test throughout is that a manifest is an *instruction to ask*
//! and never an authority: every file is hashed against the digest the listing
//! gave, every file lands under the name this store derives, and a publisher
//! moving underneath a fetch costs a request rather than a wrong store.

use std::cell::{Cell, RefCell};
use std::collections::BTreeSet;
use std::fs;
use std::io;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

use historica::core::RevisionId;
use historica::format::digest;
use historica::store::{FetchError, Source, Store, Travel, Unreachable};

/// The manifest's own name, which decision 0052 makes one more path resolving
/// against the directory it sits in.
const MANIFEST: &str = "offer.txt";

fn scratch(test: &str) -> PathBuf {
    let path = Path::new(env!("CARGO_TARGET_TMPDIR")).join(format!("fetch-{test}"));
    let _ = fs::remove_dir_all(&path);
    fs::create_dir_all(&path).expect("a scratch directory");
    path
}

fn run(directory: &Path, arguments: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_historica"))
        .arg("-C")
        .arg(directory)
        .args(arguments)
        .env("HISTORICA_AUTHOR", "Adam Harris <adam@example.com>")
        .output()
        .expect("the binary this test crate builds")
}

/// Everything the command printed, having succeeded.
fn out(directory: &Path, arguments: &[&str]) -> String {
    let output = run(directory, arguments);
    assert!(
        output.status.success(),
        "`{}` failed: {}",
        arguments.join(" "),
        String::from_utf8_lossy(&output.stderr)
    );
    String::from_utf8(output.stdout).expect("printed text")
}

fn write(directory: &Path, path: &str, text: &str) {
    let file = directory.join(path);
    if let Some(parent) = file.parent() {
        fs::create_dir_all(parent).expect("a directory");
    }
    fs::write(file, text).expect("writing a file");
}

/// An empty repository with a store in it.
fn repository(test: &str) -> PathBuf {
    let directory = scratch(test);
    assert!(run(&directory, &["init"]).status.success());
    directory
}

/// The store inside a repository, opened.
fn store(repository: &Path) -> Store {
    Store::open(repository.join("history")).expect("a store")
}

/// Publish `origin` at `root`: the export under `store/`, the manifest beside
/// it. What a person types is `historica export` and `historica offer >`.
fn publish(origin: &Path, root: &Path) {
    let copy = root.join("store");
    out(origin, &["export", &copy.to_string_lossy()]);
    let manifest = out(root, &["offer", "store"]);
    fs::write(root.join(MANIFEST), manifest).expect("the manifest beside the copy");
}

/// A published root, read as a fetcher reads it: a path in, bytes out.
///
/// Decision 0048's one method, implemented over `std::fs`. Absence is
/// `Ok(None)` — a path the publisher has moved on from — and everything else it
/// could not do at all is the error.
struct Directory {
    root: PathBuf,
    /// Every path asked for, in the order it was asked for, which is where the
    /// interruption invariant is read from.
    asked: RefCell<Vec<String>>,
    /// How many more requests this will answer before the transport fails.
    answers: Cell<usize>,
    /// A manifest to serve once, in place of the one on disk: a fetcher holding
    /// a listing the publisher has since rewritten.
    stale: RefCell<Option<String>>,
}

impl Directory {
    fn at(root: &Path) -> Self {
        Self {
            root: root.to_path_buf(),
            asked: RefCell::new(Vec::new()),
            answers: Cell::new(usize::MAX),
            stale: RefCell::new(None),
        }
    }

    /// Serve `text` the first time the manifest is asked for, and what is on
    /// disk every time after.
    fn holding(self, text: &str) -> Self {
        *self.stale.borrow_mut() = Some(text.to_owned());
        self
    }

    /// Answer this many requests and then stop, as an interrupted fetch does.
    fn answering(self, requests: usize) -> Self {
        self.answers.set(requests);
        self
    }

    fn asked(&self) -> Vec<String> {
        self.asked.borrow().clone()
    }
}

impl Source for Directory {
    fn get(&self, path: &str) -> Result<Option<Vec<u8>>, Unreachable> {
        self.asked.borrow_mut().push(path.to_owned());
        if self.answers.get() == 0 {
            return Err(Unreachable::saying("the connection went away"));
        }
        self.answers.set(self.answers.get() - 1);
        if path == MANIFEST
            && let Some(stale) = self.stale.borrow_mut().take()
        {
            return Ok(Some(stale.into_bytes()));
        }
        match fs::read(self.root.join(path)) {
            Ok(bytes) => Ok(Some(bytes)),
            Err(error) if error.kind() == io::ErrorKind::NotFound => Ok(None),
            Err(error) => Err(Unreachable::saying(error)),
        }
    }
}

/// A repository with one of everything a fetch has to decide about, and the
/// published copy of it.
fn published(test: &str) -> (PathBuf, PathBuf) {
    let origin = repository(test);
    write(&origin, "notes.md", "one\n");
    fs::create_dir_all(origin.join("notes")).expect("a directory");
    fs::write(origin.join("notes/photo.png"), [0u8, 1, 2, 255]).expect("a picture");
    out(&origin, &["record", "-m", "Start a journal"]);
    write(&origin, "notes.md", "one\ntwo\n");
    out(&origin, &["record", "-m", "A second thought"]);

    out(&origin, &["skip", "--name", "*.tmp"]);
    out(&origin, &["name", "main", "head"]);
    // What a signing tool leaves in the directory decision 0046 reserved.
    // Nothing in this crate reads a byte of it, which is the point.
    write(
        &origin,
        "history/claims/over-the-head.claim.txt",
        "claim-0\nrole author\n",
    );

    let root = scratch(&format!("{test}-published"));
    publish(&origin, &root);
    (origin, root)
}

#[test]
fn an_empty_store_is_seeded_from_an_export_and_the_manifest_beside_it() {
    // Decision 0029's first arm, which decision 0048 keeps: an empty store may
    // always be seeded, and a first fetch after `init` is exactly that.
    let (origin, root) = published("seeding");
    let here = repository("seeding-here");
    let source = Directory::at(&root);

    let fetched = store(&here)
        .fetch(&source, MANIFEST, false)
        .expect("a fetch from a published copy");

    assert_eq!(fetched.revisions.len(), 2);
    assert_eq!(fetched.payloads, 2, "the file and the picture");
    assert!(fetched.documents >= 1);
    assert_eq!(fetched.rules, 1);
    assert_eq!(fetched.names.len(), 1, "the publisher's bookmark");
    assert_eq!(fetched.reserved, 1, "the file another tool wrote");
    assert!(fetched.declined.is_empty());
    assert_eq!(fetched.refetches, 0);

    // The whole point of the operation: this store is now a store, and it says
    // so itself rather than being told.
    let report = Store::check(here.join("history"));
    assert!(report.is_ok(), "{report:?}");
    assert_eq!(
        store(&here).history().heads(),
        store(&origin).history().heads(),
        "the fetched copy is not at the origin's heads"
    );

    // Decision 0048: a fetched path is an address, not a name. Every file here
    // is under the name *this* store derives, whatever it was called there.
    for path in walked(&here.join("history/operations")) {
        let name = path.rsplit('/').next().expect("a file name").to_owned();
        let name = name.strip_suffix(".ops.txt").unwrap_or(&name);
        assert!(
            name.parse::<RevisionId>().is_ok(),
            "a fetched file kept the publisher's name: {path}"
        );
    }

    // And the folder is untouched: `update` is its catch-up, not this.
    assert!(
        !here.join("notes.md").exists(),
        "a fetch wrote into the folder; decision 0030 says `update` does that"
    );
}

#[test]
fn a_bookmark_this_store_holds_is_kept_and_a_private_one_is_never_offered() {
    let (origin, root) = published("bookmarks");
    // The name that is the disclosure, made after the first publish so that
    // the manifest is regenerated with it in the store and not in the listing.
    out(&origin, &["name", "--private", "acme-layoffs", "head"]);
    publish(&origin, &root);
    let listing = fs::read_to_string(root.join(MANIFEST)).expect("the manifest");
    assert!(listing.contains("names/main.txt"), "{listing}");
    assert!(
        !listing.contains("acme"),
        "a private bookmark's name was published: {listing}"
    );

    let here = repository("bookmarks-here");
    let fetched = store(&here)
        .fetch(&Directory::at(&root), MANIFEST, false)
        .expect("a fetch");
    assert_eq!(fetched.names.len(), 1);
    assert_eq!(fetched.kept, 0);

    // Decision 0062: the publisher's `main` is the publisher's, and a fetcher
    // who took it once and then recorded onto it has a `main` of its own. A
    // fetch that moved it back would be the only place in this design where
    // transport overwrites a mutable value without asking — and would mean a
    // publisher advancing `main` broke every fetcher who ever took it.
    out(&here, &["update"]);
    write(&here, "notes.md", "one\ntwo\nmine\n");
    out(&here, &["record", "-m", "Work of my own"]);
    let mine = out(&here, &["names"]);
    assert!(mine.contains("main"), "{mine}");

    write(&origin, "notes.md", "one\ntwo\nthree\n");
    out(&origin, &["record", "-m", "A third thought"]);
    publish(&origin, &root);

    let fetched = store(&here)
        .fetch(&Directory::at(&root), MANIFEST, false)
        .expect("a second fetch");
    assert_eq!(
        fetched.names.len(),
        0,
        "a bookmark this store held was overwritten"
    );
    assert_eq!(fetched.kept, 1);
    assert_eq!(out(&here, &["names"]), mine, "`main` moved underneath");
}

/// Decision 0071: a name may have structure in it, so a manifest line is a
/// name rather than a filename — and a manifest is a file some other store
/// wrote. The refusal that used to be "no `/` in a name" is now the grammar
/// itself, which is what keeps a line naming `../..` from choosing where in
/// this store to put bytes.
#[test]
fn a_nested_bookmark_crosses_and_a_name_that_escapes_names_does_not() {
    let (origin, root) = published("nested-bookmarks");
    out(&origin, &["name", "claude/loving-wiles-12e833", "head"]);
    publish(&origin, &root);
    let listing = fs::read_to_string(root.join(MANIFEST)).expect("the manifest");
    assert!(
        listing.contains("names/claude/loving-wiles-12e833.txt"),
        "{listing}"
    );

    let here = repository("nested-bookmarks-here");
    let fetched = store(&here)
        .fetch(&Directory::at(&root), MANIFEST, false)
        .expect("a fetch");
    assert_eq!(fetched.names.len(), 1, "the nested one");
    let names = out(&here, &["names"]);
    assert!(names.contains("claude/loving-wiles-12e833"), "{names}");
    let names = out(&here, &["names"]);
    assert!(names.contains("claude/loving-wiles-12e833"), "{names}");

    // A manifest line whose name climbs out of `names/`. The bytes are the
    // ones already published for the bookmark above, so the digest is real and
    // the only thing wrong with the line is where it asks to be put.
    let manifest = fs::read_to_string(root.join(MANIFEST)).expect("the manifest");
    let escaping = manifest
        .lines()
        .find(|line| line.contains("names/claude/loving-wiles-12e833.txt"))
        .expect("the published bookmark")
        .replace(
            "names/claude/loving-wiles-12e833.txt",
            "names/../../escaped.txt",
        );
    fs::write(
        root.join(MANIFEST),
        format!("{}\n{escaping}\n", manifest.trim_end()),
    )
    .expect("rewriting the manifest");

    let there = repository("nested-bookmarks-hostile");
    store(&there)
        .fetch(&Directory::at(&root), MANIFEST, false)
        .expect("a fetch that reads the line and places nothing");
    assert!(
        !root.join("escaped.txt").exists() && !there.join("escaped.txt").exists(),
        "a name that is not a name inside `names/` named a file outside it"
    );
    let names = out(&there, &["names"]);
    assert!(!names.contains("escaped"), "{names}");
}

#[test]
fn a_fetch_after_the_origin_advances_takes_exactly_the_difference() {
    let (origin, root) = published("incremental");
    let here = repository("incremental-here");
    store(&here)
        .fetch(&Directory::at(&root), MANIFEST, false)
        .expect("the first fetch");

    write(&origin, "notes.md", "one\ntwo\nthree\n");
    out(&origin, &["record", "-m", "A third thought"]);
    publish(&origin, &root);

    let source = Directory::at(&root);
    let fetched = store(&here)
        .fetch(&source, MANIFEST, false)
        .expect("the second fetch");
    assert_eq!(
        fetched.revisions.len(),
        1,
        "more than the difference arrived"
    );
    assert_eq!(fetched.payloads, 0, "a payload already held was fetched");
    assert_eq!(fetched.documents, 1);
    assert_eq!(fetched.rules, 0);
    assert_eq!(fetched.reserved, 0);
    // Two documents and the manifest, and nothing else was even asked for.
    assert_eq!(
        source.asked().len(),
        3,
        "a request was made for something already held: {:?}",
        source.asked()
    );

    // A third fetch, with nothing to take, is the manifest and nothing more —
    // which is what a pull on a timer costs when it is up to date.
    let source = Directory::at(&root);
    let fetched = store(&here)
        .fetch(&source, MANIFEST, false)
        .expect("a fetch with nothing to take");
    assert_eq!(fetched.revisions.len(), 0);
    assert_eq!(source.asked(), vec![MANIFEST.to_owned()]);
}

#[test]
fn a_forgetting_document_that_arrives_destroys_the_original_this_store_held() {
    // Decision 0014 travelling, through the manifest's fourth field: a fetcher
    // that took a plain set difference would keep the very bytes an arriving
    // stand-in was written to destroy.
    let origin = repository("forgetting");
    write(&origin, "notes.md", "public\nthe secret\n");
    out(&origin, &["record", "-m", "A secret"]);
    let target = head_of(&origin);
    let root = scratch("forgetting-published");
    publish(&origin, &root);

    let here = repository("forgetting-here");
    store(&here)
        .fetch(&Directory::at(&root), MANIFEST, false)
        .expect("the first fetch");
    let secret = payload_holding(&here, "the secret").expect("the payload with the secret in it");

    out(&origin, &["forget", &target, "notes.md", "--lines", "2"]);
    publish(&origin, &root);

    let fetched = store(&here)
        .fetch(&Directory::at(&root), MANIFEST, false)
        .expect("the fetch that carries the redaction");
    assert_eq!(fetched.destroyed, 1, "the original was not destroyed");
    assert!(
        payload_holding(&here, "the secret").is_none(),
        "the destroyed text is still on disk here"
    );
    assert!(
        store(&here)
            .payload(&secret)
            .expect("reading a payload")
            .is_none(),
        "the store still answers for the forgotten digest"
    );
    let report = Store::check(here.join("history"));
    assert!(report.is_ok(), "{report:?}");
}

#[test]
fn a_file_that_is_not_the_digest_offered_is_refused_and_nothing_is_written() {
    // Decision 0036 one level out: the catalogue says where to look, it never
    // says what is there. A manifest is the same claim over a wire, so it is
    // the same answer — hash it before believing a byte of it.
    let origin = repository("tampered");
    write(&origin, "notes.md", "one\n");
    out(&origin, &["record", "-m", "Only one file"]);
    let root = scratch("tampered-published");
    publish(&origin, &root);

    // The bytes at the path the manifest names, changed after it was written —
    // which is what a hostile mirror and a corrupted disk look like alike.
    let text = fs::read_to_string(root.join(MANIFEST)).expect("the manifest");
    let offered = text
        .lines()
        .find(|line| line.starts_with("payload "))
        .expect("the payload the file was created as")
        .to_owned();
    let path = offered.splitn(4, ' ').nth(3).expect("the path").to_owned();
    fs::write(root.join(&path), "not what was promised\n").expect("a tampered file");

    let here = repository("tampered-here");
    let error = store(&here)
        .fetch(&Directory::at(&root), MANIFEST, false)
        .expect_err("a tampered file was accepted");
    let FetchError::Tampered {
        path: refused,
        offered: promised,
        found,
    } = &error
    else {
        panic!("the wrong refusal: {error}");
    };
    assert_eq!(*refused, path);
    assert_ne!(promised, found);
    assert!(
        error.to_string().contains("this store is as it was"),
        "{error}"
    );

    // Nothing was written: the payload is the first thing a fetch asks for, so
    // this store is exactly as `init` left it.
    assert!(store(&here).is_empty(), "a revision arrived anyway");
    assert!(
        walked(&here.join("history/operations")).is_empty(),
        "something was written into `operations/`"
    );
}

#[test]
fn content_arrives_before_the_revisions_that_name_it_at_every_moment() {
    // Decision 0048's ordering, and the invariant it exists for: no revision in
    // this store names bytes this store does not hold. An interruption
    // understates what is reachable, and `prune` collects the rest.
    let (_origin, root) = published("ordering");

    let source = Directory::at(&root);
    let here = repository("ordering-here");
    store(&here)
        .fetch(&source, MANIFEST, false)
        .expect("a whole fetch");
    let requests = source.asked().len();

    // The order the groups were asked for, read off the manifest's own kinds.
    let manifest = fs::read_to_string(root.join(MANIFEST)).expect("the manifest");
    let kind_of = |path: &str| {
        manifest
            .lines()
            .find(|line| line.ends_with(&format!(" {path}")))
            .and_then(|line| line.split(' ').next())
            .map(str::to_owned)
    };
    // Decision 0062 puts bookmarks last, with the kinds no revision names.
    let order = [
        "payload",
        "operation",
        "revision",
        "rule",
        "reserved",
        "name",
    ];
    let positions: Vec<usize> = source
        .asked()
        .iter()
        .skip(1)
        .filter_map(|path| kind_of(path))
        .map(|kind| {
            order
                .iter()
                .position(|known| *known == kind)
                .expect("a kind the grammar names")
        })
        .collect();
    assert!(
        positions.windows(2).all(|pair| pair[0] <= pair[1]),
        "the groups were asked for out of order: {:?}",
        source.asked()
    );

    // And the invariant itself, at every moment: a fetch cut off after any
    // number of requests leaves a store that still passes `check`.
    for answers in 1..requests {
        let here = repository(&format!("ordering-cut-{answers}"));
        let source = Directory::at(&root).answering(answers);
        let _ = store(&here).fetch(&source, MANIFEST, false);
        let report = Store::check(here.join("history"));
        assert!(
            report.is_ok(),
            "a fetch cut off after {answers} requests left a broken store: {report:?}"
        );
    }
}

#[test]
fn two_unrelated_histories_are_not_joined_without_being_asked() {
    // Decision 0052: relatedness from a manifest is stricter than decision
    // 0029's, and it fails toward refusal because the arm it cannot answer
    // needs revision documents a listing deliberately omits.
    let (_origin, root) = published("unrelated");
    let here = repository("unrelated-here");
    write(&here, "elsewhere.md", "a history of its own\n");
    out(&here, &["record", "-m", "Somebody else's work"]);

    let error = store(&here)
        .fetch(&Directory::at(&root), MANIFEST, false)
        .expect_err("two unrelated histories were joined");
    assert!(matches!(error, FetchError::Unrelated), "{error}");
    assert!(error.to_string().contains("--join-unrelated"), "{error}");
    assert_eq!(store(&here).len(), 1, "something arrived anyway");

    let fetched = store(&here)
        .fetch(&Directory::at(&root), MANIFEST, true)
        .expect("`--join-unrelated` is the escape");
    assert_eq!(fetched.revisions.len(), 2);
    assert_eq!(store(&here).len(), 3);
}

#[test]
fn the_files_another_tool_wrote_arrive_add_only() {
    // Decision 0053: a `travels-and-unions` directory is written with
    // `create_new` and nothing after it, because the name was computed by
    // somebody else under a rule nothing here has read.
    let (origin, root) = published("claims");
    let here = repository("claims-here");
    let fetched = store(&here)
        .fetch(&Directory::at(&root), MANIFEST, false)
        .expect("a fetch");
    assert_eq!(fetched.reserved, 1);
    let landed = here.join("history/claims/over-the-head.claim.txt");
    assert_eq!(
        fs::read_to_string(&landed).expect("the claim"),
        "claim-0\nrole author\n"
    );

    // A name this store already holds is left exactly as it is, unread — even
    // where the origin's file under that name says something else.
    fs::write(&landed, "claim-0\nrole reviewer\n").expect("a claim of our own");
    let fetched = store(&here)
        .fetch(&Directory::at(&root), MANIFEST, false)
        .expect("a second fetch");
    assert_eq!(fetched.reserved, 0);
    assert_eq!(
        fs::read_to_string(&landed).expect("the claim"),
        "claim-0\nrole reviewer\n",
        "a fetch overwrote a file in a directory it cannot read"
    );

    // And `trust/` never crosses a boundary, in either direction, so nothing
    // that was never listed was ever asked for.
    assert!(!origin.join("history/trust").exists());
    assert!(!here.join("history/trust").exists());
}

#[test]
fn a_reserved_directory_this_build_does_not_know_is_declined_and_said_so() {
    // Decision 0056 left this open: 0053's default is to leave it behind, and
    // what was not decided is whether the decline should be audible. Decision
    // 0057 makes it an observation — not an error, because nothing is wrong,
    // and not silence, because the recipient is the only party who could
    // install the tool that reads those files.
    let (_origin, root) = published("declined");
    let copy = root.join("store");
    let bytes = b"witness-0\nsaw 2026-08-25\n";
    write(
        &copy,
        "history/witness/adam.txt",
        &String::from_utf8_lossy(bytes),
    );
    // A publisher whose historica reserves a directory this one has never heard
    // of. The kind is stable across versions on purpose (decision 0056), so
    // what varies is the directory in the path.
    let mut manifest = fs::read_to_string(root.join(MANIFEST)).expect("the manifest");
    manifest.push_str(&format!(
        "reserved {} - store/history/witness/adam.txt\n",
        digest(bytes)
    ));
    fs::write(root.join(MANIFEST), &manifest).expect("a manifest from a newer historica");

    let here = repository("declined-here");
    let source = Directory::at(&root);
    let fetched = store(&here)
        .fetch(&source, MANIFEST, false)
        .expect("a line for an unknown directory is not a refusal");

    assert_eq!(fetched.declined.len(), 1, "{:?}", fetched.declined);
    assert_eq!(fetched.declined[0].directory, "witness");
    assert_eq!(fetched.declined[0].files, 1);
    assert_eq!(fetched.declined[0].travel, Travel::LocalOnly);
    assert!(
        !here.join("history/witness").exists(),
        "a manifest talked this store into filling a directory it does not know"
    );
    assert!(
        !source.asked().iter().any(|path| path.contains("witness")),
        "the file was fetched before being declined: {:?}",
        source.asked()
    );
    // The one that *is* reserved here still arrives, so the decline is about
    // the directory rather than about the kind.
    assert_eq!(fetched.reserved, 1);
}

#[test]
fn a_path_that_has_moved_is_asked_for_again_from_a_manifest_read_again() {
    // Decision 0048: the manifest is read at one moment and the files fetched
    // after it, so a publisher who re-exports or runs `arrange` in between moves
    // the paths a fetcher is still working through. That is ordinary, and the
    // answer is to read the listing again.
    let (_origin, root) = published("moved");
    let stale = fs::read_to_string(root.join(MANIFEST)).expect("the manifest");

    // The publisher rearranges the copy: same bytes, a name a person can read.
    let copy = root.join("store");
    let moved = stale
        .lines()
        .find(|line| line.starts_with("payload "))
        .and_then(|line| line.splitn(4, ' ').nth(3))
        .expect("a payload")
        .to_owned();
    let renamed = format!("{}-renamed", moved);
    fs::rename(root.join(&moved), root.join(&renamed)).expect("arranging the copy");
    let refreshed = out(&root, &["offer", "store"]);
    fs::write(root.join(MANIFEST), &refreshed).expect("the manifest, written last");
    assert!(refreshed.contains("-renamed"), "the fixture did not move");
    assert!(copy.exists());

    let here = repository("moved-here");
    let source = Directory::at(&root).holding(&stale);
    let fetched = store(&here)
        .fetch(&source, MANIFEST, false)
        .expect("a moved path is not a failure");
    assert_eq!(fetched.refetches, 1, "the manifest was not read again");
    assert_eq!(fetched.payloads, 2);
    assert!(
        source.asked().iter().any(|path| path == &moved),
        "the old path was never asked for, so nothing was under test"
    );
    let report = Store::check(here.join("history"));
    assert!(report.is_ok(), "{report:?}");
}

#[test]
fn a_digest_gone_from_the_manifest_read_again_stops_being_wanted() {
    // The other half of the same sentence: a digest that is gone was forgotten
    // or pruned at the source, which is an answer and not an error.
    let origin = repository("withdrawn");
    write(&origin, "notes.md", "public\nthe secret\n");
    out(&origin, &["record", "-m", "A secret"]);
    let target = head_of(&origin);
    let root = scratch("withdrawn-published");
    publish(&origin, &root);
    let stale = fs::read_to_string(root.join(MANIFEST)).expect("the manifest");
    let withdrawn: RevisionId = stale
        .lines()
        .find(|line| line.starts_with("payload "))
        .and_then(|line| line.split(' ').nth(1))
        .expect("a payload")
        .parse()
        .expect("a digest");

    // The publisher redacts and republishes while a fetcher holds the old
    // listing, so the payload that listing names is destroyed at the source.
    out(&origin, &["forget", &target, "notes.md", "--lines", "2"]);
    publish(&origin, &root);

    let here = repository("withdrawn-here");
    let source = Directory::at(&root).holding(&stale);
    let fetched = store(&here)
        .fetch(&source, MANIFEST, false)
        .expect("a withdrawn digest is not a failure");
    assert_eq!(fetched.refetches, 1);
    assert!(
        store(&here)
            .payload(&withdrawn)
            .expect("reading a payload")
            .is_none(),
        "the fetch kept wanting a digest the source had destroyed"
    );
    assert!(
        payload_holding(&here, "the secret").is_none(),
        "the redacted text arrived anyway"
    );
    let report = Store::check(here.join("history"));
    assert!(report.is_ok(), "{report:?}");
}

#[test]
fn a_remote_that_has_diverged_is_fetched_from_rather_than_refused() {
    // Decision 0048: divergence is a thing this store holds and `merge`
    // resolves. Only `update` and `cat` need one answer.
    let origin = repository("divergent");
    write(&origin, "notes.md", "one\n");
    out(&origin, &["record", "-m", "A shared root"]);

    // A copy somebody took away and recorded in, which is what an export is.
    let here = scratch("divergent-here");
    let _ = fs::remove_dir_all(&here);
    out(&origin, &["export", &here.to_string_lossy()]);
    write(&here, "notes.md", "one\nmine\n");
    out(&here, &["record", "-m", "Mine"]);

    write(&origin, "notes.md", "one\ntheirs\n");
    out(&origin, &["record", "-m", "Theirs"]);
    let root = scratch("divergent-published");
    publish(&origin, &root);

    let fetched = store(&here)
        .fetch(&Directory::at(&root), MANIFEST, false)
        .expect("a divergent remote is still a remote");
    assert_eq!(fetched.revisions.len(), 1);
    assert_eq!(
        store(&here).history().heads().len(),
        2,
        "the fetch did not leave this store holding the divergence"
    );
    let report = Store::check(here.join("history"));
    assert!(report.is_ok(), "{report:?}");
}

#[test]
fn a_manifest_spelled_in_a_grammar_this_reader_does_not_know_is_discarded_whole() {
    // Decision 0048: the header is numbered because an offer is refetchable, so
    // a reader that meets a spelling it does not know falls back to fetching
    // the archive — which never stopped working, and which the refusal says.
    let (_origin, root) = published("spelling");
    let manifest = fs::read_to_string(root.join(MANIFEST)).expect("the manifest");
    let ahead = manifest.replacen("historica-offer-1", "historica-offer-2", 1);
    fs::write(root.join(MANIFEST), ahead).expect("a manifest from the future");

    let here = repository("spelling-here");
    let source = Directory::at(&root);
    let error = store(&here)
        .fetch(&source, MANIFEST, false)
        .expect_err("a manifest this reader cannot read was used anyway");
    assert!(error.to_string().contains("historica-offer-2"), "{error}");
    assert!(error.to_string().contains("archive"), "{error}");
    assert_eq!(
        source.asked(),
        vec![MANIFEST.to_owned()],
        "a file was asked for on the strength of a manifest that was refused"
    );

    // And a kind it does not know is only a line it discards, which is the
    // parting decision 0056 draws.
    let manifest = fs::read_to_string(root.join(MANIFEST))
        .expect("the manifest")
        .replacen("historica-offer-2", "historica-offer-1", 1)
        + "witness 0000000000000000000000000000000000000000000000000000000000000000 - store/history/witness/x\n";
    fs::write(root.join(MANIFEST), manifest).expect("a manifest with a newer kind in it");
    let fetched = store(&here)
        .fetch(&Directory::at(&root), MANIFEST, false)
        .expect("a kind this reader does not know is a line, not a manifest");
    assert_eq!(fetched.revisions.len(), 2);
}

// ---------------------------------------------------------------------------
// Reading the fixtures back
// ---------------------------------------------------------------------------

/// Every file under a directory, said relative to it with `/` for a separator.
fn walked(root: &Path) -> Vec<String> {
    let mut found = Vec::new();
    let mut pending = vec![root.to_path_buf()];
    while let Some(directory) = pending.pop() {
        let Ok(entries) = fs::read_dir(&directory) else {
            continue;
        };
        for entry in entries.filter_map(Result::ok) {
            let path = entry.path();
            if path.is_dir() {
                pending.push(path);
            } else {
                found.push(
                    path.strip_prefix(root)
                        .unwrap_or(&path)
                        .to_string_lossy()
                        .replace('\\', "/"),
                );
            }
        }
    }
    found.sort();
    found
}

/// The head of a repository, as a person reads it off `log`.
fn head_of(repository: &Path) -> String {
    out(repository, &["log"])
        .lines()
        .find(|line| line.contains("(head"))
        .and_then(|line| line.split_whitespace().nth(1).map(str::to_owned))
        .expect("a head")
}

/// The digest of a file under `operations/` whose bytes hold this text, if the
/// store still holds one.
fn payload_holding(repository: &Path, text: &str) -> Option<RevisionId> {
    let operations = repository.join("history/operations");
    let mut found: BTreeSet<RevisionId> = BTreeSet::new();
    for relative in walked(&operations) {
        let bytes = fs::read(operations.join(&relative)).expect("a file the walk found");
        if String::from_utf8_lossy(&bytes).contains(text) {
            found.insert(digest(&bytes));
        }
    }
    found.into_iter().next()
}
