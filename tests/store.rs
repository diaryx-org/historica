//! The store, exercised against real directories.
//!
//! The claim under test throughout is decision 0003's: identity comes from
//! content and filenames are presentation. The corpus is the best evidence
//! available, because it was hand-arranged before any of this code existed —
//! "the corpus is not a stand-in for a store, it *is* one".

use std::collections::BTreeSet;
use std::fs;
use std::path::{Path, PathBuf};

use historica::core::{ChangeState, FileId, RevisionId};
use historica::format::{OperationDocument, RevisionDocument, digest};
use historica::store::{Finding, Name, Severity, Store};

/// A fresh directory for one test, inside the target directory.
fn scratch(test: &str) -> PathBuf {
    let path = Path::new(env!("CARGO_TARGET_TMPDIR")).join(test);
    let _ = fs::remove_dir_all(&path);
    fs::create_dir_all(&path).expect("a scratch directory");
    path
}

fn corpus_files() -> Vec<PathBuf> {
    let corpus = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/corpus/revisions");
    let mut files: Vec<PathBuf> = fs::read_dir(corpus)
        .expect("the corpus")
        .filter_map(Result::ok)
        .map(|entry| entry.path())
        .filter(|path| {
            path.file_name()
                .and_then(|name| name.to_str())
                .is_some_and(|name| name.ends_with(".rev.txt"))
        })
        .collect();
    files.sort();
    files
}

/// A store holding the seven canonical corpus files, under the names they
/// already have — which is to say, an arranged store.
fn corpus_store(test: &str) -> (PathBuf, Store) {
    let root = scratch(test).join("history");
    let store = Store::init(&root).expect("a new store");
    for file in corpus_files() {
        let name = file.file_name().expect("a filename");
        fs::copy(&file, root.join("revisions").join(name)).expect("copying a revision");
    }
    let store = Store::open(store.root()).expect("reopening");
    (root, store)
}

#[test]
fn init_creates_the_layout_and_open_finds_it() {
    let root = scratch("init").join("history");
    let store = Store::init(&root).expect("a new store");
    assert!(store.is_empty());

    for directory in ["revisions", "operations", "names", "cache"] {
        assert!(root.join(directory).is_dir(), "{directory} should exist");
    }
    let header = fs::read_to_string(root.join("historica.txt")).expect("the header");
    assert_eq!(header.lines().next(), Some("historica-v1"));
    assert!(header.contains("Identity comes from content"), "{header}");
    assert!(Store::init(&root).is_err(), "twice is an error");
}

#[test]
fn discovery_walks_up_and_wants_the_header_not_the_name() {
    let base = scratch("discover");
    let root = base.join("history");
    Store::init(&root).expect("a new store");

    let deep = base.join("a/b/c");
    fs::create_dir_all(&deep).expect("nested directories");
    let found = Store::discover(&deep).expect("discovery from below");
    assert_eq!(found.root().canonicalize().ok(), root.canonicalize().ok());

    // A directory merely called `history` is not a store.
    //
    // Deliberately outside the repository rather than under
    // `CARGO_TARGET_TMPDIR`: discovery walks up to the filesystem root, and
    // `target/` sits inside a checkout that may itself hold a real
    // `history/` — as this one does, being a tool people record their own
    // work with. A lookalike there would be walked straight past and the
    // store above it found, and this assertion would be about the wrong
    // directory entirely.
    let impostor = std::env::temp_dir().join("historica-store-discover-impostor");
    let _ = fs::remove_dir_all(&impostor);
    fs::create_dir_all(impostor.join("history/revisions")).expect("a lookalike");
    assert!(Store::discover(&impostor).is_err());
}

#[test]
fn the_corpus_loads_as_the_history_it_claims_to_be() {
    let (_root, store) = corpus_store("corpus-store");
    assert_eq!(store.len(), 7);

    let history = store.history();
    assert_eq!(history.changes().len(), 5);
    assert!(history.missing_parents().is_empty());
    assert!(Store::check(store.root()).is_ok());
}

#[test]
fn renaming_every_file_changes_no_identity_and_breaks_no_reference() {
    // The headline claim of decision 0003, tested the only way that means
    // anything: rename everything to names that carry no information at all.
    let (root, before) = corpus_store("rename");
    let revisions = root.join("revisions");

    let mut renamed = 0;
    let mut files: Vec<PathBuf> = fs::read_dir(&revisions)
        .expect("revisions")
        .filter_map(Result::ok)
        .map(|entry| entry.path())
        .collect();
    files.sort();
    for (index, path) in files.iter().enumerate() {
        fs::rename(path, revisions.join(format!("{index}-anything.rev.txt"))).expect("renaming");
        renamed += 1;
    }
    assert_eq!(renamed, 7);

    let after = Store::open(&root).expect("reopening a renamed store");
    assert_eq!(before.len(), after.len());
    assert_eq!(
        before.iter().map(|(id, _)| *id).collect::<BTreeSet<_>>(),
        after.iter().map(|(id, _)| *id).collect::<BTreeSet<_>>()
    );
    assert_eq!(before.history(), after.history());
    assert!(after.history().missing_parents().is_empty());
}

#[test]
fn a_store_filed_into_directories_is_the_same_store() {
    // Decision 0016: the walk recurses, so a person may arrange the store
    // into whatever directories narrate their history. This is 0003's claim
    // one level up — a filename means nothing, and now neither does a
    // directory.
    let (root, before) = corpus_store("nested");
    let revisions = root.join("revisions");

    let mut files: Vec<PathBuf> = fs::read_dir(&revisions)
        .expect("revisions")
        .filter_map(Result::ok)
        .map(|entry| entry.path())
        .collect();
    files.sort();
    assert_eq!(files.len(), 7);

    // Buried at a different depth each, because "arbitrary" is the claim.
    for (index, path) in files.iter().enumerate() {
        let mut directory = revisions.clone();
        for level in 0..=index {
            directory = directory.join(format!("{level}"));
        }
        fs::create_dir_all(&directory).expect("directories");
        let name = path.file_name().expect("a filename");
        fs::rename(path, directory.join(name)).expect("filing it away");
    }
    assert!(
        fs::read_dir(&revisions)
            .expect("revisions")
            .filter_map(Result::ok)
            .all(|entry| entry.path().is_dir()),
        "every revision should now be inside a directory"
    );

    let after = Store::open(&root).expect("reopening a filed store");
    assert_eq!(before.len(), after.len());
    assert_eq!(before.history(), after.history());
    assert!(after.history().missing_parents().is_empty());
    assert!(Store::check(&root).is_ok());
}

#[test]
#[cfg(unix)]
fn a_symbolic_link_is_found_and_never_followed() {
    // 0011 refused a symlink in the working copy because following one reads
    // somebody else's file under this name, and a store is not the place to
    // change that answer. It is also what makes an unbounded walk safe: a
    // tree of real directories cannot contain itself.
    let (root, store) = corpus_store("links");
    let revisions = root.join("revisions");
    let held = store.len();

    // A link that would be a document if it were followed.
    std::os::unix::fs::symlink(
        revisions.join("01-root.rev.txt"),
        revisions.join("copy.rev.txt"),
    )
    .expect("a link to a document");
    // And a directory link pointing at its own parent, which is the loop an
    // unbounded walk would hang on if it followed one.
    std::os::unix::fs::symlink(&revisions, revisions.join("loop")).expect("a link to a directory");

    let after = Store::open(&root).expect("reopening");
    assert_eq!(after.len(), held, "a link is not a document");

    // Reported rather than passed over: a person who made one meant something
    // by it, and nothing here read it.
    let report = Store::check(&root);
    let unfollowed = report
        .findings()
        .iter()
        .filter(|finding| matches!(finding, Finding::Unfollowed { .. }))
        .count();
    assert_eq!(unfollowed, 2, "{report:?}");
    // Notes never fail, which is what 0006 decided a note is.
    assert!(report.is_ok(), "{report:?}");
}

#[test]
fn one_revision_stored_twice_is_one_revision() {
    let (root, store) = corpus_store("duplicate");
    let original = root.join("revisions/01-root.rev.txt");
    fs::copy(&original, root.join("revisions/a-second-copy.rev.txt")).expect("copying");

    let reopened = Store::open(&root).expect("reopening");
    assert_eq!(reopened.len(), store.len(), "still one revision");

    // Harmless, so it is a note and `check` still passes.
    let report = Store::check(&root);
    assert!(report.is_ok());
    assert!(
        report
            .notes()
            .any(|finding| matches!(finding, Finding::DuplicateContent { .. }))
    );
}

#[test]
fn only_rev_files_are_read_and_the_rest_are_merely_mentioned() {
    let (root, store) = corpus_store("foreign");
    fs::write(root.join("revisions/.DS_Store"), b"junk").expect("a file browser's droppings");
    fs::write(root.join("revisions/notes.txt"), b"not a revision").expect("a stray file");

    let reopened = Store::open(&root).expect("reopening");
    assert_eq!(reopened.len(), store.len(), "junk is not history");

    let report = Store::check(&root);
    assert!(report.is_ok(), "junk never claimed to be a revision");
    // One, not two: decision 0022 leaves what the platform wrote alone, since
    // a note on every machine whose file browser has been near the store is a
    // note that means nothing.
    let foreign: Vec<String> = report
        .notes()
        .filter(|finding| matches!(finding, Finding::ForeignFile { .. }))
        .map(ToString::to_string)
        .collect();
    assert_eq!(foreign.len(), 1, "{foreign:?}");
    assert!(foreign[0].contains("notes.txt"), "{foreign:?}");
}

#[test]
fn a_file_that_does_not_parse_is_an_error_naming_the_file() {
    let (root, _) = corpus_store("unparsable");
    fs::write(
        root.join("revisions/broken.rev.txt"),
        b"historica-v0\nnonsense\n",
    )
    .expect("a broken file");

    let error = Store::open(&root).expect_err("a store that cannot be trusted");
    let rendered = error.to_string();
    assert!(rendered.contains("broken.rev.txt"), "{rendered}");

    let report = Store::check(&root);
    assert!(!report.is_ok());
    assert!(
        report
            .errors()
            .any(|finding| matches!(finding, Finding::Unparsable { .. }))
    );
}

#[test]
fn the_writer_names_files_by_digest_and_never_overwrites() {
    let root = scratch("writer").join("history");
    let mut store = Store::init(&root).expect("a new store");

    let bytes = fs::read(
        Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/corpus/revisions/01-root.rev.txt"),
    )
    .expect("a revision");
    let document = RevisionDocument::parse(&bytes).expect("a canonical file");

    let id = store.insert(&document).expect("writing");
    assert_eq!(id, digest(&bytes));
    let written = root.join(format!("revisions/{id}.rev.txt"));
    assert!(written.is_file(), "named by its digest");
    assert_eq!(fs::read(&written).expect("reading back"), bytes);

    // Append-only: writing the same revision again is a no-op, not an error,
    // which is what lets two replicas produce one file.
    assert_eq!(store.insert(&document).expect("again"), id);
    assert_eq!(store.len(), 1);
    assert!(Store::check(&root).is_ok());
}

#[test]
fn a_filename_that_claims_a_digest_must_not_lie() {
    let (root, _) = corpus_store("lying-name");
    let source = root.join("revisions/01-root.rev.txt");
    // A name that claims to be a digest, and is the wrong one.
    let liar = root
        .join("revisions/0000000000000000000000000000000000000000000000000000000000000000.rev.txt");
    fs::rename(&source, &liar).expect("renaming");

    // The loader ignores names entirely, so the store still reads correctly.
    let store = Store::open(&root).expect("names participate in nothing");
    assert_eq!(store.len(), 7);

    // `check` is where a name that made a claim is held to it.
    let report = Store::check(&root);
    assert!(!report.is_ok());
    assert!(
        report
            .errors()
            .any(|finding| matches!(finding, Finding::FilenameLies { .. }))
    );
}

#[test]
fn a_bookmark_follows_its_change_through_an_amendment() {
    // The question decision 0001 deferred, answered by 0006: `change` is the
    // default because the bookmark then follows amend and rebase by itself.
    let (root, mut store) = corpus_store("bookmark");
    let documents: Vec<_> = store.iter().map(|(id, doc)| (*id, doc.clone())).collect();

    let amended = documents
        .iter()
        .find(|(_, doc)| !doc.supersedes.is_empty() && doc.revised_by.is_some())
        .map(|(id, doc)| (*id, doc.clone()))
        .expect("the corpus contains an amendment");

    store
        .set_name("main", Name::Change(amended.1.change))
        .expect("setting a bookmark");
    assert_eq!(
        fs::read_to_string(root.join("names/main.txt")).expect("the bookmark file"),
        format!("change {}\n", amended.1.change)
    );

    let reopened = Store::open(&root).expect("reopening");
    let Some(Name::Change(change)) = reopened.name("main") else {
        panic!("a bookmark on a change");
    };
    match reopened.history().change_state(&change) {
        // It resolves to the amendment, not to what it superseded.
        ChangeState::Resolved(current) => assert_eq!(current.id, amended.0),
        other => panic!("expected the successor, got {other:?}"),
    }
    assert!(Store::check(&root).is_ok());
}

#[test]
fn a_pinned_bookmark_names_one_revision() {
    let (root, mut store) = corpus_store("pin");
    let (id, _) = store
        .iter()
        .next()
        .map(|(id, d)| (*id, d.clone()))
        .expect("a revision");
    store
        .set_name("v0.1.0", Name::Revision(id))
        .expect("pinning");
    assert_eq!(
        fs::read_to_string(root.join("names/v0.1.0.txt")).expect("the file"),
        format!("revision {id}\n")
    );
    assert_eq!(
        Store::open(&root).expect("reopening").name("v0.1.0"),
        Some(Name::Revision(id))
    );
}

#[test]
fn a_file_bookmark_is_one_line_and_a_name_that_is_an_identifier_is_refused() {
    let (root, mut store) = corpus_store("file-bookmark");
    let file: FileId = "kmnpqrstvwxyzklmnpqrstvw".parse().expect("an identifier");

    // Decision 0024: a third key, and no second choice to make about it.
    store
        .set_name("entry", Name::File(file))
        .expect("naming a file");
    assert_eq!(
        fs::read_to_string(root.join("names/entry.txt")).expect("the file"),
        format!("file {file}\n")
    );
    assert_eq!(
        Store::open(&root).expect("reopening").name("entry"),
        Some(Name::File(file))
    );

    // A bookmark spelled as a full identifier would shadow the identifier it
    // spells, everywhere a bookmark is looked up first.
    assert!(store.set_name(&file.to_string(), Name::File(file)).is_err());
    assert!(
        store.set_name("kmnp", Name::File(file)).is_ok(),
        "an abbreviation is not an identifier"
    );
}

#[test]
fn a_malformed_bookmark_is_an_error_and_a_dangling_one_is_not() {
    let (root, _) = corpus_store("bookmarks-checked");
    fs::write(
        root.join("names/broken.txt"),
        "pointing vaguely somewhere\n",
    )
    .expect("a bad bookmark");
    fs::write(
        root.join("names/ahead.txt"),
        "change kkkkkkkkkkkkkkkkkkkkkkkk\n",
    )
    .expect("a bookmark ahead of the sync");

    let report = Store::check(&root);
    assert!(!report.is_ok());
    assert!(
        report
            .errors()
            .any(|finding| matches!(finding, Finding::MalformedBookmark { .. }))
    );
    // Ahead of the sync is not broken: the name may simply be newer.
    assert!(
        report
            .notes()
            .any(|finding| matches!(finding, Finding::DanglingBookmark { .. }))
    );
    assert!(Store::open(&root).is_err(), "loading is strict");
}

#[test]
fn an_undelivered_parent_is_a_note_and_an_absent_predecessor_is_silent() {
    let (root, _) = corpus_store("incomplete");
    // Drop the root, orphaning the revisions that name it as a parent, and
    // drop the revision that 05 supersedes.
    fs::remove_file(root.join("revisions/01-root.rev.txt")).expect("removing the root");
    fs::remove_file(root.join("revisions/02-concurrent.rev.txt")).expect("removing a predecessor");

    let report = Store::check(&root);
    assert!(report.is_ok(), "an incomplete store is not a broken one");
    assert!(
        report
            .notes()
            .any(|finding| matches!(finding, Finding::MissingParent { .. }))
    );
    // Nothing reports the absent superseded revision: the successor carries
    // the evidence precisely so that it may be gone.
    let store = Store::open(&root).expect("still loads");
    assert!(!store.history().superseded().is_empty());
}

#[test]
fn a_conflicted_copy_is_mentioned_and_forgiven() {
    let (root, _) = corpus_store("conflicted");
    let source = root.join("revisions/03-other.rev.txt");
    fs::copy(
        &source,
        root.join("revisions/03-other (conflicted copy 2025-08-19).rev.txt"),
    )
    .expect("what a sync tool does");

    let report = Store::check(&root);
    assert!(report.is_ok(), "both files are legitimate revisions");
    assert!(
        report
            .notes()
            .any(|finding| matches!(finding, Finding::SyncSuffixed { .. }))
    );
}

#[test]
fn a_store_of_an_unknown_version_refuses_rather_than_guesses() {
    let root = scratch("version").join("history");
    Store::init(&root).expect("a new store");
    fs::write(root.join("historica.txt"), "historica-v2\n").expect("a newer store");

    assert!(Store::open(&root).is_err());
    let report = Store::check(&root);
    assert!(!report.is_ok());
    assert!(
        report
            .errors()
            .any(|finding| matches!(finding, Finding::UnreadableStore { .. }))
    );
}

#[test]
fn every_finding_says_where_and_sorts_errors_first() {
    let (root, _) = corpus_store("report-shape");
    fs::write(root.join("revisions/broken.rev.txt"), b"nope\n").expect("a broken file");
    fs::write(root.join("revisions/stray.txt"), b"junk").expect("a stray file");

    let report = Store::check(&root);
    let severities: Vec<Severity> = report.findings().iter().map(Finding::severity).collect();
    let mut sorted = severities.clone();
    sorted.sort();
    assert_eq!(severities, sorted, "errors come first");

    for finding in report.findings() {
        assert!(!finding.to_string().is_empty());
    }
}

/// The tree corpus copied into a store: two files, a rename, and the operation
/// documents the revisions name.
fn tree_corpus_store(test: &str) -> (PathBuf, Store) {
    let corpus = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/corpus/tree");
    let root = scratch(test).join("history");
    let store = Store::init(&root).expect("a new store");
    for (directory, suffix) in [("revisions", ".rev.txt"), ("operations", ".ops.txt")] {
        for entry in fs::read_dir(corpus.join(directory)).expect("the corpus") {
            let path = entry.expect("an entry").path();
            let found = path.file_name().and_then(|name| name.to_str());
            if let Some(name) = found.filter(|name| name.ends_with(suffix)) {
                fs::copy(&path, root.join(directory).join(name)).expect("copying");
            }
        }
    }
    let store = Store::open(store.root()).expect("reopening");
    (root, store)
}

/// The head of that corpus: the revision nothing names as a parent.
fn head_of(store: &Store) -> RevisionId {
    let parents: BTreeSet<RevisionId> = store
        .iter()
        .flat_map(|(_, document)| document.parents.iter().copied())
        .collect();
    let heads: Vec<RevisionId> = store
        .iter()
        .map(|(id, _)| *id)
        .filter(|id| !parents.contains(id))
        .collect();
    assert_eq!(heads.len(), 1, "the tree corpus is one chain");
    heads[0]
}

#[test]
fn a_store_materialises_the_tree_and_the_files_it_describes() {
    let (root, store) = tree_corpus_store("materialise");
    let head = head_of(&store);

    let tree = store.tree(&head).expect("the file set at the head");
    assert_eq!(tree.len(), 1);
    let (file, path) = tree.files().next().expect("the surviving file");
    assert_eq!(path, "docs/README.md");

    // Content comes from the operation documents the revisions name, which the
    // store loads by digest and never by filename.
    assert_eq!(
        store.content(&head, file).expect("the README").text(),
        "# Notes\n\nA journal kept in Historica, and the notes that came with it.\n"
    );
    assert_eq!(store.operations().count(), 4);
    assert!(Store::check(&root).is_ok());
}

#[test]
fn renaming_every_operation_document_changes_nothing() {
    // Decision 0003's rule, applied to the second kind of document: identity
    // is content, and a filename is presentation.
    let (root, store) = tree_corpus_store("rename-operations");
    let head = head_of(&store);
    let before = store.tree(&head).expect("a tree");

    let directory = root.join("operations");
    for (index, entry) in fs::read_dir(&directory).expect("operations").enumerate() {
        let path = entry.expect("an entry").path();
        fs::rename(&path, directory.join(format!("{index}-renamed.ops.txt"))).expect("renaming");
    }

    let store = Store::open(&root).expect("reopening a renamed store");
    assert_eq!(store.tree(&head).expect("a tree"), before);
    assert_eq!(store.operations().count(), 4);
    assert!(Store::check(&root).is_ok());
}

#[test]
fn a_document_that_disagrees_with_its_file_is_an_error() {
    // The error decision 0007 asked for by name, which needed 0008's tree to
    // know which document belongs to which file.
    let (root, mut store) = tree_corpus_store("disagreeing-content");
    let head = head_of(&store);
    let (file, _) = {
        let tree = store.tree(&head).expect("a tree");
        let (file, path) = tree.files().next().expect("the README");
        (*file, path.to_owned())
    };

    let wrong = OperationDocument::parse(b"historica-v0\n\ndelete 0 1\n-not what is there\n")
        .expect("a document that parses");
    let wrong = store.insert_operation(&wrong).expect("writing it");

    let mut revision = store.get(&head).expect("the head").clone();
    revision.change = "ztkwnrvzlmyxqsotnkwlpvzr".parse().expect("a change ID");
    revision.parents = BTreeSet::from([head]);
    revision.added.clear();
    revision.moved.clear();
    revision.dropped.clear();
    revision.edited = [(file, wrong)].into_iter().collect();
    store.insert(&revision).expect("writing the revision");

    let report = Store::check(&root);
    assert!(!report.is_ok(), "a store that contradicts itself fails");
    let disagreements: Vec<&Finding> = report
        .errors()
        .filter(|finding| matches!(finding, Finding::ContentDisagrees { .. }))
        .collect();
    assert_eq!(disagreements.len(), 1, "{:?}", report.findings());
    let rendered = disagreements[0].to_string();
    assert!(rendered.contains("not what is there"), "{rendered}");

    // And the store says the same thing when asked for the file directly.
    let error = store
        .content(&revision.id(), &file)
        .expect_err("a document applied to the wrong file");
    assert!(error.to_string().contains("corrupt"), "{error}");
}

#[test]
fn an_undelivered_operation_document_is_a_note() {
    // Transport has more to deliver, which is ordinary — the same judgement
    // decision 0006 made about an undelivered parent.
    let (root, store) = tree_corpus_store("undelivered-operations");
    let head = head_of(&store);
    for entry in fs::read_dir(root.join("operations")).expect("operations") {
        fs::remove_file(entry.expect("an entry").path()).expect("removing");
    }

    let report = Store::check(&root);
    assert!(report.is_ok(), "{:?}", report.findings());
    let missing = report
        .notes()
        .filter(|finding| matches!(finding, Finding::MissingOperations { .. }))
        .count();
    assert_eq!(missing, 4);

    // Asking for content says which document is missing rather than guessing.
    let store = Store::open(store.root()).expect("reopening");
    let tree = store.tree(&head).expect("the tree still replays");
    let (file, _) = tree.files().next().expect("the README");
    assert!(matches!(
        store.content(&head, file),
        Err(historica::store::MaterialiseError::MissingOperations { .. })
    ));
}

#[test]
fn a_concurrent_history_materialises_rather_than_being_refused() {
    // The revisions corpus has a merge in it, and the store now walks it:
    // 0008's rules for the tree, 0007's replay for content.
    let (_, store) = corpus_store("concurrent");
    let merge = store
        .iter()
        .find(|(_, document)| document.parents.len() > 1)
        .map(|(id, _)| *id)
        .expect("the corpus has a merge");

    let merged = store.merged_tree(&merge).expect("a tree at a merge");
    assert!(
        merged.tree.is_empty() && merged.contested.is_empty(),
        "these revisions state no tree facts, so the file set is empty"
    );
}

/// One revision recorded from the folder as it stands, for the tests below.
fn record_folder(
    store: &mut Store,
    base: &Path,
    parents: Vec<RevisionId>,
    message: &str,
) -> historica::record::Recorded {
    use historica::record::{Clock as _, Platform, Recording, record};
    use historica::working::Working;

    let mut platform = Platform;
    let working = Working::read(base, store.skipped()).expect("the folder");
    record(
        store,
        &working,
        &Recording {
            parents,
            author: "Adam Harris <adam@example.com>".to_owned(),
            when: platform.now().expect("a clock"),
            message: message.to_owned(),
            moves: Vec::new(),
            at: Vec::new(),
        },
        &mut platform,
    )
    .expect("recording")
}

#[test]
fn abandoning_a_head_leaves_the_change_abandoned_and_the_content_its_parents() {
    use historica::record::{Abandoning, Clock as _, Platform, abandon};

    let base = scratch("abandon-library");
    let mut store = Store::init(base.join("history")).expect("a new store");

    fs::write(base.join("notes.md"), "First thought.\n").expect("a file");
    let first = record_folder(&mut store, &base, Vec::new(), "Start a journal");
    fs::write(base.join("notes.md"), "First thought.\nA draft.\n").expect("a file");
    let second = record_folder(&mut store, &base, vec![first.revision], "A draft");

    let mut platform = Platform;
    let abandoned = abandon(
        &mut store,
        &Abandoning {
            revision: second.revision,
            author: "Adam Harris <adam@example.com>".to_owned(),
            when: platform.now().expect("a clock"),
            message: "The draft does not survive its own example".to_owned(),
        },
        &mut platform,
    )
    .expect("abandoning a head");

    // Decision 0013: the change is `Abandoned` — every revision of it
    // superseded by a revision of another change — and reached deliberately.
    let history = store.history();
    assert!(matches!(
        history.change_state(&second.change),
        ChangeState::Abandoned
    ));

    // The tombstone is the head, and the only current one.
    let heads = history.heads();
    let superseded = history.superseded();
    let current: Vec<_> = heads.difference(&superseded).collect();
    assert_eq!(current, vec![&abandoned.revision]);

    // Content at the tombstone is content at its parent: nothing was undone,
    // because nothing that was undone was ever an ancestor.
    let file = *first.plan.added.keys().next().expect("the file");
    assert_eq!(
        store
            .content(&abandoned.revision, &file)
            .expect("content at the tombstone")
            .text(),
        store
            .content(&first.revision, &file)
            .expect("content at the parent")
            .text(),
    );
    assert!(Store::check(store.root()).is_ok());
}

#[test]
fn abandoning_wants_a_reason_and_a_run_that_is_a_line() {
    use historica::record::{Abandoning, Clock as _, Platform, RecordError, abandon};

    let base = scratch("abandon-refusals-library");
    let mut store = Store::init(base.join("history")).expect("a new store");

    fs::write(base.join("notes.md"), "Base.\n").expect("a file");
    let root = record_folder(&mut store, &base, Vec::new(), "Base");
    fs::write(base.join("notes.md"), "Base.\nLeft.\n").expect("a file");
    let left = record_folder(&mut store, &base, vec![root.revision], "Left");
    fs::write(base.join("notes.md"), "Base.\nRight.\n").expect("a file");
    let _right = record_folder(&mut store, &base, vec![root.revision], "Right");

    let platform = Platform;
    let abandoning = |revision, message: &str| Abandoning {
        revision,
        author: "Adam Harris <adam@example.com>".to_owned(),
        when: platform.now().expect("a clock"),
        message: message.to_owned(),
    };

    // No reason is a refusal: the reason is the only thing a tombstone carries.
    assert!(matches!(
        abandon(&mut store, &abandoning(left.revision, "  "), &mut Platform),
        Err(RecordError::NoReasonGiven)
    ));
    // A fork is two lines of work where a person named one.
    assert!(matches!(
        abandon(&mut store, &abandoning(root.revision, "why"), &mut Platform),
        Err(RecordError::Forked { .. })
    ));
}
