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
use historica::store::{Bookmark, Finding, Name, Placement, Severity, Store};

/// A fresh directory for one test, inside the target directory.
fn scratch(test: &str) -> PathBuf {
    let path = Path::new(env!("CARGO_TARGET_TMPDIR")).join(test);
    let _ = fs::remove_dir_all(&path);
    fs::create_dir_all(&path).expect("a scratch directory");
    path
}

/// The digest one corpus revision has, which is the digest of its own bytes.
fn corpus_revision(name: &str) -> RevisionId {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/corpus/revisions")
        .join(name);
    digest(&fs::read(path).expect("a corpus file"))
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
    assert_eq!(header.lines().next(), Some("historica"));
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
        before
            .revisions()
            .map(|(id, _)| *id)
            .collect::<BTreeSet<_>>(),
        after
            .revisions()
            .map(|(id, _)| *id)
            .collect::<BTreeSet<_>>()
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

/// Decision 0046: a root directory this format does not name belongs to
/// whichever tool wrote it.
///
/// The trust layer is that decision's case — `claims/` holds documents
/// vouching for a revision's digest and `trust/` holds the policy that weighs
/// them, both written and read by a separate tool with no Historica in it —
/// and tolerance is the whole of what Historica contributes to it. So the
/// promise is threefold and pinned here rather than left to the fact that
/// nothing currently walks the root: such a directory is not loaded as
/// history, not reported by `check` in any severity, and not moved by
/// `arrange`, which is the one command that rewrites the store's own
/// filenames. `Placement::Refiled` is the invasive spelling of it — the
/// migration that lifts every revision document into decision 0041's month —
/// and even that has no business here.
#[test]
fn a_root_directory_this_format_does_not_name_is_left_alone() {
    let (root, store) = corpus_store("foreign-directory");
    let held = store.len();

    for directory in ["claims", "trust"] {
        fs::create_dir(root.join(directory)).expect("a directory another tool owns");
    }
    let claim = root.join("claims").join("33f863f1.claim.txt");
    fs::write(&claim, "claim-0\nrevision 33f863f1\nrole reviewer\n").expect("a claim");
    let policy = root.join("trust").join("policy.txt");
    fs::write(
        &policy,
        "key RWTd8LRCGA9i53mlYecO4IzT51TGPpvWucNSCh1CBM0QTaLn73Y7GFO3\n",
    )
    .expect("a policy");

    let reopened = Store::open(&root).expect("reopening");
    assert_eq!(reopened.len(), held, "a foreign directory is not history");

    // Not an error, and not a note either. A tool that filed its own documents
    // beside this store did nothing wrong, and a note saying so on every
    // machine the trust layer has touched is a note that means nothing.
    let report = Store::check(&root);
    assert!(
        report.is_ok(),
        "a directory this format does not name is not a fault"
    );
    let mentions: Vec<String> = report
        .findings()
        .iter()
        .map(ToString::to_string)
        .filter(|finding| finding.contains("claims") || finding.contains("trust"))
        .collect();
    assert!(
        mentions.is_empty(),
        "check should say nothing about it: {mentions:?}"
    );

    let mut store = Store::open(&root).expect("reopening to arrange");
    store
        .arrange(Placement::Refiled)
        .expect("arranging a store with a stranger's directory in it");

    assert!(claim.is_file(), "the claim is where its own tool put it");
    assert!(policy.is_file(), "and so is the policy");
    assert!(Store::check(&root).is_ok(), "arranging broke nothing");
}

/// Decision 0023, amended: a rewrite reaches what it rewrote and nothing
/// standing on it, because supersession is a statement about one change's
/// revisions and parenthood is a different graph.
///
/// The corpus is a finished rewrite and the shape the half-delivered one
/// arrives in. 05 amends 02, and 06 is the rebase that carried the merge
/// standing on 02 across to the amendment — so every revision on the old side
/// is itself superseded, and there is no gap to report. Take 06 away, which is
/// the state a receive leaves when one replica rewrote a revision and the
/// other built on it, and the merge is live again on a revision that has been
/// withdrawn. That is a note: every document here still parses, hashes and
/// replays, and what the store lacks is the rest of the rewrite.
#[test]
fn work_left_standing_on_a_rewritten_revision_is_a_note() {
    let (root, _) = corpus_store("unreached-rewrite");

    let finished = Store::check(&root);
    assert!(
        !finished
            .findings()
            .iter()
            .any(|finding| matches!(finding, Finding::StandsOnSuperseded { .. })),
        "a rewrite that reached its descendants leaves no gap"
    );

    let concurrent = corpus_revision("02-concurrent.rev.txt");
    let merge = corpus_revision("04-merge.rev.txt");
    let amended = corpus_revision("05-amended.rev.txt");
    fs::remove_file(root.join("revisions/06-rebased.rev.txt")).expect("the undelivered rebase");

    let report = Store::check(&root);
    assert!(report.is_ok(), "the store contradicts nothing");
    let unreached: Vec<&Finding> = report
        .findings()
        .iter()
        .filter(|finding| matches!(finding, Finding::StandsOnSuperseded { .. }))
        .collect();
    assert_eq!(unreached.len(), 1, "{unreached:?}");

    let Finding::StandsOnSuperseded {
        revision,
        superseded,
        successors,
    } = unreached[0]
    else {
        unreachable!("filtered above")
    };
    assert_eq!(*revision, merge, "the merge is what was left behind");
    assert_eq!(
        *superseded, concurrent,
        "standing on the withdrawn revision"
    );
    assert!(
        successors.contains(&amended),
        "and the amendment is where that work belongs instead"
    );
    assert_eq!(unreached[0].severity(), Severity::Note);
}

#[test]
fn a_file_that_does_not_parse_is_an_error_naming_the_file() {
    let (root, _) = corpus_store("unparsable");
    fs::write(
        root.join("revisions/broken.rev.txt"),
        b"historica\nnonsense\n",
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
    let documents: Vec<_> = store
        .documents()
        .expect("readable")
        .into_iter()
        .map(|(id, doc)| (*id, doc.clone()))
        .collect();

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
        .documents()
        .expect("readable")
        .into_iter()
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
fn a_bookmark_is_one_line_and_at_most_one_more() {
    let (root, mut store) = corpus_store("bookmark-grammar");
    let id = corpus_revision("01-root.rev.txt");

    // Decision 0062: the axis is a second line, and `private` is the whole of
    // what a second line may say. 0006 refused a second line that could
    // *disagree* with the first; this one makes no claim about the target.
    store
        .set_bookmark("secret", Bookmark::private(Name::Revision(id)))
        .expect("a private bookmark");
    assert_eq!(
        fs::read_to_string(root.join("names/secret.txt")).expect("the file"),
        format!("revision {id}\nprivate\n")
    );
    assert_eq!(
        Store::open(&root).expect("reopening").bookmark("secret"),
        Some(Bookmark::private(Name::Revision(id)))
    );

    // A file with no second line is shared, which is every bookmark file
    // written before 0062.
    fs::write(root.join("names/old.txt"), format!("revision {id}\n")).expect("a bookmark");
    assert_eq!(
        Store::open(&root).expect("reopening").bookmark("old"),
        Some(Bookmark::shared(Name::Revision(id)))
    );

    for (label, text) in [
        ("second", format!("revision {id}\nsomething else\n")),
        ("third", format!("revision {id}\nprivate\nprivate\n")),
        ("alone", "private\n".to_owned()),
    ] {
        let path = root.join(format!("names/{label}.txt"));
        fs::write(&path, text).expect("a bookmark");
        assert!(
            Store::open(&root).is_err(),
            "`{label}` loaded, and loading is strict"
        );
        fs::remove_file(&path).expect("removing it again");
    }
}

#[test]
fn moving_a_bookmark_keeps_the_axis_and_stating_it_replaces_it() {
    let (root, mut store) = corpus_store("bookmark-axis");
    let first = corpus_revision("01-root.rev.txt");
    let second = corpus_revision("02-concurrent.rev.txt");

    store
        .set_bookmark("secret", Bookmark::private(Name::Revision(first)))
        .expect("a private bookmark");
    // Decision 0062: moving a bookmark is what `record` does on every commit,
    // and one that un-privatised itself on the way would be the leak the axis
    // exists to prevent, arriving from the command nobody reads as a
    // disclosure.
    store
        .set_name("secret", Name::Revision(second))
        .expect("moving it");
    assert_eq!(
        store.bookmark("secret"),
        Some(Bookmark::private(Name::Revision(second)))
    );

    // Stating it is what changes it, in either direction.
    store
        .set_bookmark("secret", Bookmark::shared(Name::Revision(second)))
        .expect("sharing it");
    assert_eq!(
        fs::read_to_string(root.join("names/secret.txt")).expect("the file"),
        format!("revision {second}\n")
    );
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
fn a_conflicted_copy_is_only_a_legitimate_duplicate() {
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
            .any(|finding| matches!(finding, Finding::DuplicateContent { .. }))
    );
}

#[test]
fn a_store_of_an_unknown_version_refuses_rather_than_guesses() {
    let root = scratch("version").join("history");
    Store::init(&root).expect("a new store");
    fs::write(root.join("historica.txt"), "historica-v6\n").expect("a newer store");

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
    for (directory, suffix) in [("revisions", ".rev.txt"), ("operations", "")] {
        for entry in fs::read_dir(corpus.join(directory)).expect("the corpus") {
            let path = entry.expect("an entry").path();
            let found = path.file_name().and_then(|name| name.to_str());
            // `operations/` takes everything: documents by their suffix, and
            // payloads — a file's own content — under any name at all.
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
        .revisions()
        .flat_map(|(_, revision)| revision.parents.iter().copied())
        .collect();
    let heads: Vec<RevisionId> = store
        .revisions()
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
    assert_eq!(store.operations().unwrap().len(), 2);
    assert!(Store::check(&root).is_ok());
}

#[test]
fn a_broken_operation_document_stops_the_question_that_needs_it_and_nothing_else() {
    // Opening reads `revisions/` and not `operations/`, so a graph question is
    // answerable in a store whose content documents are unreadable, and the
    // strictness lands on whatever first asks what a revision did. `check` is
    // the command that reads everything deliberately, and it says so either
    // way.
    let (root, store) = tree_corpus_store("broken-operations");
    let head = head_of(&store);
    let before = store.tree(&head).expect("the file set at the head");
    // The corpus drops the entry at its head, so the README is the file that
    // survives and the entry's documents are on nothing this asks about.
    let file = *before.files().next().expect("the surviving file").0;
    let readable = store.content(&head, &file).expect("the README").text();

    let directory = root.join("operations");
    let break_it = |name: &str| {
        fs::write(
            directory.join(name),
            b"historica
nonsense
",
        )
        .expect("breaking it");
    };

    // The document belonging to the file this head dropped.
    break_it("02-entry.ops.txt");
    let store = Store::open(&root).expect("a store whose revisions still parse");
    assert_eq!(store.len(), 4);
    assert_eq!(store.tree(&head).expect("the file set"), before);

    // Asking what the directory holds is asking about every file in it, so
    // that is where the parse failure lands, named.
    let Err(error) = store.operations() else {
        panic!("the directory does not parse");
    };
    let rendered = error.to_string();
    assert!(rendered.contains("02-entry.ops.txt"), "{rendered}");

    // And nothing else: the README's own history is untouched by a broken
    // document that belongs to another file, which decision 0036 is what
    // makes true — a reader fetches the digests it needs rather than parsing
    // the directory before it will answer anything.
    assert_eq!(
        store
            .content(&head, &file)
            .expect("still the README")
            .text(),
        readable
    );

    // The document that file *does* need is the other half of the claim.
    // Decision 0036 makes the refusal about a digest rather than a filename:
    // identity is content, so bytes a person overwrote are a document this
    // store no longer holds, whatever the file is still called.
    break_it("03-readme.ops.txt");
    let store = Store::open(&root).expect("a store whose revisions still parse");
    store
        .content(&head, &file)
        .expect_err("the content that needed it");

    // `check` reads everything deliberately, and is where a file that will
    // not parse is named as the fault it is.
    let report = Store::check(&root);
    assert!(!report.is_ok());
    assert!(
        report
            .errors()
            .any(|finding| matches!(finding, Finding::Unparsable { .. }))
    );
    assert!(
        report
            .errors()
            .any(|finding| finding.to_string().contains("03-readme.ops.txt")),
        "check names the file: {:?}",
        report.errors().map(ToString::to_string).collect::<Vec<_>>()
    );
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
        // A document keeps a document suffix — the suffix is the claim to be
        // one — and a payload keeps having none, for the same reason.
        let name = if path.to_string_lossy().ends_with(".ops.txt") {
            format!("{index}-renamed.ops.txt")
        } else {
            format!("{index}-renamed")
        };
        fs::rename(&path, directory.join(name)).expect("renaming");
    }

    let store = Store::open(&root).expect("reopening a renamed store");
    assert_eq!(store.tree(&head).expect("a tree"), before);
    assert_eq!(store.operations().unwrap().len(), 2);
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

    let wrong = OperationDocument::parse(b"historica\n\ndelete 0 1\n-not what is there\n")
        .expect("a document that parses");
    let wrong = store.insert_operation(&wrong).expect("writing it");

    let mut revision = store
        .get(&head)
        .expect("readable")
        .expect("the head")
        .clone();
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
        .filter(|finding| {
            matches!(
                finding,
                Finding::MissingOperations { .. } | Finding::MissingPayload { .. }
            )
        })
        .count();
    assert_eq!(missing, 4, "{:?}", report.findings());

    // Asking for content says what is missing rather than guessing. The
    // README's chain starts at its payload, so that is the absence it meets.
    let store = Store::open(store.root()).expect("reopening");
    let tree = store.tree(&head).expect("the tree still replays");
    let (file, _) = tree.files().next().expect("the README");
    assert!(matches!(
        store.content(&head, file),
        Err(historica::store::MaterialiseError::MissingPayload { .. }
            | historica::store::MaterialiseError::MissingOperations { .. })
    ));
}

#[test]
fn a_concurrent_history_materialises_rather_than_being_refused() {
    // The revisions corpus has a merge in it, and the store now walks it:
    // 0008's rules for the tree, 0007's replay for content.
    let (_, store) = corpus_store("concurrent");
    let merge = store
        .revisions()
        .find(|(_, revision)| revision.parents.len() > 1)
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
    use historica::record::{Clock as _, Platform, Recording, Restriction, record};
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
            accepted: BTreeSet::new(),
            only: Restriction::Everything,
            kinds: Default::default(),
        },
        &mut platform,
    )
    .expect("recording")
}

/// Decision 0030 deferred "materialising a revision into a directory
/// elsewhere", which needs no position and no rule beyond an empty
/// destination, and left it waiting for something to need it.
///
/// This is that, and the whole shape of what needs it: lay a past revision out
/// somewhere, work in it, and record the result against that revision — with
/// the folder beside the store never moving, so 0030's refusal is untouched
/// and no position is written anywhere. What makes it worth sharing `update`'s
/// machinery rather than writing the loop per caller is the three files here:
/// a payload is written as its bytes rather than as text, and a mode comes
/// with the file it belongs to.
#[test]
fn a_revision_is_laid_out_in_an_empty_directory_and_recorded_back_from_it() {
    use historica::fs::{Disk, Filesystem as _};
    use historica::update;
    use historica::working::Working;

    let root = scratch("lay-out");
    let base = root.join("repo");
    fs::create_dir_all(&base).expect("a repository");
    let mut store = Store::init(base.join("history")).expect("a new store");

    fs::write(base.join("notes.md"), "First thought.\n").expect("a file");
    fs::write(base.join("photo.bin"), [0u8, 159, 146, 150]).expect("bytes, not lines");
    fs::write(base.join("run.sh"), "#!/bin/sh\necho hi\n").expect("a script");
    Disk.set_executable(&base.join("run.sh"), true)
        .expect("a mode this platform has");
    let first = record_folder(&mut store, &base, Vec::new(), "Start a journal");

    fs::write(base.join("notes.md"), "First thought.\nA draft.\n").expect("a file");
    record_folder(&mut store, &base, vec![first.revision], "A draft");

    let elsewhere = root.join("elsewhere");
    fs::create_dir_all(&elsewhere).expect("an empty directory");
    let into = Working::read(&elsewhere, store.skipped()).expect("walking nothing");
    let plan =
        update::plan_into(&store, &into, &elsewhere, &first.revision).expect("laying it out");
    let applied = update::apply(&store, &into, &elsewhere, &plan).expect("applying");
    assert_eq!(applied.wrote.len(), 3, "{applied:?}");

    assert_eq!(
        fs::read_to_string(elsewhere.join("notes.md")).expect("the file"),
        "First thought.\n",
        "the past revision, not the head"
    );
    assert_eq!(
        fs::read(elsewhere.join("photo.bin")).expect("the payload"),
        vec![0u8, 159, 146, 150],
        "a payload is its bytes"
    );
    assert_eq!(
        Disk.executable(&elsewhere.join("run.sh")).expect("asking"),
        Some(true),
        "the mode came with the file"
    );

    // Work in it, and record against the revision it holds. The store is the
    // origin's throughout: nothing was exported and no history was copied.
    fs::write(elsewhere.join("notes.md"), "First thought.\nAnother way.\n").expect("a file");
    let branched = record_folder(&mut store, &elsewhere, vec![first.revision], "Another way");
    let tree = store.tree(&branched.revision).expect("its tree");
    let (file, _) = tree
        .files()
        .find(|(_, path)| *path == "notes.md")
        .expect("notes.md");
    assert_eq!(
        store
            .content(&branched.revision, file)
            .expect("its content")
            .text(),
        "First thought.\nAnother way.\n"
    );

    // The folder beside the store never moved, which is the whole point.
    assert_eq!(
        fs::read_to_string(base.join("notes.md")).expect("the folder"),
        "First thought.\nA draft.\n"
    );
    assert!(Store::check(store.root()).is_ok());

    // And the safety rule: a directory holding something is refused by name.
    let again = Working::read(&elsewhere, store.skipped()).expect("walking it again");
    let error = update::plan_into(&store, &again, &elsewhere, &first.revision)
        .expect_err("a directory that holds something");
    let rendered = error.to_string();
    assert!(rendered.contains("notes.md"), "{rendered}");
    assert!(rendered.contains("holding nothing"), "{rendered}");
}

/// Decision 0025's per-file rule over `Disk`, where the guard is
/// fs-transaction's: `write_if` stages the plan's look as an expectation
/// inside the apply that writes, so the comparison and the write are one
/// operation — and a set of one op takes the journal-free fast path, so no
/// journal file ever appears beside a person's own files.
#[test]
fn a_raced_edit_is_left_by_the_disk_update_too() {
    use historica::update;
    use historica::working::Working;

    let root = scratch("update-drift");
    let base = root.join("repo");
    fs::create_dir_all(&base).expect("a repository");
    let mut store = Store::init(base.join("history")).expect("a new store");

    fs::write(base.join("notes.md"), "First thought.\n").expect("a file");
    let first = record_folder(&mut store, &base, Vec::new(), "Start a journal");
    fs::write(base.join("notes.md"), "First thought.\nA second one.\n").expect("a file");
    let second = record_folder(&mut store, &base, vec![first.revision], "A second thought");

    // The folder stands at the first revision — recorded bytes, so the plan
    // may write the head back over them.
    fs::write(base.join("notes.md"), "First thought.\n").expect("recorded bytes");
    let working = Working::read(&base, store.skipped()).expect("the folder");
    let plan = update::plan(&store, &working, &base, &second.revision).expect("a plan");
    assert_eq!(plan.writes.len(), 1, "one file differs");

    // The race: an edit lands after the plan looked and before apply does.
    fs::write(base.join("notes.md"), "work the plan never saw\n").expect("the race");

    let applied = update::apply(&store, &working, &base, &plan).expect("applying");
    assert!(applied.wrote.is_empty(), "{applied:?}");
    assert_eq!(
        applied.left,
        [(
            "notes.md".to_owned(),
            "it changed underneath the update".to_owned()
        )]
    );
    assert_eq!(
        fs::read_to_string(base.join("notes.md")).expect("still here"),
        "work the plan never saw\n",
        "a raced edit is not update's to clobber"
    );
    // The fast path journaled nothing next to the person's own files.
    assert!(!base.join(".fstx-journal").exists());
}

/// The guard itself, arm by arm: `Disk::write_if` answers `Drifted` and
/// leaves the destination alone wherever the path does not hold exactly what
/// the caller said — present where nothing was expected, holding other
/// bytes, or gone — and writes only where the expectation holds, making the
/// destination's directories on the way.
#[test]
fn write_if_answers_drifted_rather_than_writing_over_a_race() {
    use historica::fs::{Disk, Filesystem as _, Guarded};

    let root = scratch("write-if");
    let path = root.join("doc.md");

    // A guarded create expects nothing; something standing there is a drift.
    fs::write(&path, "raced").expect("the race");
    assert_eq!(
        Disk.write_if(&path, None, b"new").expect("an answer"),
        Guarded::Drifted
    );
    assert_eq!(fs::read_to_string(&path).expect("untouched"), "raced");

    // A replacement expects the bytes last seen, exactly.
    assert_eq!(
        Disk.write_if(&path, Some(b"stale"), b"new")
            .expect("an answer"),
        Guarded::Drifted
    );
    assert_eq!(fs::read_to_string(&path).expect("untouched"), "raced");
    assert_eq!(
        Disk.write_if(&path, Some(b"raced"), b"new")
            .expect("an answer"),
        Guarded::Written
    );
    assert_eq!(fs::read_to_string(&path).expect("replaced"), "new");

    // A file that went away is a drift too, not a quiet re-creation.
    let gone = root.join("gone.md");
    assert_eq!(
        Disk.write_if(&gone, Some(b"was"), b"new")
            .expect("an answer"),
        Guarded::Drifted
    );
    assert!(!gone.exists());

    // A guarded create lands where nothing stands, parents included.
    let fresh = root.join("deep/fresh.md");
    assert_eq!(
        Disk.write_if(&fresh, None, b"made").expect("an answer"),
        Guarded::Written
    );
    assert_eq!(fs::read_to_string(&fresh).expect("created"), "made");
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
