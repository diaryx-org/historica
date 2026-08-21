//! The corpus is the specification, executed.
//!
//! `tests/corpus/revisions/` is hand-written, and every file in it pins down
//! something the parser must get right. These tests are what make that claim
//! checkable rather than aspirational:
//!
//! - every canonical file parses, and writing it back reproduces its bytes;
//! - every invalid file is refused, and refused for *its own* reason;
//! - the digest the model computes is the one `shasum` printed into MANIFEST;
//! - the seven canonical files really are the five-change history they claim.

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Path, PathBuf};

use historica::core::{ChangeState, History, RevisionId};
use historica::format::{ParseErrorKind, RevisionDocument, digest};

fn corpus() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/corpus/revisions")
}

/// Every `name  digest` pair in MANIFEST, which is `shasum -a 256` output.
fn manifest() -> BTreeMap<String, RevisionId> {
    let text = fs::read_to_string(corpus().join("MANIFEST")).expect("MANIFEST is readable");
    text.lines()
        .filter(|line| !line.trim().is_empty())
        .map(|line| {
            let (digest, name) = line.split_once("  ").expect("`<digest>  <name>` per line");
            (
                name.to_owned(),
                digest.parse().expect("a digest in the manifest"),
            )
        })
        .collect()
}

fn read(name: &str) -> Vec<u8> {
    fs::read(corpus().join(name)).unwrap_or_else(|_| panic!("{name} is readable"))
}

fn canonical_names() -> Vec<String> {
    manifest()
        .into_keys()
        .filter(|name| !name.starts_with("invalid/"))
        .collect()
}

#[test]
fn the_manifest_describes_the_corpus_on_disk() {
    // Guards against a corpus edited without regenerating MANIFEST, which
    // would let every other test here pass against the wrong bytes.
    for (name, expected) in manifest() {
        assert_eq!(digest(&read(&name)), expected, "{name} has drifted");
    }
}

#[test]
fn every_canonical_file_parses() {
    for name in canonical_names() {
        let bytes = read(&name);
        if let Err(error) = RevisionDocument::parse(&bytes) {
            panic!("{name} should parse, but {error}");
        }
    }
}

#[test]
fn writing_a_parsed_document_reproduces_its_bytes() {
    // The claim decision 0004 rests on: the parser accepts exactly what the
    // writer emits, so there is one byte sequence per set of facts.
    for name in canonical_names() {
        let bytes = read(&name);
        let document = RevisionDocument::parse(&bytes).expect("a canonical file");
        assert_eq!(
            document.write(),
            bytes,
            "{name} does not survive a round trip"
        );
    }
}

#[test]
fn a_documents_id_is_the_digest_of_its_file() {
    for (name, expected) in manifest() {
        if name.starts_with("invalid/") {
            continue;
        }
        let document = RevisionDocument::parse(&read(&name)).expect("a canonical file");
        assert_eq!(document.id(), expected, "{name}");
    }
}

/// What each invalid file exists to prove. A test that only asserted "this
/// fails" would pass for a parser that rejected everything.
fn expected_failures() -> Vec<(&'static str, ParseErrorKind)> {
    vec![
        (
            "invalid/carriage-returns.rev.txt",
            ParseErrorKind::CarriageReturn,
        ),
        (
            "invalid/change-id-in-the-digest-alphabet.rev.txt",
            ParseErrorKind::MalformedChangeId {
                found: "1a4f9c2e0b7d6533a8c1f40e".to_owned(),
            },
        ),
        (
            "invalid/empty-header-value.rev.txt",
            ParseErrorKind::EmptyValue,
        ),
        (
            "invalid/headers-out-of-order.rev.txt",
            ParseErrorKind::KeysOutOfOrder {
                key: "change".to_owned(),
                after: "author".to_owned(),
            },
        ),
        (
            "invalid/missing-version-header.rev.txt",
            ParseErrorKind::MissingPreamble,
        ),
        (
            "invalid/unknown-required-header.rev.txt",
            ParseErrorKind::UnknownHeader {
                key: "signed-by".to_owned(),
            },
        ),
        (
            "invalid/unknown-version.rev.txt",
            ParseErrorKind::UnknownVersion {
                found: "3".to_owned(),
            },
        ),
        (
            "invalid/unsorted-parents.rev.txt",
            ParseErrorKind::RepeatedKeyOutOfOrder {
                key: "parent".to_owned(),
            },
        ),
        (
            "invalid/empty-body-after-separator.rev.txt",
            ParseErrorKind::EmptyBodyAfterSeparator,
        ),
    ]
}

#[test]
fn every_invalid_file_is_refused_for_its_own_reason() {
    for (name, expected) in expected_failures() {
        let error = RevisionDocument::parse(&read(name))
            .err()
            .unwrap_or_else(|| panic!("{name} should not parse"));
        assert_eq!(error.kind, expected, "{name} failed for the wrong reason");
    }
}

#[test]
fn the_invalid_directory_is_entirely_covered() {
    // A new example added to the corpus without a claim about why it fails
    // would otherwise sit there proving nothing.
    let covered = expected_failures()
        .into_iter()
        .map(|(name, _)| name.to_owned())
        .collect::<BTreeSet<_>>();
    let present = manifest()
        .into_keys()
        .filter(|name| name.starts_with("invalid/"))
        .collect::<BTreeSet<_>>();
    assert_eq!(present, covered);
}

#[test]
fn every_refusal_names_a_line_and_a_fix() {
    for (name, _) in expected_failures() {
        let error = RevisionDocument::parse(&read(name)).expect_err("an invalid file");
        let rendered = error.to_string();
        assert!(
            rendered.starts_with("line "),
            "{name}: {rendered} does not name a line"
        );
        // Every message is "what is wrong; what to do about it". Decision
        // 0004 accepts strictness only on that condition.
        let (_, fix) = rendered
            .split_once(';')
            .unwrap_or_else(|| panic!("{name}: {rendered} does not say what to do"));
        assert!(!fix.trim().is_empty(), "{name}: the fix is empty");
    }
}

/// The corpus loaded as the store decision 0003 describes: identity from
/// content, filenames ignored.
fn corpus_history() -> (History, BTreeMap<String, RevisionDocument>) {
    let mut history = History::new();
    let mut documents = BTreeMap::new();
    for name in canonical_names() {
        let document = RevisionDocument::parse(&read(&name)).expect("a canonical file");
        history
            .insert(document.to_revision())
            .expect("distinct revisions");
        documents.insert(name, document);
    }
    (history, documents)
}

#[test]
fn the_corpus_is_a_five_change_history_that_resolves() {
    let (history, documents) = corpus_history();
    assert_eq!(history.len(), 7);
    assert_eq!(history.changes().len(), 5);

    // Nothing dangles: every parent named by the corpus is in the corpus.
    assert!(
        history.missing_parents().is_empty(),
        "the corpus should be complete"
    );

    let id = |name: &str| documents[name].id();

    // 05 amends 02, keeping its change ID, so that change resolves to 05.
    let amended = &documents["05-amended.rev.txt"];
    assert_eq!(amended.change, documents["02-concurrent.rev.txt"].change);
    assert!(amended.supersedes.contains(&id("02-concurrent.rev.txt")));
    match history.change_state(&amended.change) {
        ChangeState::Resolved(current) => assert_eq!(current.id, id("05-amended.rev.txt")),
        other => panic!("an amended change resolves to its successor, not {other:?}"),
    }

    // 06 is the rewrite that amendment forced: same change as the merge it
    // supersedes, reparented onto the amended revision.
    let rebased = &documents["06-rebased.rev.txt"];
    assert_eq!(rebased.change, documents["04-merge.rev.txt"].change);
    assert!(rebased.supersedes.contains(&id("04-merge.rev.txt")));
    assert!(rebased.parents.contains(&id("05-amended.rev.txt")));

    // The merge joins the two concurrent children of the root.
    let merge = &documents["04-merge.rev.txt"];
    assert_eq!(
        merge.parents,
        BTreeSet::from([id("02-concurrent.rev.txt"), id("03-other.rev.txt")])
    );

    // 01 is the only root, and 07 the only revision outside the main line.
    assert!(documents["01-root.rev.txt"].parents.is_empty());
    assert!(documents["07-verbatim-message.rev.txt"].parents.is_empty());
}

#[test]
fn authorship_is_carried_forward_and_the_reviewer_is_named_separately() {
    let (_, documents) = corpus_history();
    let original = &documents["02-concurrent.rev.txt"];
    let amended = &documents["05-amended.rev.txt"];

    // Decision 0005: `author` and `when` describe the work and are copied.
    assert_eq!(amended.author, original.author);
    assert_eq!(amended.when, original.when);

    // `revised-by` and `revised` describe this revision, and differ.
    assert_eq!(
        amended.revised_by.as_deref(),
        Some("Rowan Vale <rowan@example.org>")
    );
    assert_ne!(amended.revised_by.as_deref(), Some(amended.author.as_str()));
    assert!(amended.revised.is_some());
    assert!(original.revised.is_none());

    // The advisory header survives, prefix included.
    assert_eq!(
        amended.extensions.get("x-review-url").map(String::as_str),
        Some("https://example.org/reviews/17")
    );
}

#[test]
fn a_message_is_kept_verbatim_and_never_interpreted() {
    let (_, documents) = corpus_history();
    let verbatim = &documents["07-verbatim-message.rev.txt"];

    // A body line that reads exactly like a header is body, not a header.
    assert!(verbatim.message.contains("\nparent 0000000000000000"));
    assert!(
        verbatim
            .message
            .contains("change this-does-not-look-like-a-change-id")
    );
    assert!(verbatim.parents.is_empty());

    // Trailing space, a tab, non-ASCII, and no final newline all survive.
    assert!(
        verbatim
            .message
            .contains("trailing space at the end of this line,  \n")
    );
    assert!(verbatim.message.contains('\t'));
    assert!(verbatim.message.contains("curly quotes"));
    assert!(!verbatim.message.ends_with('\n'));

    // An empty message is spelled by omitting the separator entirely.
    assert_eq!(documents["04-merge.rev.txt"].message, "");
}
