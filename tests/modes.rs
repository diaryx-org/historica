//! A file can be run: decision 0034 executed.
//!
//! `tests/corpus/modes/` is three revisions of one publish script. It arrives
//! plain, because a file no `mode` line has ever named is plain; a revision
//! that states one mode and nothing else makes it runnable; and a third states
//! a mode and an edit together, in the order the format writes them.
//!
//! The claim these check is the one the decision turns on: the bit survives a
//! round trip. A store records what the folder said, the folder gets back what
//! the store recorded, and a reader that has never heard of version 4 refuses
//! only the documents that actually use it.

use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};

use historica::core::{FileId, RevisionId};
use historica::format::{Mode, ParseErrorKind, RevisionDocument, Version, digest};
use historica::store::Store;
use historica::tree::{Tree, TreeError};

/// The publish script, as the corpus names it.
const SCRIPT: &str = "nrqvtkzlmwyxsptonvqrklmz";

fn corpus() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/corpus/modes")
}

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

fn parsed(name: &str) -> RevisionDocument {
    RevisionDocument::parse(&read(name)).unwrap_or_else(|error| panic!("{name}: {error}"))
}

fn script() -> FileId {
    SCRIPT.parse().expect("a file ID")
}

/// The corpus, copied into a store a command could be pointed at.
fn store(name: &str) -> Store {
    let root = Path::new(env!("CARGO_TARGET_TMPDIR"))
        .join(name)
        .join("history");
    let _ = fs::remove_dir_all(root.parent().expect("a scratch directory"));
    Store::init(&root).expect("a new store");
    for directory in ["revisions", "operations"] {
        for entry in fs::read_dir(corpus().join(directory)).expect("the corpus") {
            let from = entry.expect("an entry").path();
            let to = root
                .join(directory)
                .join(from.file_name().expect("a filename"));
            fs::copy(&from, &to).expect("copying a corpus file");
        }
    }
    fs::write(root.join("historica.txt"), "historica-v4\n").expect("the version this corpus is");
    Store::open(&root).expect("the corpus opens")
}

#[test]
fn the_manifest_describes_the_corpus_on_disk() {
    for (name, expected) in manifest() {
        assert_eq!(digest(&read(&name)), expected, "{name} has drifted");
    }
}

/// Every canonical file parses, and writing it back reproduces its bytes —
/// which is what lets the digest cover the file rather than a model of it.
#[test]
fn every_canonical_file_round_trips() {
    for name in manifest().into_keys() {
        if name.starts_with("invalid/") || !name.ends_with(".rev.txt") {
            continue;
        }
        let bytes = read(&name);
        let document = parsed(&name);
        assert_eq!(document.write(), bytes, "{name} did not round trip");
    }
}

/// A document claims the lowest version that expresses it, so the revision
/// that states no mode is still version 1 and readable by every reader ever
/// published for it.
#[test]
fn only_a_document_with_a_mode_in_it_claims_version_four() {
    assert_eq!(parsed("revisions/01-start.rev.txt").version, Version::V1);
    assert_eq!(parsed("revisions/02-runnable.rev.txt").version, Version::V4);
    assert_eq!(parsed("revisions/03-plain.rev.txt").version, Version::V4);
}

/// The tree is where a mode ends up, and where a `mode` line means anything.
#[test]
fn the_bit_follows_the_file_through_the_history() {
    let store = store("modes-tree");
    let mut ids: Vec<RevisionId> = Vec::new();
    for name in [
        "revisions/01-start.rev.txt",
        "revisions/02-runnable.rev.txt",
        "revisions/03-plain.rev.txt",
    ] {
        ids.push(digest(&read(name)));
    }

    let start = store.tree(&ids[0]).expect("the tree at the root");
    assert_eq!(start.mode(&script()), Some(Mode::Plain));

    let runnable = store.tree(&ids[1]).expect("the tree after the chmod");
    assert_eq!(runnable.mode(&script()), Some(Mode::Executable));
    // A mode is not content: the file it is a fact about is untouched.
    assert_eq!(
        store
            .content(&ids[1], &script())
            .expect("the content")
            .text(),
        store
            .content(&ids[0], &script())
            .expect("the content")
            .text()
    );

    let plain = store.tree(&ids[2]).expect("the tree after the revert");
    assert_eq!(plain.mode(&script()), Some(Mode::Plain));
    assert!(
        store
            .content(&ids[2], &script())
            .expect("the content")
            .text()
            .contains("the path given"),
        "the edit in the same document still applied"
    );
}

/// A `mode` naming a file the tree does not hold is the error every other tree
/// fact already gets.
#[test]
fn a_mode_for_a_file_that_is_not_here_is_refused_by_name() {
    let document = parsed("revisions/02-runnable.rev.txt");
    let error = Tree::empty()
        .apply(&document)
        .expect_err("the file was never added");
    assert!(
        matches!(error, TreeError::Unknown { key: "mode", file } if file == script()),
        "{error:?}"
    );
}

/// Each invalid file is refused, and refused for its own stated reason.
#[test]
fn every_invalid_file_is_refused_for_its_own_reason() {
    let wanted: Vec<(&str, ParseErrorKind)> = vec![
        (
            "invalid/mode-in-version-3.rev.txt",
            ParseErrorKind::HeaderNeedsVersion {
                key: "mode".to_owned(),
                found: Version::V3,
                needs: Version::V4,
            },
        ),
        (
            "invalid/unknown-mode.rev.txt",
            ParseErrorKind::UnknownMode {
                found: "755".to_owned(),
            },
        ),
        (
            "invalid/drop-and-mode.rev.txt",
            ParseErrorKind::ContradictoryFileFacts {
                first: "drop",
                second: "mode",
                file: SCRIPT.to_owned(),
            },
        ),
        (
            "invalid/mode-stated-twice.rev.txt",
            ParseErrorKind::FileStatedTwice {
                key: "mode",
                file: SCRIPT.to_owned(),
            },
        ),
    ];

    // Every invalid file in the corpus is accounted for, so one added without
    // a reason beside it fails here rather than sitting unchecked.
    let named: Vec<&str> = wanted.iter().map(|(name, _)| *name).collect();
    for name in manifest().into_keys() {
        if name.starts_with("invalid/") {
            assert!(
                named.contains(&name.as_str()),
                "{name} has no stated reason"
            );
        }
    }

    for (name, kind) in wanted {
        let error = RevisionDocument::parse(&read(name))
            .map(|document| document.write())
            .expect_err(&format!("{name} should not parse"));
        assert_eq!(error.kind, kind, "{name} failed for the wrong reason");
        // Decision 0004: a refusal names the line and says what to do.
        assert!(error.line > 0, "{name} named no line");
        assert!(!error.kind.to_string().is_empty(), "{name} said nothing");
    }
}
