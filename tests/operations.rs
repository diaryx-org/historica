//! The operations half of the corpus, which is the specification, executed.
//!
//! `tests/corpus/operations/` is hand-written. The numbered files are the edits
//! the numbered revisions in `tests/corpus/revisions/` made to one file, so the
//! two halves describe one history — with a gap at 04, because a merge that
//! changes nothing about a file names no operation document. The unnumbered
//! files belong to no revision and exist to pin one rule each: carriage returns
//! as content, a last line without a terminator, and items that read like the
//! format but are not it.
//!
//! Nothing yet links a revision to its operation documents. That link is the
//! tree, which decision 0007 defers to 0008.

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Path, PathBuf};

use historica::core::RevisionId;
use historica::format::{Item, OperationDocument, OperationKind, ParseErrorKind, digest};

fn corpus() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/corpus/operations")
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

fn parse(name: &str) -> OperationDocument {
    OperationDocument::parse(&read(name)).unwrap_or_else(|error| panic!("{name}: {error}"))
}

#[test]
fn the_manifest_describes_the_corpus_on_disk() {
    for (name, expected) in manifest() {
        assert_eq!(digest(&read(&name)), expected, "{name} has drifted");
    }
}

#[test]
fn every_canonical_file_parses() {
    for name in canonical_names() {
        parse(&name);
    }
}

#[test]
fn writing_a_parsed_document_reproduces_its_bytes() {
    // One byte sequence per set of facts, which is what lets the digest cover
    // the file rather than a re-serialised model.
    for name in canonical_names() {
        let bytes = read(&name);
        assert_eq!(
            parse(&name).write(),
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
        assert_eq!(parse(&name).id(), expected, "{name}");
    }
}

/// What each invalid file exists to prove. A test that only asserted "this
/// fails" would pass for a parser that rejected everything.
fn expected_failures() -> Vec<(&'static str, ParseErrorKind)> {
    vec![
        (
            "invalid/adjacent-deletes.ops",
            ParseErrorKind::AdjacentDeletes { at: 0, total: 3 },
        ),
        (
            "invalid/carriage-return-in-an-operation.ops",
            ParseErrorKind::CarriageReturnInOperation,
        ),
        (
            "invalid/content-without-operation.ops",
            ParseErrorKind::ContentWithoutOperation { prefix: '+' },
        ),
        (
            "invalid/delete-after-insert.ops",
            ParseErrorKind::DeleteAfterInsert { position: 4 },
        ),
        (
            "invalid/delete-count-disagrees.ops",
            ParseErrorKind::DeleteCountDisagrees {
                stated: 2,
                found: 1,
            },
        ),
        ("invalid/empty-delete.ops", ParseErrorKind::EmptyDelete),
        ("invalid/empty-insert.ops", ParseErrorKind::EmptyInsert),
        (
            "invalid/inserts-at-one-position.ops",
            ParseErrorKind::InsertsAtOnePosition { position: 4 },
        ),
        (
            "invalid/leading-zero-position.ops",
            ParseErrorKind::MalformedNumber {
                found: "03".to_owned(),
            },
        ),
        (
            "invalid/malformed-operation.ops",
            ParseErrorKind::MalformedOperation { keyword: "delete" },
        ),
        (
            "invalid/missing-separator.ops",
            ParseErrorKind::MissingSeparator,
        ),
        (
            "invalid/no-newline-not-last.ops",
            ParseErrorKind::NoNewlineNotLast { prefix: '+' },
        ),
        (
            "invalid/no-newline-without-item.ops",
            ParseErrorKind::NoNewlineWithoutItem,
        ),
        ("invalid/no-operations.ops", ParseErrorKind::NoOperations),
        (
            "invalid/operations-out-of-order.ops",
            ParseErrorKind::OperationsOutOfOrder {
                position: 1,
                after: 5,
            },
        ),
        (
            "invalid/overlapping-operations.ops",
            ParseErrorKind::OverlappingOperations { position: 1 },
        ),
        (
            "invalid/unknown-operation.ops",
            ParseErrorKind::UnknownOperation {
                found: "replace 3 1".to_owned(),
            },
        ),
    ]
}

#[test]
fn every_invalid_file_is_refused_for_its_own_reason() {
    for (name, expected) in expected_failures() {
        let error = OperationDocument::parse(&read(name))
            .err()
            .unwrap_or_else(|| panic!("{name} should not parse"));
        assert_eq!(error.kind, expected, "{name} failed for the wrong reason");
    }
}

#[test]
fn the_invalid_directory_is_entirely_covered() {
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
        let error = OperationDocument::parse(&read(name)).expect_err("an invalid file");
        let rendered = error.to_string();
        assert!(
            rendered.starts_with("line "),
            "{name}: {rendered} does not name a line"
        );
        let (_, fix) = rendered
            .split_once(';')
            .unwrap_or_else(|| panic!("{name}: {rendered} does not say what to do"));
        assert!(!fix.trim().is_empty(), "{name}: the fix is empty");
    }
}

/// The file the root revision created, as a list of items.
fn root_state() -> Vec<Item> {
    let root = parse("01-root.ops");
    assert_eq!(root.operations.len(), 1, "a first version is one insert");
    let operation = &root.operations[0];
    assert_eq!(operation.kind, OperationKind::Insert);
    assert_eq!(operation.at, 0, "a file's first version is `insert 0`");
    operation.items.clone()
}

#[test]
fn every_deleted_item_agrees_with_the_parent_it_was_deleted_from() {
    // The redundancy decision 0007 kept on purpose: a `-` line that disagrees
    // with the parent's actual text is corruption caught at the moment of
    // replay rather than absorbed into a merge. Here the parent is the root,
    // so the check is one a person can also do by eye.
    let parent = root_state();
    for name in ["02-concurrent.ops", "03-other.ops", "05-amended.ops"] {
        for operation in &parse(name).operations {
            if operation.kind != OperationKind::Delete {
                continue;
            }
            for (offset, item) in operation.items.iter().enumerate() {
                assert_eq!(
                    Some(item),
                    parent.get(operation.at + offset),
                    "{name} deletes an item the root never held"
                );
            }
        }
    }
}

#[test]
fn the_amendment_edits_the_region_the_revision_it_supersedes_edited() {
    // Revision 05 amends 02, so the two are versions of one change, and their
    // operation documents differ: two revisions that made byte-identical edits
    // would share one document, which would make them one event.
    let original = parse("02-concurrent.ops");
    let amended = parse("05-amended.ops");
    assert_ne!(original, amended);
    assert_ne!(original.id(), amended.id());

    assert_eq!(original.operations[0], amended.operations[0]);
    assert_eq!(original.operations[1].at, amended.operations[1].at);
    assert_ne!(original.operations[1].items, amended.operations[1].items);
}

#[test]
fn concurrent_revisions_edit_the_file_through_separate_operations() {
    // 02 and 03 are the corpus's concurrent pair. Neither can be read as the
    // other's parent state, which is what makes the merge in decision 0007 a
    // replay rather than an application.
    let one = parse("02-concurrent.ops");
    let other = parse("03-other.ops");
    assert_ne!(one.id(), other.id());

    // 03 spells a replacement the canonical way, minus lines above plus lines
    // at one position; 02 anchors its insert past the run it removed.
    assert_eq!(other.operations[0].kind, OperationKind::Delete);
    assert_eq!(other.operations[1].kind, OperationKind::Insert);
    assert_eq!(other.operations[0].at, other.operations[1].at);
    assert_eq!(one.operations[1].at, one.operations[0].end());
}

#[test]
fn an_items_bytes_are_its_own_and_survive_untouched() {
    // A CRLF file's carriage returns are content, and are kept: decision 0002
    // bans a CR from the format's own lines, and a file under version control
    // is not one of them.
    let crlf = parse("crlf.ops");
    for operation in &crlf.operations {
        for item in &operation.items {
            assert!(item.text.ends_with('\r'), "a CRLF line keeps its return");
            assert!(item.bytes().ends_with(b"\r\n"));
        }
    }

    // A last line without a terminator, on both sides of a replacement.
    let ends = parse("no-newline.ops");
    for operation in &ends.operations {
        let last = operation.items.last().expect("an operation has items");
        assert!(!last.terminated);
        assert!(!last.bytes().ends_with(b"\n"));
    }

    // Items that read like the format are items: exactly one byte is stripped
    // and nothing else is trimmed, unescaped, or normalised.
    let verbatim = parse("verbatim-items.ops");
    let items = &verbatim.operations[0].items;
    let texts: Vec<&str> = items.iter().map(|item| item.text.as_str()).collect();
    assert!(texts.contains(&"historica-v0"));
    assert!(texts.contains(&""));
    assert!(texts.contains(&"insert 4"));
    assert!(texts.contains(&"-not a deletion"));
    assert!(texts.iter().any(|text| text.starts_with("\\ no newline")));
    assert!(texts.contains(&"  padded with spaces  "));
    assert!(texts.iter().any(|text| text.contains('\t')));
    assert!(texts.iter().any(|text| text.contains('\u{1f31b}')));
    assert!(
        items.iter().all(|item| item.terminated),
        "no marker, no unterminated item"
    );
}
