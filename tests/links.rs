//! A file can be a link: decision 0040 executed.
//!
//! `tests/corpus/links/` is four revisions of one journal. It starts with a
//! month, a link to that month, and a link to a machine — the two spellings
//! side by side, chosen by resolution rather than by preference. A second
//! revision retargets the first link and nothing else. A third renames the
//! file the link points at, states no `link` line at all, and claims version
//! 1: that is the whole of the decision, since a reference is to the identity
//! and the identity did not move. A fourth drops the target and restates the
//! link as the string the folder holds, which is what keeps a `file:` link
//! from ever naming a file the tree does not have.
//!
//! Eight invalid documents pin the rest: five the parser refuses and three the
//! tree does, because a link is the one thing here whose truth a fact about a
//! *different* file can undo.

use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};

use historica::core::{FileId, RevisionId};
use historica::format::{LinkTarget, ParseErrorKind, RevisionDocument, Version, digest};
use historica::store::Store;
use historica::tree::{Kind, Tree, TreeError};

/// The journal's files, as the corpus names them.
const JULY: &str = "nrqvtkzlmwyxsptonvqrklmz";
const AUGUST: &str = "swtlmnkqvzyrxopwstlnmkqv";
const CURRENT: &str = "lqxstvnmpkwyzrolvtsqnkxm";
const CONFIG: &str = "ptkwnrvzlmyxqsotnkwlpvzr";

fn corpus() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/corpus/links")
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

fn file(id: &str) -> FileId {
    id.parse().expect("a file ID")
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
    fs::write(root.join("historica.txt"), "historica-v5\n").expect("the version this corpus is");
    Store::open(&root).expect("the corpus opens")
}

/// The tree the corpus's revisions leave, up to and including `through`.
fn replayed(through: usize) -> Tree {
    let names = [
        "revisions/01-start.rev.txt",
        "revisions/02-august.rev.txt",
        "revisions/03-renamed.rev.txt",
        "revisions/04-gone.rev.txt",
    ];
    let documents: Vec<RevisionDocument> = names[..through].iter().copied().map(parsed).collect();
    historica::tree::replay(&documents).expect("a chain the tree accepts")
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
/// that renames the link's target — which states no `link` line, because there
/// was nothing to restate — is still version 1.
#[test]
fn only_a_document_with_a_link_in_it_claims_version_five() {
    assert_eq!(parsed("revisions/01-start.rev.txt").version, Version::V5);
    assert_eq!(parsed("revisions/02-august.rev.txt").version, Version::V5);
    assert_eq!(parsed("revisions/03-renamed.rev.txt").version, Version::V1);
    assert_eq!(parsed("revisions/04-gone.rev.txt").version, Version::V5);
}

/// The two spellings, chosen by resolution: a target this history holds is
/// recorded as that file, and everything else as the string a person wrote.
#[test]
fn a_target_inside_is_a_file_and_a_target_outside_is_a_string() {
    let tree = replayed(1);
    assert_eq!(tree.kind(&file(CURRENT)), Some(Kind::Link));
    assert_eq!(tree.kind(&file(CONFIG)), Some(Kind::Link));
    assert_eq!(tree.kind(&file(JULY)), Some(Kind::Lines));

    assert_eq!(
        tree.target(&file(CURRENT)),
        Some(&LinkTarget::Reference(file(JULY)))
    );
    assert_eq!(
        tree.target(&file(CONFIG)),
        Some(&LinkTarget::Verbatim("/etc/journal".to_owned()))
    );
}

/// The case every path-spelled symlink gets wrong, gone by construction. The
/// revision that renames the target says nothing about the link, and the link
/// still points at the file.
#[test]
fn a_reference_survives_the_rename_of_what_it_points_at() {
    let renamed = parsed("revisions/03-renamed.rev.txt");
    assert!(
        renamed.links.is_empty(),
        "a rename of the target is not a fact about the link"
    );

    let before = replayed(2);
    let after = replayed(3);
    assert_eq!(before.path(&file(AUGUST)), Some("2026/august.md"));
    assert_eq!(after.path(&file(AUGUST)), Some("2026/08.md"));
    assert_eq!(
        after.target(&file(CURRENT)),
        before.target(&file(CURRENT)),
        "the reference is to the identity, and the identity did not move"
    );

    // And what a folder would be given follows it, which is the point.
    assert_eq!(
        historica::update::materialise(
            &after,
            "current",
            after.target(&file(CURRENT)).expect("a link"),
        ),
        Some("2026/08.md".to_owned())
    );
}

/// A `file:` target is materialised relative to the link's own directory, so a
/// link deeper in the folder gets a target it can actually follow.
#[test]
fn a_reference_is_spelled_from_the_link_and_not_from_the_root() {
    let tree = replayed(2);
    let target = tree.target(&file(CURRENT)).expect("a link");
    assert_eq!(
        historica::update::materialise(&tree, "2026/latest.md", target),
        Some("august.md".to_owned())
    );
    assert_eq!(
        historica::update::materialise(&tree, "notes/deep/latest.md", target),
        Some("../../2026/august.md".to_owned())
    );
}

/// The revision that takes the target out restates the link as the string the
/// folder holds — which is the dangling link a person actually has, recorded
/// as the dangling string it actually is.
#[test]
fn dropping_a_target_restates_the_link_verbatim_in_the_same_revision() {
    let gone = parsed("revisions/04-gone.rev.txt");
    assert!(gone.dropped.contains(&file(AUGUST)));
    assert_eq!(
        gone.links.get(&file(CURRENT)),
        Some(&LinkTarget::Verbatim("2026/08.md".to_owned())),
        "the spelling the folder held at that moment"
    );

    let tree = replayed(4);
    assert!(tree.entry(&file(AUGUST)).is_none());
    assert_eq!(
        tree.target(&file(CURRENT)),
        Some(&LinkTarget::Verbatim("2026/08.md".to_owned()))
    );
}

/// A link has no bytes, and inventing some would be a rendering standing where
/// a file's content goes.
#[test]
fn a_link_has_no_content_to_materialise() {
    let store = store("links-content");
    let head = digest(&read("revisions/02-august.rev.txt"));
    let refused = store
        .content_at(&head, &file(CURRENT))
        .expect_err("a link holds no content");
    assert!(
        refused.to_string().contains("is a link to"),
        "{refused}: the refusal says where it points"
    );

    // The file it points at is ordinary, and reads as itself.
    assert!(
        store
            .content_at(&head, &file(AUGUST))
            .expect("the month")
            .bytes()
            .starts_with(b"# August")
    );
}

/// Each invalid file the parser refuses is refused for its own stated reason.
#[test]
fn every_invalid_document_is_refused_for_its_own_reason() {
    let parsing: Vec<(&str, ParseErrorKind)> = vec![
        (
            "invalid/link-in-version-4.rev.txt",
            ParseErrorKind::HeaderNeedsVersion {
                key: "link".to_owned(),
                found: Version::V4,
                needs: Version::V5,
            },
        ),
        (
            "invalid/malformed-file-reference.rev.txt",
            ParseErrorKind::MalformedFileId {
                found: "august".to_owned(),
            },
        ),
        (
            "invalid/link-stated-twice.rev.txt",
            ParseErrorKind::FileStatedTwice {
                key: "link",
                file: CURRENT.to_owned(),
            },
        ),
        (
            "invalid/drop-and-link.rev.txt",
            ParseErrorKind::ContradictoryFileFacts {
                first: "drop",
                second: "link",
                file: CURRENT.to_owned(),
            },
        ),
        (
            "invalid/link-and-text.rev.txt",
            ParseErrorKind::ContradictoryFileFacts {
                first: "link",
                second: "text",
                file: CURRENT.to_owned(),
            },
        ),
    ];
    // The three the tree refuses instead: each parses, because a document
    // cannot see the tree it will be applied to.
    let applying: Vec<(&str, TreeError)> = vec![
        (
            "invalid/edit-a-link.rev.txt",
            TreeError::WrongKind {
                key: "edit",
                file: file(CURRENT),
                kind: Kind::Link,
            },
        ),
        (
            "invalid/link-a-plain-file.rev.txt",
            TreeError::WrongKind {
                key: "link",
                file: file(JULY),
                kind: Kind::Lines,
            },
        ),
        (
            "invalid/drop-a-referenced-file.rev.txt",
            TreeError::Dangling {
                link: file(CURRENT),
                target: file(AUGUST),
            },
        ),
    ];

    // Every invalid file in the corpus is accounted for, so one added without
    // a reason beside it fails here rather than sitting unchecked.
    let named: Vec<&str> = parsing
        .iter()
        .map(|(name, _)| *name)
        .chain(applying.iter().map(|(name, _)| *name))
        .collect();
    for name in manifest().into_keys() {
        if name.starts_with("invalid/") {
            assert!(
                named.contains(&name.as_str()),
                "{name} has no stated reason"
            );
        }
    }

    for (name, kind) in parsing {
        let error = RevisionDocument::parse(&read(name))
            .map(|document| document.write())
            .expect_err(&format!("{name} should not parse"));
        assert_eq!(error.kind, kind, "{name} failed for the wrong reason");
        // Decision 0004: a refusal names the line and says what to do.
        assert!(error.line > 0, "{name} named no line");
        assert!(!error.kind.to_string().is_empty(), "{name} said nothing");
    }

    let tree = replayed(2);
    for (name, expected) in applying {
        let error = tree
            .apply(&parsed(name))
            .expect_err(&format!("{name} should not apply"));
        assert_eq!(error, expected, "{name} failed for the wrong reason");
        assert!(!error.to_string().is_empty(), "{name} said nothing");
    }
}
