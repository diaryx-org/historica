//! What the recorder writes down, held to hand-written examples.
//!
//! `tests/corpus/diffs/` has one directory per case: the file before, the file
//! after, and the operation document this tool records for that pair. The
//! property test in `src/diff.rs` already proves the round trip for thousands
//! of random pairs, which is the part a person cannot check by reading. These
//! are the choices it cannot see — where a replacement anchors, what happens to
//! a final newline, and what survives an edit that replaced the text around it.

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Path, PathBuf};

use historica::core::RevisionId;
use historica::diff::diff;
use historica::format::{OperationDocument, digest};
use historica::replay::State;

fn corpus() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/corpus/diffs")
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

fn text(name: &str) -> String {
    String::from_utf8(read(name)).expect("a corpus file is UTF-8")
}

/// Every case directory named by the manifest.
fn cases() -> BTreeSet<String> {
    manifest()
        .into_keys()
        .map(|name| {
            name.split_once('/')
                .expect("`<case>/<file>` per line")
                .0
                .to_owned()
        })
        .collect()
}

#[test]
fn the_manifest_describes_the_corpus_on_disk() {
    for (name, expected) in manifest() {
        assert_eq!(digest(&read(&name)), expected, "{name} has drifted");
    }
}

#[test]
fn every_case_holds_a_before_an_after_and_a_recording() {
    // A case missing its recording would silently test nothing.
    let listed = manifest().into_keys().collect::<BTreeSet<_>>();
    for case in cases() {
        for file in ["parent.txt", "child.txt", "recorded.ops"] {
            assert!(listed.contains(&format!("{case}/{file}")), "{case}/{file}");
        }
    }
    assert_eq!(
        listed.len(),
        cases().len() * 3,
        "an unlisted file is present"
    );
}

#[test]
fn each_case_records_the_document_it_says_it_does() {
    for case in cases() {
        let parent = State::from_text(&text(&format!("{case}/parent.txt")));
        let child = State::from_text(&text(&format!("{case}/child.txt")));
        let recorded = diff(&parent, &child).unwrap_or_else(|| panic!("{case} changes nothing"));
        assert_eq!(
            String::from_utf8(recorded.write()).expect("UTF-8"),
            text(&format!("{case}/recorded.ops")),
            "{case} is recorded differently now"
        );
    }
}

#[test]
fn every_recording_parses_and_replays_to_the_file_it_came_from() {
    for case in cases() {
        let parent = State::from_text(&text(&format!("{case}/parent.txt")));
        let child = State::from_text(&text(&format!("{case}/child.txt")));
        let document = OperationDocument::parse(&read(&format!("{case}/recorded.ops")))
            .unwrap_or_else(|error| panic!("{case}: {error}"));
        assert_eq!(
            parent
                .apply(&document)
                .unwrap_or_else(|error| panic!("{case}: {error}"))
                .text(),
            child.text(),
            "{case}"
        );
    }
}

#[test]
fn a_replacement_is_anchored_at_the_removed_runs_start() {
    // Decision 0009 settling what 0007 spelled two ways, in the one place the
    // two spellings are both on disk. The operations corpus holds 0007's
    // example, which anchors past the removed run; this tool anchors at its
    // start. Both parse, both replay to the same file, and they are different
    // documents with different digests.
    let operations = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/corpus/operations");
    let decisions_example = OperationDocument::parse(
        &fs::read(operations.join("02-concurrent.ops")).expect("the operations corpus"),
    )
    .expect("a canonical file");

    let recorded = OperationDocument::parse(&read("replacement-anchor/recorded.ops"))
        .expect("a recorded document");

    // The corpus case and the operations corpus describe one edit.
    let parent = State::from_text(&text("replacement-anchor/parent.txt"));
    let child = State::from_text(&text("replacement-anchor/child.txt"));
    assert_eq!(
        parent
            .apply(&decisions_example)
            .expect("0007's example")
            .text(),
        child.text()
    );

    assert_ne!(recorded, decisions_example);
    assert_ne!(recorded.id(), decisions_example.id());

    let inserts = |document: &OperationDocument| -> Vec<usize> {
        document
            .operations
            .iter()
            .filter(|operation| operation.kind == historica::format::OperationKind::Insert)
            .map(|operation| operation.at)
            .collect()
    };
    assert_eq!(
        inserts(&recorded),
        vec![3],
        "this tool anchors at the start"
    );
    assert_eq!(
        inserts(&decisions_example),
        vec![4],
        "0007's example anchors past the removed run, and still parses"
    );
}

#[test]
fn a_final_newline_is_recorded_as_a_rewrite_of_the_last_line() {
    // No special case exists for terminators: the item carries its own, so a
    // file that gains or loses one differs in that item like any other change.
    let gained = text("final-newline-gained/recorded.ops");
    let lost = text("final-newline-lost/recorded.ops");
    assert!(
        gained.contains("-An experiment in readable, convergent version control.\n\\ no newline\n")
    );
    assert!(
        lost.contains("+An experiment in readable, convergent version control.\n\\ no newline\n")
    );
    assert_ne!(gained, lost);
}

#[test]
fn a_line_between_two_rewritten_paragraphs_survives_them() {
    // A known cost of decision 0007's line granularity, on disk so that it
    // stays known: the blank line is the best anchor in either file, so every
    // matcher keeps it, and it remains an item a concurrent edit can name.
    let recorded = OperationDocument::parse(&read("surviving-line/recorded.ops"))
        .expect("a recorded document");
    let touched: Vec<usize> = recorded
        .operations
        .iter()
        .map(|operation| operation.at)
        .collect();
    assert_eq!(touched, vec![0, 0, 2, 2], "the line at 1 is untouched");
}
