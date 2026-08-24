//! A history of more than one file, with a rename in it.
//!
//! `tests/corpus/tree/` is four revisions and four operation documents: a
//! journal started with two files, an entry extended, the README filed under
//! `docs/` in the same revision that edits it, and the entry withdrawn. It is
//! the first corpus where the revisions and the operation documents describe
//! one history together rather than two halves that only narrate the same one.
//!
//! The claim it exists to check is decision 0008's: a path is a fact about a
//! file, so renaming one keeps everything recorded against it.

use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};

use historica::core::{FileId, RevisionId};
use historica::format::{OperationDocument, RevisionDocument, digest};
use historica::replay::{State, creation, replay as replay_content};
use historica::tree::{Tree, operations_for, replay as replay_tree};

/// The journal entry, and the README, as the corpus names them.
const ENTRY: &str = "nrqvtkzlmwyxsptonvqrklmz";
const README: &str = "swtlmnkqvzyrxopwstlnmkqv";

fn corpus() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/corpus/tree")
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

fn file(id: &str) -> FileId {
    id.parse().expect("a file ID")
}

/// The four revisions, oldest first, which is the order their names give and
/// the order their parents confirm.
fn history() -> Vec<RevisionDocument> {
    let mut names: Vec<String> = manifest()
        .into_keys()
        .filter(|name| name.starts_with("revisions/"))
        .collect();
    names.sort();
    names
        .iter()
        .map(|name| {
            RevisionDocument::parse(&read(name)).unwrap_or_else(|error| panic!("{name}: {error}"))
        })
        .collect()
}

/// Every operation document in the corpus, by digest.
///
/// Keyed by content and never by name, which is decision 0003's rule arriving
/// where it was always headed: the `edit` lines name digests, so the file names
/// here are presentation and nothing reads them. Only `.ops.txt` files carry
/// the grammar; everything else under `operations/` is a payload, the file
/// itself.
fn documents() -> BTreeMap<RevisionId, OperationDocument> {
    manifest()
        .into_keys()
        .filter(|name| name.starts_with("operations/") && name.ends_with(".ops.txt"))
        .map(|name| {
            let bytes = read(&name);
            let document =
                OperationDocument::parse(&bytes).unwrap_or_else(|error| panic!("{name}: {error}"));
            (digest(&bytes), document)
        })
        .collect()
}

/// The payloads in the corpus, by digest, read as text.
fn payloads() -> BTreeMap<RevisionId, String> {
    manifest()
        .into_keys()
        .filter(|name| name.starts_with("operations/") && !name.ends_with(".ops.txt"))
        .map(|name| {
            let bytes = read(&name);
            (
                digest(&bytes),
                String::from_utf8(bytes).expect("a text payload"),
            )
        })
        .collect()
}

/// Materialise one file at the end of a chain of revisions.
///
/// The creation arrives as a payload (decision 0017), which is exactly the
/// operation document that inserts every line at 0; the edits follow it.
fn content(revisions: &[RevisionDocument], file: &FileId) -> State {
    let payloads = payloads();
    let created: Option<OperationDocument> = revisions
        .iter()
        .find_map(|revision| revision.text.get(file))
        .map(|payload| creation(&payloads[payload]).expect("a payload with content"));
    let documents = documents();
    let chain: Vec<&OperationDocument> = created
        .iter()
        .chain(operations_for(revisions, file).iter().map(|id| {
            documents
                .get(id)
                .unwrap_or_else(|| panic!("the store holds {id}"))
        }))
        .collect();
    replay_content(chain).expect("a linear chain")
}

#[test]
fn the_manifest_describes_the_corpus_on_disk() {
    for (name, expected) in manifest() {
        assert_eq!(digest(&read(&name)), expected, "{name} has drifted");
    }
}

#[test]
fn the_corpus_is_one_chain_and_every_reference_in_it_resolves() {
    let history = history();
    let documents = documents();

    let mut previous: Option<RevisionId> = None;
    for revision in &history {
        match previous {
            None => assert!(revision.parents.is_empty(), "the first revision is a root"),
            Some(parent) => {
                assert_eq!(
                    revision.parents.iter().copied().collect::<Vec<_>>(),
                    vec![parent],
                    "each revision names the one before it"
                );
            }
        }
        for document in revision.edited.values() {
            assert!(
                documents.contains_key(document),
                "{document} is in the store"
            );
        }
        for payload in revision.text.values() {
            assert!(
                payloads().contains_key(payload),
                "{payload} is in the store"
            );
        }
        previous = Some(revision.id());
    }
}

#[test]
fn the_tree_is_replayed_from_what_each_revision_did_to_it() {
    let history = history();

    let started = replay_tree(&history[..1]).expect("the root");
    assert_eq!(started.len(), 2);
    assert_eq!(started.path(&file(ENTRY)), Some("notes/2025-08-19.md"));
    assert_eq!(started.path(&file(README)), Some("README.md"));

    // The second revision only edits, so the file set is untouched.
    assert_eq!(replay_tree(&history[..2]).expect("an edit"), started);

    let moved = replay_tree(&history[..3]).expect("a move");
    assert_eq!(moved.path(&file(README)), Some("docs/README.md"));
    assert!(moved.at("README.md").is_empty());
    assert_eq!(moved.at("docs/README.md"), vec![file(README)]);

    let dropped = replay_tree(&history).expect("a drop");
    assert_eq!(dropped.len(), 1);
    assert_eq!(dropped.path(&file(ENTRY)), None);
    assert_eq!(
        dropped.files().collect::<Vec<_>>(),
        vec![(&file(README), "docs/README.md")]
    );
}

#[test]
fn a_rename_keeps_everything_recorded_against_the_file() {
    // Decision 0008's reason for identifying files at all. The README is
    // edited in the same revision that moves it, and its content is the sum of
    // both of its operation documents — the one recorded when it was
    // `README.md` and the one recorded as it became `docs/README.md`.
    let history = history();
    assert_eq!(operations_for(&history, &file(README)).len(), 1);
    assert_eq!(
        content(&history, &file(README)).text(),
        "# Notes\n\nA journal kept in Historica, and the notes that came with it.\n"
    );

    // Nothing about the move appears in the operation documents themselves:
    // they describe lines, and the path is the tree's business.
    let documents = documents();
    for document in documents.values() {
        let written = String::from_utf8(document.write()).expect("UTF-8");
        assert!(!written.contains("README.md"), "a path leaked into content");
    }
}

#[test]
fn a_dropped_file_loses_its_path_and_keeps_its_history() {
    let history = history();

    // At the revision before the drop, the entry is both present and readable.
    let before = &history[..3];
    assert_eq!(
        replay_tree(before).expect("before").path(&file(ENTRY)),
        Some("notes/2025-08-19.md")
    );
    assert_eq!(
        content(before, &file(ENTRY)).text(),
        "# 2025-08-19\n\n\
         Wrote the tree decision. Files are identified; paths hang off them.\n\
         Renaming a file must not lose what was recorded against it.\n"
    );

    // After it, the file is gone from the tree and its operations are still
    // in the store: dropping a file removes it from the file set, and history
    // is not a place things are removed from.
    let after = replay_tree(&history).expect("after");
    assert!(after.path(&file(ENTRY)).is_none());
    assert_eq!(operations_for(&history, &file(ENTRY)).len(), 1);
    assert_eq!(content(&history, &file(ENTRY)).len(), 4);
}

#[test]
fn every_revision_replays_against_the_tree_it_was_recorded_from() {
    // The check decision 0008 unblocks: the tree says which operation document
    // belongs to which file, so every `-` line can be held to the parent it
    // claims to have edited.
    let history = history();
    let documents = documents();

    let payloads = payloads();
    let mut tree = Tree::empty();
    let mut states: BTreeMap<FileId, State> = BTreeMap::new();
    for revision in &history {
        tree = tree
            .apply(revision)
            .unwrap_or_else(|error| panic!("{}: {error}", revision.id()));
        for (file, payload) in &revision.text {
            states.insert(*file, State::from_text(&payloads[payload]));
        }
        for (file, id) in &revision.edited {
            let document = &documents[id];
            let state = states.entry(*file).or_insert_with(State::empty);
            *state = state
                .apply(document)
                .unwrap_or_else(|error| panic!("{}: {error}", revision.id()));
        }
    }

    assert_eq!(tree.len(), 1);
    assert_eq!(states.len(), 2, "both files were materialised on the way");
}
