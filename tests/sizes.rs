//! A file of bytes says how big it is: decision 0083 executed.
//!
//! A copy that holds the history of a photograph without the photograph —
//! fetched with `--no-bytes`, or evicted since — could say which payload a
//! file holds and nothing about it. The `bytes` line's third word is the one
//! fact such a copy most often needs next, and the claim under test is that it
//! is always the size of the bytes the digest beside it names: counted by
//! `record` in the read that took the digest, kept by the tree, restated by a
//! squash, absent rather than guessed for a line written before it, and held
//! to by `check` wherever the bytes are here to count.

use std::collections::BTreeSet;
use std::fs;
use std::path::{Path, PathBuf};

use historica::core::{FileId, RevisionId};
use historica::format::{ParseErrorKind, RevisionDocument};
use historica::record::squash::{Squashing, squash};
use historica::record::{Clock as _, Platform, Recording, Restriction, record};
use historica::store::{Finding, Store};
use historica::tree::Kind;
use historica::working::Working;

const AUTHOR: &str = "Adam Harris <adam@example.com>";

/// A fresh folder for one test, with a store inside it.
fn repository(test: &str) -> (PathBuf, Store) {
    let root = Path::new(env!("CARGO_TARGET_TMPDIR")).join(test);
    let _ = fs::remove_dir_all(&root);
    let base = root.join("repo");
    fs::create_dir_all(&base).expect("a folder");
    let store = Store::init(base.join("history")).expect("a store");
    (base, store)
}

/// Bytes no sniff could take for text, `len` of them.
fn photograph(len: usize) -> Vec<u8> {
    let mut bytes = b"\x89PNG\r\n\x1a\n\0".to_vec();
    while bytes.len() < len {
        bytes.push((bytes.len() % 251) as u8);
    }
    bytes.truncate(len);
    bytes
}

fn recording(parents: Vec<RevisionId>, message: &str) -> Recording {
    Recording {
        parents,
        author: AUTHOR.to_owned(),
        when: Platform.now().expect("a clock"),
        message: message.to_owned(),
        moves: Vec::new(),
        at: Vec::new(),
        accepted: BTreeSet::new(),
        only: Restriction::Everything,
        kinds: Default::default(),
        extensions: Default::default(),
    }
}

fn record_folder(
    base: &Path,
    store: &mut Store,
    parents: Vec<RevisionId>,
    message: &str,
) -> RevisionId {
    let working = Working::read(base, store.skipped()).expect("the folder");
    record(store, &working, &recording(parents, message), &mut Platform)
        .expect("recording")
        .revision
}

/// The one file of bytes a revision's tree holds.
fn the_photo(store: &Store, head: &RevisionId) -> FileId {
    let tree = store.tree(head).expect("the tree");
    let mut wholes = tree
        .entries()
        .filter(|(_, entry)| entry.kind == Kind::Whole)
        .map(|(file, _)| *file);
    let file = wholes.next().expect("a file of bytes");
    assert!(wholes.next().is_none(), "one file of bytes");
    file
}

#[test]
fn a_recorded_photograph_states_its_size_beside_its_digest() {
    let (base, mut store) = repository("sizes-recorded");
    fs::write(base.join("photo.png"), photograph(300_003)).expect("the photograph");
    fs::write(base.join("entry.md"), "# A day\n").expect("the entry");
    let first = record_folder(&base, &mut store, Vec::new(), "Start");

    let document = store.get(&first).expect("readable").expect("held").clone();
    let photo = the_photo(&store, &first);
    assert_eq!(document.sizes.get(&photo), Some(&300_003));
    assert_eq!(
        document.sizes.len(),
        1,
        "a file of lines has no `bytes` line to say a size on"
    );
    let written = String::from_utf8(document.write()).expect("a document is UTF-8");
    let payload = document.bytes.get(&photo).expect("the payload");
    assert!(
        written.contains(&format!("bytes {photo} {payload} 300003\n")),
        "the size is the line's third word: {written}"
    );

    let tree = store.tree(&first).expect("the tree");
    assert_eq!(tree.entry(&photo).expect("the photo").size, Some(300_003));

    // A crop is a new payload, and the line stating it states its size; the
    // tree follows the line rather than keeping the old one.
    fs::write(base.join("photo.png"), photograph(120_000)).expect("the crop");
    let second = record_folder(&base, &mut store, vec![first], "Crop");
    let tree = store.tree(&second).expect("the tree");
    assert_eq!(tree.entry(&photo).expect("the photo").size, Some(120_000));

    assert!(
        Store::check(store.root()).errors().next().is_none(),
        "a store whose sizes are true checks"
    );
}

#[test]
fn a_store_written_before_sizes_reads_as_it_did_and_knows_none() {
    // The corpus `tests/whole.rs` reads was written before decision 0083, so
    // its `bytes` lines are two words long. They still parse, still build a
    // tree, and the tree says it does not know rather than inventing a size.
    let corpus = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/corpus/whole");
    let crop = fs::read(corpus.join("revisions/02-crop.rev.txt")).expect("the revision");
    let document = RevisionDocument::parse(&crop).expect("a two-word `bytes` line reads");
    assert!(!document.bytes.is_empty());
    assert!(document.sizes.is_empty());
    assert_eq!(document.write(), crop, "and writes back byte for byte");
}

#[test]
fn a_squash_restates_the_size_the_tip_states() {
    let (base, mut store) = repository("sizes-squashed");
    fs::write(base.join("entry.md"), "# A day\n").expect("the entry");
    let root = record_folder(&base, &mut store, Vec::new(), "Start");
    fs::write(base.join("photo.png"), photograph(4_000)).expect("a photograph");
    let added = record_folder(&base, &mut store, vec![root], "Add the photo");
    fs::write(base.join("photo.png"), photograph(2_500)).expect("the crop");
    let tip = record_folder(&base, &mut store, vec![added], "Crop it");

    let squashed = squash(
        &mut store,
        &Squashing {
            base: root,
            tip,
            message: None,
            reviser: AUTHOR.to_owned(),
            revised: Platform.now().expect("a clock"),
        },
        &mut Platform,
    )
    .expect("squashing");

    let photo = the_photo(&store, &squashed.revision);
    let document = store
        .get(&squashed.revision)
        .expect("readable")
        .expect("held");
    assert_eq!(document.sizes.get(&photo), Some(&2_500));
    let tree = store.tree(&squashed.revision).expect("the tree");
    assert_eq!(tree.entry(&photo).expect("the photo").size, Some(2_500));
}

#[test]
fn check_refuses_a_size_the_bytes_do_not_have() {
    let (base, mut store) = repository("sizes-lying");
    fs::write(base.join("photo.png"), photograph(5_000)).expect("the photograph");
    let first = record_folder(&base, &mut store, Vec::new(), "Start");
    let photo = the_photo(&store, &first);

    // The same revision with its photograph's size misstated: a document
    // somebody edited by hand, or a writer with a bug.
    let mut lying = store.get(&first).expect("readable").expect("held").clone();
    lying.sizes.insert(photo, 5_001);
    lying.message = "Start, misremembered".to_owned();
    let lying = store.insert(&lying).expect("filing it");

    let report = Store::check(store.root());
    let errors: Vec<&Finding> = report.errors().collect();
    assert!(
        errors.iter().any(|finding| matches!(
            finding,
            Finding::SizeLies { named_by, stated: 5_001, actual: 5_000, .. } if *named_by == lying
        )),
        "the misstated size is an error: {errors:?}"
    );
    assert!(
        !errors.iter().any(|finding| matches!(
            finding,
            Finding::SizeLies { named_by, .. } if *named_by == first
        )),
        "and the true one is not"
    );
}

#[test]
fn a_size_is_spelled_one_way() {
    let photo = "swtlmnkqvzyrxopwstlnmkqv";
    let payload = "1e4e224e93380a25d4cd1be85d35db37f4064be4388822eba250894c6d6daa0d";
    let document = |line: &str| {
        format!(
            "historica\nchange qpvuntsmwlrkzxonmvtplsyq\n\
             author {AUTHOR}\nwhen 2025-08-19T00:47:11-06:00\n\
             move {photo} photo.png\n{line}\n\nm"
        )
    };

    for size in ["0", "7", "18446744073709551615"] {
        let bytes = document(&format!("bytes {photo} {payload} {size}"));
        let parsed = RevisionDocument::parse(bytes.as_bytes()).expect("a size");
        assert_eq!(
            parsed.sizes.values().next().map(u64::to_string).as_deref(),
            Some(size)
        );
        assert_eq!(parsed.write(), bytes.as_bytes(), "{size} writes as it read");
    }

    // Anything `write` would spell differently is not a size, since a reader
    // and a writer disagreeing about a line's bytes disagree about the
    // revision's identity.
    for size in [
        "007",
        "+7",
        "-7",
        "7.0",
        "7 7",
        "seven",
        "18446744073709551616",
    ] {
        let bytes = document(&format!("bytes {photo} {payload} {size}"));
        let refused = RevisionDocument::parse(bytes.as_bytes()).expect_err(size);
        assert!(
            matches!(
                &refused.kind,
                ParseErrorKind::MalformedSize { .. } | ParseErrorKind::MalformedDigest { .. }
            ),
            "`{size}`: {refused}"
        );
    }

    // Only `bytes` has a size: on `edit` a third word is what it always was.
    let edit = document(&format!("edit {photo} {payload} 7"));
    let refused = RevisionDocument::parse(edit.as_bytes()).expect_err("an edit has no size");
    assert!(
        matches!(&refused.kind, ParseErrorKind::MalformedDigest { .. }),
        "{refused}"
    );
}
