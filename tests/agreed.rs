//! A merge whose parents agree because they did the same thing.
//!
//! Decision 0032 lets such a merge state nothing: its file is the state both
//! parents hold. Two devices that apply one edit each record the same
//! operation document, and to the walk those are two concurrent inserts of the
//! same lines. Every revision after the merge counts its positions in the
//! agreed state, so the walk has to read the merge as that state too, or it
//! reads later edits one copy out of place.

use std::collections::BTreeSet;
use std::fs;
use std::path::{Path, PathBuf};

use historica::core::{FileId, RevisionId};
use historica::record::{Clock as _, Platform, Recording, Restriction, record};
use historica::store::Store;
use historica::working::Working;

fn scratch(test: &str) -> PathBuf {
    let path = Path::new(env!("CARGO_TARGET_TMPDIR")).join(test);
    let _ = fs::remove_dir_all(&path);
    fs::create_dir_all(&path).expect("a scratch directory");
    path
}

/// One revision recorded from the folder as it stands.
fn recorded(store: &mut Store, folder: &Path, parents: Vec<RevisionId>) -> RevisionId {
    let mut platform = Platform;
    let working = Working::read(folder, store.skipped()).expect("the folder");
    record(
        store,
        &working,
        &Recording {
            parents,
            author: "Adam Harris <adam@example.com>".to_owned(),
            when: platform.now().expect("a clock"),
            message: String::new(),
            moves: Vec::new(),
            at: Vec::new(),
            accepted: BTreeSet::new(),
            only: Restriction::Everything,
            kinds: Default::default(),
            extensions: Default::default(),
        },
        &mut platform,
    )
    .expect("recording")
    .revision
}

fn notes(store: &Store, at: &RevisionId) -> FileId {
    let tree = store.tree(at).expect("a tree");
    let found = tree.at("notes.md");
    *found.first().expect("notes.md")
}

#[test]
fn the_walk_reads_a_merge_of_the_same_edit_as_the_state_both_sides_hold() {
    let folder = scratch("same-edit-on-two-branches");
    let mut store = Store::init(folder.join("history")).expect("a new store");
    let write = |text: &str| fs::write(folder.join("notes.md"), text).expect("a file");

    write("one\ntwo\nthree\n");
    let root = recorded(&mut store, &folder, Vec::new());
    let file = notes(&store, &root);

    // Two devices, one edit: the same operation document on each side.
    write("one\nsame\nsame again\ntwo\nthree\n");
    let left = recorded(&mut store, &folder, vec![root]);
    let right = recorded(&mut store, &folder, vec![root]);
    assert_ne!(left, right, "two revisions, recorded apart");
    let (left_edit, right_edit) = (
        store.get(&left).expect("readable").expect("left").edited[&file],
        store.get(&right).expect("readable").expect("right").edited[&file],
    );
    assert_eq!(
        left_edit, right_edit,
        "one operation document on both sides"
    );

    // The parents agree, so the merge states nothing about the file.
    let merged = recorded(&mut store, &folder, vec![left, right]);
    assert!(
        !store
            .get(&merged)
            .expect("readable")
            .expect("the merge")
            .edited
            .contains_key(&file),
        "a merge whose parents agree states no resolution"
    );

    // An edit counted in the agreed state: `two` is its fourth line.
    write("one\nsame\nsame again\nthree\n");
    let after = recorded(&mut store, &folder, vec![merged]);
    // And one concurrent with it, from the merge.
    write("one\nsame\nsame again\ntwo\nthree\nfour\n");
    let beside = recorded(&mut store, &folder, vec![merged]);

    let store = Store::open(store.root()).expect("reopened");
    for (name, at) in [("the merge", merged), ("after it", after)] {
        assert_eq!(
            store.merged_content(&at, &file).expect("a walk").state,
            store.content(&at, &file).expect("the rule"),
            "{name}: the walk reads what the rule reads"
        );
    }
    assert_eq!(
        store
            .merged_content_of(&[after, beside], &file)
            .expect("a walk across both")
            .state
            .text(),
        "one\nsame\nsame again\nthree\nfour\n",
    );
}
