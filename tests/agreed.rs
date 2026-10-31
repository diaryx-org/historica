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

/// `check` reads such a merge as the reader does. Its walk has no rule to ask,
/// so the parents agree where the walk through each reads the same text, and
/// a revision after the merge that edits the lines both sides wrote is not
/// read as quoting the wrong copy.
#[test]
fn check_reads_a_merge_of_the_same_edit_as_the_state_both_sides_hold() {
    let folder = scratch("same-edit-checked");
    let mut store = Store::init(folder.join("history")).expect("a new store");
    let write = |text: &str| fs::write(folder.join("notes.md"), text).expect("a file");

    write("a\nb\n");
    let root = recorded(&mut store, &folder, Vec::new());
    write("x\na\nb\n");
    let left = recorded(&mut store, &folder, vec![root]);
    let right = recorded(&mut store, &folder, vec![root]);
    let merged = recorded(&mut store, &folder, vec![left, right]);
    // The child deletes `a`, the second line of the agreed state.
    write("x\nb\n");
    recorded(&mut store, &folder, vec![merged]);

    let report = Store::check(store.root());
    let errors: Vec<String> = report.errors().map(ToString::to_string).collect();
    assert!(
        errors.is_empty(),
        "check calls the store corrupt: {errors:#?}"
    );
}

/// `merge` proposes what `record --merge` will read. Two heads that made the
/// same edit agree, so the file is laid down as that state with nothing
/// contested: a marker drawn there would be recorded as content, since a file
/// the parents agree on is never asked for markers.
#[test]
fn heads_that_made_the_same_edit_propose_nothing_contested() {
    let folder = scratch("same-edit-proposed");
    let mut store = Store::init(folder.join("history")).expect("a new store");
    let write = |text: &str| fs::write(folder.join("notes.md"), text).expect("a file");

    write("a\n");
    let root = recorded(&mut store, &folder, Vec::new());
    let file = notes(&store, &root);
    write("x\na\n");
    let left = recorded(&mut store, &folder, vec![root]);
    let right = recorded(&mut store, &folder, vec![root]);

    let proposed = store
        .proposed_content_of(&[left, right], &file)
        .expect("a proposal");
    assert_eq!(proposed.state.text(), "x\na\n", "the state both heads hold");
    assert!(
        proposed.contested.is_empty(),
        "nothing is left to settle: {:?}",
        proposed.contested
    );
}

/// A contest a recorded merge settled is not proposed again by a later merge
/// that neither side of it touches, while the one the later merge has to
/// settle still is.
#[test]
fn a_contest_an_earlier_merge_settled_is_not_proposed_again() {
    let folder = scratch("settled-not-proposed");
    let mut store = Store::init(folder.join("history")).expect("a new store");
    let write = |name: &str, text: &str| fs::write(folder.join(name), text).expect("a file");

    write("notes.md", "a\n");
    write("other.md", "o\n");
    let root = recorded(&mut store, &folder, Vec::new());
    let file = notes(&store, &root);
    write("notes.md", "x\na\n");
    let left = recorded(&mut store, &folder, vec![root]);
    write("notes.md", "y\na\n");
    let right = recorded(&mut store, &folder, vec![root]);
    write("notes.md", "x\ny\na\n");
    let merged = recorded(&mut store, &folder, vec![left, right]);
    assert!(
        !store
            .merged_content(&merged, &file)
            .expect("a walk")
            .contested
            .is_empty(),
        "the walk still reports where the work met"
    );

    // Two heads that touch only the other file.
    write("other.md", "one\n");
    let one = recorded(&mut store, &folder, vec![merged]);
    write("other.md", "two\n");
    let two = recorded(&mut store, &folder, vec![merged]);
    let other = *store
        .tree(&one)
        .expect("a tree")
        .at("other.md")
        .first()
        .expect("other.md");

    let proposed = store
        .proposed_content_of(&[one, two], &file)
        .expect("a proposal");
    assert!(
        proposed.contested.is_empty(),
        "the earlier merge settled it: {:?}",
        proposed.contested
    );
    assert!(
        !store
            .proposed_content_of(&[one, two], &other)
            .expect("a proposal")
            .contested
            .is_empty(),
        "the file the heads disagree about is still contested"
    );
}

/// The same, where one head has moved the file on since: the heads disagree,
/// so the merge proposes the walk, and still not the contest both heads'
/// pasts already joined.
#[test]
fn a_settled_contest_stays_settled_where_the_heads_disagree() {
    let folder = scratch("settled-heads-disagree");
    let mut store = Store::init(folder.join("history")).expect("a new store");
    let write = |text: &str| fs::write(folder.join("notes.md"), text).expect("a file");

    write("a\n");
    let root = recorded(&mut store, &folder, Vec::new());
    let file = notes(&store, &root);
    write("x\na\n");
    let left = recorded(&mut store, &folder, vec![root]);
    write("y\na\n");
    let right = recorded(&mut store, &folder, vec![root]);
    write("x\ny\na\n");
    let merged = recorded(&mut store, &folder, vec![left, right]);
    write("x\ny\na\nend\n");
    let moved = recorded(&mut store, &folder, vec![merged]);
    // A sibling of `moved` that edits elsewhere in the file.
    write("start\nx\ny\na\n");
    let beside = recorded(&mut store, &folder, vec![merged]);

    let proposed = store
        .proposed_content_of(&[moved, beside], &file)
        .expect("a proposal");
    assert_eq!(proposed.state.text(), "start\nx\ny\na\nend\n");
    assert!(
        proposed.contested.is_empty(),
        "edits in different places, and an old contest settled: {:?}",
        proposed.contested
    );
}
