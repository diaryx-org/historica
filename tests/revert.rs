//! Undoing one revision through the library, as a host does: decision 0090.
//!
//! The command line is one caller of [`historica::revert::plan`]; a host
//! keeping its own folder is another, and what it needs is the same three
//! steps the command takes — plan, apply, record — with nothing decided in
//! between. These tests take them by hand.

use std::collections::BTreeSet;
use std::fs;
use std::path::{Path, PathBuf};

use historica::core::RevisionId;
use historica::record::{Clock as _, Fact, Platform, Recording, Restriction, record};
use historica::revert::{RevertError, plan};
use historica::store::Store;
use historica::update;
use historica::working::Working;

fn folder(test: &str) -> (PathBuf, Store) {
    let root = Path::new(env!("CARGO_TARGET_TMPDIR")).join(format!("revert-{test}"));
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).expect("a folder");
    let store = Store::init(root.join("history")).expect("a store");
    (root, store)
}

fn recording(parents: Vec<RevisionId>, message: &str, only: Restriction) -> Recording {
    Recording {
        parents,
        author: "Adam Harris <adam@example.com>".to_owned(),
        when: Platform.now().expect("a clock"),
        message: message.to_owned(),
        moves: Vec::new(),
        at: Vec::new(),
        accepted: BTreeSet::new(),
        only,
        kinds: Default::default(),
        extensions: Default::default(),
    }
}

fn recorded(store: &mut Store, root: &Path, parents: Vec<RevisionId>, message: &str) -> RevisionId {
    let working = Working::read(root, store.skipped()).expect("the folder");
    record(
        store,
        &working,
        &recording(parents, message, Restriction::Everything),
        &mut Platform,
    )
    .expect("recording")
    .revision
}

/// Plan, apply, record: the host's whole part, and the history it leaves.
#[test]
fn a_host_undoes_a_revision_in_three_steps() {
    let (root, mut store) = folder("host");
    fs::write(root.join("page.md"), "# Page\n\nWritten by a person.\n").expect("a file");
    let first = recorded(&mut store, &root, Vec::new(), "A page");

    fs::write(
        root.join("page.md"),
        "# Page\n\nWritten by a person.\n\nA paragraph nobody asked for.\n",
    )
    .expect("a file");
    fs::write(root.join("aside.md"), "An aside.\n").expect("a file");
    let mistake = recorded(&mut store, &root, vec![first], "Accept a change set");

    fs::write(
        root.join("page.md"),
        "# Page, retitled\n\nWritten by a person.\n\nA paragraph nobody asked for.\n",
    )
    .expect("a file");
    let head = recorded(&mut store, &root, vec![mistake], "Retitle");

    let working = Working::read(&root, store.skipped()).expect("the folder");
    let reversal = plan(&store, &working, &mistake, &head).expect("a plan");
    assert_eq!(reversal.target, mistake);
    assert_eq!(reversal.head, head);
    assert_eq!(
        reversal.facts,
        [
            (Fact::Dropped, "aside.md".to_owned()),
            (Fact::Edited, "page.md".to_owned())
        ]
    );
    assert_eq!(reversal.paths, ["aside.md", "page.md"]);
    assert!(reversal.moves.is_empty());

    let applied = update::apply(&store, &working, &root, &reversal.update).expect("applying");
    assert_eq!(applied.wrote, ["page.md"]);
    assert_eq!(applied.removed, ["aside.md"]);
    assert_eq!(
        fs::read_to_string(root.join("page.md")).expect("the page"),
        "# Page, retitled\n\nWritten by a person.\n",
        "the retitle stays and the paragraph goes"
    );

    let working = Working::read(&root, store.skipped()).expect("the folder");
    let only = Restriction::Paths(reversal.paths.iter().cloned().collect());
    let undone = record(
        &mut store,
        &working,
        &recording(vec![head], "Undo the change set", only),
        &mut Platform,
    )
    .expect("recording the undoing");
    assert_eq!(
        undone.plan.facts(),
        reversal.facts,
        "what was planned is what is stated"
    );

    // Undone once, there is nothing left of it to undo.
    let working = Working::read(&root, store.skipped()).expect("the folder");
    let again = plan(&store, &working, &mistake, &undone.revision).expect("a plan");
    assert!(again.is_settled(), "{again:?}");
    let _ = fs::remove_dir_all(&root);
}

/// A file of bytes goes back to the payload its parent held, where nothing
/// since replaced it, and is refused where something did.
#[test]
fn a_file_of_bytes_goes_back_whole_or_not_at_all() {
    let (root, mut store) = folder("bytes");
    fs::write(root.join("photo.png"), b"\x89PNG\r\n\x1a\nfirst").expect("a file");
    let first = recorded(&mut store, &root, Vec::new(), "A photograph");
    fs::write(root.join("photo.png"), b"\x89PNG\r\n\x1a\nsecond").expect("a file");
    let mistake = recorded(&mut store, &root, vec![first], "The wrong photograph");
    fs::write(root.join("note.md"), "note\n").expect("a file");
    let head = recorded(&mut store, &root, vec![mistake], "A note");

    let working = Working::read(&root, store.skipped()).expect("the folder");
    let reversal = plan(&store, &working, &mistake, &head).expect("a plan");
    update::apply(&store, &working, &root, &reversal.update).expect("applying");
    assert_eq!(
        fs::read(root.join("photo.png")).expect("the photograph"),
        b"\x89PNG\r\n\x1a\nfirst"
    );

    // Replaced again since: there is no line in a photograph to undo one
    // change by, so which one stays is a person's to say.
    fs::write(root.join("photo.png"), b"\x89PNG\r\n\x1a\nthird").expect("a file");
    let later = recorded(&mut store, &root, vec![head], "Another photograph");
    let working = Working::read(&root, store.skipped()).expect("the folder");
    match plan(&store, &working, &mistake, &later) {
        Err(RevertError::Refused { paths }) => {
            assert_eq!(paths.len(), 1, "{paths:?}");
            assert_eq!(paths[0].0, "photo.png");
        }
        other => panic!("a refusal naming the photograph, not {other:?}"),
    }
    let _ = fs::remove_dir_all(&root);
}

/// Only work behind the head can be undone on it.
#[test]
fn a_revision_the_head_does_not_stand_on_is_refused() {
    let (root, mut store) = folder("not-behind");
    fs::write(root.join("a.md"), "a\n").expect("a file");
    let first = recorded(&mut store, &root, Vec::new(), "First");
    fs::write(root.join("a.md"), "b\n").expect("a file");
    let second = recorded(&mut store, &root, vec![first], "Second");

    let working = Working::read(&root, store.skipped()).expect("the folder");
    assert!(matches!(
        plan(&store, &working, &second, &first),
        Err(RevertError::NotBehind { .. })
    ));
    let _ = fs::remove_dir_all(&root);
}

/// What a host records once the folder holds the undoing: the reversal's own
/// paths, renames and kinds, as `historica record` would be told them.
fn record_reversal(
    store: &mut Store,
    root: &Path,
    reversal: &historica::revert::Reversal,
    message: &str,
) -> historica::record::Recorded {
    let working = Working::read(root, store.skipped()).expect("the folder");
    let mut asked = recording(
        vec![reversal.head],
        message,
        Restriction::Paths(reversal.paths.iter().cloned().collect()),
    );
    asked.moves = reversal.moves.clone();
    asked.kinds = reversal.kinds.clone();
    record(store, &working, &asked, &mut Platform).expect("recording the undoing")
}

/// A file deleted by mistake comes back as the kind the history decided, not
/// as whatever its bytes sniff as now.
#[test]
fn a_restored_file_keeps_the_kind_it_was_recorded_as() {
    use historica::record::Kinds;
    use historica::tree::Kind;

    let (root, mut store) = folder("kind");
    fs::write(root.join("f"), "plain text\n").expect("a file");
    let working = Working::read(&root, store.skipped()).expect("the folder");
    let mut first = recording(Vec::new(), "Bytes, said so", Restriction::Everything);
    let mut kinds = Kinds::default();
    kinds.state("f", Kind::Whole);
    first.kinds = kinds;
    let first = record(&mut store, &working, &first, &mut Platform)
        .expect("recording")
        .revision;
    fs::remove_file(root.join("f")).expect("a delete");
    let deletion = recorded(&mut store, &root, vec![first], "Delete it");

    let working = Working::read(&root, store.skipped()).expect("the folder");
    let reversal = plan(&store, &working, &deletion, &deletion).expect("a plan");
    assert_eq!(reversal.kinds.stated("f"), Some(Kind::Whole));
    update::apply(&store, &working, &root, &reversal.update).expect("applying");
    let undone = record_reversal(&mut store, &root, &reversal, "Undo the delete");

    let tree = store.tree(&undone.revision).expect("the tree");
    let (file, _) = tree.files().next().expect("the file");
    assert_eq!(tree.kind(file), Some(Kind::Whole), "bytes, as it was");
    let _ = fs::remove_dir_all(&root);
}

/// An executable bit nobody recorded is unrecorded work: the plan refuses
/// the path rather than handing `apply` a write that would reset it.
#[cfg(unix)]
#[test]
fn an_unrecorded_mode_is_refused() {
    use std::os::unix::fs::PermissionsExt;

    let (root, mut store) = folder("dirty-mode");
    fs::write(root.join("f"), "a\n").expect("a file");
    let first = recorded(&mut store, &root, Vec::new(), "Start");
    fs::write(root.join("f"), "b\n").expect("a file");
    let edit = recorded(&mut store, &root, vec![first], "Edit");
    fs::set_permissions(root.join("f"), fs::Permissions::from_mode(0o755)).expect("a chmod");

    let working = Working::read(&root, store.skipped()).expect("the folder");
    match plan(&store, &working, &edit, &edit) {
        Err(RevertError::Refused { paths }) => assert_eq!(paths[0].0, "f", "{paths:?}"),
        other => panic!("a refusal naming f, not {other:?}"),
    }
    let _ = fs::remove_dir_all(&root);
}

/// A link naming a file by identity is re-pointed when the undoing moves
/// the file back, so applying leaves the complete undoing in the folder and
/// recording it leaves nothing differing.
#[cfg(unix)]
#[test]
fn a_rename_put_back_re_points_the_links_naming_it() {
    use std::os::unix::fs::symlink;

    let (root, mut store) = folder("rename-link");
    fs::write(root.join("f"), "x\n").expect("a file");
    symlink("f", root.join("link")).expect("a link");
    let first = recorded(&mut store, &root, Vec::new(), "Start");
    fs::rename(root.join("f"), root.join("g")).expect("a rename");
    let working = Working::read(&root, store.skipped()).expect("the folder");
    let mut renaming = recording(vec![first], "Rename", Restriction::Everything);
    renaming.moves = vec![("f".to_owned(), "g".to_owned())];
    let rename = record(&mut store, &working, &renaming, &mut Platform)
        .expect("recording the rename")
        .revision;
    // The folder catches up, so the link spells the new path.
    let working = Working::read(&root, store.skipped()).expect("the folder");
    let following = historica::following::Following::Everything;
    let caught_up =
        update::plan(&store, &working, &root, &rename, &following).expect("an update plan");
    update::apply(&store, &working, &root, &caught_up).expect("an update");
    assert_eq!(
        fs::read_link(root.join("link")).expect("a link"),
        Path::new("g")
    );

    let working = Working::read(&root, store.skipped()).expect("the folder");
    let reversal = plan(&store, &working, &rename, &rename).expect("a plan");
    assert_eq!(reversal.moves, [("g".to_owned(), "f".to_owned())]);
    assert!(reversal.paths.contains(&"link".to_owned()), "{reversal:?}");
    update::apply(&store, &working, &root, &reversal.update).expect("applying");
    assert_eq!(
        fs::read_link(root.join("link")).expect("a link"),
        Path::new("f")
    );

    let undone = record_reversal(&mut store, &root, &reversal, "Undo the rename");
    let working = Working::read(&root, store.skipped()).expect("the folder");
    let again = plan(&store, &working, &rename, &undone.revision).expect("a plan");
    assert!(again.is_settled(), "{again:?}");
    let _ = fs::remove_dir_all(&root);
}
