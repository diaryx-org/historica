//! Decision 0081's promise: the statement index changes the time a content
//! question takes and never its answer.
//!
//! Every hand-written corpus store holding files, and a generated history
//! with branches and merges in it, asked for every file at every revision
//! twice — once as a reader asks, taking the index, and once as `check`
//! asks, walking every step — with nothing kept between, so the only
//! difference is the index.

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};

use crate::core::{FileId, RevisionId};
use crate::fs::{Disk, Filesystem as _};
use crate::record::{Clock as _, Platform, Recording, Restriction, record};
use crate::working::Working;

use super::{Caching, Store};

/// A directory of its own for one store, made through the library's own
/// filesystem: decision 0025 keeps `std::fs` out of this crate, its tests
/// included.
fn scratch(name: &str) -> PathBuf {
    let moment = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map_or(0, |since| since.as_nanos());
    let path = std::env::temp_dir().join(format!(
        "historica-stating-{name}-{}-{moment}",
        std::process::id()
    ));
    Disk.create_directory(&path).expect("a scratch directory");
    path
}

/// A corpus directory's files, copied into a store under the names they have.
///
/// `prefix` is where a MANIFEST's names sit inside the store: nothing for a
/// corpus whose MANIFEST names `revisions/…` and `operations/…`.
fn from_corpus(name: &str, parts: &[(&str, &str)]) -> Store {
    let root = scratch(name).join("history");
    Store::init(&root).expect("a new store");
    let corpus = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/corpus");
    for (directory, prefix) in parts {
        let manifest = String::from_utf8(
            Disk.read(&corpus.join(directory).join("MANIFEST"))
                .expect("a MANIFEST"),
        )
        .expect("text");
        for line in manifest.lines().filter(|line| !line.trim().is_empty()) {
            let (_, file) = line.split_once("  ").expect("`<digest>  <name>`");
            if ["invalid/", "states/", "forgotten/"]
                .iter()
                .any(|skipped| file.starts_with(skipped))
            {
                continue;
            }
            let to = root.join(prefix).join(file);
            Disk.create_directory(to.parent().expect("a directory"))
                .expect("a directory");
            let bytes = Disk
                .read(&corpus.join(directory).join(file))
                .expect("a corpus file");
            Disk.write(&to, &bytes).expect("copying a corpus file");
        }
    }
    Store::open(&root).expect("the corpus as a store")
}

/// Every file any revision mentions.
fn files(store: &Store) -> BTreeSet<FileId> {
    let mut files = BTreeSet::new();
    for (_, document) in store.documents().expect("every document") {
        files.extend(document.added.keys());
        files.extend(document.edited.keys());
        files.extend(document.text.keys());
    }
    files
}

/// Every file at every revision, asked both ways.
fn answers_alike(name: &str, store: &Store) {
    let revisions: Vec<RevisionId> = store.revisions().map(|(id, _)| *id).collect();
    let files = files(store);
    let mut stated_digests = 0;
    assert!(
        !files.is_empty() && !revisions.is_empty(),
        "{name}: nothing to ask of {} revisions and {} files",
        revisions.len(),
        files.len()
    );
    for revision in &revisions {
        for file in &files {
            let taken = store.content_of_with(revision, file, Caching::Take);
            let walked = store.content_of_with(revision, file, Caching::Replay);
            match (&taken, &walked) {
                (Ok(taken), Ok(walked)) => {
                    assert_eq!(
                        taken.as_ref().map(|state| state.text()),
                        walked.as_ref().map(|state| state.text()),
                        "{file} at {revision}"
                    );
                    // Where the survey's comparison is one lookup, it is the
                    // digest of what materialising gives.
                    if let Ok(Some(stated)) = store.stated_digest(revision, file) {
                        assert_eq!(
                            Some(stated),
                            walked.as_ref().map(|state| state.digest()),
                            "the digest stated for {file} at {revision}"
                        );
                        stated_digests += 1;
                    }
                }
                (Err(taken), Err(walked)) => assert_eq!(
                    taken.to_string(),
                    walked.to_string(),
                    "{file} at {revision}"
                ),
                _ => panic!("{file} at {revision}: {taken:?} against {walked:?}"),
            }
        }
    }
    assert_ne!(
        stated_digests, 0,
        "{name}: no digest was stated, so none was checked"
    );
}

#[test]
fn the_corpus_answers_alike_with_the_index_and_without() {
    for (name, parts) in [
        ("merged", &[("merged", "")][..]),
        ("tree", &[("tree", "")][..]),
        ("links", &[("links", "")][..]),
        ("modes", &[("modes", "")][..]),
        ("whole", &[("whole", "")][..]),
    ] {
        answers_alike(name, &from_corpus(name, parts));
    }
}

/// One revision recorded from the folder as it stands.
fn recorded(
    store: &mut Store,
    folder: &Path,
    parents: Vec<RevisionId>,
    message: &str,
) -> RevisionId {
    let mut platform = Platform;
    let working = Working::read(folder, store.skipped()).expect("the folder");
    record(
        store,
        &working,
        &Recording {
            parents,
            author: "Adam Harris <adam@example.com>".to_owned(),
            when: platform.now().expect("a clock"),
            message: message.to_owned(),
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

/// Branches that each edit some files and leave others, merges that join
/// them — resolving where they differ and not where they agree — and files
/// nothing touches after the root, which is where the index goes furthest.
#[test]
fn a_history_with_branches_and_merges_answers_alike() {
    let folder = scratch("branches");
    let mut store = Store::init(folder.join("history")).expect("a new store");
    let write = |name: &str, text: &str| {
        Disk.write(&folder.join(name), text.as_bytes())
            .expect("a file");
    };
    for file in ["a", "b", "c", "d"] {
        write(&format!("{file}.md"), &format!("{file} one\n{file} two\n"));
    }
    let root = recorded(&mut store, &folder, Vec::new(), "root");

    write("a.md", "a one\na two\na left\n");
    let left = recorded(&mut store, &folder, vec![root], "left");
    write("b.md", "b one\nb two\nb left\n");
    let left = recorded(&mut store, &folder, vec![left], "left again");

    // The folder as the right branch leaves it, from the root.
    write("a.md", "a one\na two\n");
    write("b.md", "b one\nb two\n");
    write("a.md", "a right\na one\na two\n");
    let right = recorded(&mut store, &folder, vec![root], "right");
    write("c.md", "c one\nc two\nc right\n");
    let right = recorded(&mut store, &folder, vec![right], "right again");

    // Both sides of `a`, the left's `b`, the right's `c`, and `d` untouched.
    write("a.md", "a right\na one\na two\na left\n");
    write("b.md", "b one\nb two\nb left\n");
    let merged = recorded(&mut store, &folder, vec![left, right], "merged");
    write("d.md", "d one\nd two\nd after\n");
    let after = recorded(&mut store, &folder, vec![merged], "after");
    write("b.md", "b one\nb after\n");
    recorded(&mut store, &folder, vec![after], "b again");

    let store = Store::open(store.root()).expect("reopened");
    answers_alike("branches", &store);
}
