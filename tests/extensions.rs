//! A header another tool wrote, from the writing end: decision 0065 executed.
//!
//! 0065 settled what a reader does with a key that has a dot in it — parse it,
//! hash it, sort it last, never interpret it — and the parser has been doing
//! that since. What had no way in was the other end: nothing a caller could
//! state put such a header on a revision it recorded, so the room 0065 made was
//! room no tool could reach.
//!
//! [`Recording::extensions`] is that way in, and the claim under test is the
//! one a tool built on this one has to be able to rely on. A fact this format
//! has no word for — the committer git records apart from the author, the
//! signature it strips before hashing — goes in, comes back out of the store
//! byte for byte, is part of the revision's identity because the whole document
//! is, and survives the amendment that rewrites everything around it. What
//! cannot go in is a key this format could later define, because a writer that
//! filed one would be filing a document historica's own parser refuses.

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Path, PathBuf};

use historica::core::RevisionId;
use historica::format::{RevisionDocument, digest};
use historica::record::{
    Amendment, Clock as _, Platform, RecordError, Recording, Restriction, amend, record,
};
use historica::store::Store;
use historica::working::Working;

const AUTHOR: &str = "Adam Harris <adam@example.com>";

/// A fresh directory for one test, inside the target directory.
fn scratch(test: &str) -> PathBuf {
    let path = Path::new(env!("CARGO_TARGET_TMPDIR")).join(test);
    let _ = fs::remove_dir_all(&path);
    fs::create_dir_all(&path).expect("a scratch directory");
    path
}

/// The three facts git keeps that this format has no word for, which is the
/// example 0065's room was made for.
fn git_headers() -> BTreeMap<String, String> {
    BTreeMap::from([
        (
            "git.committer".to_owned(),
            "Someone Else <else@example.com> 1724668800 +0100".to_owned(),
        ),
        ("git.encoding".to_owned(), "ISO-8859-1".to_owned()),
        (
            "git.signature".to_owned(),
            "-----BEGIN PGP SIGNATURE----- iQIzBAABCgAdFiEE -----END PGP SIGNATURE-----".to_owned(),
        ),
    ])
}

/// A folder with one file in it, and a store beside it.
fn repository(name: &str) -> (PathBuf, Store) {
    let root = scratch(name);
    let base = root.join("repo");
    fs::create_dir_all(&base).expect("the folder");
    fs::write(base.join("notes.md"), "First thought.\n").expect("a file");
    let store = Store::init(base.join("history")).expect("a new store");
    (base, store)
}

fn recording(parents: Vec<RevisionId>, extensions: BTreeMap<String, String>) -> Recording {
    Recording {
        parents,
        author: AUTHOR.to_owned(),
        when: Platform.now().expect("a clock"),
        message: "Start a journal".to_owned(),
        moves: Vec::new(),
        at: Vec::new(),
        accepted: BTreeSet::new(),
        only: Restriction::Everything,
        kinds: Default::default(),
        extensions,
    }
}

#[test]
fn a_stated_header_is_recorded_and_read_back_as_it_was_given() {
    let (base, mut store) = repository("extensions-recorded");
    let working = Working::read(&base, store.skipped()).expect("the folder");
    let recorded = record(
        &mut store,
        &working,
        &recording(Vec::new(), git_headers()),
        &mut Platform,
    )
    .expect("recording");

    let store = Store::open(base.join("history")).expect("the store again");
    let document = store
        .get(&recorded.revision)
        .expect("a readable store")
        .expect("the revision");
    assert_eq!(document.extensions, git_headers());

    // Identity is the digest of the bytes, and the headers are among them: a
    // revision recorded without them is a different revision. That is the whole
    // of why a tool can hang its own identity on one.
    let bytes = document.write();
    assert_eq!(digest(&bytes), recorded.revision);
    let without = RevisionDocument {
        extensions: BTreeMap::new(),
        ..document.clone()
    };
    assert_ne!(without.id(), recorded.revision);

    // 0065's sort: last, and against their own kind by whole key.
    let text = String::from_utf8(bytes).expect("a document is text");
    let keys: Vec<&str> = text
        .lines()
        .filter(|line| line.starts_with("git."))
        .collect();
    assert_eq!(
        keys,
        [
            "git.committer Someone Else <else@example.com> 1724668800 +0100",
            "git.encoding ISO-8859-1",
            "git.signature -----BEGIN PGP SIGNATURE----- iQIzBAABCgAdFiEE -----END PGP SIGNATURE-----",
        ]
    );
    let first = text.find("git.").expect("the headers are in the document");
    assert!(
        text[..first].contains("author ") && text[..first].contains("when "),
        "every header this format defines comes before them"
    );
}

#[test]
fn an_amendment_keeps_the_headers_it_cannot_read() {
    let (base, mut store) = repository("extensions-amended");
    let working = Working::read(&base, store.skipped()).expect("the folder");
    let recorded = record(
        &mut store,
        &working,
        &recording(Vec::new(), git_headers()),
        &mut Platform,
    )
    .expect("recording");

    // The folder moves on, so the amendment restates content as well as a
    // message: everything about the revision changes except what it carries for
    // somebody else.
    fs::write(base.join("notes.md"), "First thought, revised.\n").expect("the file");
    let working = Working::read(&base, store.skipped()).expect("the folder again");
    let amended = amend(
        &mut store,
        &working,
        &Amendment {
            revision: recorded.revision,
            message: Some("Start a journal, properly".to_owned()),
            reviser: AUTHOR.to_owned(),
            revised: Platform.now().expect("a clock"),
            moves: Vec::new(),
        },
        &mut Platform,
    )
    .expect("amending");

    let document = store
        .get(&amended.revision)
        .expect("a readable store")
        .expect("the amendment");
    assert_eq!(
        document.extensions,
        git_headers(),
        "decision 0023: a writer that cannot read a header must not drop it"
    );
}

#[test]
fn a_key_this_format_could_define_is_refused_by_name() {
    let (base, mut store) = repository("extensions-refused");
    let working = Working::read(&base, store.skipped()).expect("the folder");

    // A dotless key, the shapes that name no tool, and 0002's three rules for
    // any header value.
    for (key, value) in [
        ("committer", "Someone Else <else@example.com>"),
        ("x-git-committer", "Someone Else <else@example.com>"),
        (".git", "nothing before the dot"),
        ("git.", "nothing after it"),
        ("git..committer", "nothing between two"),
        ("Git.committer", "a capital letter"),
        ("git.committer", ""),
        ("git.committer", " padded "),
        ("git.committer", "two\nlines"),
    ] {
        let stated = BTreeMap::from([(key.to_owned(), value.to_owned())]);
        let Err(refusal) = record(
            &mut store,
            &working,
            &recording(Vec::new(), stated),
            &mut Platform,
        ) else {
            panic!("`{key} {value}` is not a header this format can hold");
        };
        match refusal {
            RecordError::UnusableHeader { key: named, .. } => assert_eq!(named, key),
            other => panic!("`{key} {value}` was refused as {other}"),
        }
    }

    // And the refusal did nothing: no revision, and no operation document
    // filed on the way to saying no.
    assert!(store.is_empty(), "nothing was recorded");
    assert!(
        store.documents().expect("a readable store").is_empty(),
        "and nothing was written for it"
    );
}
