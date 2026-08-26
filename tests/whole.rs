//! Content that arrives whole: a payload is the file, and the file is a payload.
//!
//! `tests/corpus/whole/` is decision 0017 executed. Two revisions file a
//! photograph and the entry it belongs to: the entry's first content is the
//! entry, stored as itself rather than as an insert of every line of it, and
//! the photograph is a PNG that opens as a picture in the folder a person
//! browses. The second revision crops the photograph and fixes the line under
//! it, so one history holds both a payload replaced whole and an operation
//! document counted against a state a payload created.
//!
//! The claim it exists to check is that the two spellings meet: an `edit` at
//! `02` states positions into the file `01`'s payload produced, and replay has
//! to agree with it or the corpus is wrong.

use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};

use historica::core::{FileId, RevisionId};
use historica::format::{
    ForgottenPayload, ParseErrorKind, RevisionDocument, digest, is_forgotten_payload,
};
use historica::store::{Content, Store};
use historica::tree::Kind;

/// The entry, and the photograph, as the corpus names them.
const ENTRY: &str = "nrqvtkzlmwyxsptonvqrklmz";
const PHOTO: &str = "swtlmnkqvzyrxopwstlnmkqv";

fn corpus() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/corpus/whole")
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
            fs::copy(&from, &to).expect("copying the corpus");
        }
    }
    Store::open(&root).expect("the corpus is a store")
}

#[test]
fn every_file_hashes_to_what_the_manifest_says() {
    // The claim the format exists to make, checked with the tool everyone has:
    // `shasum -a 256 -c MANIFEST` says the same thing this does.
    for (name, id) in manifest() {
        let bytes = fs::read(corpus().join(&name)).expect("a corpus file");
        assert_eq!(digest(&bytes), id, "{name} is not what the manifest says");
    }
}

#[test]
fn a_created_file_is_stored_as_itself() {
    let manifest = manifest();
    let bytes = fs::read(corpus().join("revisions/01-start.rev.txt")).expect("the revision");
    let document = RevisionDocument::parse(&bytes).expect("a revision");

    assert_eq!(document.added.len(), 2);
    assert!(document.edited.is_empty(), "a creation names no operations");
    assert_eq!(
        document.text.get(&file(ENTRY)),
        manifest.get("operations/01-entry.md"),
        "the entry's first content is the entry"
    );
    assert_eq!(
        document.bytes.get(&file(PHOTO)),
        manifest.get("operations/01-photo.png"),
        "and the photograph is the photograph"
    );

    // The payload is the file, with nothing in front of the lines: this is the
    // whole of what decision 0017 was for.
    let payload = fs::read(corpus().join("operations/01-entry.md")).expect("the payload");
    let text = String::from_utf8(payload).expect("a text payload is UTF-8");
    assert!(text.starts_with("# 2026-08-20\n"), "{text}");
    assert!(!text.contains('+'), "no `+` down the left margin: {text}");
}

#[test]
fn one_history_holds_a_payload_and_the_operations_counted_against_it() {
    let store = store("whole-materialise");
    let manifest = manifest();
    let start = *manifest
        .get("revisions/01-start.rev.txt")
        .expect("the first revision");
    let crop = *manifest
        .get("revisions/02-crop.rev.txt")
        .expect("the second revision");

    // A file's kind is fixed when it is added, and the tree is what says so.
    let tree = store.tree(&crop).expect("the file set");
    assert_eq!(tree.kind(&file(ENTRY)), Some(Kind::Lines));
    assert_eq!(tree.kind(&file(PHOTO)), Some(Kind::Whole));

    // The entry replays as though its creation had been an insert of every
    // line, which is what lets `02`'s `delete 2 1` count into it and agree.
    let Content::Lines(before) = store
        .content_at(&start, &file(ENTRY))
        .expect("the entry as created")
    else {
        panic!("a file of lines");
    };
    assert!(
        before.text().ends_with("only where it sits.\n"),
        "{before:?}"
    );
    let Content::Lines(after) = store
        .content_at(&crop, &file(ENTRY))
        .expect("the entry as edited")
    else {
        panic!("a file of lines");
    };
    assert!(
        after.text().ends_with("only say where it sits.\n"),
        "{after:?}"
    );
    assert_eq!(
        before.len(),
        after.len(),
        "one line rewritten, not appended"
    );

    // And the photograph comes back byte for byte at each revision, which is
    // the whole of what a file of bytes does.
    for (revision, payload) in [
        (start, "operations/01-photo.png"),
        (crop, "operations/02-photo.png"),
    ] {
        let stored = fs::read(corpus().join(payload)).expect("the payload");
        // Decision 0067: what the tree answers is the payload's name, and the
        // bytes are asked of the store — in pieces, so that this is what
        // `historica cat` does rather than a shortcut around it.
        let Content::Whole(held) = store
            .content_at(&revision, &file(PHOTO))
            .expect("the photograph")
        else {
            panic!("a file of bytes");
        };
        assert_eq!(held, historica::format::digest(&stored), "{payload}");
        let mut streamed = Vec::new();
        assert!(
            store
                .payload_in_pieces(&held, &mut |piece| {
                    streamed.extend_from_slice(piece);
                    Ok(())
                })
                .expect("reading the payload"),
            "{payload}: the store holds it"
        );
        assert_eq!(streamed, stored, "{payload}");
        assert!(
            String::from_utf8(streamed).is_err(),
            "and it is content no list of lines could hold"
        );
    }

    // A store with a picture in it is an ordinary store.
    let report = Store::check(store.root());
    assert!(
        report.is_ok(),
        "{:?}",
        report
            .findings()
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>()
    );
}

/// The corpus's photograph, forgotten: the payload destroyed and the
/// hand-written stand-in dropped in where it sat.
///
/// Decision 0066. The store is assembled by hand rather than by running
/// `forget`, because what is under test is what a *reader* makes of the two
/// headers — a replica receives exactly this and never sees the command that
/// wrote it.
#[test]
fn a_forgotten_payload_is_two_headers_and_a_store_that_still_checks() {
    let store = store("whole-forgotten");
    let root = store.root().to_path_buf();
    drop(store);
    fs::remove_file(root.join("operations/01-photo.png")).expect("destroying the payload");
    fs::copy(
        corpus().join("forgotten/photo.ops.txt"),
        root.join("operations/01-photo.forgotten.ops.txt"),
    )
    .expect("the stand-in");

    let store = Store::open(&root).expect("the redacted corpus is a store");
    let manifest = manifest();
    let start = *manifest
        .get("revisions/01-start.rev.txt")
        .expect("the first revision");
    let payload = *manifest
        .get("operations/01-photo.png")
        .expect("the destroyed payload");

    // Decision 0067: what a revision *said* about a file of bytes is still
    // there to be read, because it is a name rather than the bytes — the
    // redaction did not reach the revision document.
    let Content::Whole(named) = store
        .content_at(&start, &file(PHOTO))
        .expect("the photograph, named")
    else {
        panic!("a file of bytes");
    };
    assert_eq!(named, payload);

    // What a person asking for the bytes themselves is told: not "not here
    // yet", which is what an undelivered payload says, but who destroyed them
    // and how many there were.
    let said = store
        .absent_payload(&named, &start)
        .expect("an answer")
        .to_string();
    assert!(said.contains("was forgotten"), "{said}");
    assert!(said.contains("69 bytes destroyed"), "{said}");

    // The revision after it is untouched: a payload is quoted by digest, so
    // forgetting one version of a file reaches exactly that version.
    let Content::Whole(held) = store
        .content_at(
            manifest
                .get("revisions/02-crop.rev.txt")
                .expect("the second revision"),
            &file(PHOTO),
        )
        .expect("the cropped photograph")
    else {
        panic!("a file of bytes");
    };
    // Decision 0067: what `content_at` answers for a file of bytes is the
    // payload's name, so the comparison is between two digests — which is
    // what a comparison of two payloads always was.
    assert_eq!(
        held,
        digest(&fs::read(corpus().join("operations/02-photo.png")).expect("the payload"))
    );

    // A forgotten store passes `check`, and the absence is accounted for
    // rather than merely observed — decision 0044's `bytes` branch, which
    // waited for this.
    let report = Store::check(&root);
    assert!(report.is_ok(), "{report:?}");
    let notes: Vec<String> = report
        .findings()
        .iter()
        .map(ToString::to_string)
        .collect::<Vec<_>>();
    assert!(
        notes
            .iter()
            .any(|note| note.contains("bytes were destroyed")),
        "{notes:?}"
    );
    assert!(
        !notes
            .iter()
            .any(|note| note.contains("may not have arrived")),
        "a destroyed payload is not a missing one: {notes:?}"
    );

    // And the store holding both at once is the resurrection `check` reports,
    // which is what a sync that carried the original back looks like.
    fs::copy(
        corpus().join("operations/01-photo.png"),
        root.join("operations/01-photo.png"),
    )
    .expect("the payload, back again");
    let report = Store::check(&root);
    let notes: Vec<String> = report
        .findings()
        .iter()
        .map(ToString::to_string)
        .collect::<Vec<_>>();
    assert!(
        notes
            .iter()
            .any(|note| note.contains("bytes are here again")),
        "{notes:?}"
    );
    assert!(
        notes
            .iter()
            .any(|note| note.contains(&payload.abbreviate(12).to_string())),
        "and it says which digest came back: {notes:?}"
    );
}

#[test]
fn every_invalid_forgotten_payload_is_refused_for_its_own_reason() {
    let cases: Vec<(&str, ParseErrorKind)> = vec![
        (
            "length-without-forgets.ops.txt",
            ParseErrorKind::MissingHeader { key: "forgets" },
        ),
        (
            "forgets-after-length.ops.txt",
            ParseErrorKind::KeysOutOfOrder {
                key: "forgets".to_owned(),
                after: "length".to_owned(),
            },
        ),
        (
            "result-of-forgetting.ops.txt",
            ParseErrorKind::ResultOfForgetting,
        ),
        (
            "with-a-body.ops.txt",
            ParseErrorKind::ForgottenPayloadWithBody,
        ),
        (
            "padded-length.ops.txt",
            ParseErrorKind::MalformedNumber {
                found: "0069".to_owned(),
            },
        ),
    ];

    for (name, expected) in cases {
        let bytes =
            fs::read(corpus().join("forgotten/invalid").join(name)).expect("an invalid stand-in");
        // Each one still claims the grammar, which is what makes refusing it
        // the reader's job rather than the dispatch's.
        assert!(
            is_forgotten_payload(&bytes),
            "forgotten/invalid/{name} should be read as a forgotten payload"
        );
        let error = ForgottenPayload::parse(&bytes)
            .map(|document| format!("{document:?}"))
            .expect_err(&format!("forgotten/invalid/{name} should not parse"));
        assert_eq!(
            error.kind, expected,
            "forgotten/invalid/{name} failed for the wrong reason"
        );
        // Decision 0004's condition on strictness: a refusal says what to do.
        let said = error.to_string();
        assert!(
            said.len() > 40,
            "forgotten/invalid/{name} says too little: {said}"
        );
    }
}

#[test]
fn every_invalid_file_is_refused_for_its_own_reason() {
    let entry = file(ENTRY).to_string();
    let cases: Vec<(&str, ParseErrorKind)> = vec![
        (
            "add-with-edit.rev.txt",
            ParseErrorKind::ContradictoryFileFacts {
                first: "add",
                second: "edit",
                file: entry.clone(),
            },
        ),
        (
            "text-without-add.rev.txt",
            ParseErrorKind::TextWithoutAdd {
                file: entry.clone(),
            },
        ),
        (
            "text-and-bytes.rev.txt",
            ParseErrorKind::ContradictoryFileFacts {
                first: "text",
                second: "bytes",
                file: entry.clone(),
            },
        ),
        (
            "edit-and-bytes.rev.txt",
            ParseErrorKind::ContradictoryFileFacts {
                first: "edit",
                second: "bytes",
                file: entry.clone(),
            },
        ),
        (
            "drop-and-bytes.rev.txt",
            ParseErrorKind::ContradictoryFileFacts {
                first: "drop",
                second: "bytes",
                file: entry.clone(),
            },
        ),
    ];

    for (name, expected) in cases {
        let bytes = fs::read(corpus().join("invalid").join(name)).expect("an invalid file");
        let error = RevisionDocument::parse(&bytes)
            .map(|document| format!("{document:?}"))
            .expect_err(&format!("invalid/{name} should not parse"));
        assert_eq!(
            error.kind, expected,
            "invalid/{name} failed for the wrong reason"
        );
        // Decision 0004's condition on strictness: a refusal says what to do.
        let said = error.to_string();
        assert!(said.len() > 40, "invalid/{name} says too little: {said}");
    }
}

/// A payload larger than the run a filesystem hands over goes in, comes back,
/// and lands in a folder byte for byte.
///
/// Decision 0067: `record`, `cat` and `update` each read and write a payload in
/// pieces now, and the seam between two pieces is the whole of what that
/// introduces. `Disk` hands over 64 KiB at a time, so this file crosses several
/// of them and ends part-way through one.
#[test]
fn a_payload_that_crosses_every_piece_boundary_round_trips() {
    use historica::record::{Clock as _, Platform, Recording, Restriction, record};
    use historica::update;
    use historica::working::Working;
    use std::collections::BTreeSet;

    let root = Path::new(env!("CARGO_TARGET_TMPDIR")).join("whole-streamed");
    let _ = fs::remove_dir_all(&root);
    let base = root.join("repo");
    fs::create_dir_all(&base).expect("a folder");
    let mut store = Store::init(base.join("history")).expect("a store");

    // Not text by decision 0017's rule from its first dozen bytes, and long
    // enough that no single read hands the whole of it over.
    let mut bytes = b"\x89PNG\r\n\x1a\n".to_vec();
    while bytes.len() < 300_003 {
        bytes.extend_from_slice(&(bytes.len() as u32).to_le_bytes());
    }
    fs::write(base.join("photo.png"), &bytes).expect("the file");

    let mut platform = Platform;
    let recording = |parents: Vec<RevisionId>, message: &str| Recording {
        parents,
        author: "Adam Harris <adam@example.com>".to_owned(),
        when: Platform.now().expect("a clock"),
        message: message.to_owned(),
        moves: Vec::new(),
        at: Vec::new(),
        accepted: BTreeSet::new(),
        only: Restriction::Everything,
        kinds: Default::default(),
        extensions: Default::default(),
    };
    let working = Working::read(&base, store.skipped()).expect("the folder");
    let recorded = record(
        &mut store,
        &working,
        &recording(Vec::new(), "A photograph"),
        &mut platform,
    )
    .expect("recording");

    // The revision names the digest, and the store hands the bytes back
    // through the streaming read every command now uses.
    let tree = store.tree(&recorded.revision).expect("the tree");
    let (file, _) = tree.files().next().expect("the photograph");
    let Content::Whole(payload) = store
        .content_at(&recorded.revision, file)
        .expect("the photograph")
    else {
        panic!("a file of bytes");
    };
    assert_eq!(payload, digest(&bytes));
    let mut streamed = Vec::new();
    assert!(
        store
            .payload_in_pieces(&payload, &mut |piece| {
                streamed.extend_from_slice(piece);
                Ok(())
            })
            .expect("reading it"),
        "the store holds it"
    );
    assert_eq!(streamed, bytes, "byte for byte, out of the store");

    // And an update lays it back down in an empty folder, straight from the
    // store's own file.
    let elsewhere = root.join("elsewhere");
    fs::create_dir_all(&elsewhere).expect("an empty directory");
    let into = Working::read(&elsewhere, store.skipped()).expect("walking nothing");
    let plan = update::plan_into(&store, &into, &elsewhere, &recorded.revision).expect("a plan");
    let applied = update::apply(&store, &into, &elsewhere, &plan).expect("applying");
    assert_eq!(applied.wrote, ["photo.png"], "{applied:?}");
    assert_eq!(
        fs::read(elsewhere.join("photo.png")).expect("the file"),
        bytes,
        "byte for byte, into the folder"
    );

    // Recording the same folder again says nothing about it, which is the
    // comparison of digests decision 0043 asked for and 0067 keeps.
    let again = Working::read(&base, store.skipped()).expect("the folder");
    assert!(
        record(
            &mut store,
            &again,
            &recording(vec![recorded.revision], "Nothing"),
            &mut platform,
        )
        .is_err(),
        "an unchanged photograph is not a revision"
    );

    let _ = fs::remove_dir_all(&root);
}

/// A streamed payload that does not hash to what it was promised to writes
/// nothing at all.
///
/// Decision 0067's one new failure: a copy learns the digest at its last piece,
/// and the refusal has to leave the destination as it stood — otherwise the
/// store would hold a file named for bytes it does not have, which is exactly
/// what `write_once` refuses for a document.
#[test]
fn a_payload_that_hashes_wrongly_leaves_nothing_behind() {
    use historica::store::StoreError;

    let root = Path::new(env!("CARGO_TARGET_TMPDIR")).join("whole-mismatch");
    let _ = fs::remove_dir_all(&root);
    let mut store = Store::init(root.join("history")).expect("a store");

    let promised = digest(b"the bytes that were promised");
    let error = store
        .insert_payload_in_pieces(&promised, &promised.to_string(), &mut |into| {
            std::io::Write::write_all(into, b"the bytes that arrived")
        })
        .expect_err("bytes that are not what was promised");
    let StoreError::PayloadMismatch { found, wanted, .. } = error else {
        panic!("{error}");
    };
    assert_eq!(wanted, promised);
    assert_eq!(found, digest(b"the bytes that arrived"));

    assert!(
        !root
            .join("history/operations")
            .join(promised.to_string())
            .exists(),
        "the name it would have gone under is free"
    );
    // And no scratch survives beside it, so the store's own walk finds nothing
    // it would report as a payload nobody named.
    let left: Vec<_> = fs::read_dir(root.join("history/operations"))
        .expect("the directory")
        .map(|entry| entry.expect("an entry").file_name())
        .collect();
    assert!(left.is_empty(), "{left:?}");

    let report = Store::check(store.root());
    assert!(report.is_ok(), "{:?}", report.findings());
}
