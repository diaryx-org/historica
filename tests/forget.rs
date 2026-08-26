//! Forgetting, exercised end to end: decision 0014's named tests.
//!
//! The claim under test throughout is the decision's central one: forgetting
//! destroys payload and preserves shape, so a redacted history materialises
//! and merges exactly as it did outside the forgotten runs — and the
//! destroyed text is recoverable from nothing the store still holds.

use std::collections::BTreeSet;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

use historica::core::RevisionId;
use historica::format::{OperationDocument, stand_in};
use historica::record::{Clock as _, Platform, Recording, Restriction, record};
use historica::store::{Extent, Finding, Forgetting, Store};
use historica::working::Working;

fn scratch(test: &str) -> PathBuf {
    let path = Path::new(env!("CARGO_TARGET_TMPDIR")).join(format!("forget-{test}"));
    let _ = fs::remove_dir_all(&path);
    fs::create_dir_all(&path).expect("a scratch directory");
    path
}

fn run(directory: &Path, arguments: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_historica"))
        .arg("-C")
        .arg(directory)
        .args(arguments)
        .env("HISTORICA_AUTHOR", "Adam Harris <adam@example.com>")
        .output()
        .expect("the binary this test crate builds")
}

fn out(directory: &Path, arguments: &[&str]) -> String {
    let output = run(directory, arguments);
    assert!(
        output.status.success(),
        "`{}` failed: {}",
        arguments.join(" "),
        String::from_utf8_lossy(&output.stderr)
    );
    String::from_utf8(output.stdout).expect("printed text")
}

fn write(directory: &Path, path: &str, text: &str) {
    fs::write(directory.join(path), text).expect("writing a file");
}

/// The revision digest a `record` line printed after ` as `.
fn digest_in(said: &str) -> String {
    said.lines()
        .find_map(|line| line.split(" as ").nth(1))
        .expect("a `... as <digest>` line")
        .trim()
        .to_owned()
}

/// Every byte of every file under the store, for asserting what is gone.
fn store_bytes(directory: &Path) -> Vec<u8> {
    let mut bytes = Vec::new();
    let mut pending = vec![directory.join("history")];
    while let Some(next) = pending.pop() {
        for entry in fs::read_dir(&next)
            .expect("a directory")
            .filter_map(Result::ok)
        {
            let path = entry.path();
            if path.is_dir() {
                pending.push(path);
            } else {
                bytes.extend(fs::read(&path).expect("a store file"));
            }
        }
    }
    bytes
}

fn contains(haystack: &[u8], needle: &str) -> bool {
    haystack
        .windows(needle.len())
        .any(|window| window == needle.as_bytes())
}

#[test]
fn forgetting_destroys_every_quote_and_the_history_still_materialises() {
    let directory = scratch("quotes");
    assert!(run(&directory, &["init"]).status.success());
    write(
        &directory,
        "notes.md",
        "keep this line\nthe secret paragraph\n",
    );
    let first = out(&directory, &["record", "-m", "Start a journal"]);
    write(&directory, "notes.md", "keep this line\n");
    out(&directory, &["record", "-m", "Second thoughts"]);

    let said = out(
        &directory,
        &["forget", &digest_in(&first), "notes.md", "--lines", "2"],
    );
    assert!(said.contains("wrote a forgetting document"), "{said}");
    assert!(said.contains("destroyed history/"), "{said}");
    assert!(said.contains("only the text is destroyed"), "{said}");

    // The decision's named test: the text of an item forgotten at its insert
    // is not recoverable from the delete that quoted it — or from anything
    // else the store still holds.
    assert!(!contains(&store_bytes(&directory), "the secret paragraph"));

    // Every revision after the forgotten one still materialises, and the
    // file at the redacted revision shows the marker where the run was.
    assert_eq!(
        out(&directory, &["cat", "head", "notes.md"]),
        "keep this line\n"
    );
    assert_eq!(
        out(&directory, &["cat", &digest_in(&first), "notes.md"]),
        "keep this line\n\\ forgotten\n"
    );

    // A forgotten store passes `check`; the redaction is a note, not a fault.
    let checked = run(&directory, &["check"]);
    assert!(
        checked.status.success(),
        "{}",
        String::from_utf8_lossy(&checked.stdout)
    );
    let report = String::from_utf8(checked.stdout).expect("printed text");
    assert!(report.contains("whose bytes were destroyed"), "{report}");

    // Forgetting twice is a no-op.
    let again = out(
        &directory,
        &["forget", &digest_in(&first), "notes.md", "--lines", "2"],
    );
    assert!(again.contains("already forgotten"), "{again}");

    // And the folder still records: nothing about the working copy changed.
    write(&directory, "notes.md", "keep this line\nnew work\n");
    let recorded = out(&directory, &["record", "-m", "Carrying on"]);
    assert!(recorded.contains("recorded "), "{recorded}");
}

#[test]
fn a_dry_run_prints_the_loss_and_destroys_nothing() {
    let directory = scratch("dry-run");
    assert!(run(&directory, &["init"]).status.success());
    write(&directory, "notes.md", "one\ntwo\n");
    let first = out(&directory, &["record", "-m", "Start"]);

    let said = out(
        &directory,
        &[
            "forget",
            &digest_in(&first),
            "notes.md",
            "--lines",
            "2",
            "--dry-run",
        ],
    );
    assert!(said.contains("would write"), "{said}");
    assert!(said.contains("would destroy"), "{said}");
    assert!(contains(&store_bytes(&directory), "two"));
    assert_eq!(out(&directory, &["cat", "head", "notes.md"]), "one\ntwo\n");
}

/// One revision recorded from the folder as it stands.
fn record_folder(
    store: &mut Store,
    base: &Path,
    parents: Vec<RevisionId>,
    message: &str,
) -> historica::record::Recorded {
    let mut platform = Platform;
    let working = Working::read(base, store.skipped()).expect("the folder");
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
        },
        &mut platform,
    )
    .expect("recording")
}

#[test]
fn a_redaction_changes_no_merge_result_except_at_the_forgotten_items() {
    // The claim decision 0014 says is worth holding the implementation to:
    // same bytes outside the forgotten runs, same attribution of every
    // surviving item to the revision that wrote it.
    let base = scratch("merge");
    let mut store = Store::init(base.join("history")).expect("a new store");

    fs::write(base.join("notes.md"), "a\nb\nc\n").expect("a file");
    let root = record_folder(&mut store, &base, Vec::new(), "Root");
    fs::write(base.join("notes.md"), "a\nb\nleft one\nleft two\nc\n").expect("a file");
    let left = record_folder(&mut store, &base, vec![root.revision], "Left");
    fs::write(base.join("notes.md"), "a\nright\nb\nc\n").expect("a file");
    let right = record_folder(&mut store, &base, vec![root.revision], "Right");

    let file = *root.plan.added.keys().next().expect("the file");
    let heads = [left.revision, right.revision];
    let before = store
        .merged_content_of(&heads, &file)
        .expect("a merge before forgetting");

    // Forget `left one`, which sits at line 4 of the file at `left`.
    assert_eq!(
        store
            .content(&left.revision, &file)
            .expect("content at left")
            .text(),
        "a\nb\nleft one\nleft two\nc\n"
    );
    let plan = store
        .forget(&Forgetting {
            revision: left.revision,
            file,
            extent: Extent::Lines { first: 3, last: 3 },
        })
        .expect("forgetting");
    assert!(!plan.is_empty());

    let store = Store::open(store.root()).expect("reopening the redacted store");
    let after = store
        .merged_content_of(&heads, &file)
        .expect("a merge after forgetting");

    // Attribution is untouched, and so is every item outside the span.
    assert_eq!(before.origins, after.origins);
    assert_eq!(before.contested, after.contested);
    assert_eq!(before.state.len(), after.state.len());
    let mut differing = Vec::new();
    for (position, (was, is)) in before
        .state
        .items()
        .iter()
        .zip(after.state.items())
        .enumerate()
    {
        if was == is {
            continue;
        }
        assert!(
            is.forgotten,
            "item {position} changed without being forgotten"
        );
        assert_eq!(was.terminated, is.terminated, "shape moved at {position}");
        differing.push(was.text.clone());
    }
    assert_eq!(differing, vec!["left one".to_owned()]);

    // `check` accepts the redacted store, with the redaction as a note.
    let report = Store::check(store.root());
    assert!(report.is_ok());
    assert!(
        report
            .notes()
            .any(|finding| matches!(finding, Finding::Forgotten { .. }))
    );
}

#[test]
fn two_forgetting_documents_union_to_the_more_forgotten_result_either_way() {
    // Decision 0014: an item is forgotten if any held forgetting document
    // forgets it. Order-independent, and never less thorough than the most
    // thorough redaction that has arrived.
    let original = OperationDocument::parse(b"historica\n\ninsert 0\n+one\n+two\n+three\n")
        .expect("a document");
    let target = original.id();

    let mut narrow = original.clone();
    narrow.forgets = Some(target);
    narrow.operations[0].items[1] = narrow.operations[0].items[1].forgetting();
    let mut wide = original.clone();
    wide.forgets = Some(target);
    wide.operations[0].items[1] = wide.operations[0].items[1].forgetting();
    wide.operations[0].items[2] = wide.operations[0].items[2].forgetting();

    let one_way = stand_in(None, &[&narrow, &wide]).expect("a stand-in");
    let other_way = stand_in(None, &[&wide, &narrow]).expect("a stand-in");
    assert_eq!(one_way.operations, other_way.operations);
    assert!(one_way.operations[0].items[1].forgotten);
    assert!(one_way.operations[0].items[2].forgotten);
    assert!(!one_way.operations[0].items[0].forgotten);

    // With the original resurrected by sync, the redaction still wins.
    let over_original = stand_in(Some(&original), &[&wide]).expect("a stand-in");
    assert!(over_original.operations[0].items[2].forgotten);
    assert_eq!(over_original.operations[0].items[0].text, "one");
}

#[test]
fn a_forgetting_document_round_trips() {
    let bytes = b"historica\nforgets 6397b3a4b3b8abd444da81f2f731dd67c4f5bcea5dc03c4e8141783d1f1b4c53\n\ndelete 3 1\n-Nothing here chooses a document syntax yet.\ninsert 4\n\\ forgotten\n\\ forgotten\n";
    let document = OperationDocument::parse(bytes).expect("decision 0014's own example");
    assert!(document.forgets.is_some());
    assert!(
        document.operations[1]
            .items
            .iter()
            .all(|item| item.forgotten)
    );
    assert!(!document.operations[0].items[0].forgotten);
    assert_eq!(document.write(), bytes.to_vec());
}

#[test]
fn the_header_states_the_format_and_forgetting_never_moves_it() {
    let directory = scratch("version");
    assert!(run(&directory, &["init"]).status.success());
    let header = || {
        fs::read_to_string(directory.join("history/historica.txt"))
            .expect("the header")
            .lines()
            .next()
            .expect("a format line")
            .to_owned()
    };
    assert_eq!(header(), "historica");

    write(&directory, "notes.md", "one\ntwo\n");
    let first = out(&directory, &["record", "-m", "Start"]);
    write(&directory, "notes.md", "one\ntwo\nthree\n");
    out(&directory, &["record", "-m", "More"]);
    out(
        &directory,
        &["forget", &digest_in(&first), "notes.md", "--lines", "2"],
    );
    assert_eq!(header(), "historica", "one spelling, before and after");
}

/// The binary file `write` cannot make: decision 0017 sniffs a file's kind
/// once, at `add`, and NUL is the byte that decides it.
fn write_bytes(directory: &Path, path: &str, bytes: &[u8]) {
    fs::write(directory.join(path), bytes).expect("writing a file");
}

/// Where one file in `operations/` sits, found by walking for its name.
fn filed(directory: &Path, name: &str) -> PathBuf {
    let operations = directory.join("history/operations");
    let mut pending = vec![operations.clone()];
    while let Some(next) = pending.pop() {
        for entry in fs::read_dir(&next)
            .expect("a directory")
            .filter_map(Result::ok)
        {
            let path = entry.path();
            if path.is_dir() {
                pending.push(path);
            } else if path.file_name().and_then(|found| found.to_str()) == Some(name) {
                return path;
            }
        }
    }
    panic!("no file called {name} under `operations/`");
}

#[test]
fn forgetting_a_payload_destroys_it_whole_and_says_how_much_there_was() {
    let directory = scratch("payload");
    assert!(run(&directory, &["init"]).status.success());
    write_bytes(
        &directory,
        "photo.png",
        b"\x89PNG\x00the secret picture\x00",
    );
    write(&directory, "notes.md", "the entry it belongs to\n");
    let first = out(&directory, &["record", "-m", "Start a journal"]);

    let said = out(&directory, &["forget", &digest_in(&first), "photo.png"]);
    assert!(said.contains("wrote a forgetting document"), "{said}");
    assert!(said.contains("destroyed history/"), "{said}");
    assert!(said.contains("only the content is destroyed"), "{said}");

    // The bytes are gone from the store, and the entry beside them is not.
    assert!(!contains(&store_bytes(&directory), "the secret picture"));
    assert!(contains(
        &store_bytes(&directory),
        "the entry it belongs to"
    ));

    // What stands where the payload was: a document at the payload's own
    // name, so a person opening the revision's folder finds an answer rather
    // than an absence.
    let stood = fs::read_to_string(filed(&directory, "photo.png.ops.txt"))
        .expect("the stand-in, filed where the payload was");
    assert!(stood.starts_with("historica\nforgets "), "{stood}");
    assert!(stood.ends_with("\nlength 24\n"), "{stood}");

    // A person asking for the file is told what became of it, and how much of
    // it there was — never that it has not arrived yet.
    let refused = run(&directory, &["cat", &digest_in(&first), "photo.png"]);
    assert!(!refused.status.success());
    let why = String::from_utf8(refused.stderr).expect("printed text");
    assert!(why.contains("was forgotten"), "{why}");
    assert!(why.contains("24 bytes destroyed"), "{why}");

    // A forgotten store passes `check`, and the note says destroyed rather
    // than not yet delivered — decision 0044's `bytes` branch, which said in
    // as many words that it was waiting for this.
    let checked = run(&directory, &["check"]);
    assert!(
        checked.status.success(),
        "{}",
        String::from_utf8_lossy(&checked.stdout)
    );
    let report = String::from_utf8(checked.stdout).expect("printed text");
    assert!(report.contains("whose bytes were destroyed"), "{report}");
    assert!(!report.contains("may not have arrived"), "{report}");

    // Forgetting twice is a no-op, here as for lines: every quote of a
    // payload is its digest, so one destruction covered all of them.
    let again = out(&directory, &["forget", &digest_in(&first), "photo.png"]);
    assert!(again.contains("already forgotten"), "{again}");
}

#[test]
fn the_two_extents_are_refused_of_the_wrong_kind_of_file() {
    let directory = scratch("extents");
    assert!(run(&directory, &["init"]).status.success());
    write_bytes(&directory, "photo.png", b"\x89PNG\x00picture\x00");
    write(&directory, "notes.md", "one\ntwo\nthree\n");
    let first = out(&directory, &["record", "-m", "Start"]);
    let at = digest_in(&first);

    // Decision 0017 fixed each file's kind when it was added, so neither
    // refusal is a guess about content — and each names the spelling that
    // would have worked.
    let span_of_bytes = run(&directory, &["forget", &at, "photo.png", "--lines", "1"]);
    assert!(!span_of_bytes.status.success());
    let why = String::from_utf8(span_of_bytes.stderr).expect("printed text");
    assert!(why.contains("bytes rather than lines"), "{why}");

    let whole_of_lines = run(&directory, &["forget", &at, "notes.md"]);
    assert!(!whole_of_lines.status.success());
    let why = String::from_utf8(whole_of_lines.stderr).expect("printed text");
    assert!(why.contains("lines rather than bytes"), "{why}");
    assert!(why.contains("--lines 1..3"), "{why}");
}

#[test]
fn each_version_of_a_file_of_bytes_is_forgotten_on_its_own() {
    let directory = scratch("versions");
    assert!(run(&directory, &["init"]).status.success());
    write_bytes(&directory, "photo.png", b"\x89PNG\x00first picture\x00");
    let first = out(&directory, &["record", "-m", "Start"]);
    write_bytes(&directory, "photo.png", b"\x89PNG\x00second picture\x00");
    out(&directory, &["record", "-m", "Crop"]);

    // A file of bytes is replaced whole, so each version is its own payload
    // under its own digest. Forgetting one is not forgetting the file, and
    // the command that leaves the rest legible says so.
    let said = out(&directory, &["forget", &digest_in(&first), "photo.png"]);
    assert!(
        said.contains("1 other version elsewhere in its history"),
        "{said}"
    );
    assert!(!contains(&store_bytes(&directory), "first picture"));
    assert!(contains(&store_bytes(&directory), "second picture"));

    let said = out(&directory, &["forget", "head", "photo.png"]);
    assert!(!said.contains("other version"), "{said}");
    assert!(!contains(&store_bytes(&directory), "second picture"));
    assert!(run(&directory, &["check"]).status.success());
}
