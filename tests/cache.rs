//! `history/cache/`, held to the one promise decision 0003 makes about it.
//!
//! > Binary indexes and snapshots may eventually exist as disposable caches,
//! > but deleting every cache must lose neither information nor meaning.
//!
//! So every test here does the same thing twice — once with whatever the cache
//! holds and once without it — and insists the two answers are the same. A
//! cache that changes an answer is not a cache, and the tests that corrupt one
//! on purpose are the ones that say so.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

/// A fresh directory for one test, inside the target directory.
fn scratch(test: &str) -> PathBuf {
    let path = Path::new(env!("CARGO_TARGET_TMPDIR")).join(format!("cache-{test}"));
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

fn stdout(directory: &Path, arguments: &[&str]) -> String {
    let output = run(directory, arguments);
    assert!(
        output.status.success(),
        "`{}` failed: {}",
        arguments.join(" "),
        String::from_utf8_lossy(&output.stderr)
    );
    String::from_utf8(output.stdout).expect("printed text")
}

/// How many revisions to record.
///
/// Comfortably past the threshold at which an answer is worth keeping, so that
/// a walk of this history is certain to leave an entry behind. The store's own
/// constant is deliberately not exported: what is being tested is that the
/// cache is invisible, and a test that knew the number would be testing the
/// number.
const REVISIONS: usize = 40;

/// A store of one file with a line rewritten per revision.
fn recorded(test: &str) -> PathBuf {
    let directory = scratch(test);
    assert!(run(&directory, &["init"]).status.success());
    for revision in 0..=REVISIONS {
        let text: String = (1..=12)
            .map(|line| {
                if line == revision % 12 + 1 {
                    format!("line {line}, as revision {revision} left it\n")
                } else {
                    format!("line {line}\n")
                }
            })
            .collect();
        fs::write(directory.join("notes.txt"), text).expect("writing the file");
        let message = format!("revision {revision}");
        assert!(
            run(&directory, &["record", "-m", &message])
                .status
                .success(),
            "recording revision {revision}"
        );
    }
    directory
}

fn cache_of(directory: &Path) -> PathBuf {
    directory.join("history/cache")
}

/// Every entry in `cache/`: a file named by a digest, and nothing else.
fn entries(directory: &Path) -> Vec<PathBuf> {
    let Ok(read) = fs::read_dir(cache_of(directory)) else {
        return Vec::new();
    };
    let mut found: Vec<PathBuf> = read
        .filter_map(Result::ok)
        .map(|entry| entry.path())
        .filter(|path| {
            path.file_name()
                .and_then(|name| name.to_str())
                .is_some_and(|name| name.len() == 64 && name.chars().all(|c| c.is_ascii_hexdigit()))
        })
        .collect();
    found.sort();
    found
}

fn head(directory: &Path) -> String {
    stdout(directory, &["log"])
        .split_whitespace()
        .next()
        .expect("a head")
        .to_owned()
}

#[test]
fn walking_a_history_leaves_an_entry_and_reading_it_again_agrees() {
    let directory = recorded("kept");
    let head = head(&directory);

    let first = stdout(&directory, &["cat", &head, "notes.txt"]);
    assert!(
        !entries(&directory).is_empty(),
        "a walk of {REVISIONS} revisions should have left something to stop at"
    );

    // The same question, now that there is something to answer it with.
    assert_eq!(stdout(&directory, &["cat", &head, "notes.txt"]), first);
    assert!(first.contains(&format!("as revision {REVISIONS} left it")));
}

#[test]
fn deleting_every_entry_loses_neither_information_nor_meaning() {
    let directory = recorded("disposable");
    let head = head(&directory);

    let with = stdout(&directory, &["cat", &head, "notes.txt"]);
    let files = stdout(&directory, &["files", &head]);
    let status = stdout(&directory, &["status"]);
    assert!(!entries(&directory).is_empty());

    // Decision 0003's promise, tested the only way it can be: take it all
    // away, ask again, and compare.
    fs::remove_dir_all(cache_of(&directory)).expect("deleting the whole cache");
    assert_eq!(stdout(&directory, &["cat", &head, "notes.txt"]), with);
    assert_eq!(stdout(&directory, &["files", &head]), files);
    assert_eq!(stdout(&directory, &["status"]), status);
    assert!(run(&directory, &["check"]).status.success());
}

#[test]
fn an_entry_that_is_not_what_it_is_named_is_refused_rather_than_believed() {
    let directory = recorded("corrupt");
    let head = head(&directory);
    let expected = stdout(&directory, &["cat", &head, "notes.txt"]);

    // An entry is named by the digest of its own bytes, exactly as every other
    // file in the store is. Rewriting one without renaming it is the case a
    // cache has to survive — a truncated write, an older version of this
    // program, a person with an editor — and the answer must come from the
    // history rather than from the file.
    let mut damaged = 0;
    for entry in entries(&directory) {
        fs::write(&entry, b"this is not that file\n").expect("damaging an entry");
        damaged += 1;
    }
    assert!(damaged > 0, "there should have been an entry to damage");

    assert_eq!(stdout(&directory, &["cat", &head, "notes.txt"]), expected);
    assert!(run(&directory, &["check"]).status.success());
}

#[test]
fn an_entry_holding_a_different_file_is_never_reached() {
    let directory = recorded("impostor");
    let head = head(&directory);
    let expected = stdout(&directory, &["cat", &head, "notes.txt"]);

    // Bytes that *do* hash to their own name, and so pass every check the
    // cache makes — but which no document states as its result, so nothing
    // ever asks for them. Content addressing is what makes planting one
    // useless rather than dangerous.
    let planted = "some other file entirely\n";
    let name = sha256_hex(planted.as_bytes());
    fs::write(cache_of(&directory).join(&name), planted).expect("planting an entry");

    assert_eq!(stdout(&directory, &["cat", &head, "notes.txt"]), expected);
}

#[test]
fn forgetting_destroys_the_copies_a_cache_would_otherwise_keep() {
    let directory = recorded("forgotten");
    let head = head(&directory);

    let secret = "line 3\n";
    let before = stdout(&directory, &["cat", &head, "notes.txt"]);
    assert!(before.contains(secret));
    assert!(
        entries(&directory)
            .iter()
            .any(|entry| fs::read_to_string(entry).is_ok_and(|held| held.contains(secret))),
        "the cache should be holding the file that is about to be redacted"
    );

    let output = run(
        &directory,
        &["forget", &head, "notes.txt", "--lines", "3..3"],
    );
    assert!(
        output.status.success(),
        "forgetting failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );

    // Decision 0014 destroys bytes. A derived copy of them is still a copy,
    // so `cache/` goes with the originals — and nothing that survives it
    // holds the line either.
    for entry in entries(&directory) {
        let held = fs::read_to_string(&entry).expect("a surviving entry is readable");
        assert!(
            !held.contains(secret),
            "{} still holds the forgotten line",
            entry.display()
        );
    }
    assert!(!stdout(&directory, &["cat", &head, "notes.txt"]).contains(secret));
}

/// The catalogue file, which decision 0036 puts in `cache/` under a name.
fn catalogue_of(directory: &Path) -> PathBuf {
    cache_of(directory).join("operations.txt")
}

#[test]
fn the_catalogue_is_written_and_then_taken() {
    let directory = recorded("catalogue-kept");
    let head = head(&directory);
    let first = stdout(&directory, &["cat", &head, "notes.txt"]);

    let catalogue = catalogue_of(&directory);
    let held = fs::read_to_string(&catalogue).expect("a catalogue");
    assert!(held.starts_with("historica-catalogue-"), "{held}");
    // One line per file in `operations/`, and every one of them names a path
    // under it — a catalogue that named anything else would be sending a
    // reader somewhere the store does not keep its documents.
    let lines: Vec<&str> = held.lines().skip(1).collect();
    assert!(!lines.is_empty());
    for line in &lines {
        let path = line.splitn(3, ' ').nth(2).expect("a path on every line");
        assert!(path.starts_with("operations/"), "{line}");
        assert!(
            directory.join("history").join(path).exists(),
            "the catalogue names a file that is there: {line}"
        );
    }

    // Reading again with it in place is the same answer, and leaves it alone:
    // nothing changed, so nothing is rewritten.
    assert_eq!(stdout(&directory, &["cat", &head, "notes.txt"]), first);
    assert_eq!(
        fs::read_to_string(&catalogue).expect("still a catalogue"),
        held
    );
}

#[test]
fn deleting_the_catalogue_loses_neither_information_nor_meaning() {
    let directory = recorded("catalogue-disposable");
    let head = head(&directory);

    let with = stdout(&directory, &["cat", &head, "notes.txt"]);
    let files = stdout(&directory, &["files", &head]);
    let status = stdout(&directory, &["status"]);

    fs::remove_file(catalogue_of(&directory)).expect("deleting the catalogue");
    assert_eq!(stdout(&directory, &["cat", &head, "notes.txt"]), with);
    assert_eq!(stdout(&directory, &["files", &head]), files);
    assert_eq!(stdout(&directory, &["status"]), status);
    assert!(run(&directory, &["check"]).status.success());
    // And it is back, because the pass that answered without it wrote it.
    assert!(catalogue_of(&directory).exists());
}

#[test]
fn a_catalogue_that_lies_about_where_a_document_is_changes_no_answer() {
    let directory = recorded("catalogue-lying");
    let head = head(&directory);
    let with = stdout(&directory, &["cat", &head, "notes.txt"]);

    // Every path in the catalogue pointed at the wrong file. The path set it
    // names is still the set the directory holds, so nothing about the
    // *shape* of it is suspicious — what refuses this is the rule that a
    // lookup hashes what it reads before believing it.
    let catalogue = catalogue_of(&directory);
    let held = fs::read_to_string(&catalogue).expect("a catalogue");
    let mut lines = held.lines();
    let header = lines.next().expect("a header");
    let rows: Vec<&str> = lines.collect();
    let mut swapped = String::from(header);
    swapped.push('\n');
    for (index, line) in rows.iter().enumerate() {
        let (digest, rest) = line.split_once(' ').expect("a digest");
        let (forgets, _) = rest.split_once(' ').expect("a forgets field");
        // Somebody else's path, from the row after this one.
        let elsewhere = rows[(index + 1) % rows.len()]
            .splitn(3, ' ')
            .nth(2)
            .expect("a path");
        swapped.push_str(&format!("{digest} {forgets} {elsewhere}\n"));
    }
    fs::write(&catalogue, swapped).expect("planting it");

    assert_eq!(stdout(&directory, &["cat", &head, "notes.txt"]), with);
    assert!(run(&directory, &["check"]).status.success());
}

#[test]
fn a_document_recorded_after_the_catalogue_was_written_is_still_found() {
    let directory = recorded("catalogue-appended");
    let before = head(&directory);
    // Reading writes the catalogue; recording then adds a file it does not
    // name. The next reader has to notice, which is the whole of what makes a
    // catalogue safe to keep.
    let _ = stdout(&directory, &["cat", &before, "notes.txt"]);
    assert!(catalogue_of(&directory).exists());

    fs::write(directory.join("notes.txt"), "a line nobody had written\n")
        .expect("editing the file");
    assert!(
        run(&directory, &["record", "-m", "after the catalogue"])
            .status
            .success()
    );
    let head = head(&directory);
    assert_eq!(
        stdout(&directory, &["cat", &head, "notes.txt"]),
        "a line nobody had written\n"
    );
    assert!(run(&directory, &["check"]).status.success());
}

#[test]
fn filing_a_flat_store_costs_a_catalogue_and_never_an_answer() {
    // Decision 0041 moves every file in a flat store one level down, which is
    // exactly the condition 0036 refuses to believe a catalogue under: the
    // paths it names are no longer the paths the directory holds. What that
    // costs is one pass over `operations/`; what it must never cost is an
    // answer, so every one of them is the same before and after.
    let directory = recorded("catalogue-filed");
    let head = head(&directory);
    let before = stdout(&directory, &["cat", &head, "notes.txt"]);
    let files = stdout(&directory, &["files", &head]);

    let operations = directory.join("history/operations");
    let months: Vec<PathBuf> = fs::read_dir(&operations)
        .expect("the operations directory")
        .filter_map(Result::ok)
        .map(|entry| entry.path())
        .collect();
    assert!(!months.is_empty(), "the writer filed nothing");
    let held = fs::read_to_string(catalogue_of(&directory)).expect("a catalogue");
    for month in &months {
        let name = month.file_name().expect("a month").to_string_lossy();
        assert!(
            held.lines()
                .skip(1)
                .all(|line| line.contains(&format!("operations/{name}/"))),
            "a filed path is just a longer string in the set: {held}"
        );
        // Flattened, as a store written before this version would have been.
        for entry in fs::read_dir(month).expect("the month").flatten() {
            fs::rename(entry.path(), operations.join(entry.file_name())).expect("flattening");
        }
        fs::remove_dir(month).expect("the emptied month");
    }

    // The catalogue on disk still names the old paths, and every answer holds.
    assert_eq!(stdout(&directory, &["cat", &head, "notes.txt"]), before);
    assert_eq!(stdout(&directory, &["files", &head]), files);
    assert!(run(&directory, &["arrange"]).status.success());
    assert_eq!(stdout(&directory, &["cat", &head, "notes.txt"]), before);
    assert_eq!(stdout(&directory, &["files", &head]), files);
    assert!(run(&directory, &["check"]).status.success());

    // And the catalogue that came back names where the files now are.
    let after = fs::read_to_string(catalogue_of(&directory)).expect("a catalogue again");
    for line in after.lines().skip(1) {
        let path = line.splitn(3, ' ').nth(2).expect("a path on every line");
        assert!(
            directory.join("history").join(path).exists(),
            "the catalogue names a file that is there: {line}"
        );
    }
}

// ---------------------------------------------------------------------------
// The folder's own catalogue, decision 0043
// ---------------------------------------------------------------------------

/// The catalogue of the working folder, which 0043 puts beside 0036's.
fn folder_catalogue_of(directory: &Path) -> PathBuf {
    cache_of(directory).join("working.txt")
}

/// A store with a file of bytes in it, which is the case that costs: decision
/// 0017 stores one whole, so "has it changed" was both copies read and
/// compared, on every command.
fn photographed(test: &str) -> PathBuf {
    let directory = scratch(test);
    assert!(run(&directory, &["init"]).status.success());
    fs::write(directory.join("notes.txt"), "one\ntwo\n").expect("a file of lines");
    fs::write(directory.join("photo.png"), [0u8, 1, 2, 0, 255, 3]).expect("a file of bytes");
    assert!(
        run(&directory, &["record", "-m", "a journal and a picture"])
            .status
            .success()
    );
    directory
}

#[test]
fn the_folder_catalogue_is_written_and_then_taken() {
    let directory = photographed("folder-kept");
    let first = stdout(&directory, &["status"]);

    let catalogue = folder_catalogue_of(&directory);
    let held = fs::read_to_string(&catalogue).expect("a catalogue of the folder");
    assert!(held.starts_with("historica-working-"), "{held}");
    // One line per path the folder holds, and every one of them names a file
    // that is there — this is a claim about the folder as it stands, never a
    // version of a file kept anywhere else. Decision 0011 refuses an index.
    let mut named: Vec<&str> = held
        .lines()
        .skip(1)
        .map(|line| line.splitn(4, ' ').nth(3).expect("a path on every line"))
        .collect();
    named.sort_unstable();
    assert_eq!(named, ["notes.txt", "photo.png"]);
    for path in &named {
        assert!(directory.join(path).is_file(), "{path}");
    }

    // Asking again is the same answer, and leaves it alone: nothing was
    // learned, so nothing is rewritten.
    assert_eq!(stdout(&directory, &["status"]), first);
    assert_eq!(
        fs::read_to_string(&catalogue).expect("still a catalogue"),
        held
    );
}

#[test]
fn deleting_the_folder_catalogue_loses_neither_information_nor_meaning() {
    let directory = photographed("folder-disposable");
    let head = head(&directory);

    // A folder that differs from the store, so that what is compared is more
    // than "nothing changed" — an edited file, a new one, and a deleted one.
    fs::write(directory.join("notes.txt"), "one\ntwo\nthree\n").expect("editing");
    fs::write(directory.join("later.txt"), "unrecorded\n").expect("a new file");
    fs::write(directory.join("photo.png"), [9u8, 9, 9]).expect("another picture");
    let status = stdout(&directory, &["status"]);
    let differences = stdout(&directory, &["diff"]);
    assert!(folder_catalogue_of(&directory).exists());

    fs::remove_file(folder_catalogue_of(&directory)).expect("deleting the catalogue");
    assert_eq!(stdout(&directory, &["status"]), status);
    assert_eq!(stdout(&directory, &["diff"]), differences);
    assert_eq!(
        stdout(&directory, &["cat", &head, "notes.txt"]),
        "one\ntwo\n"
    );
    assert!(run(&directory, &["check"]).status.success());
    // And it is back, because the pass that answered without it wrote it.
    assert!(folder_catalogue_of(&directory).exists());
}

#[test]
fn a_folder_catalogue_that_lies_about_what_a_file_holds_changes_no_answer() {
    let directory = photographed("folder-lying");
    fs::write(directory.join("notes.txt"), "one\ntwo\nthree\n").expect("editing");
    let status = stdout(&directory, &["status"]);
    let differences = stdout(&directory, &["diff"]);

    // Every line kept — the paths, the sizes and the times are all honest, so
    // nothing about the *shape* of this is suspicious — with the one field the
    // catalogue exists to supply replaced by a digest of somebody else's
    // bytes. What refuses it is 0036's rule one level up: the catalogue says
    // where to look and never what is there, so a read that disagrees with it
    // is the folder disagreeing, and the folder is the authority.
    let catalogue = folder_catalogue_of(&directory);
    let held = fs::read_to_string(&catalogue).expect("a catalogue");
    let mut lies = String::new();
    for (index, line) in held.lines().enumerate() {
        if index == 0 {
            lies.push_str(line);
            lies.push('\n');
            continue;
        }
        let rest = line.split_once(' ').expect("a digest").1;
        lies.push_str(&format!("{} {rest}\n", sha256_hex(b"nothing of the sort")));
    }
    fs::write(&catalogue, &lies).expect("planting it");

    assert_eq!(stdout(&directory, &["status"]), status);
    assert_eq!(stdout(&directory, &["diff"]), differences);
    assert!(run(&directory, &["check"]).status.success());

    // And the lie cost one read of each file rather than one on every command:
    // what the reads found is what the catalogue now says.
    let corrected = fs::read_to_string(&catalogue).expect("a catalogue again");
    assert_ne!(corrected, lies, "a wrong catalogue was left standing");
    assert!(
        corrected
            .lines()
            .skip(1)
            .all(|line| !line.starts_with(&sha256_hex(b"nothing of the sort"))),
        "{corrected}"
    );
}

#[test]
fn a_truncated_folder_catalogue_changes_no_answer() {
    let directory = photographed("folder-truncated");
    fs::write(directory.join("photo.png"), [4u8, 5, 6, 7]).expect("another picture");
    let status = stdout(&directory, &["status"]);

    for damage in ["", "historica-working-1\n", "not a catalogue at all\n"] {
        fs::write(folder_catalogue_of(&directory), damage).expect("damaging it");
        assert_eq!(stdout(&directory, &["status"]), status, "after {damage:?}");
    }
}

#[test]
fn a_file_no_older_than_the_catalogue_is_hashed_rather_than_believed() {
    let directory = photographed("folder-racy");
    let photo = directory.join("photo.png");

    // The racy case, built rather than waited for. A modification time in the
    // future is a time the catalogue's own write cannot get past, so the entry
    // written for this file is not strictly older than the catalogue holding
    // it — which is exactly the shape of a file written twice inside one tick
    // of the filesystem's clock, and is what git calls racily clean.
    let ahead = std::time::SystemTime::now() + std::time::Duration::from_secs(600);
    set_modified(&photo, ahead);
    let status = stdout(&directory, &["status"]);
    assert!(status.contains("nothing here differs"), "{status}");
    let held = fs::read_to_string(folder_catalogue_of(&directory)).expect("a catalogue");
    assert!(
        held.lines().any(|line| line.ends_with(" photo.png")),
        "the catalogue should still hold a line for it: {held}"
    );

    // Now change the bytes without changing anything the directory reports:
    // the same length, and the same modification time the entry recorded. The
    // size cannot tell, and the time cannot tell — the rule is what tells.
    fs::write(&photo, [7u8, 7, 7, 7, 7, 7]).expect("rewriting the picture");
    set_modified(&photo, ahead);
    let said = stdout(&directory, &["status"]);
    assert!(
        said.contains("photo.png"),
        "an unverifiable entry was believed: {said}"
    );
}

/// Set a file's modification time, which is how a race is arranged rather than
/// waited for.
fn set_modified(path: &Path, when: std::time::SystemTime) {
    fs::File::options()
        .write(true)
        .open(path)
        .expect("the file")
        .set_modified(when)
        .expect("setting a modification time");
}

/// `shasum -a 256`, for planting an entry that is honestly named.
fn sha256_hex(bytes: &[u8]) -> String {
    historica::format::digest(bytes).to_string()
}
