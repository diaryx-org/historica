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

/// `shasum -a 256`, for planting an entry that is honestly named.
fn sha256_hex(bytes: &[u8]) -> String {
    historica::format::digest(bytes).to_string()
}
