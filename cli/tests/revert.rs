//! `revert`, exercised as a person exercises it: decision 0090.
//!
//! A mistake found after more work was recorded on top of it is taken back
//! by a new revision on the head, and everything recorded since stays. The
//! command writes the folder and prints the `record` that writes the undoing
//! down; these tests follow that command as a person would.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

/// A repository with nothing recorded, for one test.
fn repository(test: &str) -> PathBuf {
    let path = Path::new(env!("CARGO_TARGET_TMPDIR")).join(format!("revert-{test}"));
    let _ = fs::remove_dir_all(&path);
    fs::create_dir_all(&path).expect("a scratch directory");
    assert!(run(&path, &["init"]).status.success());
    path
}

/// Run the binary against `directory` with an author stated, which is how a
/// script records (decision 0010).
fn run(directory: &Path, arguments: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_historica"))
        .env(
            "HISTORICA_CACHE_DIR",
            concat!(env!("CARGO_TARGET_TMPDIR"), "/caches"),
        )
        .env("HISTORICA_AUTHOR", "Adam Harris <adam@example.com>")
        .arg("-C")
        .arg(directory)
        .args(arguments)
        .output()
        .expect("the binary this test crate builds")
}

/// What a command that succeeded printed.
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

/// What a command that should have been refused said.
fn refused(directory: &Path, arguments: &[&str]) -> String {
    let output = run(directory, arguments);
    assert!(
        !output.status.success(),
        "`{}` should have been refused: {}",
        arguments.join(" "),
        String::from_utf8_lossy(&output.stdout)
    );
    String::from_utf8(output.stderr).expect("printed text")
}

fn write(directory: &Path, path: &str, text: &str) {
    let file = directory.join(path);
    if let Some(parent) = file.parent() {
        fs::create_dir_all(parent).expect("a directory");
    }
    fs::write(file, text).expect("writing a file");
}

fn read(directory: &Path, path: &str) -> String {
    fs::read_to_string(directory.join(path)).expect("reading a file")
}

/// Record the folder, and give back the revision written.
fn record(directory: &Path, message: &str) -> String {
    let said = out(directory, &["record", "-m", message]);
    said.lines()
        .find_map(|line| line.strip_prefix("recorded "))
        .and_then(|rest| rest.split_whitespace().nth(2))
        .expect("the revision `record` names")
        .to_owned()
}

/// The `record` command a revert printed, as the arguments it takes.
///
/// Read back the way a shell would read the single quotes the command uses.
fn printed_record(said: &str) -> Vec<String> {
    let line = said
        .lines()
        .find_map(|line| line.trim().strip_prefix("historica "))
        .unwrap_or_else(|| panic!("a `record` to run in\n{said}"));
    let mut arguments = Vec::new();
    let mut current = String::new();
    let mut quoted = false;
    let mut started = false;
    let mut characters = line.chars().peekable();
    while let Some(c) = characters.next() {
        match c {
            '\'' if quoted => quoted = false,
            '\'' => {
                quoted = true;
                started = true;
            }
            '\\' if !quoted => {
                if let Some(next) = characters.next() {
                    current.push(next);
                }
            }
            ' ' if !quoted => {
                if started {
                    arguments.push(std::mem::take(&mut current));
                    started = false;
                }
            }
            other => {
                current.push(other);
                started = true;
            }
        }
    }
    if started {
        arguments.push(current);
    }
    arguments
}

/// Follow a revert all the way: write the folder, then run the printed record.
fn revert_and_record(directory: &Path, target: &str) -> String {
    let said = out(directory, &["revert", target]);
    let arguments = printed_record(&said);
    let arguments: Vec<&str> = arguments.iter().map(String::as_str).collect();
    out(directory, &arguments)
}

/// Every recorded file, with its bytes: what a refusal must leave as it was.
fn recorded_history(directory: &Path) -> Vec<(PathBuf, Vec<u8>)> {
    let mut found = Vec::new();
    let mut looking = vec![
        directory.join("history/revisions"),
        directory.join("history/operations"),
    ];
    while let Some(at) = looking.pop() {
        let Ok(entries) = fs::read_dir(&at) else {
            continue;
        };
        for entry in entries.flatten() {
            let path = entry.path();
            if path.is_dir() {
                looking.push(path);
            } else {
                found.push((path.clone(), fs::read(&path).expect("a recorded file")));
            }
        }
    }
    found.sort();
    found
}

/// The whole point: a mistake two revisions back is taken out, and the work
/// recorded after it — in the same file and beside it — stays.
#[test]
fn a_mistake_is_undone_and_the_work_after_it_stays() {
    let directory = repository("keeps-later-work");
    write(&directory, "notes.md", "one\ntwo\nthree\nfour\nfive\n");
    write(&directory, "keep.md", "keep\n");
    record(&directory, "Start");

    write(
        &directory,
        "notes.md",
        "one\nTWO, WRONGLY\nthree\nfour\nfive\n",
    );
    write(&directory, "junk.md", "junk\n");
    fs::remove_file(directory.join("keep.md")).expect("a delete");
    let mistake = record(&directory, "An edit that was a mistake");

    write(
        &directory,
        "notes.md",
        "one\nTWO, WRONGLY\nthree\nfour\nfive\nsix\n",
    );
    write(&directory, "later.md", "later\n");
    record(&directory, "Later work");

    let said = out(&directory, &["revert", &mistake]);
    assert!(said.contains("record it with"), "{said}");
    assert_eq!(
        read(&directory, "notes.md"),
        "one\ntwo\nthree\nfour\nfive\nsix\n",
        "the mistaken line goes back and the line written after it stays"
    );
    assert_eq!(
        read(&directory, "keep.md"),
        "keep\n",
        "what it dropped returns"
    );
    assert!(!directory.join("junk.md").exists(), "what it added goes");
    assert_eq!(read(&directory, "later.md"), "later\n");

    let arguments = printed_record(&said);
    let arguments: Vec<&str> = arguments.iter().map(String::as_str).collect();
    let recorded = out(&directory, &arguments);
    assert!(recorded.contains("recorded"), "{recorded}");

    let log = out(&directory, &["log", "--limit", "1"]);
    assert!(
        log.contains("Undo \"An edit that was a mistake\""),
        "the history says what was undone: {log}"
    );
    let checked = out(&directory, &["check"]);
    assert!(checked.contains("nothing to report"), "{checked}");
    let status = out(&directory, &["status"]);
    assert!(
        status.contains("nothing here differs"),
        "the folder is the head again: {status}"
    );

    // And the mistake is still in the history, where anyone can read it.
    let shown = out(&directory, &["cat", &mistake, "notes.md"]);
    assert!(shown.contains("TWO, WRONGLY"), "{shown}");
}

/// The printed `record` names only what the undoing touched, so unrecorded
/// work elsewhere in the folder is not swept into it.
#[test]
fn unrecorded_work_elsewhere_stays_unrecorded() {
    let directory = repository("elsewhere");
    write(&directory, "a.md", "a\n");
    write(&directory, "b.md", "b\n");
    record(&directory, "Start");
    write(&directory, "a.md", "a, wrongly\n");
    let mistake = record(&directory, "Mistake");

    write(&directory, "b.md", "b, half written\n");
    revert_and_record(&directory, &mistake);

    assert_eq!(read(&directory, "a.md"), "a\n");
    assert_eq!(read(&directory, "b.md"), "b, half written\n");
    let status = out(&directory, &["status"]);
    assert!(
        status.contains("b.md") && !status.contains("a.md"),
        "only the half-written file still differs: {status}"
    );
}

/// A rename the mistake made is put back as a rename, so the file keeps its
/// identity and its history.
#[test]
fn a_rename_goes_back_as_the_same_file() {
    let directory = repository("rename");
    write(&directory, "draft.md", "draft\n");
    record(&directory, "Start");
    let before = out(&directory, &["files", "head"]);

    let renamed = out(
        &directory,
        &["record", "--move", "draft.md=final.md", "-m", "Rename"],
    );
    assert!(renamed.contains("moved"), "{renamed}");
    let rename = out(&directory, &["log", "--limit", "1"])
        .split_whitespace()
        .nth(1)
        .expect("a digest")
        .to_owned();
    write(&directory, "final.md", "draft\nmore\n");
    record(&directory, "More");

    revert_and_record(&directory, &rename);
    assert_eq!(read(&directory, "draft.md"), "draft\nmore\n");
    assert!(!directory.join("final.md").exists());
    assert_eq!(
        out(&directory, &["files", "head"])
            .split_whitespace()
            .last()
            .map(str::to_owned),
        before.split_whitespace().last().map(str::to_owned),
        "the same file identifier, at its old path"
    );
}

/// Where later work changed the very lines the mistake wrote, which to keep
/// is a person's call: the revert refuses, and nothing is written.
#[test]
fn work_that_met_the_mistake_refuses_and_writes_nothing() {
    let directory = repository("contested");
    write(&directory, "f.md", "one\ntwo\nthree\n");
    record(&directory, "Start");
    write(&directory, "f.md", "one\nTWO\nthree\n");
    let mistake = record(&directory, "Mistake");
    write(&directory, "f.md", "one\nTWO!\nthree\n");
    record(&directory, "On top of it");

    let history = recorded_history(&directory);
    let refusal = refused(&directory, &["revert", &mistake]);
    assert!(refusal.contains("f.md"), "{refusal}");
    assert!(refusal.contains("nothing was written"), "{refusal}");
    assert_eq!(read(&directory, "f.md"), "one\nTWO!\nthree\n");
    assert_eq!(history, recorded_history(&directory));
}

/// A file the mistake added and later work edited is not taken away: that
/// would take the later work with it.
#[test]
fn a_file_edited_since_it_was_added_is_not_taken_away() {
    let directory = repository("added-then-edited");
    write(&directory, "a.md", "a\n");
    record(&directory, "Start");
    write(&directory, "new.md", "new\n");
    let mistake = record(&directory, "Add");
    write(&directory, "new.md", "new\nand more\n");
    record(&directory, "More");

    let refusal = refused(&directory, &["revert", &mistake]);
    assert!(refusal.contains("new.md"), "{refusal}");
    assert!(directory.join("new.md").exists());
}

/// The folder has to hold the head where the undoing writes: what is there
/// otherwise is somebody's unrecorded work.
#[test]
fn unrecorded_work_where_the_undoing_writes_refuses() {
    let directory = repository("in-the-way");
    write(&directory, "a.md", "a\n");
    record(&directory, "Start");
    write(&directory, "a.md", "a, wrongly\n");
    let mistake = record(&directory, "Mistake");
    write(&directory, "a.md", "a, wrongly, and unrecorded\n");

    let refusal = refused(&directory, &["revert", &mistake]);
    assert!(refusal.contains("a.md"), "{refusal}");
    assert_eq!(read(&directory, "a.md"), "a, wrongly, and unrecorded\n");
}

/// A dry run says what the undoing would record and writes nothing.
#[test]
fn a_dry_run_writes_nothing() {
    let directory = repository("dry-run");
    write(&directory, "a.md", "a\n");
    record(&directory, "Start");
    write(&directory, "a.md", "b\n");
    let mistake = record(&directory, "Mistake");

    let said = out(&directory, &["revert", &mistake, "--dry-run"]);
    assert!(said.contains("edited  a.md"), "{said}");
    assert!(said.contains("historica record a.md"), "{said}");
    assert_eq!(read(&directory, "a.md"), "b\n");
}

/// Undone once, there is nothing left to undo, and saying so succeeds.
#[test]
fn undoing_twice_finds_nothing_left() {
    let directory = repository("twice");
    write(&directory, "a.md", "a\n");
    record(&directory, "Start");
    write(&directory, "a.md", "b\n");
    let mistake = record(&directory, "Mistake");
    revert_and_record(&directory, &mistake);

    let said = out(&directory, &["revert", &mistake]);
    assert!(said.contains("nothing of"), "{said}");
    assert_eq!(read(&directory, "a.md"), "a\n");
}

/// The first revision can be undone too: what it added goes, where nothing
/// since has changed it.
#[test]
fn the_first_revision_can_be_undone() {
    let directory = repository("root");
    write(&directory, "a.md", "a\n");
    let first = record(&directory, "Start");
    write(&directory, "b.md", "b\n");
    record(&directory, "Second");

    revert_and_record(&directory, &first);
    assert!(!directory.join("a.md").exists());
    assert_eq!(read(&directory, "b.md"), "b\n");
}

/// A target nobody typed is a usage error, not a guess.
#[test]
fn revert_needs_a_target() {
    let directory = repository("no-target");
    let refusal = refused(&directory, &["revert"]);
    assert!(refusal.contains("revert"), "{refusal}");
}
