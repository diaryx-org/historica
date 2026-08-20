//! The command-line front end, exercised as a person exercises it.
//!
//! Every assertion here is about what a person sees: what the commands print,
//! what they exit with, and — for `arrange` — what they leave on disk. The
//! store used throughout is `tests/corpus/tree`, which is a real history of
//! two files with a rename in it, so the answers are checkable by hand.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

/// A fresh directory for one test, inside the target directory.
fn scratch(test: &str) -> PathBuf {
    let path = Path::new(env!("CARGO_TARGET_TMPDIR")).join(format!("cli-{test}"));
    let _ = fs::remove_dir_all(&path);
    fs::create_dir_all(&path).expect("a scratch directory");
    path
}

/// Run the binary against `directory`, as `-C` does.
fn run(directory: &Path, arguments: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_historica"))
        .arg("-C")
        .arg(directory)
        .args(arguments)
        .output()
        .expect("the binary this test crate builds")
}

/// Everything the command printed to stdout, having succeeded.
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

/// Everything the command printed to stderr, having failed.
fn stderr(directory: &Path, arguments: &[&str]) -> String {
    let output = run(directory, arguments);
    assert!(
        !output.status.success(),
        "`{}` should have failed",
        arguments.join(" ")
    );
    String::from_utf8(output.stderr).expect("printed text")
}

fn corpus(kind: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/corpus")
        .join(kind)
}

/// A working copy of one corpus, as a store this binary made.
fn store_from(test: &str, kind: &str) -> PathBuf {
    let directory = scratch(test);
    assert!(run(&directory, &["init"]).status.success());

    // A corpus keeps its documents either in one directory or in the two the
    // store uses; the extension says where each file belongs either way.
    let root = corpus(kind);
    for source in [
        root.clone(),
        root.join("revisions"),
        root.join("operations"),
    ] {
        let Ok(entries) = fs::read_dir(&source) else {
            continue;
        };
        for entry in entries.filter_map(Result::ok) {
            let path = entry.path();
            let into = match path.extension().and_then(|found| found.to_str()) {
                Some("rev") => "revisions",
                Some("ops") => "operations",
                _ => continue,
            };
            let name = path.file_name().expect("a filename");
            fs::copy(&path, directory.join("history").join(into).join(name))
                .expect("copying a corpus file");
        }
    }
    directory
}

#[test]
fn init_makes_the_layout_and_refuses_to_make_it_twice() {
    let directory = scratch("init");
    let made = stdout(&directory, &["init"]);
    assert!(made.starts_with("made a store at "), "{made}");

    for entry in ["revisions", "operations", "names", "cache"] {
        assert!(directory.join("history").join(entry).is_dir(), "{entry}");
    }
    assert_eq!(
        fs::read_to_string(directory.join("history/historica")).expect("the header"),
        "historica-v0\n"
    );

    let again = stderr(&directory, &["init"]);
    assert!(again.contains("already a store"), "{again}");
}

#[test]
fn a_command_outside_a_store_says_which_one_makes_it() {
    let directory = scratch("no-store");
    let complaint = stderr(&directory, &["log"]);
    assert!(complaint.contains("historica init"), "{complaint}");
}

#[test]
fn check_passes_a_good_store_and_fails_one_that_contradicts_itself() {
    let directory = store_from("check", "tree");
    let report = stdout(&directory, &["check"]);
    assert!(report.ends_with("nothing to report\n"), "{report}");

    // A file claiming to be a revision, which does not parse: an error, and
    // therefore a non-zero exit.
    fs::write(
        directory.join("history/revisions/broken.rev"),
        "not a document\n",
    )
    .expect("writing a broken file");
    let output = run(&directory, &["check"]);
    assert_eq!(output.status.code(), Some(1));
    let report = String::from_utf8(output.stdout).expect("printed text");
    assert!(report.contains("error:"), "{report}");
    assert!(report.contains("1 error"), "{report}");
}

#[test]
fn check_takes_a_store_or_what_holds_one() {
    let directory = store_from("check-elsewhere", "tree");
    let parent = directory
        .parent()
        .expect("a scratch directory")
        .to_path_buf();
    let name = directory
        .file_name()
        .expect("a name")
        .to_string_lossy()
        .into_owned();

    let by_repository = stdout(&parent, &["check", &name]);
    let by_store = stdout(&parent, &["check", &format!("{name}/history")]);
    assert!(
        by_repository.ends_with("nothing to report\n"),
        "{by_repository}"
    );
    assert_eq!(by_repository, by_store);
}

#[test]
fn check_reports_a_note_without_failing() {
    let directory = store_from("check-note", "tree");
    // Decision 0006: a sync tool's conflicted copy is a legitimate state.
    let revisions = directory.join("history/revisions");
    fs::copy(
        revisions.join("01-start.rev"),
        revisions.join("01-start (Adam's conflicted copy 2025-08-19).rev"),
    )
    .expect("a conflicted copy");

    let report = stdout(&directory, &["check"]);
    assert!(report.contains("note:"), "{report}");
    assert!(!report.contains("error:"), "{report}");
}

#[test]
fn log_reads_from_the_work_back() {
    let directory = store_from("log", "tree");
    let log = stdout(&directory, &["log"]);

    let summaries: Vec<&str> = log
        .lines()
        .filter(|line| line.starts_with("    ") && !line.contains("@example.com"))
        .map(str::trim)
        .filter(|line| !line.is_empty() && !line.starts_with("added") && !line.starts_with("moved"))
        .collect();
    assert_eq!(
        summaries,
        [
            "dropped 1",
            "Withdraw the entry, keeping what it taught",
            "File the README under docs, and say what it covers",
            "edited 1",
            "Say why a path is not an identity",
            "Start a journal",
        ]
    );

    // The head is marked, and so is the file set each revision touched.
    assert!(log.contains("(head)"), "{log}");
    assert!(log.contains("added 2  edited 2"), "{log}");
}

#[test]
fn log_takes_a_target_and_shows_only_its_ancestry() {
    let directory = store_from("log-target", "tree");
    let everything = stdout(&directory, &["log"]);
    let ancestry = stdout(&directory, &["log", "qpvuntsm"]);

    assert!(everything.contains("Withdraw the entry"), "{everything}");
    assert!(!ancestry.contains("Withdraw the entry"), "{ancestry}");
    assert!(ancestry.contains("Start a journal"), "{ancestry}");
}

#[test]
fn a_target_is_a_bookmark_a_change_or_a_digest() {
    let directory = store_from("targets", "tree");
    let by_change = stdout(&directory, &["show", "mzvwutkl"]);

    let digest = by_change
        .lines()
        .find_map(|line| line.strip_prefix("parent "))
        .expect("the revision names a parent");
    assert!(stdout(&directory, &["show", &digest[..8]]).contains("change kxryzmor"));

    stdout(&directory, &["name", "here", "mzvwutkl"]);
    assert_eq!(stdout(&directory, &["show", "here"]), by_change);

    let refused = stderr(&directory, &["show", "not-a-target"]);
    assert!(refused.contains("neither a change ID"), "{refused}");
}

#[test]
fn show_prints_the_file_as_it_is_stored() {
    let directory = store_from("show", "tree");
    let stored = fs::read(corpus("tree").join("revisions/03-move.rev")).expect("the corpus file");
    let printed = run(&directory, &["show", "mzvwutkl"]);
    assert_eq!(printed.stdout, stored, "`show` must not reformat anything");
}

#[test]
fn show_with_a_path_prints_what_that_revision_did_to_that_file() {
    let directory = store_from("show-ops", "tree");
    let stored =
        fs::read(corpus("tree").join("operations/03-readme.ops")).expect("the corpus file");
    let printed = run(&directory, &["show", "mzvwutkl", "docs/README.md"]);
    assert_eq!(printed.stdout, stored);

    let untouched = stderr(&directory, &["show", "mzvwutkl", "notes/2025-08-19.md"]);
    assert!(untouched.contains("did not edit"), "{untouched}");
}

#[test]
fn files_and_cat_materialise_the_tree_and_its_content() {
    let directory = store_from("files", "tree");

    let before = stdout(&directory, &["files", "qpvuntsm"]);
    assert!(before.contains("README.md"), "{before}");
    assert!(!before.contains("docs/README.md"), "{before}");

    let after = stdout(&directory, &["files", "mzvwutkl"]);
    assert!(after.contains("docs/README.md"), "{after}");

    // A rename keeps the identity, so the file ID is the same on both sides.
    let file = after
        .lines()
        .find(|line| line.starts_with("docs/README.md"))
        .and_then(|line| line.split_whitespace().next_back())
        .expect("a file ID");
    assert!(before.contains(file), "{before}");

    // And the content is reachable by either path, or by the ID itself.
    let content = stdout(&directory, &["cat", "mzvwutkl", "docs/README.md"]);
    assert_eq!(content, stdout(&directory, &["cat", "mzvwutkl", file]));
    assert!(content.starts_with('#'), "{content}");

    let dropped = stdout(&directory, &["files", "nwlxsqot"]);
    assert!(!dropped.contains("notes/"), "{dropped}");
    // History is not a place things are removed from: the content survives the
    // drop even though the file set no longer holds it.
    assert!(!stdout(&directory, &["cat", "mzvwutkl", "notes/2025-08-19.md"]).is_empty());
}

#[test]
fn a_path_that_is_not_there_says_what_lists_the_ones_that_are() {
    let directory = store_from("missing-path", "tree");
    let refused = stderr(&directory, &["cat", "qpvuntsm", "docs/README.md"]);
    assert!(refused.contains("historica files"), "{refused}");
}

#[test]
fn names_records_a_change_by_default_and_a_revision_when_pinned() {
    let directory = store_from("names", "tree");
    assert_eq!(stdout(&directory, &["names"]), "no bookmarks here yet\n");

    stdout(&directory, &["name", "main", "nwlxsqot"]);
    stdout(&directory, &["name", "pinned", "nwlxsqot", "--revision"]);

    let bookmark = fs::read_to_string(directory.join("history/names/main")).expect("the bookmark");
    assert_eq!(bookmark, "change nwlxsqotvkzmuprysltnwxqk\n");
    assert!(
        fs::read_to_string(directory.join("history/names/pinned"))
            .expect("the bookmark")
            .starts_with("revision ")
    );

    let listed = stdout(&directory, &["names"]);
    assert!(listed.contains("main    change nwlxsqot"), "{listed}");
    assert!(listed.contains("pinned  revision "), "{listed}");
}

#[test]
fn arrange_renames_presentation_and_changes_nothing_else() {
    let directory = store_from("arrange", "tree");
    let before = stdout(&directory, &["log"]);

    let planned = stdout(&directory, &["arrange", "-n"]);
    assert!(planned.contains("would rename"), "{planned}");
    assert!(
        directory.join("history/revisions/01-start.rev").exists(),
        "a dry run renames nothing"
    );

    let done = stdout(&directory, &["arrange"]);
    assert!(done.contains("4 renamed"), "{done}");
    assert!(
        directory
            .join("history/revisions/2025-08-19 Start a journal.rev")
            .exists(),
        "{done}"
    );

    // Identity comes from content, so nothing about the history moved.
    assert_eq!(stdout(&directory, &["log"]), before);
    assert!(
        stdout(&directory, &["check"]).ends_with("nothing to report\n"),
        "an arranged store is as valid as a digest-named one"
    );

    let again = stdout(&directory, &["arrange"]);
    assert!(again.contains("0 renamed, 4 already arranged"), "{again}");
}

#[test]
fn a_history_with_a_merge_in_it_is_refused_rather_than_ordered() {
    let directory = store_from("merge", "revisions");
    // The log walks the graph, so a merge is ordinary there.
    let log = stdout(&directory, &["log"]);
    assert!(log.contains("merge"), "{log}");

    // Materialising is where 0007's merge would be needed, and it is not built.
    let head = log
        .lines()
        .find(|line| line.contains("(head, merge"))
        .and_then(|line| line.split_whitespace().nth(1))
        .expect("a merge at a head");
    let refused = stderr(&directory, &["files", head]);
    assert!(refused.contains("joins two lines of history"), "{refused}");
    assert!(!refused.contains("  "), "the message runs on one line");
}

#[test]
fn a_command_line_that_is_wrong_prints_the_usage_and_exits_two() {
    let directory = store_from("usage", "tree");
    let output = run(&directory, &["frobnicate"]);
    assert_eq!(output.status.code(), Some(2));
    let complaint = String::from_utf8(output.stderr).expect("printed text");
    assert!(complaint.contains("no `frobnicate` command"), "{complaint}");
    assert!(complaint.contains("usage: historica"), "{complaint}");

    let missing = run(&directory, &["cat", "qpvuntsm"]);
    assert_eq!(missing.status.code(), Some(2));

    // Asking for help is not an error.
    let help = run(&directory, &["help"]);
    assert!(help.status.success());
    assert!(String::from_utf8_lossy(&help.stdout).contains("usage: historica"));
}
