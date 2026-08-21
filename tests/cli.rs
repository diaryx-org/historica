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
    // Deliberately outside the repository rather than under
    // `CARGO_TARGET_TMPDIR`. `locate` walks up to the filesystem root, and
    // `target/` is inside a checkout that may itself hold a `history/` — as
    // this one does, being a tool people record their own work with. A
    // scratch directory there would find that store and this test would
    // assert the opposite of what it means.
    let directory = std::env::temp_dir().join("historica-cli-no-store");
    let _ = fs::remove_dir_all(&directory);
    fs::create_dir_all(&directory).expect("a scratch directory outside the repository");

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
fn arrange_files_operation_documents_under_the_revision_that_names_them() {
    let directory = repository("arrange-nesting");
    fs::create_dir_all(directory.join("src/cli")).expect("directories");
    write(&directory, "src/cli/mod.rs", "one\n");
    write(&directory, "a.md", "start\n");
    out(recorded(&directory, &["record", "-m", "Start a journal"]));
    write(&directory, "src/cli/mod.rs", "one edited\n");
    out(recorded(&directory, &["record", "-m", "Say more"]));

    out(recorded(&directory, &["arrange"]));

    // The directory carries the revision, so the filename is free to be the
    // path — and the two directories are visibly the two `.rev` files.
    let operations = directory.join("history/operations");
    let filed: Vec<String> = walk_names(&operations);
    assert!(
        filed.iter().all(|name| name.contains('/')),
        "every document should sit under a revision directory: {filed:?}"
    );
    assert!(
        filed
            .iter()
            .any(|name| name.ends_with("Start a journal/src⁄cli⁄mod.rs.ops")),
        "{filed:?}"
    );
    assert!(
        filed
            .iter()
            .any(|name| name.ends_with("Say more/src⁄cli⁄mod.rs.ops")),
        "one path, two revisions, two directories: {filed:?}"
    );
    assert!(
        filed.iter().all(|name| !name.contains(".ops.ops")),
        "{filed:?}"
    );

    // Nothing about the history moved, and nothing is left at the top.
    assert!(
        stdout(&directory, &["check"]).ends_with("nothing to report\n"),
        "a nested store is as valid as a flat one"
    );
    assert_eq!(
        stdout(&directory, &["cat", "head", "src/cli/mod.rs"]),
        "one edited\n"
    );

    // Arranging an arranged store moves nothing.
    let again = stdout(&directory, &["arrange"]);
    assert!(again.contains("0 renamed, 3 already arranged"), "{again}");
}

#[test]
fn arrange_tidies_the_directory_it_emptied_and_spares_the_one_it_did_not() {
    let directory = repository("arrange-tidy");
    write(&directory, "a.md", "one\n");
    write(&directory, "b.md", "other\n");
    out(recorded(&directory, &["record", "-m", "First"]));

    // Two documents, filed by hand into two directories of a person's own.
    let operations = directory.join("history/operations");
    let mut documents = walk_names(&operations);
    documents.retain(|name| name.ends_with(".ops"));
    assert_eq!(documents.len(), 2, "{documents:?}");

    let alone = operations.join("alone");
    let shared = operations.join("shared");
    fs::create_dir_all(&alone).expect("a directory");
    fs::create_dir_all(&shared).expect("a directory");
    fs::rename(operations.join(&documents[0]), alone.join(&documents[0])).expect("filing");
    fs::rename(operations.join(&documents[1]), shared.join(&documents[1])).expect("filing");
    // Something that is not a document, and not this command's to delete.
    fs::write(shared.join("notes.txt"), "why these are here\n").expect("a file");

    out(recorded(&directory, &["arrange"]));

    // The directory arranging emptied is gone. The one still holding
    // something is not: `remove_dir` refuses a directory that holds anything,
    // which is the whole of the guard.
    assert!(
        !alone.exists(),
        "an emptied directory should be tidied away"
    );
    assert!(shared.exists(), "a directory in use should be left alone");
    assert!(shared.join("notes.txt").exists());
    // `stdout` asserts a zero exit, so the store is still sound; the note is
    // `check` having walked into the directory and found the one file there
    // that is not a document.
    let report = stdout(&directory, &["check"]);
    assert!(report.contains("notes.txt"), "{report}");
    assert!(report.contains("nothing reads it"), "{report}");
}

#[test]
fn recording_into_an_arranged_store_leaves_it_readable() {
    // The writer still writes flat and the reader reads both, which is what
    // makes arranging safe to do at any time rather than once at the end.
    let directory = repository("arrange-then-record");
    write(&directory, "a.md", "one\n");
    out(recorded(&directory, &["record", "-m", "First"]));
    out(recorded(&directory, &["arrange"]));

    write(&directory, "a.md", "two\n");
    out(recorded(&directory, &["record", "-m", "Second"]));

    // A store that is half filed and half flat is one store.
    assert_eq!(stdout(&directory, &["cat", "head", "a.md"]), "two\n");
    assert!(
        stdout(&directory, &["check"]).ends_with("nothing to report\n"),
        "half-arranged is not half-valid"
    );

    let done = stdout(&directory, &["arrange"]);
    assert!(done.contains("1 renamed, 1 already arranged"), "{done}");
}

#[test]
fn arranging_is_the_same_wherever_it_is_done() {
    // Decision 0006's hard rule, which nesting does not get to weaken: two
    // replicas of one history must produce one set of names, or sync sees two
    // files per document.
    let one = repository("arrange-replica-one");
    write(&one, "notes/a.md", "one\n");
    out(recorded(&one, &["record", "-m", "A journal entry"]));
    write(&one, "notes/a.md", "two\n");
    out(recorded(&one, &["record", "-m", "A second entry"]));

    // The same store, copied before arranging and arranged separately.
    let two = scratch("arrange-replica-two");
    copy_tree(&one.join("history"), &two.join("history"));

    out(recorded(&one, &["arrange"]));
    out(recorded(&two, &["arrange"]));
    assert_eq!(
        walk_names(&one.join("history")),
        walk_names(&two.join("history")),
        "two replicas disagreed about a name"
    );
}

/// Every file under a directory, relative and sorted, directories included in
/// the spelling so a nested arrangement is visible.
fn walk_names(root: &Path) -> Vec<String> {
    let mut found = Vec::new();
    let mut pending = vec![root.to_path_buf()];
    while let Some(next) = pending.pop() {
        let Ok(entries) = fs::read_dir(&next) else {
            continue;
        };
        for entry in entries.filter_map(Result::ok) {
            let path = entry.path();
            if path.is_dir() {
                pending.push(path);
            } else {
                found.push(
                    path.strip_prefix(root)
                        .unwrap_or(&path)
                        .to_string_lossy()
                        .into_owned(),
                );
            }
        }
    }
    found.sort();
    found
}

fn copy_tree(from: &Path, to: &Path) {
    fs::create_dir_all(to).expect("a directory");
    for entry in fs::read_dir(from).expect("a directory").flatten() {
        let path = entry.path();
        let target = to.join(entry.file_name());
        if path.is_dir() {
            copy_tree(&path, &target);
        } else {
            fs::copy(&path, &target).expect("copying a file");
        }
    }
}

#[test]
fn arrange_renames_a_filed_revision_where_it_sits() {
    let directory = store_from("arrange-nested", "tree");
    let revisions = directory.join("history/revisions");
    let filed = revisions.join("early/2025");
    fs::create_dir_all(&filed).expect("directories");
    fs::rename(revisions.join("01-start.rev"), filed.join("01-start.rev"))
        .expect("filing a revision away");

    let before = stdout(&directory, &["log"]);
    let done = stdout(&directory, &["arrange"]);

    // Renamed, not moved. A person who filed it there meant to.
    assert!(
        filed.join("2025-08-19 Start a journal.rev").exists(),
        "{done}"
    );
    assert!(
        !revisions.join("2025-08-19 Start a journal.rev").exists(),
        "arranging must not flatten what a person arranged"
    );
    assert_eq!(stdout(&directory, &["log"]), before);

    // And arranging an arranged store is a no-op, at whatever depth.
    let again = stdout(&directory, &["arrange"]);
    assert!(again.contains("4 already arranged"), "{again}");
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
fn a_history_with_a_merge_in_it_materialises_rather_than_being_refused() {
    let directory = store_from("merge", "revisions");
    let log = stdout(&directory, &["log"]);
    assert!(log.contains("merge"), "{log}");

    // 0007's merge and 0008's tree rules are what the store now walks, so a
    // merge is an ordinary place to ask what the file set is.
    let head = log
        .lines()
        .find(|line| line.contains("(head, merge"))
        .and_then(|line| line.split_whitespace().nth(1))
        .expect("a merge at a head");
    let files = stdout(&directory, &["files", head]);
    assert_eq!(
        files, "no files here\n",
        "these revisions state no tree facts"
    );
    assert!(stdout(&directory, &["check"]).ends_with("nothing to report\n"));
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

/// A repository with an author set, ready to record into.
fn repository(test: &str) -> PathBuf {
    let directory = scratch(test);
    assert!(run(&directory, &["init"]).status.success());
    directory
}

/// Run with an author stated, which is how a script records (decision 0010).
fn recorded(directory: &Path, arguments: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_historica"))
        .arg("-C")
        .arg(directory)
        .args(arguments)
        .env("HISTORICA_AUTHOR", "Adam Harris <adam@example.com>")
        .output()
        .expect("the binary this test crate builds")
}

fn write(directory: &Path, path: &str, text: &str) {
    let file = directory.join(path);
    if let Some(parent) = file.parent() {
        fs::create_dir_all(parent).expect("a directory");
    }
    fs::write(file, text).expect("writing a file");
}

fn out(output: Output) -> String {
    assert!(
        output.status.success(),
        "failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    String::from_utf8(output.stdout).expect("printed text")
}

#[test]
fn recording_builds_a_history_check_accepts() {
    let directory = repository("record");
    write(&directory, "2026-08-20.md", "# Notes\n\nA journal.\n");

    let planned = out(recorded(&directory, &["record", "--dry-run"]));
    assert!(planned.contains("added   2026-08-20.md"), "{planned}");
    assert!(
        out(recorded(&directory, &["log"])).contains("no revisions"),
        "a dry run records nothing"
    );

    let first = out(recorded(&directory, &["record", "-m", "Start a journal"]));
    assert!(first.contains("added   2026-08-20.md"), "{first}");
    assert!(first.contains("this is a root"), "{first}");

    write(
        &directory,
        "2026-08-20.md",
        "# Notes\n\nA journal.\n\nMore.\n",
    );
    let second = out(recorded(&directory, &["record", "-m", "Say more"]));
    assert!(second.contains("edited  2026-08-20.md"), "{second}");

    assert!(
        out(recorded(&directory, &["check"])).ends_with("nothing to report\n"),
        "every revision is held to the file set and the operations it names"
    );
    let content = out(recorded(&directory, &["cat", "head", "2026-08-20.md"]));
    assert_eq!(content, "# Notes\n\nA journal.\n\nMore.\n");
}

#[test]
fn a_rename_is_stated_and_performed() {
    let directory = repository("record-move");
    write(&directory, "notes.md", "one\n");
    out(recorded(&directory, &["record", "-m", "Start"]));

    let moved = out(recorded(
        &directory,
        &[
            "record",
            "-m",
            "File the notes",
            "--move",
            "notes.md=docs/notes.md",
        ],
    ));
    assert!(moved.contains("moved   docs/notes.md"), "{moved}");
    assert!(
        directory.join("docs/notes.md").is_file() && !directory.join("notes.md").exists(),
        "`--move` performs the rename when a person has not"
    );

    // The identity survived the rename, which is what file IDs are for.
    let files = out(recorded(&directory, &["files", "head"]));
    assert!(files.starts_with("docs/notes.md"), "{files}");
    let file = files.split_whitespace().next_back().expect("a file ID");
    let content = out(recorded(&directory, &["cat", "head", file]));
    assert_eq!(content, "one\n", "the file is the same file it was");

    // And a deletion needs no flag at all.
    fs::remove_file(directory.join("docs/notes.md")).expect("removing a file");
    let dropped = out(recorded(&directory, &["record", "-m", "Withdraw it"]));
    assert!(dropped.contains("dropped docs/notes.md"), "{dropped}");
    assert!(out(recorded(&directory, &["files", "head"])).contains("no files"));
}

#[test]
fn a_bookmark_follows_the_work_forward() {
    let directory = repository("record-bookmark");
    write(&directory, "a.md", "one\n");
    out(recorded(&directory, &["record", "-m", "First"]));
    out(recorded(&directory, &["name", "main", "head"]));

    write(&directory, "a.md", "two\n");
    let second = out(recorded(&directory, &["record", "-m", "Second"]));
    assert!(second.contains("main -> "), "{second}");

    let named = out(recorded(&directory, &["names"]));
    let logged = out(recorded(&directory, &["log"]));
    let head = logged.lines().next().expect("a head").split_whitespace();
    let change = head.into_iter().next().expect("a change ID");
    assert!(named.contains(change), "{named} should follow {change}");
}

#[test]
fn what_the_format_cannot_hold_is_refused_by_name() {
    let directory = repository("record-refusals");
    write(&directory, "fine.md", "text\n");
    fs::write(directory.join("picture.bin"), [0xff, 0xfe, 0x00]).expect("bytes");

    let refused = recorded(&directory, &["record", "-m", "Everything"]);
    assert!(!refused.status.success());
    let complaint = String::from_utf8_lossy(&refused.stderr).into_owned();
    assert!(complaint.contains("picture.bin"), "{complaint}");
    assert!(complaint.contains("skip"), "{complaint}");

    // Which is the fix the message names.
    write(&directory, "history/skipped", "skip-suffix .bin\n");
    assert!(out(recorded(&directory, &["record", "-m", "Everything"])).contains("fine.md"));

    // And nothing to say is refused too.
    let again = recorded(&directory, &["record", "-m", "Again"]);
    assert!(!again.status.success());
    assert!(
        String::from_utf8_lossy(&again.stderr).contains("would mean nothing"),
        "a revision that states nothing is not recorded"
    );
}

#[test]
fn skip_writes_the_line_a_person_would_have_typed() {
    let directory = repository("skip-command");
    fs::create_dir_all(directory.join("target")).expect("a directory");
    write(&directory, "notes/a.md", "one\n");
    write(&directory, "target/out.bin", "junk\n");

    // A directory gets the trailing slash the parser wants, which is the one
    // thing leaving off changes the meaning of.
    let written = out(recorded(
        &directory,
        &["skip", "target", "--suffix", ".tmp"],
    ));
    assert!(written.contains("skip target/"), "{written}");
    assert!(written.contains("skip-suffix .tmp"), "{written}");

    let text = fs::read_to_string(directory.join("history/skipped")).expect("the file");
    assert_eq!(text, "skip target/\nskip-suffix .tmp\n");

    // With no arguments it prints them, as `names` prints the bookmarks.
    assert_eq!(out(recorded(&directory, &["skip"])), text);

    // And the rules are the ones recording honours.
    let first = out(recorded(&directory, &["record", "-m", "First"]));
    assert!(first.contains("notes/a.md"), "{first}");
    assert!(!first.contains("out.bin"), "{first}");

    // Saying it twice writes one line and says so.
    let again = out(recorded(&directory, &["skip", "target/"]));
    assert!(again.contains("already there"), "{again}");
    assert_eq!(
        fs::read_to_string(directory.join("history/skipped")).expect("the file"),
        text
    );
}

#[test]
fn skip_refuses_a_rule_over_what_history_holds_and_writes_nothing() {
    let directory = repository("skip-command-refusal");
    write(&directory, "drafts/one.md", "one\n");
    out(recorded(&directory, &["record", "-m", "First"]));

    // Decision 0011, answered before the file is written rather than at the
    // next record: the person is standing in front of the answer now.
    let refused = recorded(&directory, &["skip", "drafts", "--suffix", ".tmp"]);
    assert!(!refused.status.success());
    let complaint = String::from_utf8_lossy(&refused.stderr).into_owned();
    assert!(complaint.contains("drafts/one.md"), "{complaint}");

    // Nothing is written, the good rule in the same command included: a
    // command that half-applied would leave a person guessing which half.
    assert!(!directory.join("history/skipped").exists());
}

#[test]
fn skip_leaves_the_file_a_person_wrote_alone() {
    let directory = repository("skip-command-append");
    write(
        &directory,
        "history/skipped",
        "skip one/\n\nskip-suffix .bin\n",
    );

    out(recorded(&directory, &["skip", "two/"]));

    // The blank line the parser ignores is a blank line the person meant.
    assert_eq!(
        fs::read_to_string(directory.join("history/skipped")).expect("the file"),
        "skip one/\n\nskip-suffix .bin\nskip two/\n"
    );
}

#[test]
fn a_skip_rule_over_a_tracked_file_is_refused() {
    let directory = repository("skip-tracked");
    write(&directory, "drafts/one.md", "one\n");
    write(&directory, "kept.md", "kept\n");
    out(recorded(&directory, &["record", "-m", "First"]));

    // The harm decision 0011 names: the walk stops offering the path, so the
    // next record would spell a request for privacy as a deletion of the very
    // file it names, into a history that is append-only.
    write(&directory, "history/skipped", "skip drafts/\n");
    let refused = recorded(&directory, &["record", "-m", "Second"]);
    assert!(!refused.status.success());
    let complaint = String::from_utf8_lossy(&refused.stderr).into_owned();
    assert!(complaint.contains("drafts/one.md"), "{complaint}");
    assert!(complaint.contains("history/skipped"), "{complaint}");

    // A rule over a path nothing has recorded is ordinary, which is the whole
    // point of the file.
    write(&directory, "history/skipped", "skip-suffix .tmp\n");
    write(&directory, "scratch.tmp", "noise\n");
    write(&directory, "kept.md", "edited\n");
    let recorded_second = out(recorded(&directory, &["record", "-m", "Second"]));
    assert!(recorded_second.contains("kept.md"), "{recorded_second}");
    assert!(
        !recorded_second.contains("scratch.tmp"),
        "{recorded_second}"
    );

    // And the way out is the one the message names: delete the file, record
    // the deletion, and only then does the rule become sayable.
    fs::remove_dir_all(directory.join("drafts")).expect("the drafts");
    out(recorded(&directory, &["record", "-m", "Away"]));
    write(&directory, "history/skipped", "skip drafts/\n");
    write(&directory, "kept.md", "again\n");
    assert!(
        recorded(&directory, &["record", "-m", "Third"])
            .status
            .success()
    );
}

#[test]
fn a_message_that_looks_like_a_comment_survives() {
    let directory = repository("record-message");
    write(&directory, "a.md", "one\n");
    out(recorded(
        &directory,
        &["record", "-m", "# A heading, and a body\n\nstill here\n"],
    ));

    let shown = out(recorded(&directory, &["show", "head"]));
    assert!(
        shown.ends_with("# A heading, and a body\n\nstill here\n"),
        "0002 says the body is never interpreted: {shown}"
    );
}

#[test]
fn recording_without_an_author_refuses_and_says_where_to_say_so() {
    let directory = repository("record-anonymous");
    write(&directory, "a.md", "one\n");

    let refused = Command::new(env!("CARGO_BIN_EXE_historica"))
        .arg("-C")
        .arg(&directory)
        .args(["record", "-m", "Anonymous"])
        .env_remove("HISTORICA_AUTHOR")
        .env("XDG_CONFIG_HOME", directory.join("nowhere"))
        .output()
        .expect("the binary");
    assert!(!refused.status.success());
    let complaint = String::from_utf8_lossy(&refused.stderr).into_owned();
    assert!(complaint.contains("historica identity"), "{complaint}");
    assert!(complaint.contains("nothing is guessed"), "{complaint}");
}

/// Two lines of work from one root, editing the same file differently.
fn diverged(test: &str, mine: &str, theirs: &str) -> (PathBuf, String, String) {
    let directory = repository(test);
    write(&directory, "f.md", "one\ntwo\nthree\n");
    out(recorded(&directory, &["record", "-m", "root"]));
    let root = out(recorded(&directory, &["log"]))
        .lines()
        .next()
        .and_then(|line| line.split_whitespace().nth(1))
        .expect("the root")
        .to_owned();

    write(&directory, "f.md", mine);
    out(recorded(&directory, &["record", "-m", "mine"]));
    write(&directory, "f.md", theirs);
    out(recorded(
        &directory,
        &["record", "--onto", &root, "-m", "theirs"],
    ));

    let log = out(recorded(&directory, &["log"]));
    let mut heads = log
        .lines()
        .filter(|line| line.contains("(head"))
        .map(|line| line.split_whitespace().next().expect("a change").to_owned());
    let (one, two) = (heads.next().expect("a head"), heads.next().expect("a head"));
    (directory, one, two)
}

#[test]
fn a_merge_is_rendered_resolved_and_then_recorded() {
    let (directory, mine, theirs) = diverged(
        "merge-conflict",
        "one\nMINE\nthree\n",
        "one\nTHEIRS\nthree\n",
    );

    let merging = out(recorded(&directory, &["merge", &mine, &theirs]));
    assert!(merging.contains("1 file holds work that met"), "{merging}");

    // Both runs are in one fence, each labelled with who wrote it.
    let rendered = fs::read_to_string(directory.join("f.md")).expect("the merged file");
    assert_eq!(rendered.matches("vvv historica: ").count(), 2, "{rendered}");
    assert_eq!(rendered.matches("^^^ historica: ").count(), 1, "{rendered}");
    assert!(rendered.contains("MINE") && rendered.contains("THEIRS"));

    // Recording while a marker still stands is refused, per line.
    let refused = recorded(
        &directory,
        &["record", "--merge", &mine, "--merge", &theirs, "-m", "Join"],
    );
    assert!(!refused.status.success());
    assert!(
        String::from_utf8_lossy(&refused.stderr).contains("still marked"),
        "a partially resolved merge is not a state this keeps"
    );

    // Resolving is ordinary editing, and the resolution is what gets recorded.
    write(&directory, "f.md", "one\nBOTH\nthree\n");
    let joined = out(recorded(
        &directory,
        &["record", "--merge", &mine, "--merge", &theirs, "-m", "Join"],
    ));
    assert!(joined.contains("this joins 2 lines of work"), "{joined}");
    assert!(out(recorded(&directory, &["log"])).contains("merge"));
    assert!(out(recorded(&directory, &["check"])).ends_with("nothing to report\n"));
    assert_eq!(
        out(recorded(&directory, &["cat", "head", "f.md"])),
        "one\nBOTH\nthree\n"
    );
}

#[test]
fn a_merge_that_needed_no_help_records_no_operations() {
    let directory = repository("merge-clean");
    write(&directory, "a.md", "a\n");
    out(recorded(&directory, &["record", "-m", "root"]));
    let root = out(recorded(&directory, &["log"]))
        .lines()
        .next()
        .and_then(|line| line.split_whitespace().nth(1))
        .expect("the root")
        .to_owned();

    write(&directory, "b.md", "b\n");
    out(recorded(&directory, &["record", "-m", "mine"]));
    // The other branch touches a third file, from the root.
    fs::remove_file(directory.join("b.md")).expect("removing a file");
    write(&directory, "c.md", "c\n");
    out(recorded(
        &directory,
        &["record", "--onto", &root, "-m", "theirs"],
    ));

    let log = out(recorded(&directory, &["log"]));
    let mut heads = log
        .lines()
        .filter(|line| line.contains("(head"))
        .map(|line| line.split_whitespace().next().expect("a change").to_owned());
    let (mine, theirs) = (heads.next().expect("a head"), heads.next().expect("a head"));

    let merging = out(recorded(&directory, &["merge", &mine, &theirs]));
    assert!(merging.contains("nothing is contested"), "{merging}");
    assert!(directory.join("b.md").is_file() && directory.join("c.md").is_file());

    let joined = out(recorded(
        &directory,
        &["record", "--merge", &mine, "--merge", &theirs, "-m", "Join"],
    ));
    assert!(joined.contains("joins 2 lines"), "{joined}");
    let document = out(recorded(&directory, &["show", "head"]));
    assert!(
        !document.contains("\nedit "),
        "a merge that changed nothing about a file names no document: {document}"
    );
}

#[test]
fn a_document_about_merge_markers_records_like_any_other() {
    let directory = repository("merge-prose");
    write(
        &directory,
        "notes.md",
        "A fence reads `vvv historica: 0badbeef wrote vvv`.\n",
    );
    let recorded = out(recorded(&directory, &["record", "-m", "On merging"]));
    assert!(recorded.contains("added   notes.md"), "{recorded}");
}

#[test]
fn status_says_where_the_folder_is_and_what_it_differs_by() {
    let directory = repository("status-position");

    // A store with no revisions has no first line to print, and everything in
    // the folder is an add against the empty tree.
    let empty = out(recorded(&directory, &["status"]));
    assert!(empty.starts_with("no revisions here yet"), "{empty}");

    write(&directory, "notes.md", "one\ntwo\n");
    let before = out(recorded(&directory, &["status"]));
    assert!(before.contains("added   notes.md"), "{before}");

    out(recorded(&directory, &["record", "-m", "First"]));
    out(recorded(&directory, &["name", "journal", "head"]));

    // The position is `log`'s first line, and the bookmark is what a person
    // reads instead of a digest.
    let after = out(recorded(&directory, &["status"]));
    assert!(after.contains("(head, journal)"), "{after}");
    assert!(
        after.contains("nothing here differs from what is recorded"),
        "{after}"
    );

    // Decision 0015: status mints nothing, so it cannot answer twice over.
    let again = out(recorded(&directory, &["status"]));
    assert_eq!(after, again, "status is derived, so it repeats itself");
}

#[test]
fn status_and_a_dry_run_state_the_same_facts() {
    let directory = repository("status-dry-run");
    write(&directory, "a.md", "one\n");
    out(recorded(&directory, &["record", "-m", "First"]));

    write(&directory, "a.md", "one\ntwo\n");
    write(&directory, "b.md", "new\n");

    let planned = out(recorded(&directory, &["record", "--dry-run"]));
    let status = out(recorded(&directory, &["status"]));
    let facts: String = status
        .lines()
        .filter(|line| line.starts_with("added") || line.starts_with("edited"))
        .map(|line| format!("{line}\n"))
        .collect();
    assert_eq!(planned, facts, "one survey, so one answer");
}

#[test]
fn status_lists_every_refusal_and_the_facts_beside_them() {
    let directory = repository("status-refusals");
    write(&directory, "fine.md", "text\n");
    fs::write(directory.join("picture.bin"), [0xff, 0xfe, 0x00]).expect("bytes");
    #[cfg(unix)]
    std::os::unix::fs::symlink("/etc/hosts", directory.join("link")).expect("a symlink");

    // The point of the list: one command names every file, so the `skip` rules
    // are written in one pass rather than one command per file.
    let listed = out(recorded(&directory, &["status"]));
    assert!(listed.contains("added   fine.md"), "{listed}");
    assert!(
        listed.contains("refused picture.bin: not UTF-8 text"),
        "{listed}"
    );
    #[cfg(unix)]
    assert!(
        listed.contains("refused link: not a regular file"),
        "{listed}"
    );

    // And recording refuses the same files, all of them at once.
    let refused = recorded(&directory, &["record", "-m", "Everything"]);
    assert!(!refused.status.success());
    let complaint = String::from_utf8_lossy(&refused.stderr).into_owned();
    assert!(complaint.contains("picture.bin"), "{complaint}");
    assert!(complaint.contains("skip"), "{complaint}");
    #[cfg(unix)]
    assert!(complaint.contains("link"), "{complaint}");
}

#[test]
fn status_suggests_a_rename_only_where_the_bytes_are_identical() {
    let directory = repository("status-renames");
    write(&directory, "old.md", "one\ntwo\n");
    write(&directory, "empty.md", "");
    out(recorded(&directory, &["record", "-m", "First"]));

    // A `mv` and nothing else: the facts are still an add and a drop, and the
    // suggestion sits beside them rather than replacing them.
    fs::rename(directory.join("old.md"), directory.join("new.md")).expect("a rename");
    let moved = out(recorded(&directory, &["status"]));
    assert!(moved.contains("added   new.md"), "{moved}");
    assert!(moved.contains("dropped old.md"), "{moved}");
    assert!(moved.contains("--move old.md=new.md"), "{moved}");

    // An empty file that moved suggests nothing: every empty file has the
    // bytes of every other.
    fs::rename(directory.join("empty.md"), directory.join("blank.md")).expect("a rename");
    let blank = out(recorded(&directory, &["status"]));
    assert!(!blank.contains("--move empty.md=blank.md"), "{blank}");

    // Two files holding one dropped file's bytes is a guess nobody makes.
    write(&directory, "copy.md", "one\ntwo\n");
    let ambiguous = out(recorded(&directory, &["status"]));
    assert!(!ambiguous.contains("--move old.md"), "{ambiguous}");
    fs::remove_file(directory.join("copy.md")).expect("removing the copy");

    // A rename that was also edited is missed, and says nothing rather than
    // guessing: decision 0015 refuses the similarity threshold that would
    // catch it.
    write(&directory, "new.md", "one\ntwo\nthree\n");
    let edited = out(recorded(&directory, &["status"]));
    assert!(edited.contains("added   new.md"), "{edited}");
    assert!(edited.contains("dropped old.md"), "{edited}");
    assert!(!edited.contains("--move"), "{edited}");
}

#[test]
fn status_with_several_heads_refuses_and_names_them() {
    let (directory, mine, _theirs) = diverged("status-heads", "one\nMINE\n", "one\nTHEIRS\n");
    out(recorded(&directory, &["name", "journal", &mine]));

    let refused = String::from_utf8_lossy(&recorded(&directory, &["status"]).stderr).into_owned();
    assert!(refused.contains("2 heads"), "{refused}");
    assert!(refused.contains("--onto"), "{refused}");
    assert!(
        refused.contains("journal"),
        "a head a person named should say so: {refused}"
    );

    // Naming one is the whole of the fix, and the same flag `record` takes.
    let named = out(recorded(&directory, &["status", "--onto", &mine]));
    assert!(named.contains("journal"), "{named}");
}

#[test]
fn a_marker_line_is_ordinary_until_a_person_restates_the_merge() {
    let (directory, mine, theirs) = diverged(
        "status-markers",
        "one\nMINE\nthree\n",
        "one\nTHEIRS\nthree\n",
    );
    out(recorded(&directory, &["merge", &mine, &theirs]));

    // Outside a merge the rendered lines are content, which is what lets a
    // document about merge markers be an ordinary document.
    let ordinary = out(recorded(&directory, &["status", "--onto", &mine]));
    assert!(ordinary.contains("edited  f.md"), "{ordinary}");
    assert!(!ordinary.contains("marked"), "{ordinary}");

    // Restating it is what scopes the detection, and the count is the one
    // `record` refuses on.
    let joining = out(recorded(
        &directory,
        &["status", "--merge", &mine, "--merge", &theirs],
    ));
    assert!(joining.contains("marked  f.md"), "{joining}");
}

#[test]
fn a_path_two_files_claim_prints_under_status_and_refuses_under_record() {
    let directory = repository("status-contested");
    write(&directory, "root.md", "a\n");
    out(recorded(&directory, &["record", "-m", "root"]));
    let root = out(recorded(&directory, &["log"]))
        .lines()
        .next()
        .and_then(|line| line.split_whitespace().nth(1))
        .expect("the root")
        .to_owned();

    // Two lines of work each adding a file at one path, which 0008 allows and
    // only `--at` settles.
    write(&directory, "both.md", "mine\n");
    out(recorded(&directory, &["record", "-m", "mine"]));
    let mine = out(recorded(&directory, &["log"]))
        .lines()
        .next()
        .and_then(|line| line.split_whitespace().nth(1))
        .expect("a head")
        .to_owned();
    fs::remove_file(directory.join("both.md")).expect("removing it");
    write(&directory, "both.md", "theirs\n");
    out(recorded(
        &directory,
        &["record", "--onto", &root, "-m", "theirs"],
    ));
    let theirs = out(recorded(&directory, &["log"]))
        .lines()
        .find(|line| line.contains("(head") && !line.contains(&mine))
        .and_then(|line| line.split_whitespace().nth(1))
        .expect("the other head")
        .to_owned();

    let joining = out(recorded(
        &directory,
        &["status", "--merge", &mine, "--merge", &theirs],
    ));
    assert!(joining.contains("claimed both.md"), "{joining}");
    assert!(joining.contains("--at"), "{joining}");

    // The same path recording refuses rather than resolving to whichever a
    // map happened to keep.
    let refused = recorded(
        &directory,
        &["record", "--merge", &mine, "--merge", &theirs, "-m", "Join"],
    );
    assert!(!refused.status.success());
    let complaint = String::from_utf8_lossy(&refused.stderr).into_owned();
    assert!(complaint.contains("both.md"), "{complaint}");
    assert!(complaint.contains("--at"), "{complaint}");
}
