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
            let name = path
                .file_name()
                .and_then(|found| found.to_str())
                .unwrap_or_default();
            let into = match () {
                _ if name.ends_with(".rev.txt") => "revisions",
                _ if name.ends_with(".ops.txt") => "operations",
                _ => continue,
            };
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
    // Decision 0021: the first line is the version, and the rest of the file
    // tells whoever opens the folder what they are looking at.
    let header = fs::read_to_string(directory.join("history/historica.txt")).expect("the header");
    let mut lines = header.lines();
    assert_eq!(lines.next(), Some("historica-v1"));
    assert!(header.contains("Identity comes from content"), "{header}");
    assert!(header.contains("revisions/"), "{header}");
    assert!(header.contains("cache/"), "{header}");
    let cache_note =
        fs::read_to_string(directory.join("history/cache/README.txt")).expect("the cache note");
    assert!(
        cache_note.contains("Everything in this directory is derived"),
        "{cache_note}"
    );
    let skipped = fs::read_to_string(directory.join("history/skipped.txt")).expect("the rule file");
    assert!(
        skipped
            .lines()
            .all(|line| line.is_empty() || line.starts_with('#')),
        "nothing is skipped by default: {skipped}"
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
        directory.join("history/revisions/broken.rev.txt"),
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
    // Decision 0027: a sync tool's conflicted copy is a legitimate duplicate,
    // with no guess about which tool chose its filename.
    let revisions = directory.join("history/revisions");
    fs::copy(
        revisions.join("01-start.rev.txt"),
        revisions.join("01-start (Adam's conflicted copy 2025-08-19).rev.txt"),
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
    let stored =
        fs::read(corpus("tree").join("revisions/03-move.rev.txt")).expect("the corpus file");
    let printed = run(&directory, &["show", "mzvwutkl"]);
    assert_eq!(printed.stdout, stored, "`show` must not reformat anything");
}

#[test]
fn show_with_a_path_prints_what_that_revision_did_to_that_file() {
    let directory = store_from("show-ops", "tree");
    let stored =
        fs::read(corpus("tree").join("operations/03-readme.ops.txt")).expect("the corpus file");
    let printed = run(&directory, &["show", "mzvwutkl", "docs/README.md"]);
    assert_eq!(printed.stdout, stored);

    let untouched = stderr(&directory, &["show", "mzvwutkl", "notes/2025-08-19.md"]);
    assert!(untouched.contains("said nothing about"), "{untouched}");
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

    // And the content is reachable by either path, or by the ID itself —
    // decision 0024, which gives the identifier a spelling a path cannot have
    // by accident.
    let content = stdout(&directory, &["cat", "mzvwutkl", "docs/README.md"]);
    assert_eq!(
        content,
        stdout(&directory, &["cat", "mzvwutkl", &format!("file:{file}")])
    );
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

    let bookmark =
        fs::read_to_string(directory.join("history/names/main.txt")).expect("the bookmark");
    assert_eq!(bookmark, "change nwlxsqotvkzmuprysltnwxqk\n");
    assert!(
        fs::read_to_string(directory.join("history/names/pinned.txt"))
            .expect("the bookmark")
            .starts_with("revision ")
    );

    let listed = stdout(&directory, &["names"]);
    assert!(listed.contains("main    change nwlxsqot"), "{listed}");
    assert!(listed.contains("pinned  revision "), "{listed}");
}

/// The file identifiers in the tree corpus, which are fixed by its documents.
const README_FILE: &str = "swtlmnkqvzyrxopwstlnmkqv";
const NOTES_FILE: &str = "nrqvtkzlmwyxsptonvqrklmz";

#[test]
fn a_file_is_addressed_by_the_identifier_it_keeps() {
    let directory = store_from("file-spelling", "tree");
    let by_path = stdout(&directory, &["cat", "mzvwutkl", "docs/README.md"]);

    // Decision 0024: the identifier is spelled, and abbreviates to any prefix
    // unique among the files at that revision, as a change ID does.
    assert_eq!(
        by_path,
        stdout(
            &directory,
            &["cat", "mzvwutkl", &format!("file:{README_FILE}")]
        )
    );
    assert_eq!(by_path, stdout(&directory, &["cat", "mzvwutkl", "file:sw"]));

    // And at the revision before the rename, the same identifier names the
    // same file under the name it had then — which is the whole point.
    assert_eq!(
        stdout(&directory, &["cat", "kxryzmor", "README.md"]),
        stdout(&directory, &["cat", "kxryzmor", "file:sw"])
    );

    // `show` takes it in the same position, and prints the same document.
    assert_eq!(
        stdout(&directory, &["show", "mzvwutkl", "docs/README.md"]),
        stdout(&directory, &["show", "mzvwutkl", "file:sw"])
    );
}

#[test]
fn a_file_spelling_that_names_nothing_says_what_lists_the_ones_that_do() {
    let directory = store_from("file-refusals", "tree");

    let unknown = stderr(&directory, &["cat", "mzvwutkl", "file:kkkk"]);
    assert!(unknown.contains("identifier starting `kkkk`"), "{unknown}");
    assert!(unknown.contains("historica files"), "{unknown}");

    // A file dropped at this revision is not in the file set, so its
    // identifier does not name a file here even though history holds it.
    let gone = stderr(
        &directory,
        &["cat", "nwlxsqot", &format!("file:{NOTES_FILE}")],
    );
    assert!(gone.contains("identifier starting"), "{gone}");

    // Neither a bookmark nor the alphabet an identifier is spelled in.
    let nonsense = stderr(&directory, &["cat", "mzvwutkl", "file:not-an-id"]);
    assert!(nonsense.contains("`k`–`z`"), "{nonsense}");

    let empty = stderr(&directory, &["cat", "mzvwutkl", "file:"]);
    assert!(empty.contains("wants an identifier"), "{empty}");
}

#[test]
fn a_prefix_that_could_be_two_files_is_refused_and_names_both() {
    // Two identifiers alike to twenty-three characters, which minting will not
    // produce on demand. The revision is hand-written for that reason and for
    // no other: two `add` lines, each a file created empty.
    let directory = repository("file-ambiguous");
    let one = "kmnpqrstvwxyzklmnpqrstvw";
    let two = "kmnpqrstvwxyzklmnpqrstvx";
    fs::write(
        directory.join("history/revisions/two-alike.rev.txt"),
        format!(
            "historica-v0\n\
             change qpvuntsmwlrkzxonmvtplsyq\n\
             author Adam Harris <adam@example.com>\n\
             when 2026-08-21T09:00:00-06:00\n\
             add {one} one.md\n\
             add {two} two.md\n\
             \n\
             Two files whose names are nearly one name\n"
        ),
    )
    .expect("a hand-written revision");

    let refused = stderr(&directory, &["cat", "head", "file:kmnp"]);
    assert!(refused.contains("could be 2 files"), "{refused}");
    assert!(
        refused.contains(&format!("file:{one}  one.md")),
        "{refused}"
    );
    assert!(
        refused.contains(&format!("file:{two}  two.md")),
        "{refused}"
    );

    // Spelled in full, each names its own file, which is empty.
    assert_eq!(
        stdout(&directory, &["cat", "head", &format!("file:{one}")]),
        ""
    );
    let report = stdout(&directory, &["check"]);
    assert!(report.ends_with("nothing to report\n"), "{report}");
}

#[test]
fn a_path_spelled_like_an_identifier_is_still_a_path() {
    // The reason decision 0024 gives the identifier a spelling of its own: a
    // path is a value a person chose, and a person may choose this one.
    let directory = repository("file-lookalike");
    let lookalike = "kmnpqrstvwxyzklmnpqrstvw";
    write(&directory, lookalike, "a file with an unusual name\n");
    write(&directory, "file:notes.md", "a file with a worse one\n");
    out(recorded(&directory, &["record", "-m", "Start a journal"]));

    assert_eq!(
        out(recorded(&directory, &["cat", "head", lookalike])),
        "a file with an unusual name\n"
    );
    assert_eq!(
        out(recorded(
            &directory,
            &["cat", "head", &format!("path:{lookalike}")]
        )),
        "a file with an unusual name\n"
    );
    // Nothing here was minted with that identifier, and the spelling says so
    // rather than quietly handing over the file that is called it.
    let as_an_identifier = refused(&directory, &["cat", "head", &format!("file:{lookalike}")]);
    assert!(
        as_an_identifier.contains("identifier starting"),
        "{as_an_identifier}"
    );

    // And `path:` is what reaches a file whose own name begins `file:`.
    assert_eq!(
        out(recorded(&directory, &["cat", "head", "path:file:notes.md"])),
        "a file with a worse one\n"
    );
    let read_as_a_spelling = refused(&directory, &["cat", "head", "file:notes.md"]);
    assert!(
        read_as_a_spelling.contains("`k`–`z`"),
        "{read_as_a_spelling}"
    );
}

#[test]
fn a_bookmark_names_a_file_and_follows_it_through_a_rename() {
    let directory = repository("file-bookmark");
    write(&directory, "notes.md", "one\n");
    out(recorded(&directory, &["record", "-m", "Start a journal"]));

    let said = out(recorded(&directory, &["name", "entry", "head", "notes.md"]));
    assert!(said.starts_with("entry -> file "), "{said}");
    let file = said
        .split_whitespace()
        .next_back()
        .expect("an identifier")
        .to_owned();

    // Decision 0006's format, with 0024's third key, under 0021's suffix.
    assert_eq!(
        fs::read_to_string(directory.join("history/names/entry.txt")).expect("the bookmark"),
        format!("file {file}\n")
    );

    // A bookmark is usable wherever an identifier is.
    assert_eq!(
        out(recorded(&directory, &["cat", "head", "file:entry"])),
        "one\n"
    );

    out(recorded(
        &directory,
        &[
            "record",
            "-m",
            "File it",
            "--move",
            "notes.md=docs/notes.md",
        ],
    ));
    assert_eq!(
        out(recorded(&directory, &["cat", "head", "file:entry"])),
        "one\n"
    );

    // What it resolves to is where the file is now, which is the question the
    // bookmark was made to stop having to ask.
    let listed = out(recorded(&directory, &["names"]));
    assert!(listed.contains(&format!("entry  file {file}")), "{listed}");
    assert!(listed.contains("->  docs/notes.md"), "{listed}");

    let report = out(recorded(&directory, &["check"]));
    assert!(report.ends_with("nothing to report\n"), "{report}");
}

#[test]
fn names_lists_the_three_kinds_apart() {
    let directory = repository("names-three-kinds");
    write(&directory, "notes.md", "one\n");
    out(recorded(&directory, &["record", "-m", "Start a journal"]));

    out(recorded(&directory, &["name", "main", "head"]));
    out(recorded(
        &directory,
        &["name", "pinned", "head", "--revision"],
    ));
    out(recorded(&directory, &["name", "entry", "head", "notes.md"]));

    let listed = out(recorded(&directory, &["names"]));
    assert_eq!(listed.lines().count(), 3, "{listed}");
    assert!(listed.contains("entry   file "), "{listed}");
    assert!(listed.contains("main    change "), "{listed}");
    assert!(listed.contains("pinned  revision "), "{listed}");
}

#[test]
fn a_file_bookmark_is_not_a_revision_and_says_so() {
    let directory = repository("file-bookmark-position");
    write(&directory, "notes.md", "one\n");
    out(recorded(&directory, &["record", "-m", "Start a journal"]));
    out(recorded(&directory, &["name", "entry", "head", "notes.md"]));

    let as_a_target = refused(&directory, &["show", "entry"]);
    assert!(
        as_a_target.contains("a file is not a revision"),
        "{as_a_target}"
    );
    assert!(as_a_target.contains("file:entry"), "{as_a_target}");

    // And the other way: a change bookmark where a file belongs.
    out(recorded(&directory, &["name", "main", "head"]));
    let other = refused(&directory, &["cat", "head", "file:main"]);
    assert!(other.contains("names a change"), "{other}");
}

#[test]
fn naming_a_file_the_store_does_not_hold_is_refused() {
    let directory = repository("file-bookmark-refusals");
    write(&directory, "notes.md", "one\n");
    out(recorded(&directory, &["record", "-m", "Start a journal"]));

    let absent = refused(&directory, &["name", "gone", "head", "docs/nope.md"]);
    assert!(absent.contains("holds no file at"), "{absent}");
    assert!(
        !directory.join("history/names/gone.txt").exists(),
        "a bookmark nothing could resolve is not written"
    );

    let unknown = refused(&directory, &["name", "gone", "head", "file:kkkk"]);
    assert!(unknown.contains("identifier starting"), "{unknown}");

    // A file bookmark has nothing to pin, which is said rather than ignored.
    let pinned = refused(
        &directory,
        &["name", "gone", "head", "notes.md", "--revision"],
    );
    assert!(pinned.contains("nothing to pin"), "{pinned}");
}

#[test]
fn a_bookmark_spelled_as_an_identifier_is_refused() {
    let directory = repository("bookmark-lookalike");
    write(&directory, "notes.md", "one\n");
    out(recorded(&directory, &["record", "-m", "Start a journal"]));

    // Every position looks a bookmark up before parsing anything, so a name
    // spelled as an identifier would shadow the identifier it spells.
    let spelled = "kmnpqrstvwxyzklmnpqrstvw";
    let refused_file = refused(&directory, &["name", spelled, "head", "notes.md"]);
    assert!(
        refused_file.contains("spelled as an identifier"),
        "{refused_file}"
    );
    let refused_change = refused(&directory, &["name", spelled, "head"]);
    assert!(
        refused_change.contains("spelled as an identifier"),
        "{refused_change}"
    );

    // An abbreviation is not an identifier: decision 0001's answer stands.
    out(recorded(&directory, &["name", "kmnp", "head"]));
}

#[test]
fn an_external_identifier_joins_a_history_as_a_bookmark_name() {
    // The constraint decision 0024 was written for. An outside system whose
    // identifiers contain digits cannot supply a file identifier without
    // breaking 0001's disjoint alphabets, so the join is a bookmark whose
    // *name* is the outside identifier — a name being just a string.
    let directory = repository("external-name");
    write(&directory, "notes.md", "one\n");
    out(recorded(&directory, &["record", "-m", "Start a journal"]));

    let noid = "3t9x5kf2qw";
    out(recorded(&directory, &["name", noid, "head", "notes.md"]));
    assert_eq!(
        out(recorded(
            &directory,
            &["cat", "head", &format!("file:{noid}")]
        )),
        "one\n"
    );

    out(recorded(
        &directory,
        &[
            "record",
            "-m",
            "File it",
            "--move",
            "notes.md=docs/notes.md",
        ],
    ));
    assert_eq!(
        out(recorded(
            &directory,
            &["cat", "head", &format!("file:{noid}")]
        )),
        "one\n",
        "the outside system's name survives what the path does not"
    );
}

#[test]
fn at_takes_a_bookmark_where_it_takes_an_identifier() {
    let directory = repository("at-bookmark");
    write(&directory, "notes.md", "one\n");
    out(recorded(&directory, &["record", "-m", "Start a journal"]));
    out(recorded(&directory, &["name", "entry", "head", "notes.md"]));

    fs::create_dir_all(directory.join("docs")).expect("a directory");
    fs::rename(directory.join("notes.md"), directory.join("docs/notes.md")).expect("a rename");
    let said = out(recorded(
        &directory,
        &["record", "-m", "File it", "--at", "entry=docs/notes.md"],
    ));
    assert!(said.contains("moved   docs/notes.md"), "{said}");

    // The other kinds of bookmark are refused there rather than parsed.
    out(recorded(&directory, &["name", "main", "head"]));
    let other = refused(
        &directory,
        &["record", "-m", "x", "--at", "main=docs/notes.md"],
    );
    assert!(other.contains("this position names a file"), "{other}");
}

#[test]
fn a_hand_written_file_bookmark_naming_nothing_is_a_note() {
    let directory = store_from("file-bookmark-note", "tree");
    fs::write(
        directory.join("history/names/elsewhere.txt"),
        "file kmnpqrstvwxyzklmnpqrstvw\n",
    )
    .expect("a bookmark");

    // Decision 0006's reason, unchanged: the name may be ahead of the sync.
    let report = stdout(&directory, &["check"]);
    assert!(report.contains("note: `elsewhere`"), "{report}");
    assert!(!report.contains("error:"), "{report}");

    // And one naming a file the store does hold is neither.
    fs::write(
        directory.join("history/names/entry.txt"),
        format!("file {README_FILE}\n"),
    )
    .expect("a bookmark");
    let malformed = stdout(&directory, &["check"]);
    assert!(!malformed.contains("`entry`"), "{malformed}");

    fs::write(
        directory.join("history/names/broken.txt"),
        "file nonsense\n",
    )
    .expect("a bookmark");
    let output = run(&directory, &["check"]);
    assert_eq!(output.status.code(), Some(1));
    let report = String::from_utf8(output.stdout).expect("printed text");
    assert!(report.contains("`file` and a file identifier"), "{report}");
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

    // The directory carries the revision, so what is left is the path — and
    // decision 0018 says a path as a path, so the revision's folder is the
    // subtree of the repository that revision touched.
    let operations = directory.join("history/operations");
    let filed: Vec<String> = walk_names(&operations);
    assert!(
        filed.iter().all(|name| name.contains('/')),
        "every document should sit under a revision directory: {filed:?}"
    );
    assert!(
        filed.iter().all(|name| !name.contains('⁄')),
        "nothing stands in for a separator: {filed:?}"
    );
    // Decision 0017: the first revision states the file's lines outright, so
    // what sits under it is the file, under its own name, in its own folder.
    assert!(
        filed
            .iter()
            .any(|name| name.ends_with("Start a journal/src/cli/mod.rs")),
        "{filed:?}"
    );
    assert!(
        filed
            .iter()
            .any(|name| name.ends_with("Start a journal/a.md")),
        "{filed:?}"
    );
    assert!(
        filed
            .iter()
            .any(|name| name.ends_with("Say more/src/cli/mod.rs.ops.txt")),
        "one path, two revisions, two directories: {filed:?}"
    );
    // And the directories are real ones a person can open.
    let journal = fs::read_dir(&operations)
        .expect("the operations directory")
        .filter_map(Result::ok)
        .map(|entry| entry.path())
        .find(|path| path.to_string_lossy().ends_with("Start a journal"))
        .expect("a directory per revision");
    assert!(journal.join("src/cli").is_dir(), "{filed:?}");
    assert!(
        filed.iter().all(|name| !name.contains(".ops.txt.ops.txt")),
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
fn a_payload_and_a_document_one_path_apart_are_parted_by_a_digest() {
    let directory = repository("arrange-collision");
    fs::create_dir_all(directory.join("notes")).expect("directories");
    write(&directory, "notes/x", "the file\n");
    out(recorded(&directory, &["record", "-m", "First"]));

    // One revision that edits `notes/x` — filed as `notes/x.ops` — and adds a
    // file actually called `notes/x.ops`, filed as itself. The only two names
    // decision 0018 leaves that can still meet.
    write(&directory, "notes/x", "the file, edited\n");
    write(
        &directory,
        "notes/x.ops.txt",
        "a file that is not a document\n",
    );
    out(recorded(&directory, &["record", "-m", "Both"]));
    out(recorded(&directory, &["arrange"]));

    let filed = walk_names(&directory.join("history/operations"));
    let both: Vec<&String> = filed
        .iter()
        .filter(|name| name.contains("Both/notes/"))
        .collect();
    assert_eq!(both.len(), 2, "{filed:?}");
    assert!(
        both.iter().any(|name| name.ends_with(".ops.txt")),
        "the document keeps the suffix that says it is one: {both:?}"
    );
    assert!(
        both.iter()
            .any(|name| name.contains("x.ops.txt ") && !name.ends_with(".ops.txt")),
        "and the payload keeps clear of the suffix a reader claims: {both:?}"
    );
    assert!(
        stdout(&directory, &["check"]).ends_with("nothing to report\n"),
        "{filed:?}"
    );
}

#[test]
fn a_file_of_this_formats_own_extension_is_still_content() {
    // Found by recording Historica into itself: the corpus holds `.ops` files
    // that are deliberately invalid, and filing one under its own name handed
    // it to the parser, which refused it. A store that writes something it
    // cannot read back is the one failure this format is least willing to
    // produce, so a payload never carries the suffix that says "document".
    let directory = repository("record-ops-payload");
    fs::create_dir_all(directory.join("corpus")).expect("directories");
    let invalid = "historica-v0\n\ndelete 0 1\n-a\ndelete 1 2\n-b\n-c\n";
    let other = "historica-v0\n\ninsert 0\n+a\ninsert 0\n+b\n";
    write(&directory, "corpus/adjacent-deletes.ops", invalid);
    write(&directory, "corpus/also-invalid.ops.txt", other);
    write(&directory, "notes.md", "an entry\n");
    out(recorded(&directory, &["record", "-m", "Initial state"]));

    let filed = walk_names(&directory.join("history/operations"));
    assert!(
        filed.iter().all(|name| !name.ends_with(".ops.txt")),
        "a payload must not be filed as a document: {filed:?}"
    );
    // Decision 0021 spent the format's one free moment on this: `.ops` is no
    // longer a name a reader claims, so a file called that keeps its own.
    assert!(
        filed
            .iter()
            .any(|name| name.ends_with("corpus/adjacent-deletes.ops")),
        "an ordinary `.ops` file keeps its name: {filed:?}"
    );
    assert!(
        filed
            .iter()
            .any(|name| name.contains("corpus/also-invalid.ops.txt ")),
        "and only the written suffix yields: {filed:?}"
    );

    // The store reads back, and the file comes out byte for byte.
    let status = out(recorded(&directory, &["status"]));
    assert!(
        status.contains("nothing here differs from what is recorded"),
        "{status}"
    );
    assert_eq!(
        stdout(&directory, &["cat", "head", "corpus/adjacent-deletes.ops"]),
        invalid
    );
    assert!(
        stdout(&directory, &["check"]).ends_with("nothing to report\n"),
        "{filed:?}"
    );
}

#[test]
fn a_file_browser_writing_into_the_store_breaks_nothing() {
    // Found by opening a store in Finder, which writes a `.DS_Store` into
    // every folder it displays and does not ask. The payload it landed on was
    // destroyed, and every command that opened the store failed on content it
    // said it held. Decision 0022: a payload is never filed under a name the
    // store does not own, and a file inside the store carrying one is
    // somebody else's rather than content.
    let directory = repository("record-platform-names");
    write(&directory, "notes.md", "an entry\n");
    // Recorded deliberately, so `skipped.txt`'s default is not what is under
    // test: a person may record one, and the store still has to survive it.
    fs::write(directory.join(".DS_Store"), [0x00, 0x01, 0x42, 0xff]).expect("metadata");
    out(recorded(&directory, &["skip"]));
    fs::write(
        directory.join("history/skipped.txt"),
        "skip nothing-at-all\n",
    )
    .expect("rules");
    out(recorded(&directory, &["record", "-m", "Initial state"]));

    let filed = walk_names(&directory.join("history/operations"));
    assert!(
        filed.iter().all(|name| !name.ends_with("/.DS_Store")),
        "a payload must not sit where a file browser will write: {filed:?}"
    );
    assert!(
        filed.iter().any(|name| name.contains(".DS_Store ")),
        "and it keeps its name, with the digest that moves it aside: {filed:?}"
    );

    // Now be the file browser: write one into every directory of the store,
    // `revisions/` and `names/` included.
    let operations = directory.join("history/operations");
    let mut directories = vec![
        directory.join("history"),
        directory.join("history/revisions"),
        directory.join("history/names"),
        operations.clone(),
    ];
    for name in &filed {
        if let Some(parent) = operations.join(name).parent() {
            directories.push(parent.to_path_buf());
        }
    }
    for at in directories {
        fs::write(at.join(".DS_Store"), b"finder's own metadata\n").expect("a stray file");
    }

    // The store is unharmed, and says nothing about the files it did not write.
    assert_eq!(
        run(&directory, &["cat", "head", ".DS_Store"]).stdout,
        [0x00, 0x01, 0x42, 0xff],
        "the payload is still what was recorded"
    );
    assert!(
        stdout(&directory, &["check"]).ends_with("nothing to report\n"),
        "somebody else's file in our folder is not a finding"
    );
    let status = out(recorded(&directory, &["status"]));
    assert!(
        status.contains("nothing here differs from what is recorded"),
        "{status}"
    );
}

#[test]
fn a_file_where_another_needs_a_directory_yields_its_readable_name() {
    // 0008 has no directories, so a history may hold both `notes` and
    // `notes/photo.png`. No working copy can, which is why this store is built
    // by hand — and no filesystem can file both under their own names either.
    let directory = repository("arrange-file-and-directory");
    let store = directory.join("history");
    let short = fs::read(corpus("whole").join("operations/01-photo.png")).expect("a payload");
    let long = fs::read(corpus("whole").join("operations/02-photo.png")).expect("a payload");
    let short_id = historica::format::digest(&short);
    let long_id = historica::format::digest(&long);
    fs::write(store.join("operations").join(short_id.to_string()), &short).expect("a payload");
    fs::write(store.join("operations").join(long_id.to_string()), &long).expect("a payload");

    let revision = format!(
        "historica-v1\n\
         change qpvuntsmwlrkzxonmvtplsyq\n\
         author Adam Harris <adam@example.com>\n\
         when 2026-08-20T09:14:02-06:00\n\
         add kkkkkkkkkkkkkkkkkkkkkkkk notes\n\
         add llllllllllllllllllllllll notes/photo.png\n\
         bytes kkkkkkkkkkkkkkkkkkkkkkkk {short_id}\n\
         bytes llllllllllllllllllllllll {long_id}\n\
         \n\
         A file and a directory of one name\n"
    );
    fs::write(
        store.join("revisions").join("hand-written.rev.txt"),
        &revision,
    )
    .expect("a revision");

    out(recorded(&directory, &["arrange"]));
    let filed = walk_names(&store.join("operations"));
    assert!(
        filed.iter().any(|name| name.ends_with("/notes/photo.png")),
        "the longer path keeps its name: {filed:?}"
    );
    assert!(
        filed
            .iter()
            .any(|name| name.ends_with(&format!("/{short_id}"))),
        "and the file at the shorter path yields to its digest: {filed:?}"
    );
}

#[test]
fn arrange_tidies_the_directory_it_emptied_and_spares_the_one_it_did_not() {
    let directory = repository("arrange-tidy");
    write(&directory, "a.md", "one\n");
    write(&directory, "b.md", "other\n");
    out(recorded(&directory, &["record", "-m", "First"]));

    // Two payloads, re-filed by hand into two directories of a person's own,
    // which decision 0003 says they may do and 0019 says is not a fault.
    let operations = directory.join("history/operations");
    let documents = walk_names(&operations);
    assert_eq!(documents.len(), 2, "{documents:?}");

    // The first is filed several directories deep, which decision 0018's
    // upward tidy has to walk back out of.
    let alone = operations.join("alone/and/deeper/still");
    let shared = operations.join("shared");
    fs::create_dir_all(&alone).expect("a directory");
    fs::create_dir_all(&shared).expect("a directory");
    let basename = |name: &String| name.rsplit('/').next().expect("a filename").to_owned();
    fs::rename(
        operations.join(&documents[0]),
        alone.join(basename(&documents[0])),
    )
    .expect("filing");
    fs::rename(
        operations.join(&documents[1]),
        shared.join(basename(&documents[1])),
    )
    .expect("filing");
    // Something that is not a document, and not this command's to delete.
    fs::write(shared.join("notes.txt"), "why these are here\n").expect("a file");

    out(recorded(&directory, &["arrange"]));

    // The directory arranging emptied is gone. The one still holding
    // something is not: `remove_dir` refuses a directory that holds anything,
    // which is the whole of the guard.
    assert!(
        !operations.join("alone").exists(),
        "an emptied directory should be tidied away, and so should the ones above it"
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
fn a_store_is_written_readable_and_arrange_has_nothing_to_do() {
    // Decision 0019: the name a file is written under is the name it keeps, so
    // the folder a person opens is readable without their having learnt that a
    // command exists. `arrange` moving nothing is the test that says the
    // writer and the scheme agree.
    let directory = repository("record-names");
    fs::create_dir_all(directory.join("notes")).expect("directories");
    write(&directory, "notes/a.md", "one\n");
    out(recorded(&directory, &["record", "-m", "Start a journal"]));
    write(&directory, "notes/a.md", "two\n");
    out(recorded(&directory, &["record", "-m", "Say more"]));

    let revisions = walk_names(&directory.join("history/revisions"));
    assert!(
        revisions
            .iter()
            .any(|name| name.ends_with("Start a journal.rev.txt")),
        "{revisions:?}"
    );
    assert!(
        revisions
            .iter()
            .any(|name| name.ends_with("Say more.rev.txt")),
        "{revisions:?}"
    );
    let filed = walk_names(&directory.join("history/operations"));
    assert!(
        filed
            .iter()
            .any(|name| name.ends_with("Start a journal/notes/a.md")),
        "{filed:?}"
    );
    assert!(
        filed
            .iter()
            .any(|name| name.ends_with("Say more/notes/a.md.ops.txt")),
        "{filed:?}"
    );
    // And nothing in the folder is a hash.
    let hashed = |name: &String| {
        let last = name.rsplit('/').next().expect("a filename");
        let stem = last
            .strip_suffix(".rev.txt")
            .or_else(|| last.strip_suffix(".ops.txt"));
        let stem = stem.unwrap_or(last);
        stem.len() == 64 && stem.chars().all(|c| c.is_ascii_hexdigit())
    };
    assert!(
        !filed.iter().chain(&revisions).any(hashed),
        "{filed:?} {revisions:?}"
    );

    assert_eq!(stdout(&directory, &["cat", "head", "notes/a.md"]), "two\n");
    let done = stdout(&directory, &["arrange"]);
    assert!(done.contains("0 renamed, 2 already arranged"), "{done}");
    assert!(
        stdout(&directory, &["check"]).ends_with("nothing to report\n"),
        "a store nobody arranged is an ordinary store"
    );
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
fn receive_unions_independent_work_without_touching_either_working_copy() {
    let here = repository("receive-here");
    write(&here, "notes.md", "common\n");
    out(recorded(&here, &["record", "-m", "Common root"]));

    let there = scratch("receive-there");
    copy_tree(&here, &there);
    write(&here, "notes.md", "ours\n");
    out(recorded(&here, &["record", "-m", "Work done here"]));
    write(&there, "notes.md", "theirs\n");
    out(recorded(&there, &["record", "-m", "Work done there"]));

    let source = there.to_string_lossy();
    let before_source = walk_names(&there.join("history"));
    let planned = run(&here, &["receive", &source, "--dry-run"]);
    assert!(planned.status.success());
    let planned = String::from_utf8(planned.stdout).expect("printed text");
    assert!(planned.contains("would receive 1 revisions"), "{planned}");
    assert!(
        !stdout(&here, &["log"]).contains("Work done there"),
        "a dry run imported history"
    );

    let received = stdout(&here, &["receive", &source]);
    assert!(received.contains("received 1 revisions"), "{received}");
    let log = stdout(&here, &["log"]);
    assert!(log.contains("Work done here"), "{log}");
    assert!(log.contains("Work done there"), "{log}");
    assert_eq!(
        fs::read_to_string(here.join("notes.md")).expect("working file"),
        "ours\n"
    );
    assert_eq!(
        fs::read_to_string(there.join("notes.md")).expect("working file"),
        "theirs\n"
    );
    assert_eq!(walk_names(&there.join("history")), before_source);
    assert!(stdout(&here, &["check"]).ends_with("nothing to report\n"));
}

#[test]
fn receive_reports_mutable_conflicts_before_writing_history() {
    let here = repository("receive-conflict-here");
    write(&here, "notes.md", "common\n");
    out(recorded(&here, &["record", "-m", "Common root"]));
    let there = scratch("receive-conflict-there");
    copy_tree(&here, &there);

    write(&here, "notes.md", "ours\n");
    out(recorded(&here, &["record", "-m", "Work done here"]));
    out(recorded(&here, &["name", "shared", "head"]));
    write(&there, "notes.md", "theirs\n");
    out(recorded(&there, &["record", "-m", "Work done there"]));
    out(recorded(&there, &["name", "shared", "head"]));

    let source = there.to_string_lossy();
    let planned = run(&here, &["receive", &source, "--dry-run"]);
    assert_eq!(planned.status.code(), Some(1));
    let planned = String::from_utf8(planned.stdout).expect("printed text");
    assert!(planned.contains("conflict: name shared"), "{planned}");

    let complaint = stderr(&here, &["receive", &source]);
    assert!(complaint.contains("mutable"), "{complaint}");
    assert!(
        !stdout(&here, &["log"]).contains("Work done there"),
        "a refused receive wrote immutable history before noticing the conflict"
    );
}

#[test]
fn receiving_a_forgetting_document_destroys_the_original() {
    let here = repository("receive-forgetting-here");
    write(&here, "notes.md", "public\nsecret\n");
    out(recorded(&here, &["record", "-m", "A secret"]));
    let there = scratch("receive-forgetting-there");
    copy_tree(&here, &there);

    let target = head_of(&there);
    out(recorded(
        &there,
        &["forget", &target, "notes.md", "--lines", "2"],
    ));
    assert_eq!(
        stdout(&here, &["cat", "head", "notes.md"]),
        "public\nsecret\n"
    );

    let source = there.to_string_lossy();
    let received = stdout(&here, &["receive", &source]);
    assert!(received.contains("destroyed"), "{received}");
    assert_eq!(
        stdout(&here, &["cat", "head", "notes.md"]),
        "public\n\\ forgotten\n"
    );
    assert_eq!(
        fs::read_to_string(here.join("notes.md")).expect("working file"),
        "public\nsecret\n",
        "receive changed the working copy"
    );
}

#[test]
fn receive_requires_an_explicit_join_for_unrelated_histories() {
    let here = repository("receive-unrelated-here");
    write(&here, "here.md", "here\n");
    out(recorded(&here, &["record", "-m", "Here"]));
    let there = repository("receive-unrelated-there");
    write(&there, "there.md", "there\n");
    out(recorded(&there, &["record", "-m", "There"]));

    let source = there.to_string_lossy();
    let complaint = stderr(&here, &["receive", &source]);
    assert!(complaint.contains("unrelated"), "{complaint}");
    out(recorded(&here, &["receive", &source, "--join-unrelated"]));
    assert!(stdout(&here, &["log"]).contains("There"));
}

#[test]
fn arrange_renames_a_filed_revision_where_it_sits() {
    let directory = store_from("arrange-nested", "tree");
    let revisions = directory.join("history/revisions");
    let filed = revisions.join("early/2025");
    fs::create_dir_all(&filed).expect("directories");
    fs::rename(
        revisions.join("01-start.rev.txt"),
        filed.join("01-start.rev.txt"),
    )
    .expect("filing a revision away");

    let before = stdout(&directory, &["log"]);
    let done = stdout(&directory, &["arrange"]);

    // Renamed, not moved. A person who filed it there meant to.
    assert!(
        filed.join("2025-08-19 Start a journal.rev.txt").exists(),
        "{done}"
    );
    assert!(
        !revisions
            .join("2025-08-19 Start a journal.rev.txt")
            .exists(),
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
        directory
            .join("history/revisions/01-start.rev.txt")
            .exists(),
        "a dry run renames nothing"
    );

    let done = stdout(&directory, &["arrange"]);
    assert!(done.contains("4 renamed"), "{done}");
    assert!(
        directory
            .join("history/revisions/2025-08-19 Start a journal.rev.txt")
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

/// Everything a command that should have failed said, with an author stated.
fn refused(directory: &Path, arguments: &[&str]) -> String {
    let output = recorded(directory, arguments);
    assert!(
        !output.status.success(),
        "`{}` should have been refused: {}",
        arguments.join(" "),
        String::from_utf8_lossy(&output.stdout)
    );
    String::from_utf8(output.stderr).expect("printed text")
}

/// The digest of the current head, as `log` abbreviates it.
fn head_of(directory: &Path) -> String {
    out(recorded(directory, &["log"]))
        .lines()
        .find(|line| line.contains("(head") && !line.contains("superseded"))
        .and_then(|line| line.split_whitespace().nth(1))
        .expect("a head nothing has rewritten")
        .to_owned()
}

/// The one file identifier `files` prints at a revision.
fn one_file(directory: &Path, target: &str) -> String {
    out(recorded(directory, &["files", target]))
        .split_whitespace()
        .next_back()
        .expect("a file ID")
        .to_owned()
}

/// One header line of a stored document, by its key.
fn header(document: &str, key: &str) -> String {
    document
        .lines()
        .find(|line| line.starts_with(&format!("{key} ")))
        .unwrap_or_else(|| panic!("a `{key}` line in\n{document}"))
        .to_owned()
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
    let content = out(recorded(
        &directory,
        &["cat", "head", &format!("file:{file}")],
    ));
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
#[cfg(unix)]
fn what_the_format_cannot_hold_is_refused_by_name() {
    let directory = repository("record-refusals");
    write(&directory, "fine.md", "text\n");
    std::os::unix::fs::symlink("/etc/hosts", directory.join("link")).expect("a symlink");

    let refused = recorded(&directory, &["record", "-m", "Everything"]);
    assert!(!refused.status.success());
    let complaint = String::from_utf8_lossy(&refused.stderr).into_owned();
    assert!(complaint.contains("link"), "{complaint}");
    assert!(complaint.contains("skip"), "{complaint}");

    // Which is the fix the message names.
    write(&directory, "history/skipped.txt", "skip link\n");
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
fn a_file_of_bytes_is_recorded_whole_and_comes_back_byte_for_byte() {
    let directory = repository("record-bytes");
    let picture: Vec<u8> = vec![0xff, 0xd8, 0xff, 0x00, 0x10, 0x9a, 0x00];
    write(
        &directory,
        "notes.md",
        "an entry, and the picture it is about\n",
    );
    fs::create_dir_all(directory.join("notes")).expect("a directory");
    fs::write(directory.join("notes/photo.png"), &picture).expect("the picture");

    let recorded_out = out(recorded(&directory, &["record", "-m", "Keep the photo"]));
    assert!(recorded_out.contains("notes/photo.png"), "{recorded_out}");

    // Decision 0017: the payload in the store *is* the file.
    let stored = walk_names(&directory.join("history/operations"));
    assert_eq!(
        stored.len(),
        2,
        "two payloads, no operation documents: {stored:?}"
    );
    let held: Vec<Vec<u8>> = stored
        .iter()
        .map(|name| fs::read(directory.join("history/operations").join(name)).expect("a payload"))
        .collect();
    assert!(held.contains(&picture), "the picture is stored as itself");
    assert!(
        held.contains(&b"an entry, and the picture it is about\n".to_vec()),
        "and so is the entry: no `+` down the left margin"
    );

    // And it comes back out unchanged.
    let printed = run(&directory, &["cat", "head", "notes/photo.png"]);
    assert_eq!(printed.stdout, picture);

    // A file's kind is fixed when it is added, so editing the bytes is
    // ordinary and states the whole content again.
    let edited: Vec<u8> = vec![0xff, 0xd8, 0xff, 0x01];
    fs::write(directory.join("notes/photo.png"), &edited).expect("the picture");
    let status = out(recorded(&directory, &["status"]));
    assert!(status.contains("edited  notes/photo.png"), "{status}");
    out(recorded(&directory, &["record", "-m", "A better crop"]));
    assert_eq!(
        run(&directory, &["cat", "head", "notes/photo.png"]).stdout,
        edited
    );

    assert!(
        stdout(&directory, &["check"]).ends_with("nothing to report\n"),
        "a store with a picture in it is an ordinary store"
    );
}

#[test]
fn a_file_recorded_as_lines_that_stops_being_text_is_refused_with_the_fix() {
    let directory = repository("record-kind-change");
    write(&directory, "notes.md", "prose\n");
    out(recorded(&directory, &["record", "-m", "An entry"]));

    // Decision 0017: the kind belongs to the file's identity, so this is not
    // an edit, and the refusal says what it is instead.
    fs::write(directory.join("notes.md"), [0xff, 0xfe, 0x00]).expect("bytes");
    let listed = out(recorded(&directory, &["status"]));
    assert!(listed.contains("refused notes.md"), "{listed}");
    assert!(listed.contains("drop it and add it again"), "{listed}");
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

    // Appended after the syntax note `init` wrote. Nothing is skipped by
    // default; defaults belong to the host or project.
    let text = fs::read_to_string(directory.join("history/skipped.txt")).expect("the file");
    assert!(text.starts_with('#'), "{text}");
    assert!(!text.contains("skip-suffix .DS_Store"), "{text}");
    assert!(text.ends_with("skip target/\nskip-suffix .tmp\n"), "{text}");

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
        fs::read_to_string(directory.join("history/skipped.txt")).expect("the file"),
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
    let text = fs::read_to_string(directory.join("history/skipped.txt")).expect("the file");
    assert!(!text.contains("drafts"), "{text}");
    assert!(!text.contains(".tmp"), "{text}");
}

#[test]
fn skip_leaves_the_file_a_person_wrote_alone() {
    let directory = repository("skip-command-append");
    write(
        &directory,
        "history/skipped.txt",
        "skip one/\n\nskip-suffix .bin\n",
    );

    out(recorded(&directory, &["skip", "two/"]));

    // The blank line the parser ignores is a blank line the person meant.
    assert_eq!(
        fs::read_to_string(directory.join("history/skipped.txt")).expect("the file"),
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
    write(&directory, "history/skipped.txt", "skip drafts/\n");
    let refused = recorded(&directory, &["record", "-m", "Second"]);
    assert!(!refused.status.success());
    let complaint = String::from_utf8_lossy(&refused.stderr).into_owned();
    assert!(complaint.contains("drafts/one.md"), "{complaint}");
    assert!(complaint.contains("history/skipped.txt"), "{complaint}");

    // A rule over a path nothing has recorded is ordinary, which is the whole
    // point of the file.
    write(&directory, "history/skipped.txt", "skip-suffix .tmp\n");
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
    write(&directory, "history/skipped.txt", "skip drafts/\n");
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

/// Decision 0032's tool-less merge, carried out and then read.
///
/// `tests/by-hand.sh` builds a whole store — root, two branches, a merge
/// stating its resolution, and a revision counting into what that merge
/// stated — with nothing but `cat` and a checksum program. Before 0032 the
/// merge in it could not be written at all: not laboriously, not carefully,
/// at all, because the only spelling of a resolution was a delta positioned
/// into a state no editor can compute.
///
/// What this asserts is the other direction of the same claim. The tool reads
/// what the hand wrote, finds nothing to report, materialises the file, and
/// records on top of it.
#[test]
fn a_store_written_by_hand_is_one_this_tool_reads_and_carries_on_from() {
    let directory = scratch("by-hand");
    let script = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/by-hand.sh");
    let built = Command::new("sh")
        .arg(&script)
        .arg(directory.join("history"))
        .output()
        .expect("a shell");
    assert!(
        built.status.success(),
        "{}",
        String::from_utf8_lossy(&built.stderr)
    );

    assert!(
        out(recorded(&directory, &["check"])).ends_with("nothing to report\n"),
        "a store written with an editor is a store"
    );
    let log = out(recorded(&directory, &["log"]));
    assert!(
        log.contains("Read both sides and say what the file is"),
        "{log}"
    );

    // The merge materialises by following its resolution, and the revision
    // after it by arithmetic against what that resolution stated.
    assert_eq!(
        out(recorded(&directory, &["cat", "head", "notes.txt"])),
        "alpha\ndelta\nbravo\necho\ngolf\n"
    );

    // And the tool carries on from it: the folder is written out, edited, and
    // recorded, against a history no part of which this binary wrote.
    out(recorded(&directory, &["update"]));
    assert_eq!(
        fs::read_to_string(directory.join("notes.txt")).expect("the materialised file"),
        "alpha\ndelta\nbravo\necho\ngolf\n"
    );
    write(
        &directory,
        "notes.txt",
        "alpha\ndelta\nbravo\necho\ngolf\nhotel\n",
    );
    let recording = out(recorded(&directory, &["record", "-m", "and on"]));
    assert!(recording.contains("edited  notes.txt"), "{recording}");
    assert!(out(recorded(&directory, &["check"])).ends_with("nothing to report\n"));
}

/// Decision 0033: a folder that hands back a decomposed name records the
/// composed one, and goes on holding the file it already had.
#[test]
fn a_decomposed_filename_is_recorded_under_one_spelling() {
    let directory = repository("nfc");
    // `café.md`, written with `e` and a combining acute — which is what a
    // filesystem that normalises to NFD hands back, and what some editors
    // and some keyboards produce directly.
    write(&directory, "cafe\u{301}.md", "un café\n");
    let recording = out(recorded(&directory, &["record", "-m", "a decomposed name"]));
    assert!(recording.contains("caf\u{e9}.md"), "{recording}");

    let document = out(recorded(&directory, &["show", "head"]));
    assert!(
        document.contains("caf\u{e9}.md"),
        "the store records the composed spelling: {document}"
    );
    assert!(
        !document.contains("cafe\u{301}.md"),
        "and only that one: {document}"
    );

    // Reading it back works under either spelling a person might type.
    for spelling in ["caf\u{e9}.md", "cafe\u{301}.md"] {
        assert_eq!(
            out(recorded(&directory, &["cat", "head", spelling])),
            "un café\n",
            "{spelling:?}"
        );
    }

    // And nothing has changed: the folder is the file it already had, under
    // the name it already had, whatever the store spells it.
    let status = out(recorded(&directory, &["status"]));
    assert!(status.contains("nothing"), "{status}");

    // An update that has to write goes to the file the folder holds rather
    // than laying a composed twin beside a decomposed original.
    write(&directory, "cafe\u{301}.md", "un café serré\n");
    out(recorded(&directory, &["record", "-m", "stronger"]));
    let stronger = out(recorded(&directory, &["log"]))
        .lines()
        .next()
        .and_then(|line| line.split_whitespace().next())
        .expect("the head")
        .to_owned();
    out(recorded(
        &directory,
        &["abandon", &stronger, "-m", "not that strong"],
    ));
    out(recorded(&directory, &["update"]));
    assert_eq!(
        fs::read_to_string(directory.join("cafe\u{301}.md")).expect("the file the folder holds"),
        "un café\n"
    );

    let names: Vec<String> = fs::read_dir(&directory)
        .expect("the repository")
        .filter_map(Result::ok)
        .map(|entry| entry.file_name().to_string_lossy().into_owned())
        .filter(|name| name.ends_with(".md"))
        .collect();
    assert_eq!(
        names.len(),
        1,
        "no second file was laid beside it: {names:?}"
    );
}

#[test]
fn a_recorded_merge_states_its_resolution_and_the_next_revision_counts_into_it() {
    let (directory, mine, theirs) = diverged(
        "merge-resolution",
        "one\nMINE\nthree\n",
        "one\nTHEIRS\nthree\n",
    );
    write(&directory, "f.md", "one\nBOTH\nthree\n");
    out(recorded(
        &directory,
        &["record", "--merge", &mine, "--merge", &theirs, "-m", "Join"],
    ));

    // Decision 0032: the merge's `edit` line names a resolution, and a
    // resolution names the documents its lines come from rather than
    // restating them.
    let operations = directory.join("history/operations");
    let resolution = walk_names(&operations)
        .into_iter()
        .map(|name| fs::read_to_string(operations.join(name)).expect("a document"))
        .find(|text| text.contains("\nkeep "))
        .expect("a resolution");
    assert!(
        resolution.starts_with("historica-v3\nresult "),
        "{resolution}"
    );
    // `one` and `three` survive under their own names, so the only line the
    // resolution restates is the one the person wrote while resolving.
    assert_eq!(
        resolution.lines().filter(|line| *line == "+BOTH").count(),
        1,
        "{resolution}"
    );
    assert_eq!(
        resolution
            .lines()
            .filter(|line| line.starts_with('+'))
            .count(),
        1,
        "{resolution}"
    );

    // And the revision after counts its positions into the file the merge
    // stated, which is arithmetic rather than an algorithm.
    write(&directory, "f.md", "one\nBOTH\nthree\nfour\n");
    out(recorded(&directory, &["record", "-m", "carry on"]));
    assert_eq!(
        out(recorded(&directory, &["cat", "head", "f.md"])),
        "one\nBOTH\nthree\nfour\n"
    );
    assert!(out(recorded(&directory, &["check"])).ends_with("nothing to report\n"));
}

/// Decision 0032's grammar has no resolution with no pieces, so a merge
/// cannot also be the revision that empties a contested file.
#[test]
fn a_merge_that_would_empty_a_contested_file_says_so() {
    let (directory, mine, theirs) = diverged(
        "merge-emptied",
        "one\nMINE\nthree\n",
        "one\nTHEIRS\nthree\n",
    );
    write(&directory, "f.md", "");
    let refused = recorded(
        &directory,
        &["record", "--merge", &mine, "--merge", &theirs, "-m", "Join"],
    );
    assert!(!refused.status.success());
    let complaint = String::from_utf8_lossy(&refused.stderr);
    assert!(complaint.contains("f.md"), "{complaint}");
    assert!(complaint.contains("no way to state"), "{complaint}");
}

#[test]
fn a_contested_attachment_is_recorded_only_when_accepted_by_path() {
    let directory = repository("merge-attachment");
    fs::write(directory.join("photo.bin"), [0x00, 0x01]).expect("the root attachment");
    out(recorded(&directory, &["record", "-m", "root"]));
    let root = out(recorded(&directory, &["log"]))
        .lines()
        .next()
        .and_then(|line| line.split_whitespace().nth(1))
        .expect("the root")
        .to_owned();

    fs::write(directory.join("photo.bin"), [0x00, 0x02]).expect("our attachment");
    out(recorded(&directory, &["record", "-m", "mine"]));
    fs::write(directory.join("photo.bin"), [0x00, 0x03]).expect("their attachment");
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

    let status = out(recorded(
        &directory,
        &["status", "--merge", &mine, "--merge", &theirs],
    ));
    assert!(status.contains("accept  photo.bin"), "{status}");
    assert!(status.contains("--accept photo.bin"), "{status}");

    let refused = recorded(
        &directory,
        &["record", "--merge", &mine, "--merge", &theirs, "-m", "Join"],
    );
    assert!(!refused.status.success());
    let complaint = String::from_utf8_lossy(&refused.stderr);
    assert!(complaint.contains("--accept photo.bin"), "{complaint}");

    let unnecessary = recorded(
        &directory,
        &[
            "record",
            "--merge",
            &mine,
            "--merge",
            &theirs,
            "--accept",
            "photo.bin",
            "--accept",
            "other.bin",
            "-m",
            "Join",
        ],
    );
    assert!(!unnecessary.status.success());
    assert!(
        String::from_utf8_lossy(&unnecessary.stderr).contains("other.bin"),
        "an acceptance must name contested bytes"
    );

    let joined = out(recorded(
        &directory,
        &[
            "record",
            "--merge",
            &mine,
            "--merge",
            &theirs,
            "--accept",
            "photo.bin",
            "-m",
            "Join",
        ],
    ));
    assert!(joined.contains("joins 2 lines"), "{joined}");
    assert_eq!(
        run(&directory, &["cat", "head", "photo.bin"]).stdout,
        [0x00, 0x03]
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
    // Decision 0017: a file of bytes is content, not a refusal.
    assert!(listed.contains("added   picture.bin"), "{listed}");
    #[cfg(unix)]
    assert!(
        listed.contains("refused link: not a regular file"),
        "{listed}"
    );

    // And recording refuses the same files, all of them at once.
    #[cfg(unix)]
    {
        let refused = recorded(&directory, &["record", "-m", "Everything"]);
        assert!(!refused.status.success());
        let complaint = String::from_utf8_lossy(&refused.stderr).into_owned();
        assert!(complaint.contains("link"), "{complaint}");
        assert!(complaint.contains("skip"), "{complaint}");
    }
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

#[test]
fn an_amendment_keeps_the_work_and_works_the_folder_out_again() {
    let directory = repository("amend");
    write(&directory, "notes.md", "one\n");
    out(recorded(&directory, &["record", "-m", "Start a journal"]));

    let before = out(recorded(&directory, &["show", "head"]));
    let file = one_file(&directory, "head");

    write(&directory, "notes.md", "one\ntwo\n");
    write(&directory, "aside.md", "an aside\n");
    let amended = out(recorded(
        &directory,
        &["amend", "-m", "Start a journal, with an aside"],
    ));
    // The survey is against the amended revision's parents, and this one is a
    // root — so the file it created is created again rather than edited, which
    // is decision 0017's `text` and is why keeping the identifier matters.
    assert!(amended.contains("added   notes.md"), "{amended}");
    assert!(amended.contains("added   aside.md"), "{amended}");
    let superseded = amended
        .lines()
        .find(|line| line.starts_with("it supersedes "))
        .and_then(|line| line.split_whitespace().nth(2))
        .expect("the digest it replaced")
        .trim_end_matches(',')
        .to_owned();

    // Decision 0010's table: the change, the author, and the moment the work
    // was first recorded are copied, and `revised` carries the later act.
    let after = out(recorded(&directory, &["show", "head"]));
    assert_eq!(header(&after, "change"), header(&before, "change"));
    assert_eq!(header(&after, "author"), header(&before, "author"));
    assert_eq!(header(&after, "when"), header(&before, "when"));
    assert!(
        after.contains(&format!("supersedes {superseded}")),
        "{after}"
    );
    assert!(
        after.lines().any(|line| line.starts_with("revised ")),
        "an amendment stamps rather than copying: {after}"
    );

    // Decision 0023: the identifier the predecessor minted for this path is
    // kept, so the file in the folder is the file history already held.
    assert!(after.contains(&format!("add {file} notes.md")), "{after}");
    assert_eq!(
        out(recorded(
            &directory,
            &["cat", "head", &format!("file:{file}")]
        )),
        "one\ntwo\n"
    );
    assert!(
        out(recorded(&directory, &["check"])).ends_with("nothing to report\n"),
        "the store still holds together"
    );
}

#[test]
fn a_reword_changes_the_message_and_leaves_every_fact_alone() {
    let directory = repository("amend-reword");
    write(&directory, "notes.md", "one\n");
    out(recorded(&directory, &["record", "-m", "Teh journal"]));
    let before = out(recorded(&directory, &["show", "head"]));

    let amended = out(recorded(&directory, &["amend", "-m", "The journal"]));
    assert!(!amended.contains("edited"), "{amended}");

    let after = out(recorded(&directory, &["show", "head"]));
    for line in before
        .lines()
        .filter(|line| line.starts_with("add ") || line.starts_with("text "))
    {
        assert!(
            after.contains(line),
            "`{line}` should survive a reword:\n{after}"
        );
    }
    assert!(after.ends_with("The journal"), "{after}");
    assert!(!after.contains("Teh journal"), "{after}");
    assert!(out(recorded(&directory, &["check"])).ends_with("nothing to report\n"));
}

#[test]
fn amending_a_revision_that_renamed_a_file_keeps_the_rename() {
    let directory = repository("amend-move");
    write(&directory, "notes.md", "one\n");
    out(recorded(&directory, &["record", "-m", "Start"]));
    out(recorded(
        &directory,
        &[
            "record",
            "-m",
            "File the notes",
            "--move",
            "notes.md=docs/notes.md",
        ],
    ));
    let file = one_file(&directory, "head");

    // Decision 0023: a recomputation cannot observe a rename, so the amended
    // revision's own `move` line is inherited rather than spelled as a
    // deletion of one path and an addition of another.
    write(&directory, "docs/notes.md", "one\ntwo\n");
    let amended = out(recorded(&directory, &["amend"]));
    assert!(amended.contains("moved   docs/notes.md"), "{amended}");
    assert!(!amended.contains("dropped"), "{amended}");
    let after = out(recorded(&directory, &["show", "head"]));
    assert!(
        after.contains(&format!("move {file} docs/notes.md")),
        "{after}"
    );
    assert!(
        after.ends_with("File the notes"),
        "the message is copied too"
    );

    // And a person may state a different one, against the path this revision
    // currently has the file at, which is where the folder holds it.
    let again = out(recorded(
        &directory,
        &["amend", "--move", "docs/notes.md=notes/entry.md"],
    ));
    assert!(again.contains("moved   notes/entry.md"), "{again}");
    assert!(
        directory.join("notes/entry.md").is_file() && !directory.join("docs/notes.md").exists(),
        "`--move` performs the rename when a person has not"
    );
    assert_eq!(
        one_file(&directory, "head"),
        file,
        "the file is still the same file"
    );

    // Decision 0019's third tier, which nothing could reach until an
    // amendment existed: three revisions want one name here, and each is
    // written under its own without anything being renamed or overwritten.
    let filed: Vec<String> = fs::read_dir(directory.join("history/revisions"))
        .expect("the revisions directory")
        .filter_map(|entry| Some(entry.ok()?.file_name().to_string_lossy().into_owned()))
        .filter(|name| name.contains("File the notes"))
        .collect();
    assert_eq!(filed.len(), 3, "{filed:?}");
    assert!(out(recorded(&directory, &["check"])).ends_with("nothing to report\n"));
}

#[test]
fn only_a_revision_nothing_follows_and_nothing_replaced_can_be_amended() {
    let directory = repository("amend-refusals");
    write(&directory, "notes.md", "one\n");
    out(recorded(&directory, &["record", "-m", "First"]));
    let first = head_of(&directory);
    write(&directory, "notes.md", "two\n");
    out(recorded(&directory, &["record", "-m", "Second"]));

    // Decision 0023: rewriting the first would have to restate what the second
    // did against content that moved, which is 0007's merge under another name.
    let standing = refused(&directory, &["amend", &first]);
    assert!(standing.contains("not built yet"), "{standing}");
    assert!(standing.contains("nothing follows"), "{standing}");

    // Amending the head is allowed, and amending what it replaced is not:
    // superseding one revision twice is a divergence nobody asked for.
    let second = head_of(&directory);
    write(&directory, "notes.md", "three\n");
    out(recorded(&directory, &["amend"]));
    let twice = refused(&directory, &["amend", &second]);
    assert!(twice.contains("already been rewritten"), "{twice}");
    assert!(twice.contains(&head_of(&directory)), "{twice}");
}

#[test]
fn an_amendment_that_says_what_is_already_said_is_refused() {
    let directory = repository("amend-nothing");
    write(&directory, "notes.md", "one\n");
    out(recorded(&directory, &["record", "-m", "Start"]));

    let again = refused(&directory, &["amend"]);
    assert!(again.contains("already says exactly this"), "{again}");
    let same = refused(&directory, &["amend", "-m", "Start"]);
    assert!(same.contains("already says exactly this"), "{same}");
    assert_eq!(
        out(recorded(&directory, &["log"]))
            .lines()
            .filter(|line| line.contains("(head"))
            .count(),
        1,
        "a refusal writes nothing"
    );
}

#[test]
fn the_position_after_a_rewrite_is_the_revision_that_rewrote_it() {
    let directory = repository("amend-position");
    write(&directory, "notes.md", "one\n");
    out(recorded(&directory, &["record", "-m", "Start"]));
    write(&directory, "notes.md", "one\ntwo\n");
    out(recorded(&directory, &["amend"]));

    // Decision 0023: an amended revision is still a head by parent edges, and
    // the position is the head nothing has rewritten — so the ordinary case of
    // one line of work amended once does not have to be disambiguated.
    let head = head_of(&directory);
    assert!(out(recorded(&directory, &["files", "head"])).contains("notes.md"));
    let where_we_are = out(recorded(&directory, &["status"]));
    assert!(where_we_are.contains(&head), "{where_we_are}");

    write(&directory, "notes.md", "one\ntwo\nthree\n");
    let onwards = out(recorded(&directory, &["record", "-m", "Say more"]));
    assert!(onwards.contains("edited  notes.md"), "{onwards}");
    assert!(!onwards.contains("this is a root"), "{onwards}");

    // The superseded revision is still in the store and still says so, which
    // decision 0013 makes the whole of the undo history.
    let log = out(recorded(&directory, &["log"]));
    assert!(log.contains("superseded"), "{log}");
    assert!(out(recorded(&directory, &["check"])).ends_with("nothing to report\n"));
}

#[test]
fn a_dry_run_of_an_amendment_writes_nothing() {
    let directory = repository("amend-dry-run");
    write(&directory, "notes.md", "one\n");
    out(recorded(&directory, &["record", "-m", "Start"]));
    let head = head_of(&directory);

    // An amendment restates the whole of what it replaces, so an untouched
    // folder is a full plan rather than an empty one — and an amendment that
    // would say nothing new is a refusal by then rather than a report.
    let unchanged = refused(&directory, &["amend", "--dry-run"]);
    assert!(
        unchanged.contains("already says exactly this"),
        "{unchanged}"
    );

    write(&directory, "notes.md", "one\ntwo\n");
    let planned = out(recorded(&directory, &["amend", "-n"]));
    assert!(planned.contains("added   notes.md"), "{planned}");
    assert!(
        planned.contains(&format!("this would supersede {head}")),
        "{planned}"
    );
    assert_eq!(head_of(&directory), head, "a dry run rewrites nothing");

    // The refusals happen before the folder is read, so a dry run meets them
    // at the same moment the real thing would.
    let standing = refused(&directory, &["amend", "--dry-run", "nosuchtarget"]);
    assert!(!standing.is_empty(), "an unresolvable target still refuses");
    let unknown = refused(&directory, &["amend", "--frobnicate"]);
    assert!(
        unknown.contains("is not an argument `amend` takes"),
        "{unknown}"
    );
    let two = refused(&directory, &["amend", &head, &head]);
    assert!(two.contains("is a second"), "{two}");
}

/// The revision digest a `record` or `amend` line printed after ` as `.
fn digest_in(said: &str) -> String {
    said.lines()
        .find_map(|line| line.split(" as ").nth(1))
        .expect("a `... as <digest>` line")
        .trim()
        .to_owned()
}

/// Copy a repository wholesale, which is what a replica is (decision 0003).
fn mirror(from: &Path, to: &Path) {
    for entry in fs::read_dir(from)
        .expect("a directory")
        .filter_map(Result::ok)
    {
        let source = entry.path();
        let target = to.join(entry.file_name());
        if source.is_dir() {
            fs::create_dir_all(&target).expect("a directory");
            mirror(&source, &target);
        } else {
            fs::copy(&source, &target).expect("copying a file");
        }
    }
}

#[test]
fn abandoning_a_head_leaves_a_tombstone_and_the_parents_content() {
    let directory = repository("abandon-head");
    write(&directory, "notes.md", "First thought.\n");
    out(recorded(&directory, &["record", "-m", "Start a journal"]));
    write(&directory, "notes.md", "First thought.\nA draft.\n");
    out(recorded(&directory, &["record", "-m", "A draft"]));

    let said = out(recorded(
        &directory,
        &[
            "abandon",
            "head",
            "-m",
            "The argument does not survive its own example",
        ],
    ));
    assert!(said.contains("abandoned "), "{said}");
    assert!(said.contains("the tombstone is "), "{said}");
    // Decision 0013: pruning is a different act, and the command that records
    // the fact says where the disk half lives.
    assert!(said.contains("`historica prune`"), "{said}");

    // The content falls out of the ancestry: the head holds the parent's text.
    assert_eq!(
        stdout(&directory, &["cat", "head", "notes.md"]),
        "First thought.\n"
    );
    // The tombstone is an ordinary revision, and its reason is in the log.
    let log = stdout(&directory, &["log"]);
    assert!(
        log.contains("The argument does not survive its own example"),
        "{log}"
    );
    assert!(stdout(&directory, &["check"]).ends_with("nothing to report\n"));
}

#[test]
fn abandoning_without_a_reason_is_refused() {
    let directory = repository("abandon-reason");
    write(&directory, "notes.md", "First.\n");
    out(recorded(&directory, &["record", "-m", "Start"]));

    let said = refused(&directory, &["abandon", "head", "-m", ""]);
    assert!(said.contains("reason"), "{said}");
}

#[test]
fn one_tombstone_abandons_a_run_ending_at_a_head() {
    let directory = repository("abandon-run");
    write(&directory, "notes.md", "Kept.\n");
    out(recorded(&directory, &["record", "-m", "Keep this"]));
    write(&directory, "notes.md", "Kept.\nDraft one.\n");
    let first = out(recorded(&directory, &["record", "-m", "Draft one"]));
    write(&directory, "notes.md", "Kept.\nDraft one.\nDraft two.\n");
    out(recorded(&directory, &["record", "-m", "Draft two"]));

    let target = digest_in(&first);
    let planned = out(recorded(&directory, &["abandon", &target, "--dry-run"]));
    assert_eq!(planned.matches("would abandon ").count(), 2, "{planned}");

    let said = out(recorded(
        &directory,
        &["abandon", &target, "-m", "Neither draft says it"],
    ));
    assert_eq!(said.matches("abandoned ").count(), 2, "{said}");
    assert_eq!(stdout(&directory, &["cat", "head", "notes.md"]), "Kept.\n");
}

#[test]
fn abandoning_refuses_a_fork_and_a_rewritten_revision() {
    let directory = repository("abandon-fork");
    write(&directory, "notes.md", "Base.\n");
    let base = out(recorded(&directory, &["record", "-m", "Base"]));
    write(&directory, "notes.md", "Base.\nLeft.\n");
    out(recorded(&directory, &["record", "-m", "Left"]));
    write(&directory, "notes.md", "Base.\nRight.\n");
    out(recorded(
        &directory,
        &["record", "-m", "Right", "--onto", &digest_in(&base)],
    ));
    let said = refused(&directory, &["abandon", &digest_in(&base), "-m", "why"]);
    assert!(said.contains("lines of work stand on"), "{said}");

    let directory = repository("abandon-rewritten");
    write(&directory, "notes.md", "First.\n");
    let first = out(recorded(&directory, &["record", "-m", "Start"]));
    out(recorded(&directory, &["amend", "-m", "Start, reworded"]));
    let said = refused(&directory, &["abandon", &digest_in(&first), "-m", "why"]);
    assert!(said.contains("already been rewritten"), "{said}");
}

#[test]
fn a_change_bookmark_follows_abandoned_work_to_the_tombstone() {
    let directory = repository("abandon-bookmark");
    write(&directory, "notes.md", "First.\n");
    out(recorded(&directory, &["record", "-m", "Start"]));
    write(&directory, "notes.md", "First.\nMore.\n");
    out(recorded(&directory, &["record", "-m", "More"]));
    stdout(&directory, &["name", "draft", "head"]);

    let said = out(recorded(
        &directory,
        &["abandon", "head", "-m", "Not this way"],
    ));
    assert!(said.contains("draft -> "), "{said}");
    // The tombstone stands where the abandoned revision stood, and the
    // bookmark still resolves — to it.
    let names = stdout(&directory, &["names"]);
    assert!(names.contains("draft"), "{names}");
    assert_eq!(
        stdout(&directory, &["cat", "draft", "notes.md"]),
        "First.\n"
    );
}

#[test]
fn prune_removes_a_superseded_orphan_and_what_only_it_named() {
    let directory = repository("prune-orphan");
    write(&directory, "notes.md", "First.\n");
    out(recorded(&directory, &["record", "-m", "Start"]));
    write(&directory, "notes.md", "First.\nA draft.\n");
    out(recorded(&directory, &["record", "-m", "A draft"]));
    out(recorded(&directory, &["abandon", "head", "-m", "No"]));

    // The dry run prints the files and removes none of them.
    let planned = stdout(&directory, &["prune", "--dry-run"]);
    assert!(
        planned.contains("would remove history/revisions/"),
        "{planned}"
    );
    assert!(
        planned.contains("would remove history/operations/"),
        "{planned}"
    );
    assert_eq!(walk_names(&directory.join("history/revisions")).len(), 3);

    let said = stdout(&directory, &["prune"]);
    assert!(said.contains("removed history/revisions/"), "{said}");
    // The draft's operation document went with it: nothing kept names it.
    assert!(said.contains("removed history/operations/"), "{said}");
    assert_eq!(walk_names(&directory.join("history/revisions")).len(), 2);

    // A pruned store still passes `check`, still materialises, and pruning
    // twice removes nothing the second time.
    assert!(stdout(&directory, &["check"]).ends_with("nothing to report\n"));
    assert_eq!(stdout(&directory, &["cat", "head", "notes.md"]), "First.\n");
    let again = stdout(&directory, &["prune"]);
    assert!(again.contains("nothing here is prunable"), "{again}");
}

#[test]
fn an_operation_document_two_revisions_share_survives_pruning_one() {
    let directory = repository("prune-shared");
    write(&directory, "notes.md", "First.\n");
    out(recorded(&directory, &["record", "-m", "Start"]));
    write(&directory, "notes.md", "First.\nThe same line.\n");
    out(recorded(&directory, &["record", "-m", "Once"]));
    out(recorded(
        &directory,
        &["abandon", "head", "-m", "Right edit, wrong change"],
    ));
    // The same edit again, against the same content: byte-identical
    // operations, so decision 0007 gives both revisions one document.
    write(&directory, "notes.md", "First.\nThe same line.\n");
    out(recorded(&directory, &["record", "-m", "Again"]));

    let said = stdout(&directory, &["prune"]);
    assert!(said.contains("removed history/revisions/"), "{said}");
    assert!(!said.contains("removed history/operations/"), "{said}");
    assert_eq!(
        stdout(&directory, &["cat", "head", "notes.md"]),
        "First.\nThe same line.\n"
    );
}

#[test]
fn prune_leaves_a_superseded_revision_work_still_stands_on() {
    let directory = repository("prune-parent");
    write(&directory, "notes.md", "First.\n");
    out(recorded(&directory, &["record", "-m", "Start"]));

    // Another replica, by copy — which is what a replica is (decision 0003).
    let replica = scratch("prune-parent-replica");
    mirror(&directory, &replica);

    // Here, work stands on the first revision; there, it is amended.
    write(&directory, "notes.md", "First.\nMore.\n");
    out(recorded(&directory, &["record", "-m", "More"]));
    out(recorded(&replica, &["amend", "-m", "Start, reworded"]));

    // Sync by union: the replica's new document arrives by copy.
    for entry in fs::read_dir(replica.join("history/revisions"))
        .expect("the replica's revisions")
        .filter_map(Result::ok)
    {
        let into = directory.join("history/revisions").join(entry.file_name());
        if !into.exists() {
            fs::copy(entry.path(), &into).expect("syncing a revision");
        }
    }

    // `Start` is superseded, but `More` names it as a parent, so it stays —
    // and so does its successor, which carries the evidence of supersession.
    let said = stdout(&directory, &["prune"]);
    assert!(said.contains("nothing here is prunable"), "{said}");
}

#[test]
fn prune_refuses_a_store_check_calls_broken() {
    let directory = repository("prune-broken");
    write(&directory, "notes.md", "First.\n");
    out(recorded(&directory, &["record", "-m", "Start"]));
    fs::write(
        directory.join("history/revisions/broken.rev.txt"),
        "not a revision\n",
    )
    .expect("writing a broken file");

    let said = stderr(&directory, &["prune"]);
    assert!(said.contains("check"), "{said}");
    // Nothing was deleted on the way to the refusal.
    assert!(directory.join("history/revisions/broken.rev.txt").exists());
}

/// Decision 0030: a received store updates an empty folder to files
/// byte-identical with the source's, payloads included.
#[test]
fn update_fills_an_empty_folder_from_a_received_store() {
    let there = repository("update-fill-source");
    write(&there, "notes/2026-08-20.md", "# Notes\n\nA journal.\n");
    fs::write(there.join("photo.bin"), [0xffu8, 0x00, 0x7f]).expect("a payload");
    out(recorded(&there, &["record", "-m", "Start a journal"]));

    let here = scratch("update-fill");
    assert!(run(&here, &["init"]).status.success());
    let source = there.to_string_lossy();
    stdout(&here, &["receive", &source]);

    let updated = stdout(&here, &["update"]);
    assert!(updated.contains("wrote   notes/2026-08-20.md"), "{updated}");
    assert!(updated.contains("wrote   photo.bin"), "{updated}");
    assert!(updated.contains("the folder holds"), "{updated}");
    assert_eq!(
        fs::read_to_string(here.join("notes/2026-08-20.md")).expect("the entry"),
        "# Notes\n\nA journal.\n"
    );
    assert_eq!(
        fs::read(here.join("photo.bin")).expect("the payload"),
        [0xffu8, 0x00, 0x7f]
    );

    // Updating twice is the identity the second time.
    let again = stdout(&here, &["update"]);
    assert!(again.contains("the folder already holds"), "{again}");
    assert!(!again.contains("wrote"), "{again}");
}

/// An update refuses, all of it, while one path holds unrecorded bytes.
#[test]
fn update_refuses_while_unrecorded_work_stands_in_the_way() {
    let directory = repository("update-refuses");
    write(&directory, "f.md", "recorded\n");
    write(&directory, "g.md", "recorded too\n");
    out(recorded(&directory, &["record", "-m", "both"]));
    write(&directory, "f.md", "recorded\nagain\n");
    out(recorded(&directory, &["record", "-m", "more"]));

    // Stand the folder at the older revision, then edit one file: the edit is
    // work nothing has recorded, so nothing at all may move.
    write(&directory, "f.md", "recorded\n");
    write(&directory, "g.md", "unrecorded\n");
    let said = stderr(&directory, &["update"]);
    assert!(said.contains("nothing was written"), "{said}");
    assert!(
        said.contains("g.md: it holds work nothing has recorded"),
        "{said}"
    );
    assert_eq!(
        fs::read_to_string(directory.join("f.md")).expect("untouched"),
        "recorded\n",
        "a refusal writes nothing"
    );
}

/// A two-headed store switches the folder between heads and back, leaving a
/// stray unrecorded file untouched throughout.
#[test]
fn update_switches_between_heads_and_back() {
    let (directory, one, two) = diverged(
        "update-switch",
        "one\nMINE\nthree\n",
        "one\nTHEIRS\nthree\n",
    );
    // `diverged` promises two heads, not which is which.
    let (mine, theirs) = if stdout(&directory, &["cat", &one, "f.md"]).contains("MINE") {
        (one, two)
    } else {
        (two, one)
    };
    write(&directory, "stray.md", "nobody recorded this\n");

    stdout(&directory, &["update", &mine]);
    assert_eq!(
        fs::read_to_string(directory.join("f.md")).expect("the file"),
        "one\nMINE\nthree\n"
    );
    stdout(&directory, &["update", &theirs]);
    assert_eq!(
        fs::read_to_string(directory.join("f.md")).expect("the file"),
        "one\nTHEIRS\nthree\n"
    );
    assert_eq!(
        fs::read_to_string(directory.join("stray.md")).expect("still here"),
        "nobody recorded this\n",
        "a stray unrecorded file is not update's to touch"
    );
}

/// A folder standing at a superseded state catches up to the head with no
/// flags: the rule is bytes some revision records, not bytes the head holds.
#[test]
fn update_catches_the_folder_up_with_no_flags() {
    let directory = repository("update-catch-up");
    write(&directory, "f.md", "one\n");
    write(&directory, "notes/g.md", "g\n");
    out(recorded(&directory, &["record", "-m", "first"]));
    write(&directory, "f.md", "one\ntwo\n");
    fs::remove_file(directory.join("notes/g.md")).expect("a deletion");
    out(recorded(&directory, &["record", "-m", "second"]));

    // Put the folder back at the first revision's state, by hand — every byte
    // of it is recorded, so update may replace it.
    write(&directory, "f.md", "one\n");
    write(&directory, "notes/g.md", "g\n");

    let updated = stdout(&directory, &["update"]);
    assert!(updated.contains("wrote   f.md"), "{updated}");
    assert!(updated.contains("removed notes/g.md"), "{updated}");
    assert_eq!(
        fs::read_to_string(directory.join("f.md")).expect("the file"),
        "one\ntwo\n"
    );
    assert!(
        !directory.join("notes").exists(),
        "a removal that empties a directory removes the directory"
    );
}

/// `abandon` then `update` returns the folder to the state before the run,
/// removing the file the run added: going back, on the record.
#[test]
fn abandon_then_update_returns_the_folder() {
    let directory = repository("update-abandon");
    write(&directory, "entry.md", "keep\n");
    out(recorded(&directory, &["record", "-m", "good"]));
    write(&directory, "entry.md", "keep\nruin\n");
    write(&directory, "mess.md", "mess\n");
    out(recorded(&directory, &["record", "-m", "bad"]));

    let head = head_of(&directory);
    out(recorded(
        &directory,
        &["abandon", &head, "-m", "a bad afternoon"],
    ));

    let updated = stdout(&directory, &["update"]);
    assert!(updated.contains("wrote   entry.md"), "{updated}");
    assert!(updated.contains("removed mess.md"), "{updated}");
    assert_eq!(
        fs::read_to_string(directory.join("entry.md")).expect("the entry"),
        "keep\n"
    );
    assert!(!directory.join("mess.md").exists());
}

/// A revision that is not a head is refused by name, and the refusal says
/// what serves the want instead.
#[test]
fn update_refuses_a_revision_that_is_not_a_head() {
    let directory = repository("update-not-a-head");
    write(&directory, "f.md", "one\n");
    out(recorded(&directory, &["record", "-m", "first"]));
    let root = head_of(&directory);
    write(&directory, "f.md", "one\ntwo\n");
    out(recorded(&directory, &["record", "-m", "second"]));

    let said = stderr(&directory, &["update", &root]);
    assert!(said.contains("is not a head"), "{said}");
    assert!(said.contains("abandon"), "{said}");
}

/// `--dry-run` prints the plan and writes nothing.
#[test]
fn update_dry_run_writes_nothing() {
    let directory = repository("update-dry-run");
    write(&directory, "f.md", "one\n");
    out(recorded(&directory, &["record", "-m", "first"]));
    write(&directory, "f.md", "one\ntwo\n");
    out(recorded(&directory, &["record", "-m", "second"]));
    write(&directory, "f.md", "one\n");

    let planned = stdout(&directory, &["update", "--dry-run"]);
    assert!(planned.contains("write   f.md"), "{planned}");
    assert_eq!(
        fs::read_to_string(directory.join("f.md")).expect("untouched"),
        "one\n",
        "a dry run writes nothing"
    );
}

/// A store missing a payload refuses to update: a folder cannot be partially
/// at a head, and receiving the rest is the fix.
#[test]
fn update_refuses_when_the_store_cannot_produce_a_file() {
    let directory = repository("update-missing-payload");
    fs::write(directory.join("photo.bin"), [0xffu8, 0x00, 0x7f]).expect("a payload");
    write(&directory, "f.md", "one\n");
    out(recorded(&directory, &["record", "-m", "first"]));

    // The payload leaves — an undelivered store is a legitimate state — and
    // so does the folder's copy, so an update would have to write it back.
    let payload = find_bytes(&directory.join("history/operations"), &[0xffu8, 0x00, 0x7f])
        .expect("the payload file");
    fs::remove_file(payload).expect("removing the payload");
    fs::remove_file(directory.join("photo.bin")).expect("the folder's copy");

    let said = stderr(&directory, &["update"]);
    assert!(said.contains("photo.bin"), "{said}");
    assert!(said.contains("does not hold the content"), "{said}");
}

/// The one file beneath `path` holding exactly these bytes.
fn find_bytes(path: &Path, bytes: &[u8]) -> Option<PathBuf> {
    if path.is_dir() {
        fs::read_dir(path)
            .expect("a directory")
            .filter_map(|entry| find_bytes(&entry.expect("an entry").path(), bytes))
            .next()
    } else if fs::read(path).is_ok_and(|held| held == bytes) {
        Some(path.to_path_buf())
    } else {
        None
    }
}
