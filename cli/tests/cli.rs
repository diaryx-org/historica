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
        .join("../tests/corpus")
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
                // Everything else in a corpus's `operations/` is a payload:
                // a file's own content, stored whole, under any name.
                _ if source.ends_with("operations") && path.is_file() => "operations",
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
    // Decision 0021: the first line is the format, and the rest of the file
    // tells whoever opens the folder what they are looking at.
    let header = fs::read_to_string(directory.join("history/historica.txt")).expect("the header");
    let mut lines = header.lines();
    assert_eq!(lines.next(), Some("historica"));
    assert!(header.contains("Identity comes from content"), "{header}");
    assert!(header.contains("revisions/"), "{header}");
    assert!(header.contains("cache/"), "{header}");
    let cache_note =
        fs::read_to_string(directory.join("history/cache/README.txt")).expect("the cache note");
    assert!(
        cache_note.contains("Everything in this directory is derived"),
        "{cache_note}"
    );
    let skipped =
        fs::read_to_string(directory.join("history/skipped/README.txt")).expect("the rule note");
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

/// A store missing an ancestor contradicts nothing, so `check` still passes
/// it — and still says what it costs. `--complete` is the caller who has
/// decided that for this store, at this moment, delivery should have finished.
#[test]
fn check_says_which_heads_it_cannot_produce_and_complete_fails_on_them() {
    let directory = store_from("check-complete", "tree");
    assert!(stdout(&directory, &["check"]).contains("nothing to report"));
    assert!(run(&directory, &["check", "--complete"]).status.success());

    // Remove the root, which every later revision stands on.
    let revisions = directory.join("history/revisions");
    fs::remove_file(revisions.join("01-start.rev.txt")).expect("the root");

    let report = stdout(&directory, &["check"]);
    assert!(report.contains("note:"), "{report}");
    assert!(!report.contains("error:"), "{report}");
    assert!(report.contains("cannot produce"), "{report}");
    assert!(
        report.contains("head here cannot be produced"),
        "the summary should say the consequence: {report}"
    );

    // Notes never fail, exactly as decision 0006 requires.
    assert!(run(&directory, &["check"]).status.success());
    let asked = run(&directory, &["check", "--complete"]);
    assert!(!asked.status.success());
    assert!(
        String::from_utf8_lossy(&asked.stdout).contains("cannot produce"),
        "the reason belongs with the failure"
    );
}

/// An undelivered payload is as fatal to producing a head as a missing
/// ancestor, and is counted the same way.
#[test]
fn check_complete_counts_content_the_store_does_not_hold() {
    let directory = repository("check-complete-content");
    write(&directory, "f.md", "one\ntwo\n");
    out(recorded(&directory, &["record", "-m", "root"]));
    assert!(run(&directory, &["check", "--complete"]).status.success());

    // The payload a created file arrives as, per decision 0017.
    let operations = directory.join("history/operations");
    let payload = walk(&operations)
        .into_iter()
        .find(|path| {
            path.file_name()
                .and_then(|name| name.to_str())
                .is_some_and(|name| !name.ends_with(".ops.txt"))
        })
        .expect("the payload");
    fs::remove_file(payload).expect("removing the payload");

    let report = out(recorded(&directory, &["check"]));
    assert!(report.contains("cannot produce"), "{report}");
    assert!(!run(&directory, &["check", "--complete"]).status.success());
}

/// Every file under a directory, to any depth.
fn walk(root: &Path) -> Vec<PathBuf> {
    let mut found = Vec::new();
    let Ok(entries) = fs::read_dir(root) else {
        return found;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            found.extend(walk(&path));
        } else {
            found.push(path);
        }
    }
    found
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
    assert!(log.contains("added 2"), "{log}");
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

/// Decision 0063: `<from>..<to>` is what `<to>` has behind it and `<from>`
/// does not, so the end already had is the one left out.
#[test]
fn log_takes_a_range_and_shows_what_the_far_end_has() {
    let directory = store_from("log-range", "tree");
    let range = stdout(&directory, &["log", "kxryzmor..head"]);

    assert_eq!(entries(&range).len(), 2);
    assert!(range.contains("Withdraw the entry"), "{range}");
    assert!(range.contains("File the README under docs"), "{range}");
    // The near end is behind the far one, so neither it nor anything behind
    // it is in the answer.
    assert!(
        !range.contains("Say why a path is not an identity"),
        "{range}"
    );
    assert!(!range.contains("Start a journal"), "{range}");
}

/// A range whose far end is already behind its near one is an answer rather
/// than a fault, and a different answer from a store with nothing in it.
#[test]
fn log_over_a_range_holding_nothing_says_so_and_succeeds() {
    let directory = store_from("log-range-empty", "tree");
    let said = stdout(&directory, &["log", "head..kxryzmor"]);

    assert!(said.contains("holds nothing"), "{said}");
    assert!(!said.contains("no revisions here yet"), "{said}");
}

/// The subtraction is over two ancestries, so a range between two revisions
/// the graph left concurrent is as well defined as one along a chain: what is
/// shown is the other side of the fork, and the shared root is not on it.
#[test]
fn log_over_a_range_shows_the_other_side_of_a_fork() {
    let directory = store_from("log-range-fork", "revisions");
    let range = stdout(&directory, &["log", "mzvwutkl..nwlxsqot"]);

    assert!(
        range.contains("Reject two revisions claiming one digest"),
        "{range}"
    );
    // The near end, and the root both ends share, are behind the near end.
    assert!(
        !range.contains("Name parents a revision has not received yet"),
        "{range}"
    );
    assert_eq!(entries(&range).len(), 2);
}

/// The filters are about revisions and the range is about which revisions, so
/// they compose the way the filters compose with each other.
#[test]
fn log_over_a_range_composes_with_the_filters() {
    let directory = store_from("log-range-filters", "tree");

    let limited = stdout(&directory, &["log", "qpvuntsm..head", "--limit", "1"]);
    assert_eq!(entries(&limited).len(), 1);
    assert!(limited.contains("Withdraw the entry"), "{limited}");

    // Decision 0008 again: the path is read at the far end, which is the
    // position the range names, and the file is followed from there.
    let followed = stdout(
        &directory,
        &["log", "qpvuntsm..head", "--path", "docs/README.md"],
    );
    assert_eq!(entries(&followed).len(), 1);
    assert!(
        followed.contains("File the README under docs"),
        "{followed}"
    );
}

/// Both ends are said outright, and the refusal prints what to type instead.
#[test]
fn log_refuses_a_range_missing_an_end() {
    let directory = store_from("log-range-refusals", "tree");

    let one = stderr(&directory, &["log", "kxryzmor.."]);
    assert!(one.contains("leaves the other blank"), "{one}");
    assert!(one.contains("`head`"), "{one}");

    let neither = stderr(&directory, &["log", ".."]);
    assert!(neither.contains("names neither end"), "{neither}");

    // Git's three-dot spelling means the work either side of a fork, which
    // has no spelling here; the generic refusal would send a person looking
    // for a bookmark called `.head`.
    let symmetric = stderr(&directory, &["log", "kxryzmor...head"]);
    assert!(symmetric.contains("three dots"), "{symmetric}");
}

/// The fields of one line of a `--fields` listing.
fn columns(line: &str) -> Vec<&str> {
    line.split(' ').collect()
}

/// Every line of a `--fields` listing under its header.
fn listed(out: &str) -> Vec<&str> {
    let mut lines = out.lines();
    assert_eq!(lines.next(), Some("historica-log-1"));
    lines.filter(|line| !line.is_empty()).collect()
}

/// Decision 0064: a header, then one line per revision, spelled whole.
#[test]
fn log_fields_prints_a_header_and_one_line_a_revision() {
    let directory = store_from("log-fields", "tree");
    let out = stdout(&directory, &["log", "--fields"]);
    let lines = listed(&out);
    assert_eq!(lines.len(), 4);

    // The newest revision first, as the reading for a person orders it.
    let newest = columns(lines[0]);
    assert_eq!(newest.len(), 5, "{out}");
    assert_eq!(newest[0].len(), 64, "a whole digest: {out}");
    assert_eq!(newest[1].len(), 24, "a whole change ID: {out}");
    assert_eq!(newest[2], "2025-08-21T22:05:00-06:00");
    assert_eq!(newest[3], "head");
    // One parent, spelled whole, which is the next line's own digest.
    assert_eq!(newest[4], columns(lines[1])[0]);

    // A root has no parents, so its line ends after the marks, and a mark
    // field is never empty.
    let root = columns(lines[3]);
    assert_eq!(root.len(), 4, "{out}");
    assert_eq!(root[3], "-");

    // Nothing a person wrote is in it: `show` is where those live.
    assert!(!out.contains("Start a journal"), "{out}");
    assert!(!out.contains("@example.com"), "{out}");
}

/// The marks are the graph's own findings, and a revision may carry several.
#[test]
fn log_fields_states_what_only_the_graph_knows() {
    let directory = store_from("log-fields-marks", "revisions");
    let out = stdout(&directory, &["log", "--fields"]);

    let marks: Vec<&str> = listed(&out).iter().map(|line| columns(line)[3]).collect();
    assert!(marks.contains(&"head"), "{out}");
    assert!(marks.contains(&"head,superseded"), "{out}");
    assert!(marks.contains(&"superseded"), "{out}");
    assert!(marks.contains(&"-"), "{out}");

    // `merge` and `rewrites` are not marks here: the document states both
    // outright, and this listing does not restate what the file says.
    assert!(!out.contains("merge"), "{out}");
    assert!(!out.contains("rewrites"), "{out}");

    // A merge names both its parents, in the order the document does.
    let merge = listed(&out)
        .into_iter()
        .map(columns)
        .find(|fields| fields.len() == 6)
        .expect("the merge, with two parents");
    assert_ne!(merge[4], merge[5]);
}

/// Whole spellings, because an abbreviation is a fact about what else the
/// store holds rather than about the revision it names.
#[test]
fn log_fields_never_abbreviates_what_the_reading_for_a_person_does() {
    let directory = store_from("log-fields-whole", "tree");
    let people = stdout(&directory, &["log"]);
    let machines = stdout(&directory, &["log", "--fields"]);

    assert!(people.contains("bcede0a1"), "{people}");
    assert!(!people.contains("bcede0a19aab563f"), "{people}");
    assert!(
        machines.contains("bcede0a19aab563f83610feb966f4fe26facb32a49b98f6db788acd4e1b81d7b"),
        "{machines}"
    );
}

/// The filters and the range say which revisions, and this says how they are
/// printed, so the two compose.
#[test]
fn log_fields_composes_with_the_filters_and_a_range() {
    let directory = store_from("log-fields-filters", "tree");

    let ranged = stdout(&directory, &["log", "kxryzmor..head", "--fields"]);
    assert_eq!(listed(&ranged).len(), 2);

    let limited = stdout(&directory, &["log", "--fields", "--limit", "1"]);
    assert_eq!(listed(&limited).len(), 1);

    // `--author` and `--grep` read text this listing does not print, which is
    // the filters doing their own job rather than a disagreement.
    let by_author = stdout(&directory, &["log", "--fields", "--author", "Adam"]);
    assert_eq!(listed(&by_author).len(), 4);
}

/// Every sentence the reading for a person prints when it has nothing to show
/// would arrive at a caller as a line where it expected a revision. The
/// machine reading says the same thing by having a header and nothing under
/// it, and still succeeds.
#[test]
fn log_fields_says_nothing_where_there_is_nothing_to_say() {
    let directory = store_from("log-fields-empty", "tree");

    for arguments in [
        ["log", "--fields", "--grep", "nothing-says-this"].as_slice(),
        ["log", "head..kxryzmor", "--fields"].as_slice(),
    ] {
        let out = stdout(&directory, arguments);
        assert_eq!(out, "historica-log-1\n", "{arguments:?}");
    }

    let empty = scratch("log-fields-nothing");
    assert!(run(&empty, &["init"]).status.success());
    assert_eq!(stdout(&empty, &["log", "--fields"]), "historica-log-1\n");
}

/// A bookmark is looked up whole before the spelling is cut, for the reason
/// one may be called `head`: a name somebody chose beats a spelling the tool
/// reserved.
#[test]
fn a_bookmark_whose_name_holds_the_separator_still_names_itself() {
    let directory = store_from("log-range-bookmark", "tree");
    assert!(
        run(&directory, &["name", "before..after", "kxryzmor"])
            .status
            .success()
    );

    let log = stdout(&directory, &["log", "before..after"]);
    assert!(log.contains("Say why a path is not an identity"), "{log}");
    // The bookmark's own ancestry, which a range between those two ends
    // would not have been: `head` is not behind `kxryzmor`.
    assert!(log.contains("Start a journal"), "{log}");
    assert!(!log.contains("Withdraw the entry"), "{log}");
}

/// The first line of each entry a log printed.
///
/// Every other line of an entry is indented, and a message's blank lines are
/// printed as blank lines, so what is left is one line per revision shown.
fn entries(log: &str) -> Vec<&str> {
    log.lines()
        .filter(|line| !line.is_empty() && !line.starts_with(' '))
        .collect()
}

#[test]
fn log_stops_after_the_limit() {
    let directory = store_from("log-limit", "tree");
    assert_eq!(entries(&stdout(&directory, &["log"])).len(), 4);

    let two = stdout(&directory, &["log", "--limit", "2"]);
    assert_eq!(entries(&two).len(), 2);
    assert!(two.contains("Withdraw the entry"), "{two}");
    assert!(!two.contains("Start a journal"), "{two}");

    let refused = stderr(&directory, &["log", "--limit", "soon"]);
    assert!(refused.contains("is not a count"), "{refused}");
}

/// Decision 0005 copies authorship forward, so the author is the person whose
/// work it is — and a reviser who rewrote it is somebody else.
#[test]
fn log_by_author_reads_the_author_and_not_the_reviser() {
    let directory = store_from("log-author", "revisions");
    let everything = stdout(&directory, &["log"]);
    assert!(everything.contains("revised by Rowan Vale"), "{everything}");

    let rowan = stdout(&directory, &["log", "--author", "Rowan"]);
    assert_eq!(entries(&rowan).len(), 1);
    assert!(
        rowan.contains("Name parents a revision has not received yet"),
        "{rowan}"
    );

    let nobody = stdout(&directory, &["log", "--author", "Nobody"]);
    assert!(nobody.contains("no revision here matches"), "{nobody}");
}

#[test]
fn log_by_grep_reads_the_message() {
    let directory = store_from("log-grep", "tree");
    let readme = stdout(&directory, &["log", "--grep", "README"]);
    assert_eq!(entries(&readme).len(), 1);
    assert!(readme.contains("File the README under docs"), "{readme}");
}

/// Decision 0008 is what makes this answerable: the path is read once, and
/// what the log follows is the file it named, through the `move` that renamed
/// it and the edits either side of it.
#[test]
fn log_by_path_follows_the_file_through_a_rename() {
    let directory = store_from("log-path", "tree");
    let readme = stdout(&directory, &["log", "--path", "docs/README.md"]);
    assert_eq!(entries(&readme).len(), 2);
    assert!(readme.contains("File the README under docs"), "{readme}");
    // Added as `README.md`, two revisions before it acquired that path.
    assert!(readme.contains("Start a journal"), "{readme}");
    assert!(
        !readme.contains("Say why a path is not an identity"),
        "that revision edited the other file: {readme}"
    );

    // The identifier is the name that never moved, and it selects the same
    // revisions the path it currently sits at does.
    assert_eq!(stdout(&directory, &["log", "--path", "file:swtl"]), readme);

    // A path is read at the revision named, where the old one still names it.
    let before = stdout(&directory, &["log", "kxryzmor", "--path", "README.md"]);
    assert_eq!(entries(&before).len(), 1);
    assert!(before.contains("Start a journal"), "{before}");

    let gone = stderr(&directory, &["log", "--path", "README.md"]);
    assert!(gone.contains("holds no file at README.md"), "{gone}");
}

/// The bound is read in each revision's own offset, because decision 0002
/// leaves no shared instant here to compare against.
#[test]
fn log_since_and_until_bound_the_recorded_time() {
    let directory = store_from("log-when", "tree");

    let after = stdout(&directory, &["log", "--since", "2025-08-20"]);
    assert_eq!(entries(&after).len(), 2);
    assert!(!after.contains("Start a journal"), "{after}");

    // A whole date is that whole day: the second revision was recorded at
    // 09:02:40 on it, and is inside `--until` for it.
    let before = stdout(&directory, &["log", "--until", "2025-08-19"]);
    assert_eq!(entries(&before).len(), 2);
    assert!(
        before.contains("Say why a path is not an identity"),
        "{before}"
    );

    // The stored spelling is taken as it is written, and both bounds include
    // the moment they name.
    let exact = stdout(&directory, &["log", "--since", "2025-08-19T09:02:40-06:00"]);
    assert_eq!(entries(&exact).len(), 3);

    let both = stdout(
        &directory,
        &["log", "--since", "2025-08-19", "--until", "2025-08-20"],
    );
    assert_eq!(entries(&both).len(), 3);
    assert!(!both.contains("Withdraw the entry"), "{both}");

    let refused = stderr(&directory, &["log", "--since", "yesterday"]);
    assert!(refused.contains("is neither"), "{refused}");
    let impossible = stderr(&directory, &["log", "--until", "2025-02-30"]);
    assert!(impossible.contains("is neither"), "{impossible}");
}

#[test]
fn log_filters_compose_and_the_limit_counts_what_they_left() {
    let directory = store_from("log-filters", "tree");
    let combined = stdout(
        &directory,
        &["log", "--path", "docs/README.md", "--since", "2025-08-20"],
    );
    assert_eq!(entries(&combined).len(), 1);
    assert!(
        combined.contains("File the README under docs"),
        "{combined}"
    );

    // The newest revision of all is the drop, which touched the other file. A
    // limit applied before the filters would have left this printing nothing.
    let newest = stdout(
        &directory,
        &["log", "--path", "docs/README.md", "--limit", "1"],
    );
    assert_eq!(entries(&newest).len(), 1);
    assert!(newest.contains("File the README under docs"), "{newest}");

    let none = stdout(
        &directory,
        &["log", "--grep", "README", "--author", "Rowan"],
    );
    assert!(none.contains("no revision here matches"), "{none}");
}

#[test]
fn log_marks_the_head_whatever_is_filtered_out() {
    let directory = store_from("log-head", "tree");
    let newest = stdout(&directory, &["log", "--limit", "1"]);
    assert!(newest.contains("(head)"), "{newest}");

    // And invents none where the head is not shown.
    let older = stdout(&directory, &["log", "--grep", "Start a journal"]);
    assert_eq!(entries(&older).len(), 1);
    assert!(!older.contains("(head)"), "{older}");
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
            "historica\n\
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

/// Decision 0073: the other direction of `name`, and what goes is the label.
#[test]
fn a_bookmark_is_deleted_by_name_and_the_history_stays() {
    let directory = repository("bookmark-deletion");
    write(&directory, "notes.md", "one\n");
    out(recorded(&directory, &["record", "-m", "Start a journal"]));
    out(recorded(&directory, &["name", "main", "head"]));
    out(recorded(
        &directory,
        &["name", "--private", "feature/x", "head"],
    ));

    let said = out(recorded(&directory, &["name", "--delete", "feature/x"]));
    // What it pointed at, because a deletion nobody meant is undone by typing
    // it back, and this is the line that says how.
    assert!(said.contains("deleted feature/x, which was"), "{said}");
    assert!(said.contains("(private)"), "{said}");
    assert!(said.contains("on the next receive"), "{said}");
    assert!(
        !directory.join("history/names/feature").exists(),
        "decision 0071's directory goes with the last name in it"
    );

    let listed = out(recorded(&directory, &["names"]));
    assert_eq!(listed.lines().count(), 1, "{listed}");
    assert!(listed.contains("main"), "{listed}");

    // The label went and the work did not, which is the whole of what this
    // command does.
    let history = out(recorded(&directory, &["log"]));
    assert!(history.contains("Start a journal"), "{history}");
    let report = out(recorded(&directory, &["check"]));
    assert!(report.ends_with("nothing to report\n"), "{report}");

    // A name that is not here is somebody's typo rather than a deletion that
    // succeeded.
    let absent = refused(&directory, &["name", "--delete", "feature/x"]);
    assert!(
        absent.contains("there is no bookmark `feature/x` here"),
        "{absent}"
    );

    // A bookmark that is going has no target and no axis.
    let shaped = refused(&directory, &["name", "--delete", "main", "--private"]);
    assert!(shaped.contains("nothing left for it to say"), "{shaped}");
    let extra = refused(&directory, &["name", "--delete", "main", "head"]);
    assert!(extra.contains("takes one bookmark"), "{extra}");
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
    // Decision 0041: and the whole of that sits under the revision's month,
    // which is the one directory `operations/` itself now holds. The month
    // is the date the name already carries, so the name checks itself.
    for name in &filed {
        let (month, rest) = name.split_once('/').expect("a month directory");
        assert_eq!(month, &rest[..month.len()], "{filed:?}");
    }
    let months: Vec<String> = fs::read_dir(&operations)
        .expect("the operations directory")
        .filter_map(|entry| Some(entry.ok()?.file_name().to_string_lossy().into_owned()))
        .collect();
    assert_eq!(months.len(), 1, "one month, one directory: {months:?}");

    // And the directories are real ones a person can open.
    let journal = fs::read_dir(operations.join(&months[0]))
        .expect("the month directory")
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
    let invalid = "historica\n\ndelete 0 1\n-a\ndelete 1 2\n-b\n-c\n";
    let other = "historica\n\ninsert 0\n+a\ninsert 0\n+b\n";
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
    // Recorded deliberately, so no default rule is what is under test: a
    // person may record one, and the store still has to survive it.
    fs::write(directory.join(".DS_Store"), [0x00, 0x01, 0x42, 0xff]).expect("metadata");
    out(recorded(&directory, &["skip"]));
    write(
        &directory,
        "history/skipped/nothing-at-all.txt",
        "skip nothing-at-all\n",
    );
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
        // Decision 0045 built one more folder for a person to open, which is
        // one more folder Finder writes into.
        directory.join("history/skipped"),
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
        "historica\n\
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

    // Decision 0041: and the writer files each of them under the revision's
    // own month, so a store kept the way a journal is kept never becomes one
    // flat listing of thousands. The month is the first seven characters of
    // the date the name already carries, which is what lets the name be
    // checked against itself without this test knowing what day it is.
    for name in filed.iter().chain(&revisions) {
        let (month, rest) = name.split_once('/').expect("a month directory");
        assert_eq!(month.len(), "2026-08".len(), "{name}");
        assert_eq!(month, &rest[..month.len()], "{name}");
    }

    assert_eq!(stdout(&directory, &["cat", "head", "notes/a.md"]), "two\n");
    let untouched = walk_names(&directory.join("history"));
    let done = stdout(&directory, &["arrange"]);
    assert!(done.contains("0 renamed, 2 already arranged"), "{done}");
    // And `--refile` has nothing to do either: a writer-fresh store is
    // already where refiling would put it, so the migration is a no-op on
    // everything that never needed migrating.
    let refiled = stdout(&directory, &["arrange", "--refile"]);
    assert!(
        refiled.contains("0 renamed, 2 already arranged"),
        "{refiled}"
    );
    assert_eq!(
        walk_names(&directory.join("history")),
        untouched,
        "neither placement moved a file the writer had already placed"
    );
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

    // And again with the placement that moves things, since a rule about two
    // replicas is a rule about what one command produces from one input.
    out(recorded(&one, &["arrange", "--refile"]));
    out(recorded(&two, &["arrange", "--refile"]));
    assert_eq!(
        walk_names(&one.join("history")),
        walk_names(&two.join("history")),
        "two replicas disagreed about where a name goes"
    );
}

#[test]
fn a_collision_suffix_is_the_same_whichever_placement_arranged_it() {
    // Decision 0006's hard rule reaches both placements. A suffix is derived
    // from the documents — the change ID, then the digest — so it cannot
    // depend on the directory the file was going to land in, and two stores
    // of one history arranged the two ways differ by a month directory and by
    // nothing else at all.
    let kept = repository("arrange-collide-kept");
    write(&kept, "notes/a.md", "one\n");
    out(recorded(&kept, &["record", "-m", "Notes"]));
    write(&kept, "notes/a.md", "two\n");
    out(recorded(&kept, &["record", "-m", "Notes"]));

    // Flat to start with, so both placements have something to do.
    flatten(&kept.join("history"));
    let refiled = scratch("arrange-collide-refiled");
    copy_tree(&kept.join("history"), &refiled.join("history"));

    out(recorded(&kept, &["arrange"]));
    out(recorded(&refiled, &["arrange", "--refile"]));

    let here = walk_names(&kept.join("history/revisions"));
    let there = walk_names(&refiled.join("history/revisions"));
    assert_eq!(here.len(), 2, "{here:?}");
    assert!(
        here.iter().all(|name| name.contains("Notes ")),
        "two revisions under one summary needed a suffix: {here:?}"
    );
    assert!(here.iter().all(|name| !name.contains('/')), "{here:?}");
    assert!(there.iter().all(|name| name.contains('/')), "{there:?}");

    let filename = |names: &[String]| -> Vec<String> {
        names
            .iter()
            .map(|name| name.rsplit('/').next().expect("a filename").to_owned())
            .collect()
    };
    assert_eq!(
        filename(&here),
        filename(&there),
        "a suffix that differed by placement would not be content-derived"
    );
    // And `operations/` is one tree either way, because it is filed by the
    // revision's stem under both.
    assert_eq!(
        walk_names(&kept.join("history/operations")),
        walk_names(&refiled.join("history/operations")),
    );
}

#[test]
fn refiling_files_a_flat_store_and_then_has_nothing_left_to_do() {
    // Decision 0041's migration, which is what `--refile` is: a store written
    // flat — by an older version, by another tool, or by hand — is one
    // `arrange --refile` away from the layout this version writes, and a
    // second one moves nothing. Plain `arrange` is deliberately not that
    // command, because a revision sitting in `revisions/` is indistinguishable
    // from one a person put there.
    let directory = repository("arrange-flatten");
    write(&directory, "notes/a.md", "one\n");
    out(recorded(&directory, &["record", "-m", "Start a journal"]));
    write(&directory, "notes/a.md", "two\n");
    out(recorded(&directory, &["record", "-m", "Say more"]));

    // The store as the version before this one would have left it: the same
    // names, one level up.
    let history = directory.join("history");
    flatten(&history);
    let before = stdout(&directory, &["log"]);
    let flat = walk_names(&history.join("revisions"));
    assert!(
        flat.iter().all(|name| !name.contains('/')),
        "the store is flat to start with: {flat:?}"
    );

    // Plain `arrange` files `operations/`, which has been its territory since
    // 0016 — the directory there says which revision and which path, which is
    // a fact about the history rather than a folder anybody chose — and
    // leaves the revision documents exactly where they are.
    let kept = stdout(&directory, &["arrange"]);
    let still = walk_names(&history.join("revisions"));
    assert!(
        still.iter().all(|name| !name.contains('/')),
        "plain arranging must not move what a person may have filed: {still:?} {kept}"
    );
    for name in walk_names(&history.join("operations")) {
        let (month, rest) = name.split_once('/').expect("a month directory");
        assert_eq!(month, &rest[..month.len()], "{kept}");
    }

    // `--refile` is the migration, and it is the revisions it comes for.
    let done = stdout(&directory, &["arrange", "--refile"]);
    assert!(done.contains("2 renamed"), "{done}");
    for name in walk_names(&history.join("revisions")) {
        let (month, rest) = name.split_once('/').expect("a month directory");
        assert_eq!(month, &rest[..month.len()], "{done}");
    }
    // The bytes never moved, so neither did the history.
    assert_eq!(stdout(&directory, &["log"]), before);
    assert!(
        stdout(&directory, &["check"]).ends_with("nothing to report\n"),
        "a filed store is as valid as a flat one"
    );

    // Refiling twice moves nothing, and neither does the default afterwards:
    // a store that has been migrated is a store the writer could have written.
    let again = stdout(&directory, &["arrange", "--refile"]);
    assert!(again.contains("0 renamed, 2 already arranged"), "{again}");
    let settled = stdout(&directory, &["arrange"]);
    assert!(
        settled.contains("0 renamed, 2 already arranged"),
        "{settled}"
    );
}

/// Lift both store directories out of their months, leaving the flat store a
/// version before decision 0041 would have written.
fn flatten(history: &Path) {
    for directory in ["revisions", "operations"] {
        let within = history.join(directory);
        let months: Vec<PathBuf> = fs::read_dir(&within)
            .expect("the directory")
            .filter_map(Result::ok)
            .map(|entry| entry.path())
            .collect();
        assert_eq!(months.len(), 1, "one month was written: {months:?}");
        for month in months {
            for entry in fs::read_dir(&month).expect("the month").flatten() {
                fs::rename(entry.path(), within.join(entry.file_name())).expect("flattening");
            }
            fs::remove_dir(&month).expect("the emptied month");
        }
    }
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

/// Decision 0062: the target conflicts and the axis joins. A name marked
/// private on one machine reaches the person's other machines by the transport
/// already running, which is what 0051 calls the feature; a name pointing two
/// ways is the conflict it always was, and a *privacy* disagreement is not one,
/// because `ReceiveError::Mutable` refuses the whole receive and a deadlocked
/// sync is the manufactured conflict 0045 removed.
#[test]
fn receive_takes_a_private_bookmark_and_joins_the_axis() {
    let here = repository("receive-axis-here");
    write(&here, "notes.md", "common\n");
    out(recorded(&here, &["record", "-m", "Common root"]));
    out(recorded(&here, &["name", "main", "head"]));
    let there = scratch("receive-axis-there");
    copy_tree(&here, &there);

    // One name only the source has, and private. It arrives whole.
    out(recorded(
        &there,
        &["name", "--private", "acme-layoffs", "head"],
    ));
    // And one both hold at one target, which the source alone calls private.
    out(recorded(&there, &["name", "--private", "main", "head"]));

    let source = there.to_string_lossy();
    let received = stdout(&here, &["receive", &source]);
    assert!(received.contains("received 2 bookmarks"), "{received}");

    let names = stdout(&here, &["names"]);
    assert!(names.contains("acme-layoffs"), "{names}");
    assert_eq!(
        names
            .lines()
            .filter(|line| line.contains("(private)"))
            .count(),
        2,
        "the axis did not join: {names}"
    );

    // Idempotent: a second receive has nothing left to join.
    let again = stdout(&here, &["receive", &source]);
    assert!(!again.contains("bookmarks"), "{again}");

    // The target is still what conflicts, and a conflict writes nothing.
    write(&here, "notes.md", "ours\n");
    out(recorded(&here, &["record", "-m", "Work done here"]));
    write(&there, "notes.md", "theirs\n");
    out(recorded(&there, &["record", "-m", "Work done there"]));
    let refused = run(&here, &["receive", &source]);
    assert!(!refused.status.success());
    let said = String::from_utf8(refused.stderr).expect("printed text");
    assert!(said.contains("disagree about mutable files"), "{said}");
    assert!(said.contains("name main:"), "{said}");
    assert!(
        said.contains("(private)"),
        "the axis is unprintable: {said}"
    );
}

/// Decision 0053: a reserved directory travels by its class. `claims/` is
/// `travels-and-unions`, so a receive adds the names it lacks and leaves the
/// names it holds exactly as they are — it never reads one, so "the same
/// file" can only mean the same name. `trust/` is `local-only`, and a receive
/// that wrote it would be authority arriving from the party the policy exists
/// to judge.
#[test]
fn receive_unions_claims_and_never_writes_trust() {
    let here = repository("receive-claims-here");
    write(&here, "notes.md", "common\n");
    out(recorded(&here, &["record", "-m", "Common root"]));

    let there = scratch("receive-claims-there");
    copy_tree(&here, &there);
    write(&there, "notes.md", "theirs\n");
    out(recorded(&there, &["record", "-m", "Work done there"]));

    // A claim each, a name both stores hold under different bytes, and the
    // trust policy the source states about itself.
    write(&here, "history/claims/ours.claim.txt", "claim-0\nours\n");
    write(
        &here,
        "history/claims/both.claim.txt",
        "claim-0\nheld here\n",
    );
    write(
        &there,
        "history/claims/theirs.claim.txt",
        "claim-0\ntheirs\n",
    );
    write(
        &there,
        "history/claims/theirs.claim.txt.minisig",
        "untrusted comment: signature from minisign secret key\n",
    );
    write(
        &there,
        "history/claims/both.claim.txt",
        "claim-0\nheld there\n",
    );
    write(&there, "history/trust/them.txt", "trust-0\nkey RWTd8LRC…\n");

    let planned = stdout(&here, &["receive", &there.to_string_lossy(), "--dry-run"]);
    assert!(
        planned.contains("would receive 2 files another tool wrote"),
        "{planned}"
    );
    let received = stdout(&here, &["receive", &there.to_string_lossy()]);
    assert!(
        received.contains("received 2 files another tool wrote"),
        "{received}"
    );

    // Add-only: what arrived is what this store had no name for.
    assert_eq!(
        walk_names(&here.join("history/claims")),
        vec![
            "both.claim.txt".to_owned(),
            "ours.claim.txt".to_owned(),
            "theirs.claim.txt".to_owned(),
            "theirs.claim.txt.minisig".to_owned(),
        ]
    );
    assert_eq!(
        fs::read_to_string(here.join("history/claims/both.claim.txt")).expect("the held claim"),
        "claim-0\nheld here\n",
        "a name this store already held was overwritten"
    );
    assert!(
        !here.join("history/trust").exists(),
        "0046's trust policy crossed a store boundary"
    );
    // Nothing went the other way either: a receive reads the source.
    assert!(!there.join("history/claims/ours.claim.txt").exists());

    // And a second run has nothing to add, which is what makes this a union
    // rather than a copy that keeps arriving.
    let again = stdout(&here, &["receive", &there.to_string_lossy()]);
    assert!(
        !again.contains("files another tool wrote"),
        "the union is not idempotent: {again}"
    );
    assert!(stdout(&here, &["check"]).ends_with("nothing to report\n"));
}

/// Decision 0032 gave `operations/` a second grammar, and transport carries
/// it. A receive that copied only operation documents delivered every
/// revision of a merge and not the document its `edit` line names — and then
/// said, on the next run, that there was nothing left to send, while the head
/// it had just delivered would not read.
#[test]
fn receive_carries_the_resolution_a_merge_states() {
    let (there, mine, theirs) = diverged(
        "receive-merge-there",
        "one\nMINE\nthree\n",
        "one\nTHEIRS\nthree\n",
    );
    out(recorded(&there, &["merge", &mine, &theirs]));
    write(&there, "f.md", "one\nMINE\nBOTH\nTHEIRS\nthree\n");
    out(recorded(
        &there,
        &["record", "--merge", &mine, "--merge", &theirs, "-m", "Join"],
    ));

    let here = repository("receive-merge-here");
    let source = there.to_string_lossy();
    let received = stdout(&here, &["receive", &source]);
    assert!(received.contains("received 4 revisions"), "{received}");

    // The head reads, which is the whole claim: the resolution arrived.
    assert_eq!(
        stdout(&here, &["cat", "head", "f.md"]),
        "one\nMINE\nBOTH\nTHEIRS\nthree\n"
    );
    assert!(
        stdout(&here, &["check", "--complete"]).contains("nothing to report"),
        "a store that received a merge is complete"
    );
    // Byte for byte, in the grammar it was written in.
    assert_eq!(
        stdout(&here, &["show", "head", "f.md"]),
        stdout(&there, &["show", "head", "f.md"])
    );

    let again = stdout(&here, &["receive", &source]);
    assert!(again.contains("received 0 revisions"), "{again}");
    assert!(again.contains("received 0 content documents"), "{again}");
}

/// `show` prints what is stored, and decision 0032 made "what is stored" have
/// two possible grammars. Asking only the older one reported a document the
/// store was holding perfectly well as one it had not received.
#[test]
fn show_prints_the_resolution_a_merge_states() {
    let (directory, mine, theirs) = diverged(
        "show-resolution",
        "one\nMINE\nthree\n",
        "one\nTHEIRS\nthree\n",
    );
    out(recorded(&directory, &["merge", &mine, &theirs]));
    write(&directory, "f.md", "one\nBOTH\nthree\n");
    out(recorded(
        &directory,
        &["record", "--merge", &mine, "--merge", &theirs, "-m", "Join"],
    ));

    let document = stdout(&directory, &["show", "head", "f.md"]);
    assert!(document.starts_with("historica\nresult "), "{document}");
    assert!(document.contains("\nkeep "), "{document}");
    assert!(
        document.contains("\ninsert\n+BOTH\n"),
        "the line typed while resolving is in the document: {document}"
    );
}

/// Decision 0014 reaching decision 0032's second grammar.
///
/// Text a person types while resolving a merge exists only as `insert` items
/// in the resolution, so before the resolution grammar could say an item was
/// destroyed there was no way to redact it at all.
#[test]
fn forget_reaches_the_lines_a_merge_minted() {
    let (directory, mine, theirs) = diverged(
        "forget-minted",
        "one\nMINE\nthree\n",
        "one\nTHEIRS\nthree\n",
    );
    out(recorded(&directory, &["merge", &mine, &theirs]));

    // Both runs kept in the order the walk proposed them, and one line typed
    // under them — the only piece this resolution mints.
    let rendered = fs::read_to_string(directory.join("f.md")).expect("the merged file");
    let mut lines: Vec<&str> = rendered
        .lines()
        .filter(|line| !line.starts_with("vvv historica: ") && !line.starts_with("^^^ historica: "))
        .collect();
    lines.push("SECRET");
    write(&directory, "f.md", &format!("{}\n", lines.join("\n")));
    out(recorded(
        &directory,
        &["record", "--merge", &mine, "--merge", &theirs, "-m", "Join"],
    ));

    let at = lines.len();
    let forgotten = stdout(
        &directory,
        &["forget", "head", "f.md", "--lines", &format!("{at}..{at}")],
    );
    assert!(forgotten.contains("forgetting document"), "{forgotten}");

    let read = stdout(&directory, &["cat", "head", "f.md"]);
    assert!(!read.contains("SECRET"), "the text was destroyed: {read}");
    assert!(
        read.contains("\\ forgotten"),
        "its shape and place are kept: {read}"
    );

    // The stand-in is a resolution, because a stand-in has the shape of what
    // it stands in for: `forgets`, no `result`, every `keep` intact.
    let document = stdout(&directory, &["show", "head", "f.md"]);
    assert!(document.contains("\nforgets "), "{document}");
    assert!(!document.contains("\nresult "), "{document}");
    assert!(document.contains("\ninsert\n\\ forgotten\n"), "{document}");

    let checked = stdout(&directory, &["check", "--complete"]);
    assert!(checked.contains("no errors"), "{checked}");
    assert!(
        stdout(
            &directory,
            &["forget", "head", "f.md", "--lines", &format!("{at}..{at}")]
        )
        .contains("already forgotten"),
        "forgetting twice is a no-op"
    );
}

/// A resolution cannot reorder the items it keeps — the walk records which
/// survive, never where they go — so a person who moves a run while resolving
/// leaves the recorder no way to name it and it is minted again, under the
/// resolution's own name. That copy is the same text with a different name.
///
/// Redacting the original alone destroyed the bytes, passed `check`, and left
/// the text readable at the head, with `forget` reporting success.
#[test]
fn forget_reaches_the_copy_a_merge_made_of_a_moved_line() {
    let (directory, mine, theirs) =
        diverged("forget-moved", "one\nMINE\nthree\n", "one\nTHEIRS\nthree\n");
    out(recorded(&directory, &["merge", &mine, &theirs]));

    // The two runs in the opposite order to the one the walk proposed, which
    // is what makes the recorder mint a copy of the one that moved.
    let rendered = fs::read_to_string(directory.join("f.md")).expect("the merged file");
    let mut lines: Vec<&str> = rendered
        .lines()
        .filter(|line| !line.starts_with("vvv historica: ") && !line.starts_with("^^^ historica: "))
        .collect();
    lines.swap(1, 2);
    write(&directory, "f.md", &format!("{}\n", lines.join("\n")));
    out(recorded(
        &directory,
        &["record", "--merge", &mine, "--merge", &theirs, "-m", "Join"],
    ));
    let moved = lines[1].to_owned();
    assert!(
        stdout(&directory, &["show", "head", "f.md"]).contains(&format!("\n+{moved}\n")),
        "the merge restated the run it could not name"
    );

    // Forget it where it was written, which is an ancestor of the merge and
    // says nothing about the copy. Found by what the revision holds rather
    // than by which head came back first.
    let wrote = [&mine, &theirs]
        .into_iter()
        .find(|head| stdout(&directory, &["cat", head, "f.md"]).lines().nth(1) == Some(&moved))
        .expect("the branch that wrote the run that moved");
    let forgotten = stdout(&directory, &["forget", wrote, "f.md", "--lines", "2..2"]);
    assert!(forgotten.contains("forgetting document"), "{forgotten}");

    let read = stdout(&directory, &["cat", "head", "f.md"]);
    assert!(
        !read.contains(&moved),
        "the copy the merge minted is still readable at the head: {read}"
    );
    // Only that run: the other branch's line is nobody's redaction.
    assert!(
        read.contains(lines[2]),
        "the run that did not move is untouched: {read}"
    );
    let checked = stdout(&directory, &["check", "--complete"]);
    assert!(checked.contains("no errors"), "{checked}");
}

/// A forgetting document is named by nothing — a revision's `edit` line still
/// names the digest whose bytes were destroyed — so every command that keeps
/// one alive, carries it, or complies with it finds it by asking each
/// document what it forgets. Each of them has to ask both grammars.
#[test]
fn a_redacted_merge_travels_and_stays_redacted() {
    let (there, mine, theirs) = diverged(
        "redacted-merge-there",
        "one\nMINE\nthree\n",
        "one\nTHEIRS\nthree\n",
    );
    out(recorded(&there, &["merge", &mine, &theirs]));
    let rendered = fs::read_to_string(there.join("f.md")).expect("the merged file");
    let mut lines: Vec<&str> = rendered
        .lines()
        .filter(|line| !line.starts_with("vvv historica: ") && !line.starts_with("^^^ historica: "))
        .collect();
    lines.push("SECRET");
    write(&there, "f.md", &format!("{}\n", lines.join("\n")));
    out(recorded(
        &there,
        &["record", "--merge", &mine, "--merge", &theirs, "-m", "Join"],
    ));
    let at = lines.len();
    out(recorded(
        &there,
        &["forget", "head", "f.md", "--lines", &format!("{at}..{at}")],
    ));
    let redacted = stdout(&there, &["cat", "head", "f.md"]);
    assert!(!redacted.contains("SECRET"), "{redacted}");

    // Received into a store that never held the original.
    let here = repository("redacted-merge-here");
    let source = there.to_string_lossy();
    out(recorded(&here, &["receive", &source]));
    assert_eq!(stdout(&here, &["cat", "head", "f.md"]), redacted);
    assert!(
        stdout(&here, &["check", "--complete"]).contains("no errors"),
        "a received redaction leaves a sound store"
    );

    // And exported out of the redacted store, which has to carry a stand-in
    // nothing names.
    let copy = scratch("redacted-merge-copy").join("out");
    out(recorded(&there, &["export", &copy.to_string_lossy()]));
    assert_eq!(stdout(&copy, &["cat", "head", "f.md"]), redacted);
    assert!(
        stdout(&copy, &["check", "--complete"]).contains("no errors"),
        "an exported redaction leaves a sound store"
    );
    assert!(
        !fs::read_to_string(copy.join("f.md"))
            .expect("the folder")
            .contains("SECRET"),
        "the folder the export wrote holds the redacted file"
    );
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
fn two_replicas_that_each_wrote_a_rule_union_them() {
    // Decision 0045, and the failure it was written from: this was a conflict
    // `receive` refused over, and the merge it refused to perform was *both
    // lines*. `skips` asks every rule, so neither replica ever contradicted
    // the other — only the file they were written into could.
    let here = repository("receive-rules-here");
    write(&here, "notes.md", "common\n");
    out(recorded(&here, &["record", "-m", "Common root"]));
    let there = scratch("receive-rules-there");
    copy_tree(&here, &there);

    out(recorded(&here, &["skip", "target"]));
    out(recorded(&there, &["skip", "--name", "*.tmp"]));
    write(&there, "notes.md", "theirs\n");
    out(recorded(&there, &["record", "-m", "Work done there"]));

    let source = there.to_string_lossy();
    let planned = run(&here, &["receive", &source, "--dry-run"]);
    assert_eq!(planned.status.code(), Some(0), "a union is not a conflict");
    let planned = String::from_utf8(planned.stdout).expect("printed text");
    assert!(planned.contains("would receive 1 rules"), "{planned}");

    let received = stdout(&here, &["receive", &source]);
    assert!(received.contains("received 1 rules"), "{received}");
    let listed = out(recorded(&here, &["skip"]));
    assert!(listed.contains("skip target"), "{listed}");
    assert!(listed.contains("skip-name *.tmp"), "{listed}");

    // The rule arrived as the file that states it, under the label the writer
    // chose, so deleting it is what dropping the rule means. Decision 0051
    // makes that label the rule's digest, because the value holds a `*`.
    let tmp_rule = walk_names(&here.join("history/skipped"))
        .into_iter()
        .find(|label| {
            fs::read_to_string(here.join("history/skipped").join(label))
                .is_ok_and(|text| text == "skip-name *.tmp\n")
        })
        .expect("the file stating the rule that arrived");
    assert!(!tmp_rule.contains('*'), "{tmp_rule}");

    // And receiving again adds nothing, because a rule already stated is a
    // rule this store has.
    let again = stdout(&here, &["receive", &source]);
    assert!(!again.contains("rules"), "{again}");

    // A rule deleted here and still stated there comes back, which decision
    // 0045 accepts as the recoverable direction: keeping a file out of a
    // history can be undone, and taking one in cannot.
    fs::remove_file(here.join(format!("history/skipped/{tmp_rule}"))).expect("the rule");
    assert!(!out(recorded(&here, &["skip"])).contains(".tmp"));
    let back = stdout(&here, &["receive", &source]);
    assert!(back.contains("received 1 rules"), "{back}");
    assert!(out(recorded(&here, &["skip"])).contains("skip-name *.tmp"));
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

    // Renamed, not moved. A person who filed it there meant to — decision
    // 0016's rule about a name that differs, which decision 0041's revision
    // extends from `check` to `arrange` itself. The filename is the whole
    // date either way, so the file still says when it is from.
    assert!(
        filed.join("2025-08-19 Start a journal.rev.txt").exists(),
        "{done}"
    );
    assert!(
        !revisions
            .join("2025-08/2025-08-19 Start a journal.rev.txt")
            .exists(),
        "arranging must not flatten what a person arranged: {done}"
    );
    assert!(revisions.join("early").exists(), "{done}");
    assert_eq!(stdout(&directory, &["log"]), before);

    // And arranging an arranged store is a no-op, at whatever depth.
    let again = stdout(&directory, &["arrange"]);
    assert!(again.contains("4 already arranged"), "{again}");

    // `--refile` is the one thing that overrules the folder they chose, and
    // it takes the emptied folder with it rather than leaving a husk.
    let refiled = stdout(&directory, &["arrange", "--refile"]);
    assert!(
        revisions
            .join("2025-08/2025-08-19 Start a journal.rev.txt")
            .exists(),
        "{refiled}"
    );
    assert!(!revisions.join("early").exists(), "{refiled}");
    assert_eq!(stdout(&directory, &["log"]), before);

    // After which the default has nothing left to disagree with.
    let settled = stdout(&directory, &["arrange"]);
    assert!(
        settled.contains("0 renamed, 4 already arranged"),
        "{settled}"
    );
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
    // In `revisions/` itself, because that is where these sat: a corpus store
    // is flat, and flat is a placement `arrange` respects like any other.
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

    // And `--refile` is what puts the same names under decision 0041's month.
    let refiled = stdout(&directory, &["arrange", "--refile"]);
    assert!(refiled.contains("4 renamed"), "{refiled}");
    assert!(
        directory
            .join("history/revisions/2025-08/2025-08-19 Start a journal.rev.txt")
            .exists(),
        "{refiled}"
    );
    assert_eq!(stdout(&directory, &["log"]), before);
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

/// Decision 0017 fixes a kind when a file is added and lets the recorder sniff
/// it — valid UTF-8 with no NUL is lines. `docs/cli.md` has always called that
/// the tool's rule rather than the format's, and these are what being the
/// tool's means.
#[test]
fn a_person_says_which_kind_a_file_being_added_is() {
    let directory = repository("stated-kinds");
    // Text by the sniff's reckoning, and a thing nobody wants line-merged.
    write(&directory, "bundle.min.js", "{\"a\":1}\n");
    // UTF-8 that holds a NUL, which the sniff cannot tell from a photograph.
    fs::write(directory.join("odd.txt"), b"text with\x00a nul\n").expect("a file");
    write(&directory, "notes.md", "alpha\n");

    assert!(
        recorded(
            &directory,
            &[
                "record",
                "--bytes",
                "bundle.min.js",
                "--lines",
                "odd.txt",
                "-m",
                "base"
            ],
        )
        .status
        .success()
    );

    // The document is where the answer is: `bytes` for the one stated as
    // bytes, `text` for the one stated as lines, and the sniff for the rest.
    let listed = out(recorded(&directory, &["log", "--fields"]));
    let revision = listed
        .lines()
        .nth(1)
        .expect("a revision")
        .split(' ')
        .next()
        .expect("a digest");
    let document = out(recorded(&directory, &["show", revision]));
    let kind = |path: &str| {
        let file = document
            .lines()
            .find(|line| line.starts_with("add ") && line.ends_with(&format!(" {path}")))
            .and_then(|line| line.split(' ').nth(1))
            .expect("an added file");
        document
            .lines()
            .find(|line| {
                (line.starts_with("text ") || line.starts_with("bytes "))
                    && line.split(' ').nth(1) == Some(file)
            })
            .and_then(|line| line.split(' ').next())
            .expect("a kind")
            .to_owned()
    };
    assert_eq!(kind("bundle.min.js"), "bytes");
    assert_eq!(kind("odd.txt"), "text");
    assert_eq!(kind("notes.md"), "text");
}

/// The one thing stating a kind cannot do: an item is text, and no flag makes
/// bytes that are not UTF-8 into lines.
#[test]
fn lines_cannot_be_stated_for_bytes_that_are_not_utf8() {
    let directory = repository("stated-not-lines");
    fs::write(directory.join("utf16.txt"), b"\xff\xfeU\x00T\x00F\x00").expect("a file");

    let refused = recorded(&directory, &["record", "--lines", "utf16.txt", "-m", "no"]);
    assert!(!refused.status.success());
    let why = String::from_utf8(refused.stderr).expect("printed text");
    assert!(why.contains("its bytes are not UTF-8"), "{why}");
    assert!(why.contains("Record it as bytes"), "{why}");
}

/// Decision 0017 fixes a kind at `add`, so a statement about a file the
/// history already holds is one arriving too late.
#[test]
fn a_kind_cannot_be_stated_for_a_file_already_recorded() {
    let directory = repository("kind-already-fixed");
    write(&directory, "notes.md", "alpha\n");
    assert!(
        recorded(&directory, &["record", "-m", "base"])
            .status
            .success()
    );

    write(&directory, "notes.md", "beta\n");
    let refused = recorded(&directory, &["record", "--bytes", "notes.md", "-m", "no"]);
    assert!(!refused.status.success());
    let why = String::from_utf8(refused.stderr).expect("printed text");
    assert!(why.contains("already recorded as lines"), "{why}");
    assert!(why.contains("`drop` and an `add`"), "{why}");
}

/// Decision 0023: an amendment restates what its predecessor said, and which
/// kind each file it added is is one of those things — so a stated kind is not
/// quietly re-sniffed into the other answer.
#[test]
fn an_amendment_keeps_the_kind_its_predecessor_stated() {
    let directory = repository("amend-keeps-kind");
    write(&directory, "bundle.min.js", "{\"a\":1}\n");
    assert!(
        recorded(
            &directory,
            &["record", "--bytes", "bundle.min.js", "-m", "base"],
        )
        .status
        .success()
    );

    write(&directory, "bundle.min.js", "{\"a\":2}\n");
    assert!(
        recorded(&directory, &["amend", "-m", "amended"])
            .status
            .success()
    );

    let listed = out(recorded(&directory, &["log", "--fields"]));
    let revision = listed
        .lines()
        .nth(1)
        .expect("a revision")
        .split(' ')
        .next()
        .expect("a digest");
    let document = out(recorded(&directory, &["show", revision]));
    assert!(
        document.lines().any(|line| line.starts_with("bytes ")),
        "the amendment sniffed it back into lines:\n{document}"
    );
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
fn naming_paths_records_those_and_leaves_the_rest_unlooked_at() {
    let directory = repository("record-paths");
    write(&directory, "a.md", "one\n");
    write(&directory, "b.md", "one\n");
    out(recorded(&directory, &["record", "-m", "Start"]));

    write(&directory, "a.md", "one\ntwo\n");
    write(&directory, "b.md", "one\ntwo\n");
    write(&directory, "c.md", "arrived\n");

    let planned = out(recorded(
        &directory,
        &["record", "a.md", "c.md", "--dry-run"],
    ));
    assert_eq!(
        planned, "added   c.md\nedited  a.md\n",
        "only what was named is compared with the tree"
    );

    let restricted = out(recorded(
        &directory,
        &["record", "a.md", "c.md", "-m", "The two I meant"],
    ));
    assert!(restricted.contains("added   c.md"), "{restricted}");
    assert!(restricted.contains("edited  a.md"), "{restricted}");
    assert!(!restricted.contains("b.md"), "{restricted}");

    // Nothing was said about `b.md`, so history still holds what it held and
    // the folder still holds what a person wrote — which is what `status`
    // says, and what the next record with nothing named takes.
    assert_eq!(
        out(recorded(&directory, &["cat", "head", "b.md"])),
        "one\n",
        "an unnamed file is not recorded, and not touched either"
    );
    let after = out(recorded(&directory, &["status"]));
    assert!(after.contains("edited  b.md"), "{after}");
    let rest = out(recorded(&directory, &["record", "-m", "And the rest"]));
    assert!(rest.contains("edited  b.md"), "{rest}");
    assert_eq!(
        out(recorded(&directory, &["cat", "head", "b.md"])),
        "one\ntwo\n"
    );
    assert!(out(recorded(&directory, &["check"])).ends_with("nothing to report\n"));
}

#[test]
fn a_named_path_the_folder_no_longer_holds_is_a_deletion_observed() {
    let directory = repository("record-paths-dropped");
    write(&directory, "a.md", "one\n");
    write(&directory, "docs/b.md", "one\n");
    write(&directory, "docs/c.md", "one\n");
    out(recorded(&directory, &["record", "-m", "Start"]));

    // A path in the tree and not in the folder: absence is a fact, and it is
    // one of the facts a person may name.
    fs::remove_file(directory.join("docs/b.md")).expect("removing a file");
    write(&directory, "a.md", "one\ntwo\n");
    let dropped = out(recorded(&directory, &["record", "docs/b.md", "-m", "Gone"]));
    assert_eq!(
        dropped.lines().next(),
        Some("dropped docs/b.md"),
        "{dropped}"
    );
    assert_eq!(
        out(recorded(&directory, &["cat", "head", "a.md"])),
        "one\n",
        "the edit nobody named is still unrecorded"
    );

    // A directory names everything under it, there being no directories in
    // this format for it to name instead.
    write(&directory, "docs/c.md", "one\ntwo\n");
    write(&directory, "docs/d.md", "arrived\n");
    let under = out(recorded(&directory, &["record", "docs", "-m", "The docs"]));
    assert!(under.contains("edited  docs/c.md"), "{under}");
    assert!(under.contains("added   docs/d.md"), "{under}");
    assert!(!under.contains("a.md"), "{under}");
}

#[test]
fn a_restriction_may_not_spell_half_a_rename() {
    let directory = repository("record-paths-move");
    write(&directory, "notes.md", "one\n");
    write(&directory, "other.md", "one\n");
    out(recorded(&directory, &["record", "-m", "Start"]));

    let refused_move = refused(
        &directory,
        &[
            "record",
            "other.md",
            "--move",
            "notes.md=docs/notes.md",
            "-m",
            "File it",
        ],
    );
    assert!(refused_move.contains("notes.md"), "{refused_move}");
    assert!(refused_move.contains("docs/notes.md"), "{refused_move}");
    // And it refused before it rearranged anything: `--move` performs the
    // rename, so a refusal that arrived afterwards would have left the folder
    // holding a move nobody recorded.
    assert!(
        directory.join("notes.md").is_file() && !directory.join("docs/notes.md").exists(),
        "the folder is where it was"
    );

    // Both ends named is an ordinary rename.
    let moved = out(recorded(
        &directory,
        &[
            "record",
            "notes.md",
            "docs/notes.md",
            "--move",
            "notes.md=docs/notes.md",
            "-m",
            "File it",
        ],
    ));
    assert!(moved.contains("moved   docs/notes.md"), "{moved}");
    assert!(directory.join("docs/notes.md").is_file());
}

#[test]
fn a_merge_states_every_contested_file_or_is_not_recorded() {
    let (directory, mine, theirs) = diverged("record-paths-merge", "one\nMINE\n", "one\nTHEIRS\n");
    out(recorded(&directory, &["merge", &mine, &theirs]));
    write(&directory, "f.md", "one\nBOTH\n");

    let refused_merge = refused(
        &directory,
        &[
            "record", "f.md", "--merge", &mine, "--merge", &theirs, "-m", "Join",
        ],
    );
    assert!(
        refused_merge.contains("every contested file"),
        "{refused_merge}"
    );
    assert!(refused_merge.contains("no paths named"), "{refused_merge}");

    // The whole merge is still there to record.
    let joined = out(recorded(
        &directory,
        &["record", "--merge", &mine, "--merge", &theirs, "-m", "Join"],
    ));
    assert!(joined.contains("this joins 2 lines of work"), "{joined}");
}

#[test]
fn a_path_nothing_answers_to_is_refused_by_name() {
    let directory = repository("record-paths-unknown");
    write(&directory, "a.md", "one\n");
    out(recorded(&directory, &["record", "-m", "Start"]));

    write(&directory, "a.md", "one\ntwo\n");
    let unknown = refused(&directory, &["record", "nowhere.md", "-m", "x"]);
    assert!(unknown.contains("nowhere.md"), "{unknown}");
    assert!(
        unknown.contains("neither in the folder nor in this history"),
        "{unknown}"
    );

    // A path a rule keeps out is told apart from a path nobody has, because
    // the two have different fixes.
    out(recorded(&directory, &["skip", "notes.tmp"]));
    write(&directory, "notes.tmp", "scratch\n");
    let skipped = refused(&directory, &["record", "notes.tmp", "-m", "x"]);
    assert!(skipped.contains("skipped/"), "{skipped}");
    assert!(skipped.contains("notes.tmp"), "{skipped}");

    // Neither refusal recorded anything on its way past the file that changed.
    assert_eq!(out(recorded(&directory, &["cat", "head", "a.md"])), "one\n");
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
    use std::os::unix::ffi::OsStrExt as _;

    let directory = repository("record-refusals");
    write(&directory, "fine.md", "text\n");
    // Decision 0040 records a link rather than refusing one — but not a link
    // to a name this store cannot spell, because a store is UTF-8 text.
    std::os::unix::fs::symlink(
        std::ffi::OsStr::from_bytes(b"/etc/\xffhosts"),
        directory.join("link"),
    )
    .expect("a symlink");

    let refused = recorded(&directory, &["record", "-m", "Everything"]);
    assert!(!refused.status.success());
    let complaint = String::from_utf8_lossy(&refused.stderr).into_owned();
    assert!(complaint.contains("link"), "{complaint}");
    assert!(complaint.contains("skip"), "{complaint}");

    // Which is the fix the message names.
    write(&directory, "history/skipped/link.txt", "skip link\n");
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
    let written = out(recorded(&directory, &["skip", "target", "--name", "*.tmp"]));
    assert!(written.contains("skip target/"), "{written}");
    assert!(written.contains("skip-name *.tmp"), "{written}");
    // Decision 0045: it says which file states each rule, since deleting that
    // file is the whole of what removing a rule means.
    assert!(
        written.contains("history/skipped/target/all.txt"),
        "{written}"
    );
    // Decision 0051: a value holding a `*` is a filename no Windows volume
    // will carry and a shell will not leave alone, so the label is the
    // digest of the rule's own line.
    let tmp_rule = walk_names(&directory.join("history/skipped"))
        .into_iter()
        .find(|label| {
            fs::read_to_string(directory.join("history/skipped").join(label))
                .is_ok_and(|text| text == "skip-name *.tmp\n")
        })
        .expect("the digest label the pattern rule took");
    assert!(!tmp_rule.contains('*'), "{written}");
    assert!(written.contains(&tmp_rule), "{written}");

    // One rule to a file, and the label is a label: what the file holds is the
    // line a person would have typed.
    assert_eq!(
        fs::read_to_string(directory.join("history/skipped/target/all.txt")).expect("the file"),
        "skip target/\n"
    );
    assert_eq!(
        fs::read_to_string(directory.join(format!("history/skipped/{tmp_rule}")))
            .expect("the file"),
        "skip-name *.tmp\n"
    );
    // Nothing is skipped by default; defaults belong to the host or project.
    let note = fs::read_to_string(directory.join("history/skipped/README.txt")).expect("the note");
    assert!(!note.contains("skip-name .DS_Store"), "{note}");

    // With no arguments it prints them, as `names` prints the bookmarks.
    let listed = out(recorded(&directory, &["skip"]));
    assert!(listed.contains("skip target/"), "{listed}");
    assert!(listed.contains(&tmp_rule), "{listed}");
    // Decision 0051: the listing says which side of the travel axis each rule
    // is on, because `export` treats the two differently.
    assert!(listed.contains("shared"), "{listed}");

    // And the rules are the ones recording honours.
    let first = out(recorded(&directory, &["record", "-m", "First"]));
    assert!(first.contains("notes/a.md"), "{first}");
    assert!(!first.contains("out.bin"), "{first}");

    // Saying it twice writes one file and says so.
    let again = out(recorded(&directory, &["skip", "target/"]));
    assert!(again.contains("already there"), "{again}");
    assert_eq!(
        walk_names(&directory.join("history/skipped")).len(),
        3,
        "the note and the two rules"
    );
}

#[test]
fn skip_refuses_a_rule_over_what_history_holds_and_writes_nothing() {
    let directory = repository("skip-command-refusal");
    write(&directory, "drafts/one.md", "one\n");
    out(recorded(&directory, &["record", "-m", "First"]));

    // Decision 0011, answered before the file is written rather than at the
    // next record: the person is standing in front of the answer now.
    let refused = recorded(&directory, &["skip", "drafts", "--name", "*.tmp"]);
    assert!(!refused.status.success());
    let complaint = String::from_utf8_lossy(&refused.stderr).into_owned();
    assert!(complaint.contains("drafts/one.md"), "{complaint}");

    // Nothing is written, the good rule in the same command included: a
    // command that half-applied would leave a person guessing which half.
    assert_eq!(
        walk_names(&directory.join("history/skipped")),
        vec!["README.txt".to_owned()],
        "only the note `init` wrote"
    );
}

#[test]
fn skip_leaves_the_files_a_person_wrote_alone() {
    let directory = repository("skip-command-append");
    // A person's own files, under their own names, with their own comments.
    write(
        &directory,
        "history/skipped/mine/one.txt",
        "# the build\nskip one/\n",
    );
    write(
        &directory,
        "history/skipped/binaries.txt",
        "skip-name *.bin\n",
    );

    out(recorded(&directory, &["skip", "two/"]));

    // Decision 0045: adding a rule creates a file, so there is no file to
    // rewrite and nothing of anybody's to lose.
    assert_eq!(
        fs::read_to_string(directory.join("history/skipped/mine/one.txt")).expect("the file"),
        "# the build\nskip one/\n"
    );
    assert_eq!(
        fs::read_to_string(directory.join("history/skipped/two/all.txt")).expect("the file"),
        "skip two/\n"
    );
    let listed = out(recorded(&directory, &["skip"]));
    for rule in ["skip one/", "skip-name *.bin", "skip two/"] {
        assert!(listed.contains(rule), "{listed}");
    }
}

#[test]
fn a_private_rule_keeps_a_file_out_and_its_own_text_out_of_a_copy() {
    // Decision 0051's travel axis, end to end. `private` keeps a file out of
    // history exactly as `skip` does; what parts them is one line of one copy.
    let directory = repository("skip-private");
    write(&directory, "notes.md", "kept\n");
    fs::create_dir_all(directory.join("clients/acme-layoffs")).expect("a directory");
    write(
        &directory,
        "clients/acme-layoffs/plan.md",
        "not for anybody\n",
    );

    let written = out(recorded(
        &directory,
        &["skip", "--private", "clients/acme-layoffs"],
    ));
    assert!(
        written.contains("private clients/acme-layoffs/"),
        "{written}"
    );
    assert_eq!(
        fs::read_to_string(directory.join("history/skipped/clients/acme-layoffs/all.txt"))
            .expect("the file"),
        "private clients/acme-layoffs/\n"
    );

    // It keeps the file out of history, which is the half it shares with
    // `skip`.
    let first = out(recorded(&directory, &["record", "-m", "First"]));
    assert!(first.contains("notes.md"), "{first}");
    assert!(!first.contains("acme-layoffs"), "{first}");

    // And the listing says which side of the axis it is on.
    let listed = out(recorded(&directory, &["skip"]));
    assert!(listed.contains("private"), "{listed}");

    // The copy never learns the client's name.
    out(recorded(&directory, &["skip", "target/"]));
    let copy = scratch("skip-private-copy").join("journal");
    let said = out(recorded(&directory, &["export", &copy.to_string_lossy()]));
    assert!(said.contains("exported 1 rules"), "{said}");
    assert!(said.contains("held back 1 private rules"), "{said}");
    let rules = out(recorded(&copy, &["skip"]));
    assert!(rules.contains("skip target/"), "{rules}");
    assert!(
        !rules.contains("acme"),
        "the private rule's text travelled: {rules}"
    );
}

#[test]
fn a_name_rule_matches_a_component_at_any_depth() {
    // Decision 0051: one path component, `*` for any run inside it, and the
    // trailing slash making the same parting the paths make.
    let directory = repository("skip-name");
    write(&directory, "notes.md", "kept\n");
    write(&directory, "docs/draft-one.md", "a dropping\n");
    write(&directory, "app/node_modules/left-pad/index.js", "junk\n");
    write(
        &directory,
        "node_modules",
        "a file of that name, not a folder\n",
    );

    out(recorded(&directory, &["skip", "--name", "draft-*.md"]));
    out(recorded(&directory, &["skip", "--name", "node_modules/"]));

    let first = out(recorded(&directory, &["record", "-m", "First"]));
    assert!(first.contains("notes.md"), "{first}");
    assert!(!first.contains("draft-one.md"), "{first}");
    assert!(!first.contains("left-pad"), "{first}");
    assert!(
        first.contains("node_modules"),
        "a directory rule took a file of that name: {first}"
    );
}

#[test]
fn a_pattern_that_holds_a_separator_or_only_stars_is_refused() {
    let directory = repository("skip-name-refused");
    let complaint = refused(&directory, &["skip", "--name", "docs/*.tmp"]);
    assert!(complaint.contains("one path component"), "{complaint}");
    let complaint = refused(&directory, &["skip", "--name", "*"]);
    assert!(complaint.contains("whole folder"), "{complaint}");
    // And the retired flag says what to type instead.
    let complaint = refused(&directory, &["skip", "--suffix", ".tmp"]);
    assert!(complaint.contains("`--suffix` is retired"), "{complaint}");
    assert_eq!(
        walk_names(&directory.join("history/skipped")),
        vec!["README.txt".to_owned()]
    );
}

#[test]
fn check_names_a_path_covered_both_privately_and_shared() {
    // Decision 0051's one way the travel axis fails: a union takes both, so
    // the shared rule names the path in every copy and the private rule
    // accomplishes nothing. Two files a receive can legitimately produce, so
    // it is a finding rather than a refusal.
    let directory = repository("skip-both-ways");
    write(&directory, "history/skipped/docs/all.txt", "skip docs/\n");
    write(&directory, "history/skipped/mine.txt", "private docs/\n");

    let checked = String::from_utf8_lossy(&recorded(&directory, &["check"]).stdout).into_owned();
    assert!(checked.contains("covered privately"), "{checked}");
    assert!(checked.contains("history/skipped/mine.txt"), "{checked}");
    assert!(
        checked.contains("history/skipped/docs/all.txt"),
        "{checked}"
    );
    assert!(checked.contains("error"), "{checked}");

    // Deleting either file is the fix.
    fs::remove_file(directory.join("history/skipped/mine.txt")).expect("the rule");
    assert!(out(recorded(&directory, &["check"])).ends_with("nothing to report\n"));
}

#[test]
fn check_names_the_spelling_that_replaces_a_retired_rule() {
    let directory = repository("skip-retired");
    write(&directory, "history/skipped/old.txt", "skip-suffix .tmp\n");

    let checked = String::from_utf8_lossy(&recorded(&directory, &["check"]).stdout).into_owned();
    assert!(checked.contains("skip-name *.tmp"), "{checked}");
    assert!(checked.contains("history/skipped/old.txt"), "{checked}");

    // And every other command stops at it, because a rule that does not read
    // would take a file somebody asked it to leave.
    let complaint = refused(&directory, &["status"]);
    assert!(
        complaint.contains("`skip-suffix` is retired"),
        "{complaint}"
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
    write(
        &directory,
        "history/skipped/drafts/all.txt",
        "skip drafts/\n",
    );
    let refused = recorded(&directory, &["record", "-m", "Second"]);
    assert!(!refused.status.success());
    let complaint = String::from_utf8_lossy(&refused.stderr).into_owned();
    assert!(complaint.contains("drafts/one.md"), "{complaint}");
    assert!(complaint.contains("history/skipped/"), "{complaint}");

    // And `check` says the same thing about the store, naming the one file
    // that has to go — the state decision 0045 lets a `receive` produce.
    let checked = String::from_utf8_lossy(&recorded(&directory, &["check"]).stdout).into_owned();
    assert!(
        checked.contains("history/skipped/drafts/all.txt"),
        "{checked}"
    );

    fs::remove_file(directory.join("history/skipped/drafts/all.txt")).expect("the rule");

    // A rule over a path nothing has recorded is ordinary, which is the whole
    // point of the file.
    write(&directory, "history/skipped/tmp.txt", "skip-name *.tmp\n");
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
    write(
        &directory,
        "history/skipped/drafts/all.txt",
        "skip drafts/\n",
    );
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
    let script = Path::new(env!("CARGO_MANIFEST_DIR")).join("../tests/by-hand.sh");
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
    assert!(resolution.starts_with("historica\nresult "), "{resolution}");
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
    {
        use std::os::unix::ffi::OsStrExt as _;

        std::os::unix::fs::symlink(
            std::ffi::OsStr::from_bytes(b"/etc/\xffhosts"),
            directory.join("link"),
        )
        .expect("a symlink");
    }

    // The point of the list: one command names every file, so the `skip` rules
    // are written in one pass rather than one command per file.
    let listed = out(recorded(&directory, &["status"]));
    assert!(listed.contains("added   fine.md"), "{listed}");
    // Decision 0017: a file of bytes is content, not a refusal.
    assert!(listed.contains("added   picture.bin"), "{listed}");
    #[cfg(unix)]
    assert!(
        listed.contains("refused link: a link pointing at a name that is not UTF-8"),
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

    // A digest is the one thing about a head that says nothing about which
    // line of work it is. What a person recognises is the message they wrote,
    // the name on it, and the moment — so the refusal states all three.
    assert!(refused.contains("mine"), "{refused}");
    assert!(refused.contains("theirs"), "{refused}");
    assert!(
        refused.contains("Adam Harris <adam@example.com>"),
        "{refused}"
    );
    assert!(
        refused.contains("historica merge"),
        "the refusal should say what joins them: {refused}"
    );

    // Naming one is the whole of the fix, and the same flag `record` takes.
    let named = out(recorded(&directory, &["status", "--onto", &mine]));
    assert!(named.contains("journal"), "{named}");
}

/// Decision 0034's whole point: record an executable file, remove it, put it
/// back from the store, and it is still executable.
#[cfg(unix)]
#[test]
fn the_executable_bit_survives_a_round_trip_through_the_store() {
    use std::os::unix::fs::PermissionsExt as _;

    let executable = |directory: &Path, path: &str| {
        fs::metadata(directory.join(path))
            .expect("the file")
            .permissions()
            .mode()
            & 0o111
            != 0
    };

    let directory = repository("mode-round-trip");
    write(&directory, "run.sh", "#!/bin/sh\necho hi\n");
    write(&directory, "notes.md", "prose\n");
    fs::set_permissions(directory.join("run.sh"), fs::Permissions::from_mode(0o755))
        .expect("a runnable script");

    // Before it is recorded, `status` says so — a fact `record` writes that
    // `status` never mentioned is what decision 0015 exists to prevent.
    out(recorded(&directory, &["record", "-m", "a script"]));
    let shown = out(recorded(&directory, &["show", "head"]));
    assert!(shown.contains("mode "), "{shown}");
    assert!(shown.contains("executable"), "{shown}");
    assert!(shown.starts_with("historica"), "{shown}");

    // A store gains the version the day it first holds a document that needs
    // one, and not before.
    let header = fs::read_to_string(directory.join("history/historica.txt")).expect("the marker");
    assert!(header.starts_with("historica"), "{header}");

    fs::remove_file(directory.join("run.sh")).expect("removing the script");
    let updated = out(recorded(&directory, &["update"]));
    assert!(updated.contains("wrote   run.sh"), "{updated}");
    assert!(
        updated.contains("mode    run.sh  (executable)"),
        "{updated}"
    );
    assert!(executable(&directory, "run.sh"), "the bit came back");
    assert!(
        !executable(&directory, "notes.md"),
        "prose is not a program"
    );

    // The bit alone is a change, and `update` is what puts it back when the
    // bytes were right all along.
    fs::set_permissions(directory.join("run.sh"), fs::Permissions::from_mode(0o644))
        .expect("taking the bit off");
    let status = out(recorded(&directory, &["status"]));
    assert!(status.contains("mode    run.sh"), "{status}");
    let updated = out(recorded(&directory, &["update"]));
    assert!(
        updated.contains("mode    run.sh  (executable)"),
        "{updated}"
    );
    assert!(executable(&directory, "run.sh"), "the bit came back again");

    // And taking it off is an ordinary thing to record.
    fs::set_permissions(directory.join("run.sh"), fs::Permissions::from_mode(0o644))
        .expect("taking the bit off");
    out(recorded(&directory, &["record", "-m", "not a program"]));
    let shown = out(recorded(&directory, &["show", "head"]));
    assert!(shown.contains("mode "), "{shown}");
    assert!(shown.contains("plain"), "{shown}");
    assert!(out(recorded(&directory, &["check"])).contains("nothing to report"));
}

/// A merge lays the merged mode down with the merged content. If it did not,
/// the survey `record --merge` runs would see the folder's stale bit and
/// record a mode change nobody made — undoing, silently, the chmod that was
/// one side of the work being joined.
#[cfg(unix)]
#[test]
fn a_merge_writes_the_mode_it_resolved_into_the_folder() {
    use std::os::unix::fs::PermissionsExt as _;

    let directory = repository("mode-merge");
    write(&directory, "run.sh", "#!/bin/sh\necho one\n");
    out(recorded(&directory, &["record", "-m", "root"]));
    let root = out(recorded(&directory, &["log"]))
        .lines()
        .next()
        .and_then(|line| line.split_whitespace().nth(1))
        .expect("the root")
        .to_owned();

    // One side edits the content; the other makes it runnable.
    write(&directory, "run.sh", "#!/bin/sh\necho two\n");
    out(recorded(&directory, &["record", "-m", "edited"]));
    write(&directory, "run.sh", "#!/bin/sh\necho one\n");
    fs::set_permissions(directory.join("run.sh"), fs::Permissions::from_mode(0o755))
        .expect("a runnable script");
    out(recorded(
        &directory,
        &["record", "--onto", &root, "-m", "made runnable"],
    ));

    // Put the folder back where the edit left it, bit and all, so the merge
    // has something stale to correct.
    fs::set_permissions(directory.join("run.sh"), fs::Permissions::from_mode(0o644))
        .expect("taking the bit off");
    write(&directory, "run.sh", "#!/bin/sh\necho two\n");

    let merging = out(recorded(&directory, &["merge"]));
    assert!(merging.contains("made run.sh executable"), "{merging}");
    assert!(
        fs::metadata(directory.join("run.sh"))
            .expect("the script")
            .permissions()
            .mode()
            & 0o111
            != 0
    );

    let mut arguments: Vec<&str> = merging
        .lines()
        .find(|line| line.contains("historica record"))
        .expect("the printed command")
        .split_whitespace()
        .skip(1)
        .collect();
    arguments.pop();
    arguments.push("joined");
    out(recorded(&directory, &arguments));

    // The merge states the content it resolved and nothing about the mode,
    // because nothing about the mode changed at the merge.
    let shown = out(recorded(&directory, &["show", "head"]));
    assert!(!shown.contains("mode "), "{shown}");
    assert!(out(recorded(&directory, &["status"])).contains("nothing here differs"));
}

/// Divergence is the state `merge` exists for, and in it the store already
/// knows both answers — so naming neither is enough, and the command printed
/// afterwards states every head it joined rather than only the ones typed.
/// Decision 0023, amended: `amend` refuses to rewrite a revision something
/// stands on, and a receive delivers exactly that anyway — one replica rewrote
/// a revision, the other built on it, and a union holds both.
///
/// Merging the two is not merging concurrent work. A rewrite mints its own
/// items for the lines its predecessor already minted, so both sides carry the
/// same lines under different names and every one of them arrives contested —
/// which reads, in the folder, as the other side having retyped work that was
/// already there. So `merge` says whose ground it is standing on before it
/// writes a marker, and `check` says the same thing about the store.
#[test]
fn merging_onto_a_rewrite_nobody_finished_says_so_first() {
    let here = repository("unreached-here");
    write(&here, "note.txt", "one\ntwo\n");
    out(recorded(&here, &["record", "-m", "Start the note"]));

    // A replica taken before the rewrite, which is the whole of how this state
    // is reached: neither side did anything a command would refuse.
    let there = scratch("unreached-there");
    copy_tree(&here, &there);

    write(&here, "note.txt", "one\ntwo\nthree\n");
    out(recorded(
        &here,
        &["amend", "-m", "Start the note, with three"],
    ));
    write(&there, "note.txt", "one\ntwo\nfour\n");
    out(recorded(&there, &["record", "-m", "Add four"]));

    let source = there.to_string_lossy();
    out(recorded(&here, &["receive", &source]));

    // The store contradicts nothing, so this never fails — it says what the
    // rewrite did not reach, which is the thing no other finding covers.
    let checked = stdout(&here, &["check"]);
    assert!(
        checked.contains("Run `historica carry` to repair automatically"),
        "{checked}"
    );
    assert!(checked.contains("no errors"), "{checked}");

    let merged = out(recorded(&here, &["merge"]));
    let (first, _) = merged.split_once('\n').expect("a line before the rest");
    assert!(
        first.contains("which something rewrote"),
        "the warning comes before the markers: {merged}"
    );
    assert!(
        first.contains("rather than work done twice"),
        "and says what the contest below is likely to be: {merged}"
    );

    // The lines the rewrite re-minted do meet, which is what the warning is
    // for: `one` and `two` were typed once and are contested anyway.
    let held = fs::read_to_string(here.join("note.txt")).expect("the merged folder");
    assert_eq!(held.matches("one").count(), 2, "{held}");
    assert_eq!(held.matches("two").count(), 2, "{held}");
}

#[test]
fn merge_joins_the_standing_heads_without_being_told_which() {
    let (directory, _mine, _theirs) =
        diverged("merge-bare", "MINE\ntwo\nthree\n", "one\ntwo\nTHEIRS\n");

    let merging = out(recorded(&directory, &["merge"]));
    assert!(merging.contains("nothing is contested"), "{merging}");
    assert_eq!(
        merging.matches("--merge").count(),
        2,
        "the printed record must name both heads: {merging}"
    );

    // The folder now holds both edits, and the printed command records it.
    let joined = fs::read_to_string(directory.join("f.md")).expect("the merged file");
    assert_eq!(joined, "MINE\ntwo\nTHEIRS\n");

    let recording: Vec<&str> = merging
        .lines()
        .find(|line| line.contains("historica record"))
        .expect("the printed command")
        .split_whitespace()
        .skip(1)
        .collect();
    let mut arguments = recording;
    let last = arguments.pop().expect("the message placeholder");
    assert_eq!(last, "<message>");
    arguments.push("joined");
    out(recorded(&directory, &arguments));

    let log = out(recorded(&directory, &["log"]));
    assert_eq!(log.matches("(head").count(), 1, "{log}");
    assert!(log.contains("merge"), "{log}");
}

/// Naming one head is enough too: the other is the one thing left.
#[test]
fn merge_fills_in_the_head_that_was_not_named() {
    let (directory, mine, _theirs) =
        diverged("merge-one", "MINE\ntwo\nthree\n", "one\ntwo\nTHEIRS\n");

    let merging = out(recorded(&directory, &["merge", &mine]));
    assert_eq!(merging.matches("--merge").count(), 2, "{merging}");
    // The spelling a person typed is said back to them, not a digest they
    // would have to match up against the one they used.
    assert!(merging.contains(&format!("--merge {mine}")), "{merging}");
}

/// One head and nothing named is not a merge, and says so.
#[test]
fn merge_with_one_line_of_work_refuses() {
    let directory = repository("merge-linear");
    write(&directory, "f.md", "one\n");
    out(recorded(&directory, &["record", "-m", "root"]));

    let refused = String::from_utf8_lossy(&recorded(&directory, &["merge"]).stderr).into_owned();
    assert!(refused.contains("two lines of work"), "{refused}");
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

/// The command `merge` prints has to be one that records.
///
/// A path two files claim is settled by `--at` and by nothing else, so the
/// command printed without one refuses the moment it is typed — which is
/// exactly the state a person reaches by following the instructions. This
/// runs what was printed, verbatim.
#[test]
fn the_command_a_merge_prints_records_the_path_two_files_claim() {
    let directory = repository("merge-prints-at");
    write(&directory, "root.md", "a\n");
    out(recorded(&directory, &["record", "-m", "root"]));
    let root = head_of(&directory);

    write(&directory, "notes.md", "mine\n");
    out(recorded(&directory, &["record", "-m", "mine"]));
    fs::remove_file(directory.join("notes.md")).expect("removing it");
    write(&directory, "notes.md", "theirs\n");
    out(recorded(
        &directory,
        &["record", "--onto", &root, "-m", "theirs"],
    ));

    let printed = out(recorded(&directory, &["merge"]));
    assert!(printed.contains("--at"), "{printed}");

    // The second file is written beside the first under a name Windows will
    // accept and an editor will still open: no colon, and the marker before
    // the extension rather than after it.
    let beside: Vec<PathBuf> = fs::read_dir(&directory)
        .expect("the folder")
        .filter_map(|entry| entry.ok().map(|entry| entry.path()))
        .filter(|path| {
            path.file_name()
                .and_then(|name| name.to_str())
                .is_some_and(|name| name.contains("historica"))
        })
        .collect();
    let beside = match beside.as_slice() {
        [only] => only.file_name().and_then(|n| n.to_str()).expect("a name"),
        other => panic!("one file beside the path, not {other:?}"),
    };
    assert!(!beside.contains(':'), "no colon in `{beside}`");
    assert!(beside.ends_with(".md"), "still a .md file: `{beside}`");

    // Everything after `historica ` on the printed line, run as it stands.
    let line = printed
        .lines()
        .find(|line| line.trim_start().starts_with("historica record"))
        .expect("the command it printed");
    let arguments = shell_words(line.trim().trim_start_matches("historica "));
    let arguments: Vec<&str> = arguments
        .iter()
        .map(String::as_str)
        .map(|argument| {
            if argument == "<message>" {
                "Join them"
            } else {
                argument
            }
        })
        .collect();
    let joined = out(recorded(&directory, &arguments));
    assert!(joined.contains("joins 2 lines of work"), "{joined}");

    // Both files survive the merge, under the two paths the command named.
    let files = out(recorded(&directory, &["files", &head_of(&directory)]));
    assert!(files.contains("notes.md"), "{files}");
    assert!(files.contains(beside), "{files}");
}

/// Split a printed command the way a shell would, honouring double quotes.
///
/// A rendered path has a space in it by construction, so the command names it
/// quoted; a test that split on whitespace would be testing something no
/// person types.
fn shell_words(line: &str) -> Vec<String> {
    let mut words = Vec::new();
    let mut word = String::new();
    let mut quoted = false;
    let mut any = false;
    for character in line.chars() {
        match character {
            '"' => {
                quoted = !quoted;
                any = true;
            }
            character if character.is_whitespace() && !quoted => {
                if any {
                    words.push(std::mem::take(&mut word));
                    any = false;
                }
            }
            character => {
                word.push(character);
                any = true;
            }
        }
    }
    if any {
        words.push(word);
    }
    words
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
    let filed: Vec<String> = walk_names(&directory.join("history/revisions"))
        .into_iter()
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

    // Decision 0059: rewriting the first would have to say what its content
    // is, and the folder states the head's content and can state nothing
    // else — so the act available is a reword, and the refusal names it.
    let standing = refused(&directory, &["amend", &first]);
    assert!(
        standing.contains("the act available is a reword"),
        "{standing}"
    );
    assert!(standing.contains("give -m"), "{standing}");

    // A rename is a fact about the folder, and a reword has no folder in it.
    let renaming = refused(
        &directory,
        &[
            "amend",
            &first,
            "-m",
            "First",
            "--move",
            "notes.md=other.md",
        ],
    );
    assert!(renaming.contains("is a reword"), "{renaming}");

    // Amending the head is allowed, and amending what it replaced is not:
    // superseding one revision twice is a divergence nobody asked for.
    let second = head_of(&directory);
    write(&directory, "notes.md", "three\n");
    out(recorded(&directory, &["amend"]));
    let twice = refused(&directory, &["amend", &second]);
    assert!(twice.contains("already been rewritten"), "{twice}");
    assert!(twice.contains(&head_of(&directory)), "{twice}");
}

/// Decision 0059: a revision work stands on can have its message fixed, and
/// nothing else. No base moves, so the stack re-digests and not one operation
/// document is written — which is the whole of what "verbatim" means here.
#[test]
fn a_middle_revision_can_be_reworded_and_the_stack_carries_verbatim() {
    let directory = repository("amend-reword");
    write(&directory, "notes.md", "one\n");
    out(recorded(&directory, &["record", "-m", "Frist"]));
    let first = head_of(&directory);
    write(&directory, "notes.md", "one\ntwo\n");
    out(recorded(&directory, &["record", "-m", "Second"]));
    write(&directory, "notes.md", "one\ntwo\nthree\n");
    out(recorded(&directory, &["record", "-m", "Third"]));

    let before = operation_documents(&directory);
    let said = out(recorded(&directory, &["amend", &first, "-m", "First"]));
    assert!(said.contains("carried"), "{said}");
    assert_eq!(
        said.lines()
            .filter(|line| line.starts_with("carried "))
            .count(),
        2,
        "both descendants are part of the same event: {said}"
    );

    // The promise: a reword names the same operation documents, so the store
    // gains none.
    assert_eq!(
        before,
        operation_documents(&directory),
        "a reword writes no operations"
    );

    // From the head, which is the carried stack: the typo is not in it, and
    // the revision it superseded is still in the store as the undo.
    let log = out(recorded(&directory, &["log", "head"]));
    assert!(log.contains("First"), "{log}");
    assert!(
        !log.contains("Frist"),
        "the typo is behind a rewrite: {log}"
    );
    assert!(
        out(recorded(&directory, &["log"])).contains("Frist"),
        "and the revision that held it is still here"
    );
    assert_eq!(
        out(recorded(&directory, &["cat", "head", "notes.md"])),
        "one\ntwo\nthree\n",
        "carrying restates the work, it does not change it"
    );
    let checked = out(recorded(&directory, &["check"]));
    assert!(checked.contains("nothing to report"), "{checked}");
}

/// Decision 0059: `--only` abandons the one revision and carries what stood
/// on it onto the tombstone. The abandoned work leaves the ancestry; the work
/// above it stays, restated against a base the abandonment moved.
#[test]
fn abandoning_only_one_revision_carries_what_stood_on_it() {
    let directory = repository("abandon-only");
    write(&directory, "a.txt", "a\n");
    out(recorded(&directory, &["record", "-m", "First"]));
    write(&directory, "b.txt", "b\n");
    out(recorded(&directory, &["record", "-m", "Second"]));
    let second = head_of(&directory);
    write(&directory, "c.txt", "c\n");
    out(recorded(&directory, &["record", "-m", "Third"]));

    // The unflagged sentence is untouched: it still takes the run.
    let sweeping = out(recorded(
        &directory,
        &["abandon", &second, "-m", "x", "--dry-run"],
    ));
    assert_eq!(
        sweeping
            .lines()
            .filter(|line| line.starts_with("would abandon"))
            .count(),
        2,
        "without --only, this revision and everything standing on it: {sweeping}"
    );

    let said = out(recorded(
        &directory,
        &["abandon", &second, "--only", "-m", "Not needed"],
    ));
    assert_eq!(
        said.lines()
            .filter(|line| line.starts_with("abandoned "))
            .count(),
        1,
        "--only abandons the one: {said}"
    );
    assert!(
        said.contains("carried"),
        "and carries what stood on it: {said}"
    );

    let files = out(recorded(&directory, &["files", "head"]));
    assert!(
        !files.contains("b.txt"),
        "the abandoned work is gone: {files}"
    );
    assert!(files.contains("a.txt"), "{files}");
    assert!(
        files.contains("c.txt"),
        "the work above it survives: {files}"
    );
    let checked = out(recorded(&directory, &["check"]));
    assert!(checked.contains("nothing to report"), "{checked}");
}

/// Decision 0059: a descendant that edited what the abandoned revision did is
/// a contested span, and the refusal leaves the recorded history exactly as
/// it found it — the plan is computed whole before anything is written.
#[test]
fn a_contested_abandonment_refuses_with_the_history_untouched() {
    let directory = repository("abandon-contested");
    write(&directory, "f.txt", "one\ntwo\nthree\n");
    out(recorded(&directory, &["record", "-m", "First"]));
    write(&directory, "f.txt", "one\nTWO\nthree\n");
    out(recorded(&directory, &["record", "-m", "Second"]));
    let second = head_of(&directory);
    write(&directory, "f.txt", "one\nTWO!\nthree\n");
    out(recorded(&directory, &["record", "-m", "Third"]));

    let before = recorded_history(&directory);
    let refusal = refused(&directory, &["abandon", &second, "--only", "-m", "Gone"]);
    assert!(refusal.contains("regions"), "a contested span: {refusal}");
    assert!(refusal.contains("nothing was written"), "{refusal}");
    assert_eq!(
        before,
        recorded_history(&directory),
        "a refused plan writes no revision and no operation"
    );
}

/// Decision 0059's authored move: the same restating, with a person deciding
/// where. The revision named is stamped from the clock; the stack above it
/// derives from that, so an amendment and the carries it forces read as one
/// event.
#[test]
fn work_can_be_restated_against_a_parent_a_person_names() {
    let directory = repository("carry-onto");
    write(&directory, "base.txt", "base\n");
    out(recorded(&directory, &["record", "-m", "Base"]));
    let base = head_of(&directory);
    write(&directory, "a.txt", "a\n");
    out(recorded(&directory, &["record", "-m", "A"]));
    write(&directory, "b.txt", "b\n");
    out(recorded(&directory, &["record", "-m", "B"]));
    let b = head_of(&directory);
    write(&directory, "c.txt", "c\n");
    out(recorded(&directory, &["record", "-m", "C"]));

    // Onto something standing on what would move: the result would stand on
    // a revision the act supersedes, which is the state `carry` repairs.
    let inward = refused(&directory, &["carry", &b, "--onto", &head_of(&directory)]);
    assert!(inward.contains("supersedes"), "{inward}");

    let said = out(recorded(&directory, &["carry", &b, "--onto", &base]));
    assert_eq!(
        said.lines()
            .filter(|line| line.starts_with("carried "))
            .count(),
        2,
        "B moves and C follows it: {said}"
    );

    let files = out(recorded(&directory, &["files", "head"]));
    assert!(
        !files.contains("a.txt"),
        "A is no longer beneath this: {files}"
    );
    assert!(
        files.contains("b.txt") && files.contains("c.txt"),
        "{files}"
    );
    assert!(files.contains("base.txt"), "{files}");
    let checked = out(recorded(&directory, &["check"]));
    assert!(checked.contains("nothing to report"), "{checked}");
}

/// Decision 0059: `--onto` is a decision about one piece of work, a merge's
/// parents' agreement is not something to guess at, and a revision already
/// standing where it was asked to stand has nothing to restate.
#[test]
fn the_moves_that_are_not_a_persons_to_make_are_refused() {
    let directory = repository("carry-onto-refusals");
    write(&directory, "base.txt", "base\n");
    out(recorded(&directory, &["record", "-m", "Base"]));
    let base = head_of(&directory);
    write(&directory, "a.txt", "a\n");
    out(recorded(&directory, &["record", "-m", "A"]));
    let a = head_of(&directory);

    let there = refused(&directory, &["carry", &a, "--onto", &base]);
    assert!(there.contains("already stands on"), "{there}");

    let sweeping = refused(&directory, &["carry", "--onto", &base]);
    assert!(sweeping.contains("wants the work to move"), "{sweeping}");

    let root = refused(&directory, &["carry", &base, "--onto", &a]);
    assert!(root.contains("where this history starts"), "{root}");
}

/// Every recorded file, with its bytes: `revisions/` and `operations/`, which
/// is the history. `cache/` is left out because it is nobody's (decision
/// 0035) and every command that reads the store may rewrite it.
fn recorded_history(directory: &Path) -> Vec<(String, Vec<u8>)> {
    let mut found: Vec<(String, Vec<u8>)> = Vec::new();
    let history = directory.join("history");
    let mut looking = vec![history.join("revisions"), history.join("operations")];
    while let Some(at) = looking.pop() {
        let Ok(entries) = fs::read_dir(&at) else {
            continue;
        };
        for entry in entries.flatten() {
            let path = entry.path();
            if path.is_dir() {
                looking.push(path);
            } else {
                let name = path.strip_prefix(&history).unwrap_or(&path);
                found.push((
                    name.to_string_lossy().into_owned(),
                    fs::read(&path).expect("a file just listed"),
                ));
            }
        }
    }
    found.sort();
    found
}

/// Every file under `history/operations/`, by name.
fn operation_documents(directory: &Path) -> Vec<String> {
    let mut found: Vec<String> = Vec::new();
    let mut looking = vec![directory.join("history").join("operations")];
    while let Some(at) = looking.pop() {
        let Ok(entries) = fs::read_dir(&at) else {
            continue;
        };
        for entry in entries.flatten() {
            let path = entry.path();
            if path.is_dir() {
                looking.push(path);
            } else {
                found.push(entry.file_name().to_string_lossy().into_owned());
            }
        }
    }
    found.sort();
    found
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

// ---------------------------------------------------------------------------
// Decision 0040: a file can be a link

/// Where a link points, read rather than followed.
#[cfg(unix)]
fn points_at(directory: &Path, path: &str) -> String {
    fs::read_link(directory.join(path))
        .expect("a symbolic link")
        .to_str()
        .expect("a UTF-8 target")
        .to_owned()
}

#[cfg(unix)]
fn link(directory: &Path, at: &str, target: &str) {
    let file = directory.join(at);
    if let Some(parent) = file.parent() {
        fs::create_dir_all(parent).expect("a directory");
    }
    let _ = fs::remove_file(&file);
    std::os::unix::fs::symlink(target, file).expect("a symlink");
}

/// The store beside a repository, as an argument.
fn history_of(directory: &Path) -> String {
    directory
        .join("history")
        .to_str()
        .expect("a path")
        .to_owned()
}

/// The digest of the newest revision, as `log` prints it.
fn head_digest(directory: &Path) -> String {
    out(recorded(directory, &["log", "--limit", "1"]))
        .lines()
        .next()
        .expect("a head")
        .split_whitespace()
        .nth(1)
        .expect("a digest")
        .to_owned()
}

/// Every current head, as `log` marks them.
fn heads_of(directory: &Path) -> Vec<String> {
    out(recorded(directory, &["log"]))
        .lines()
        .filter(|line| line.contains("(head"))
        .filter_map(|line| line.split_whitespace().nth(1).map(str::to_owned))
        .collect()
}

/// The two spellings, chosen by resolution and nothing else.
#[test]
#[cfg(unix)]
fn a_link_inside_is_recorded_as_a_file_and_one_outside_as_a_string() {
    let directory = repository("link-two-spellings");
    write(&directory, "2026/july.md", "July\n");
    link(&directory, "current", "2026/july.md");
    link(&directory, "config", "/etc/journal");

    let status = out(recorded(&directory, &["status"]));
    assert!(status.contains("added   current"), "{status}");
    assert!(status.contains("added   config"), "{status}");

    out(recorded(&directory, &["record", "-m", "The journal"]));
    let shown = out(recorded(&directory, &["show", "head"]));
    // One resolves to a file this history holds, and is that file.
    assert!(shown.contains(" file:"), "{shown}");
    // The other is a machine, and is the string a person wrote.
    assert!(shown.contains("/etc/journal"), "{shown}");
    // Only a document with a link in it claims version 5.
    assert!(shown.starts_with("historica\n"), "{shown}");

    // And recording again states nothing: the round trip is stable.
    assert!(
        refused(&directory, &["record", "-m", "Again"]).contains("would mean nothing"),
        "recording what the folder already says states nothing"
    );
}

/// The point of the reference: the link follows its target through a rename,
/// which is the case every path-spelled symlink gets wrong.
#[test]
#[cfg(unix)]
fn a_reference_follows_its_target_through_a_rename() {
    let directory = repository("link-follows");
    write(&directory, "2026/july.md", "July\n");
    link(&directory, "current", "2026/july.md");
    out(recorded(&directory, &["record", "-m", "The journal"]));

    // The rename, stated as decision 0011 requires. The link on disk is
    // pointed at the new name in the same breath, which is what a person who
    // renamed the file by hand would do.
    fs::rename(directory.join("2026/july.md"), directory.join("2026/07.md")).expect("a rename");
    link(&directory, "current", "2026/07.md");
    out(recorded(
        &directory,
        &[
            "record",
            "-m",
            "Shorten it",
            "--move",
            "2026/july.md=2026/07.md",
        ],
    ));

    // The rename did not restate the link: a reference is to the identity.
    let shown = out(recorded(&directory, &["show", "head"]));
    assert!(!shown.contains("link "), "{shown}");

    // A second folder catches up, and the link it is given points at where the
    // file is now rather than at where it was.
    let elsewhere = scratch("link-follows-elsewhere");
    assert!(run(&elsewhere, &["init"]).status.success());
    out(recorded(&elsewhere, &["receive", &history_of(&directory)]));
    let said = out(recorded(&elsewhere, &["update"]));
    assert!(said.contains("linked  current"), "{said}");
    assert_eq!(points_at(&elsewhere, "current"), "2026/07.md");

    // And the folder now holds the head, so recording it states nothing.
    assert!(
        refused(&elsewhere, &["record", "-m", "Again"]).contains("would mean nothing"),
        "recording what `update` wrote states nothing"
    );
}

/// A retarget is a `link` line and nothing else, and `diff` says so on one
/// line, with the path a `file:` target resolves to beside the identity.
#[test]
#[cfg(unix)]
fn a_retarget_is_one_fact_and_reads_as_one_line() {
    let directory = repository("link-retarget");
    write(&directory, "2026/july.md", "July\n");
    write(&directory, "2026/august.md", "August\n");
    link(&directory, "current", "2026/july.md");
    out(recorded(&directory, &["record", "-m", "The journal"]));

    link(&directory, "current", "2026/august.md");
    let seen = out(recorded(&directory, &["diff"]));
    assert!(seen.contains("link current 2026/july.md (file:"), "{seen}");
    assert!(seen.contains("-> 2026/august.md"), "{seen}");

    let status = out(recorded(&directory, &["status"]));
    assert!(status.contains("link    current"), "{status}");

    let said = out(recorded(&directory, &["record", "-m", "Point at August"]));
    assert!(said.contains("link    current"), "{said}");
    let logged = out(recorded(&directory, &["log", "--limit", "1"]));
    assert!(logged.contains("link 1"), "{logged}");
}

/// A verbatim target that leaves the folder round trips as itself.
#[test]
#[cfg(unix)]
fn a_link_out_of_the_folder_keeps_the_string_a_person_wrote() {
    let directory = repository("link-outside");
    write(&directory, "notes.md", "notes\n");
    link(&directory, "deep/away", "../../elsewhere/thing");
    out(recorded(&directory, &["record", "-m", "A link outward"]));

    let elsewhere = scratch("link-outside-elsewhere");
    assert!(run(&elsewhere, &["init"]).status.success());
    out(recorded(&elsewhere, &["receive", &history_of(&directory)]));
    out(recorded(&elsewhere, &["update"]));
    assert_eq!(points_at(&elsewhere, "deep/away"), "../../elsewhere/thing");
    assert!(
        refused(&elsewhere, &["record", "-m", "Again"]).contains("would mean nothing"),
        "recording what `update` wrote states nothing"
    );
}

/// `cat` on a link says where it points rather than inventing bytes.
#[test]
#[cfg(unix)]
fn cat_on_a_link_names_the_target() {
    let directory = repository("link-cat");
    write(&directory, "2026/july.md", "July\n");
    link(&directory, "current", "2026/july.md");
    out(recorded(&directory, &["record", "-m", "The journal"]));

    let said = refused(&directory, &["cat", "head", "current"]);
    assert!(said.contains("is a link to"), "{said}");
    assert!(said.contains("2026/july.md"), "{said}");
}

/// Taking the target out restates the link as the string the folder holds, in
/// the same revision as the drop.
#[test]
#[cfg(unix)]
fn dropping_a_target_restates_the_link_verbatim() {
    let directory = repository("link-dangling");
    write(&directory, "2026/july.md", "July\n");
    link(&directory, "current", "2026/july.md");
    out(recorded(&directory, &["record", "-m", "The journal"]));

    fs::remove_file(directory.join("2026/july.md")).expect("taking the month out");
    let said = out(recorded(&directory, &["record", "-m", "Take July out"]));
    assert!(said.contains("dropped 2026/july.md"), "{said}");
    assert!(said.contains("link    current"), "{said}");

    let shown = out(recorded(&directory, &["show", "head"]));
    assert!(shown.contains("link "), "{shown}");
    assert!(!shown.contains("file:"), "{shown}: nothing to point at");

    // The store reads, which is the whole of what the rule protects.
    let checked = out(recorded(&directory, &["check"]));
    assert!(checked.contains("nothing to report"), "{checked}");
}

/// A restriction that names the target and not the link is the one way to ask
/// for a drop the restatement cannot reach, and it is refused by name.
#[test]
#[cfg(unix)]
fn a_drop_that_would_dangle_a_link_nobody_is_looking_at_is_refused() {
    let directory = repository("link-dangling-narrow");
    write(&directory, "2026/july.md", "July\n");
    link(&directory, "current", "2026/july.md");
    out(recorded(&directory, &["record", "-m", "The journal"]));

    fs::remove_file(directory.join("2026/july.md")).expect("taking the month out");
    let said = refused(&directory, &["record", "-m", "Just the month", "2026"]);
    assert!(said.contains("current"), "{said}");
    assert!(said.contains("2026/july.md"), "{said}");
}

/// A path that changed between a link and a file is a `drop` and an `add`.
#[test]
#[cfg(unix)]
fn a_link_that_becomes_a_file_is_a_drop_and_an_add() {
    let directory = repository("link-kind-change");
    write(&directory, "2026/july.md", "July\n");
    link(&directory, "current", "2026/july.md");
    out(recorded(&directory, &["record", "-m", "The journal"]));

    fs::remove_file(directory.join("current")).expect("the link");
    write(&directory, "current", "July, copied\n");
    let said = out(recorded(&directory, &["record", "-m", "Make it real"]));
    assert!(said.contains("added   current"), "{said}");
    assert!(said.contains("dropped current"), "{said}");

    assert_eq!(
        out(recorded(&directory, &["cat", "head", "current"])),
        "July, copied\n"
    );
}

/// Two folders retarget one link, and the merge decides by digest and says so.
#[test]
#[cfg(unix)]
fn concurrent_retargets_resolve_by_digest_and_are_reported() {
    let directory = repository("link-merge-target");
    write(&directory, "a.md", "a\n");
    write(&directory, "b.md", "b\n");
    write(&directory, "c.md", "c\n");
    link(&directory, "current", "a.md");
    out(recorded(&directory, &["record", "-m", "The journal"]));
    let root = head_digest(&directory);

    link(&directory, "current", "b.md");
    out(recorded(&directory, &["record", "-m", "Point at b"]));

    // The other side, recorded against the same root.
    link(&directory, "current", "c.md");
    out(recorded(
        &directory,
        &["record", "-m", "Point at c", "--onto", &root],
    ));

    let merged = out(recorded(&directory, &["merge"]));
    assert!(merged.contains("points at"), "{merged}");
    assert!(merged.contains("which is the lower digest of"), "{merged}");
    // The folder was laid out to match, so joining the work does not record a
    // retarget nobody made.
    let heads = heads_of(&directory);
    out(recorded(
        &directory,
        &[
            "record", "--merge", &heads[0], "--merge", &heads[1], "-m", "Join",
        ],
    ));
    assert!(
        refused(&directory, &["record", "-m", "Again"]).contains("would mean nothing"),
        "the merge left the folder holding what it recorded"
    );
}

/// Destruction yields to reference: a `drop` concurrent with a link naming the
/// file it drops loses, and a person is told.
#[test]
#[cfg(unix)]
fn a_drop_loses_to_a_concurrent_link_that_names_it() {
    let directory = repository("link-merge-drop");
    write(&directory, "a.md", "a\n");
    write(&directory, "b.md", "b\n");
    link(&directory, "current", "b.md");
    out(recorded(&directory, &["record", "-m", "The journal"]));
    let root = head_digest(&directory);

    // One side points the link at `a.md`.
    link(&directory, "current", "a.md");
    out(recorded(&directory, &["record", "-m", "Point at a"]));

    // The other drops `a.md`, having never seen that.
    link(&directory, "current", "b.md");
    fs::remove_file(directory.join("a.md")).expect("taking a out");
    out(recorded(
        &directory,
        &["record", "-m", "Drop a", "--onto", &root],
    ));

    let merged = out(recorded(&directory, &["merge"]));
    assert!(merged.contains("still points at it"), "{merged}");
    // The merge lays the folder out as the joined tree, and the file that was
    // dropped is in it: destruction yields to reference.
    assert!(
        directory.join("a.md").is_file(),
        "{merged}: the file stayed"
    );
}

/// Naming one link is a record about one link.
#[test]
#[cfg(unix)]
fn a_record_can_name_a_link_and_nothing_else() {
    let directory = repository("link-named");
    write(&directory, "a.md", "a\n");
    write(&directory, "b.md", "b\n");
    link(&directory, "current", "a.md");
    out(recorded(&directory, &["record", "-m", "The journal"]));

    write(&directory, "a.md", "a, edited\n");
    link(&directory, "current", "b.md");
    let said = out(recorded(
        &directory,
        &["record", "-m", "Just the link", "current"],
    ));
    assert!(said.contains("link    current"), "{said}");
    assert!(!said.contains("a.md"), "{said}: the rest was not looked at");
}

/// The same rename, with nobody touching the link — which is what a person who
/// runs `mv` actually has, since `mv` never rewrites the links pointing at what
/// it moved. The stale string is what `update` last wrote, so it is not an
/// observation of anything, and the record states no `link` line at all.
#[test]
#[cfg(unix)]
fn a_move_of_the_target_alone_states_nothing_about_the_link() {
    let directory = repository("link-target-moves");
    write(&directory, "2026/july.md", "July\n");
    link(&directory, "current", "2026/july.md");
    out(recorded(&directory, &["record", "-m", "The journal"]));

    fs::rename(directory.join("2026/july.md"), directory.join("2026/07.md")).expect("a rename");
    // The link still spells `2026/july.md`, which the new tree does not hold.
    assert_eq!(points_at(&directory, "current"), "2026/july.md");
    let said = out(recorded(
        &directory,
        &[
            "record",
            "-m",
            "Shorten it",
            "--move",
            "2026/july.md=2026/07.md",
        ],
    ));
    assert!(said.contains("moved"), "{said}");
    assert!(
        !said.contains("link    current"),
        "{said}: nobody retargeted"
    );

    // Nothing was stated about the link, so the reference stands — and `cat`
    // reads it as the file at its new path rather than as a dead string.
    let shown = out(recorded(&directory, &["show", "head"]));
    assert!(!shown.contains("link "), "{shown}");
    let said = refused(&directory, &["cat", "head", "current"]);
    assert!(said.contains("2026/07.md"), "{said}");

    // The folder is briefly stale, and 0030's command is what fixes it: the
    // link is rewritten to where the file is now, and said out loud.
    let said = out(recorded(&directory, &["update"]));
    assert!(said.contains("linked  current"), "{said}");
    assert!(said.contains("2026/07.md"), "{said}");
    assert_eq!(points_at(&directory, "current"), "2026/07.md");

    // And what `update` wrote records as nothing, which closes the trip.
    assert!(
        refused(&directory, &["record", "-m", "Again"]).contains("would mean nothing"),
        "recording what `update` wrote states nothing"
    );
}

/// The other half of the rule: a person who rewrites the string said
/// something, and it is recorded.
#[test]
#[cfg(unix)]
fn a_retarget_beside_a_move_of_the_target_is_still_recorded() {
    let directory = repository("link-retarget-and-move");
    write(&directory, "2026/july.md", "July\n");
    write(&directory, "2026/august.md", "August\n");
    link(&directory, "current", "2026/july.md");
    out(recorded(&directory, &["record", "-m", "The journal"]));

    // July moves, and the person points the link at August in the same breath.
    fs::rename(directory.join("2026/july.md"), directory.join("2026/07.md")).expect("a rename");
    link(&directory, "current", "2026/august.md");
    let said = out(recorded(
        &directory,
        &[
            "record",
            "-m",
            "August now",
            "--move",
            "2026/july.md=2026/07.md",
        ],
    ));
    assert!(said.contains("link    current"), "{said}");

    let shown = out(recorded(&directory, &["show", "head"]));
    assert!(shown.contains("link "), "{shown}");
    let said = refused(&directory, &["cat", "head", "current"]);
    assert!(said.contains("2026/august.md"), "{said}");
}

/// The drop restatement takes precedence over the unchanged string: the folder
/// holds exactly what `update` wrote, and the record restates it verbatim
/// anyway, because the fact it stood for is one the new tree cannot hold.
#[test]
#[cfg(unix)]
fn dropping_the_target_restates_a_link_nobody_touched() {
    let directory = repository("link-dangling-untouched");
    write(&directory, "2026/july.md", "July\n");
    link(&directory, "current", "2026/july.md");
    out(recorded(&directory, &["record", "-m", "The journal"]));

    // Not one byte of the link changed; the file it names went.
    fs::remove_file(directory.join("2026/july.md")).expect("taking the month out");
    assert_eq!(points_at(&directory, "current"), "2026/july.md");
    let said = out(recorded(&directory, &["record", "-m", "Take July out"]));
    assert!(said.contains("dropped 2026/july.md"), "{said}");
    assert!(said.contains("link    current"), "{said}");

    let shown = out(recorded(&directory, &["show", "head"]));
    assert!(shown.contains("link "), "{shown}");
    assert!(!shown.contains("file:"), "{shown}: nothing to point at");
    let checked = out(recorded(&directory, &["check"]));
    assert!(checked.contains("nothing to report"), "{checked}");
}

/// An amendment works the folder out again against the amended revision's
/// parents, where the target still sits at its old path — so it inherits the
/// same rule, and does not turn the reference it is rewriting into a string.
#[test]
#[cfg(unix)]
fn amending_a_move_of_the_target_leaves_the_reference_alone() {
    let directory = repository("link-amend-move");
    write(&directory, "2026/july.md", "July\n");
    link(&directory, "current", "2026/july.md");
    out(recorded(&directory, &["record", "-m", "The journal"]));

    fs::rename(directory.join("2026/july.md"), directory.join("2026/07.md")).expect("a rename");
    out(recorded(
        &directory,
        &[
            "record",
            "-m",
            "Shorten it",
            "--move",
            "2026/july.md=2026/07.md",
        ],
    ));

    // The folder is still stale, exactly as the record left it, and the
    // amendment surveys against the grandparent, where July is still July and
    // the string the folder holds is the one that was written for it.
    assert_eq!(points_at(&directory, "current"), "2026/july.md");
    let said = out(recorded(
        &directory,
        &["amend", "-m", "Shorten it, better said"],
    ));
    assert!(
        !said.contains("link    current"),
        "{said}: nobody retargeted"
    );

    let shown = out(recorded(&directory, &["show", "head"]));
    assert!(!shown.contains("link "), "{shown}");
    let said = refused(&directory, &["cat", "head", "current"]);
    assert!(said.contains("2026/07.md"), "{said}");
}

/// A chain whose arithmetic does not add up is still reported.
///
/// A history with no merge in it is replayed forward rather than walked, and
/// the walk is what used to notice this. The document here quotes a line its
/// parent does not hold, with every digest around it recomputed so the store
/// is self-consistent about everything except the one fact that matters.
#[test]
fn a_chain_whose_delete_quotes_the_wrong_line_is_reported() {
    use historica::format::digest;

    let directory = repository("chain-disagrees");
    fs::write(directory.join("a.txt"), "alpha\nbeta\ngamma\n").expect("a file");
    out(recorded(&directory, &["record", "-m", "one"]));
    fs::write(directory.join("a.txt"), "alpha\nBETA\ngamma\n").expect("a file");
    out(recorded(&directory, &["record", "-m", "two"]));

    // The head is the revision that names a parent, and the document it
    // names is found the way the store finds one: by hashing, not by name.
    let revisions = files_under(&directory.join("history/revisions"));
    let head = revisions
        .iter()
        .find(|path| {
            String::from_utf8_lossy(&fs::read(path).expect("a revision")).contains("\nparent ")
        })
        .expect("a revision with a parent");
    let text = fs::read_to_string(head).expect("a revision");
    let named: String = text
        .lines()
        .find_map(|line| line.strip_prefix("edit "))
        .and_then(|rest| rest.split_once(' '))
        .map(|(_, id)| id.to_owned())
        .expect("an edit line");

    let operations = files_under(&directory.join("history/operations"));
    let document = operations
        .iter()
        .find(|path| digest(&fs::read(path).expect("a document")).to_string() == named)
        .expect("the document the head names")
        .clone();

    // One quoted line, replaced by a line the parent never held. The counts,
    // the positions and the stated result are all left alone: what is wrong
    // is only what the delete claims to be deleting.
    let stored = fs::read_to_string(&document).expect("a document");
    let corrupted = stored.replace("\n-beta\n", "\n-never this\n");
    assert_ne!(corrupted, stored, "the document quoted the line it deleted");
    let renamed = digest(corrupted.as_bytes()).to_string();
    fs::remove_file(&document).expect("the old document");
    fs::write(
        document.with_file_name(format!("{renamed}.ops.txt")),
        &corrupted,
    )
    .expect("the corrupted document");
    // And the revision naming it, which nothing stands on, so nothing else
    // has to move with it.
    fs::remove_file(head).expect("the old revision");
    let rewritten = text.replace(&named, &renamed);
    // Named by its own digest, because a filename that claims one is held to
    // it — and the fault under test here is not a name.
    let stem = digest(rewritten.as_bytes()).to_string();
    fs::write(head.with_file_name(format!("{stem}.rev.txt")), &rewritten)
        .expect("the rewritten revision");

    let report = run(&directory, &["check"]);
    let said = String::from_utf8_lossy(&report.stdout).into_owned()
        + &String::from_utf8_lossy(&report.stderr);
    assert!(
        !report.status.success(),
        "a store that disagrees passed: {said}"
    );
    assert!(
        said.contains(
            "the document deletes `never this` at position 1, where the parent holds `beta`"
        ),
        "{said}"
    );
}

/// Every file under a directory, at any depth, for a test doing surgery.
fn files_under(root: &Path) -> Vec<PathBuf> {
    let mut found = Vec::new();
    let Ok(entries) = fs::read_dir(root) else {
        return found;
    };
    for entry in entries.filter_map(Result::ok) {
        let path = entry.path();
        if path.is_dir() {
            found.extend(files_under(&path));
        } else {
            found.push(path);
        }
    }
    found.sort();
    found
}

/// Every file under one store directory, by path relative to it, with its
/// bytes — the whole answer to "did two replicas write the same thing".
fn store_files(directory: &Path, under: &str) -> std::collections::BTreeMap<String, Vec<u8>> {
    let root = directory.join("history").join(under);
    files_under(&root)
        .into_iter()
        .map(|path| {
            let relative = path
                .strip_prefix(&root)
                .expect("a file under the walked root")
                .to_string_lossy()
                .into_owned();
            (relative, fs::read(&path).expect("a readable store file"))
        })
        .collect()
}

/// Decision 0059: the rewrite a receive delivered half of, finished by a
/// command that derives everything from the store. The rewrite touched the
/// first line and the stranded work appended, so the two never meet, and the
/// carried head holds both.
#[test]
fn carry_finishes_a_rewrite_transport_delivered_half_of() {
    let here = repository("carry-finishes");
    write(&here, "note.txt", "one\ntwo\nthree\n");
    out(recorded(&here, &["record", "-m", "Start the note"]));

    let there = scratch("carry-finishes-there");
    copy_tree(&here, &there);

    write(&here, "note.txt", "uno\ntwo\nthree\n");
    out(recorded(
        &here,
        &["amend", "-m", "Start the note, in Spanish"],
    ));
    write(&there, "note.txt", "one\ntwo\nthree\nfour\n");
    out(recorded(&there, &["record", "-m", "Add four"]));

    let source = there.to_string_lossy().into_owned();
    out(recorded(&here, &["receive", &source]));
    let checked = stdout(&here, &["check"]);
    assert!(
        checked.contains("Run `historica carry` to repair automatically"),
        "{checked}"
    );

    let carried = stdout(&here, &["carry"]);
    assert!(carried.contains("carried"), "{carried}");
    assert!(carried.contains("restated note.txt"), "{carried}");

    // The note is gone, and the folder catches up to a head holding both
    // edits: the amendment's first line, the stranded revision's last.
    let checked = stdout(&here, &["check"]);
    assert!(!checked.contains("historica carry"), "{checked}");
    out(recorded(&here, &["update"]));
    let content = fs::read_to_string(here.join("note.txt")).expect("the updated folder");
    assert_eq!(content, "uno\ntwo\nthree\nfour\n");

    // Run again, it finds nothing: the repair is idempotent.
    let again = stdout(&here, &["carry"]);
    assert!(again.contains("nothing to carry"), "{again}");
}

/// Two replicas repairing one history write byte-identical files, under one
/// filename: the carried revision derives everything from the store, so the
/// replica holding the rewrite and the replica holding the descendant end up
/// with one revision rather than two spellings of it.
#[test]
fn two_replicas_carrying_one_stack_write_identical_files() {
    let here = repository("carry-converges");
    write(&here, "note.txt", "one\ntwo\nthree\n");
    out(recorded(&here, &["record", "-m", "Start the note"]));
    let there = scratch("carry-converges-there");
    copy_tree(&here, &there);

    write(&here, "note.txt", "uno\ntwo\nthree\n");
    out(recorded(
        &here,
        &["amend", "-m", "Start the note, in Spanish"],
    ));
    write(&there, "note.txt", "one\ntwo\nthree\nfour\n");
    out(recorded(&there, &["record", "-m", "Add four"]));

    let here_source = here.to_string_lossy().into_owned();
    let there_source = there.to_string_lossy().into_owned();
    out(recorded(&here, &["receive", &there_source]));
    out(recorded(&there, &["receive", &here_source]));

    let here_before = store_files(&here, "revisions");
    let there_before = store_files(&there, "revisions");
    out(recorded(&here, &["carry"]));
    out(recorded(&there, &["carry"]));

    let new = |after: std::collections::BTreeMap<String, Vec<u8>>,
               before: &std::collections::BTreeMap<String, Vec<u8>>| {
        after
            .into_iter()
            .filter(|(name, _)| !before.contains_key(name))
            .collect::<Vec<_>>()
    };
    let here_new = new(store_files(&here, "revisions"), &here_before);
    let there_new = new(store_files(&there, "revisions"), &there_before);
    assert_eq!(here_new.len(), 1, "one carried revision");
    assert_eq!(here_new, there_new);
}

/// A carry whose operations meet the rewrite's refuses whole: resolving
/// concurrent work is a person's, and the store is left exactly as found.
#[test]
fn a_contested_carry_refuses_and_writes_nothing() {
    let here = repository("carry-contested");
    write(&here, "note.txt", "one\ntwo\n");
    out(recorded(&here, &["record", "-m", "Start the note"]));
    let there = scratch("carry-contested-there");
    copy_tree(&here, &there);

    // Both append at the same position, which is a contest to report rather
    // than an order to invent.
    write(&here, "note.txt", "one\ntwo\nthree\n");
    out(recorded(
        &here,
        &["amend", "-m", "Start the note, with three"],
    ));
    write(&there, "note.txt", "one\ntwo\nfour\n");
    out(recorded(&there, &["record", "-m", "Add four"]));

    let source = there.to_string_lossy().into_owned();
    out(recorded(&here, &["receive", &source]));

    let revisions = store_files(&here, "revisions");
    let operations = store_files(&here, "operations");
    let refused = stderr(&here, &["carry"]);
    assert!(refused.contains("by hand"), "{refused}");
    assert_eq!(store_files(&here, "revisions"), revisions);
    assert_eq!(store_files(&here, "operations"), operations);

    // The note stands, because nothing was repaired.
    let checked = stdout(&here, &["check"]);
    assert!(checked.contains("historica carry"), "{checked}");
}

/// A reword moves no content, so the carried stack names the operation
/// documents it already had: nothing is restated, and `operations/` gains
/// nothing.
#[test]
fn a_carry_across_a_reword_is_verbatim() {
    let here = repository("carry-reword");
    write(&here, "note.txt", "one\ntwo\n");
    out(recorded(&here, &["record", "-m", "Start the note"]));
    let there = scratch("carry-reword-there");
    copy_tree(&here, &there);

    out(recorded(&here, &["amend", "-m", "Start the notebook"]));
    write(&there, "note.txt", "one\ntwo\nthree\n");
    out(recorded(&there, &["record", "-m", "Add three"]));

    let source = there.to_string_lossy().into_owned();
    out(recorded(&here, &["receive", &source]));

    let operations = store_files(&here, "operations");
    let carried = stdout(&here, &["carry"]);
    assert!(!carried.contains("restated"), "{carried}");
    assert_eq!(store_files(&here, "operations"), operations);
    let checked = stdout(&here, &["check"]);
    assert!(!checked.contains("historica carry"), "{checked}");
}

/// `carry` with a target wants a revision standing on a rewritten one, and
/// `--dry-run` says what it would do while writing nothing.
#[test]
fn carry_names_its_target_and_dry_run_writes_nothing() {
    let here = repository("carry-target");
    write(&here, "note.txt", "one\ntwo\nthree\n");
    out(recorded(&here, &["record", "-m", "Start the note"]));
    let there = scratch("carry-target-there");
    copy_tree(&here, &there);

    write(&here, "note.txt", "uno\ntwo\nthree\n");
    let amended = out(recorded(
        &here,
        &["amend", "-m", "Start the note, in Spanish"],
    ));
    let rewrite = amended
        .lines()
        .find_map(|line| {
            line.strip_prefix("amended ")
                .and_then(|rest| rest.split(" as ").nth(1))
        })
        .expect("the amendment's digest")
        .to_owned();
    write(&there, "note.txt", "one\ntwo\nthree\nfour\n");
    out(recorded(&there, &["record", "-m", "Add four"]));

    let source = there.to_string_lossy().into_owned();
    out(recorded(&here, &["receive", &source]));

    // The rewrite itself stands on nothing rewritten.
    let refused = stderr(&here, &["carry", &rewrite]);
    assert!(
        refused.contains("does not stand on a rewritten revision"),
        "{refused}"
    );

    let revisions = store_files(&here, "revisions");
    let planned = stdout(&here, &["carry", "--dry-run"]);
    assert!(planned.contains("would carry"), "{planned}");
    assert_eq!(store_files(&here, "revisions"), revisions);
    let checked = stdout(&here, &["check"]);
    assert!(checked.contains("historica carry"), "{checked}");
}
