//! `blame`, exercised as a person exercises it.
//!
//! Decision 0038. The claim under test is the one that separates this from
//! every other tool's blame: attribution is read out of the operations rather
//! than recovered from the bytes, so a line keeps its author through a
//! rename, through a merge that did not touch it, and through a revision that
//! rewrote everything around it.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

fn scratch(test: &str) -> PathBuf {
    let path = Path::new(env!("CARGO_TARGET_TMPDIR")).join(format!("blame-{test}"));
    let _ = fs::remove_dir_all(&path);
    fs::create_dir_all(&path).expect("a scratch directory");
    path
}

fn run(directory: &Path, author: &str, arguments: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_historica"))
        .arg("-C")
        .arg(directory)
        .args(arguments)
        .env("HISTORICA_AUTHOR", author)
        .output()
        .expect("the binary this test crate builds")
}

/// Every command a test does not care about the author of.
const ADA: &str = "Ada Lovelace <ada@example.com>";
/// The second person, for the tests that need two.
const CHARLES: &str = "Charles Babbage <charles@example.com>";

fn out(directory: &Path, arguments: &[&str]) -> String {
    let output = run(directory, ADA, arguments);
    assert!(
        output.status.success(),
        "`{}` failed: {}",
        arguments.join(" "),
        String::from_utf8_lossy(&output.stderr)
    );
    String::from_utf8(output.stdout).expect("printed text")
}

fn write(directory: &Path, path: &str, text: &str) {
    let file = directory.join(path);
    if let Some(parent) = file.parent() {
        fs::create_dir_all(parent).expect("a directory");
    }
    fs::write(file, text).expect("writing a file");
}

fn record(directory: &Path, author: &str, arguments: &[&str]) {
    let output = run(directory, author, arguments);
    assert!(
        output.status.success(),
        "`{}` failed: {}",
        arguments.join(" "),
        String::from_utf8_lossy(&output.stderr)
    );
}

fn repository(test: &str) -> PathBuf {
    let directory = scratch(test);
    assert!(run(&directory, ADA, &["init"]).status.success());
    directory
}

/// Every head, as `log` prints them.
fn heads(directory: &Path) -> Vec<String> {
    out(directory, &["log"])
        .lines()
        .filter(|line| line.contains("(head"))
        .filter_map(|line| line.split_whitespace().nth(1).map(str::to_owned))
        .collect()
}

/// Who each printed line says wrote it, as `(author, text)`.
///
/// The columns are separated by two spaces and padded with more, so a run of
/// two or more is the separator and a single one is content.
fn attributed(rendered: &str) -> Vec<(String, String)> {
    rendered
        .lines()
        .filter(|line| !line.starts_with('\\'))
        .map(|line| {
            let columns: Vec<&str> = line
                .split("  ")
                .map(str::trim)
                .filter(|column| !column.is_empty())
                .collect();
            assert_eq!(
                columns.len(),
                5,
                "`<change>  <author>  <day>  <number>  <text>`: {line}"
            );
            (columns[1].to_owned(), columns[4].to_owned())
        })
        .collect()
}

#[test]
fn each_line_is_attributed_to_the_revision_that_wrote_it() {
    let directory = repository("basic");
    write(&directory, "notes.md", "alpha\nbeta\ngamma\n");
    record(&directory, ADA, &["record", "-m", "the first three"]);
    write(&directory, "notes.md", "alpha\nBETA\ngamma\ndelta\n");
    record(&directory, CHARLES, &["record", "-m", "an edit and an add"]);

    assert_eq!(
        attributed(&out(&directory, &["blame", "head", "notes.md"])),
        vec![
            ("Ada Lovelace".to_owned(), "alpha".to_owned()),
            ("Charles Babbage".to_owned(), "BETA".to_owned()),
            ("Ada Lovelace".to_owned(), "gamma".to_owned()),
            ("Charles Babbage".to_owned(), "delta".to_owned()),
        ]
    );
}

/// 0008 hangs paths off identifiers, so a file is one file for its whole life
/// and the attribution reaches back through every path it has had. Nothing
/// here is a similarity threshold, and nothing asked for `--follow`.
#[test]
fn a_line_keeps_its_author_through_a_rename() {
    let directory = repository("rename");
    write(&directory, "notes.md", "alpha\nbeta\n");
    record(&directory, ADA, &["record", "-m", "base"]);

    fs::remove_file(directory.join("notes.md")).expect("removing it");
    write(&directory, "docs/notes.md", "alpha\nbeta\ngamma\n");
    record(
        &directory,
        CHARLES,
        &[
            "record",
            "--move",
            "notes.md=docs/notes.md",
            "-m",
            "move and extend",
        ],
    );

    assert_eq!(
        attributed(&out(&directory, &["blame", "head", "docs/notes.md"])),
        vec![
            ("Ada Lovelace".to_owned(), "alpha".to_owned()),
            ("Ada Lovelace".to_owned(), "beta".to_owned()),
            ("Charles Babbage".to_owned(), "gamma".to_owned()),
        ]
    );
}

/// The property three-way merge cannot have. Decision 0032 keeps items under
/// their own names rather than restating them, so a merge authors only the
/// lines somebody actually typed into it.
#[test]
fn a_merge_authors_only_what_it_typed() {
    let directory = repository("merge");
    write(&directory, "f.txt", "one\ntwo\nthree\nfour\nfive\n");
    record(&directory, ADA, &["record", "-m", "base"]);
    let base = heads(&directory).pop().expect("one head");

    write(&directory, "f.txt", "ONE\ntwo\nthree\nfour\nfive\n");
    record(&directory, ADA, &["record", "-m", "the top"]);
    write(&directory, "f.txt", "one\ntwo\nthree\nfour\nFIVE\n");
    record(
        &directory,
        CHARLES,
        &["record", "--onto", &base, "-m", "the bottom"],
    );

    let two = heads(&directory);
    assert_eq!(two.len(), 2, "two lines of work");
    // The order a person does it in: `merge` writes the folder, `record`
    // writes it down — so what is recorded is what they were shown.
    record(&directory, ADA, &["merge", &two[0], &two[1]]);
    record(
        &directory,
        "Grace Hopper <grace@example.com>",
        &[
            "record",
            "--merge",
            &two[0],
            "--merge",
            &two[1],
            "-m",
            "join them",
        ],
    );

    let rendered = out(&directory, &["blame", "head", "f.txt"]);
    assert_eq!(
        attributed(&rendered),
        vec![
            ("Ada Lovelace".to_owned(), "ONE".to_owned()),
            ("Ada Lovelace".to_owned(), "two".to_owned()),
            ("Ada Lovelace".to_owned(), "three".to_owned()),
            ("Ada Lovelace".to_owned(), "four".to_owned()),
            ("Charles Babbage".to_owned(), "FIVE".to_owned()),
        ]
    );
    // The revision that joined them wrote none of it, and says so by absence.
    assert!(!rendered.contains("Grace Hopper"), "{rendered}");
}

/// With no target the right side is the folder, exactly as `diff` reads it —
/// and a line the folder has and history does not is marked rather than
/// attributed, because attributing it would attribute unrecorded work.
#[test]
fn the_folder_marks_what_is_not_recorded_yet() {
    let directory = repository("folder");
    write(&directory, "notes.md", "alpha\nbeta\n");
    record(&directory, ADA, &["record", "-m", "base"]);
    write(&directory, "notes.md", "alpha\nbeta\ngamma\n");

    assert_eq!(
        attributed(&out(&directory, &["blame", "notes.md"])),
        vec![
            ("Ada Lovelace".to_owned(), "alpha".to_owned()),
            ("Ada Lovelace".to_owned(), "beta".to_owned()),
            ("(the folder)".to_owned(), "gamma".to_owned()),
        ]
    );

    // A file history has never heard of is every line the folder's own.
    write(&directory, "new.txt", "nobody\n");
    assert_eq!(
        attributed(&out(&directory, &["blame", "new.txt"])),
        vec![("(the folder)".to_owned(), "nobody".to_owned())]
    );
}

/// The other side of reading rather than guessing. A line moved down a file
/// is recorded as a removal and an arrival, so it belongs to whoever moved
/// it — which is what `show` says, what `diff` renders, and what this prints.
/// `-M` and `-C` are the guess that would say otherwise, and there is none.
#[test]
fn a_moved_line_belongs_to_whoever_moved_it() {
    let directory = repository("moved");
    write(&directory, "f.txt", "header\none\ntwo\n");
    record(&directory, ADA, &["record", "-m", "base"]);
    write(&directory, "f.txt", "one\ntwo\nheader\n");
    record(
        &directory,
        CHARLES,
        &["record", "-m", "move the header down"],
    );

    assert_eq!(
        attributed(&out(&directory, &["blame", "head", "f.txt"])),
        vec![
            ("Ada Lovelace".to_owned(), "one".to_owned()),
            ("Ada Lovelace".to_owned(), "two".to_owned()),
            ("Charles Babbage".to_owned(), "header".to_owned()),
        ]
    );
    // And the store says exactly that, in the document `show` prints.
    let stated = out(&directory, &["show", "head", "f.txt"]);
    assert!(stated.contains("delete 0 1"), "{stated}");
    assert!(stated.contains("insert 3"), "{stated}");
}

/// Decision 0014 destroys text and preserves shape, and who wrote a line is
/// shape. A redaction is not an unpersoning.
#[test]
fn a_forgotten_line_still_has_an_author() {
    let directory = repository("forgotten");
    write(&directory, "s.txt", "keep\nsecret\nkeep\n");
    record(&directory, ADA, &["record", "-m", "base"]);
    record(
        &directory,
        ADA,
        &["forget", "head", "s.txt", "--lines", "2"],
    );

    assert_eq!(
        attributed(&out(&directory, &["blame", "head", "s.txt"])),
        vec![
            ("Ada Lovelace".to_owned(), "keep".to_owned()),
            ("Ada Lovelace".to_owned(), "\\ forgotten".to_owned()),
            ("Ada Lovelace".to_owned(), "keep".to_owned()),
        ]
    );
}

/// One argument is a target or a path by 0001's disjoint alphabets, and
/// `--lines` is spelled the way `forget` already spells a span.
#[test]
fn a_span_limits_what_is_printed() {
    let directory = repository("span");
    write(&directory, "notes.md", "one\ntwo\nthree\nfour\n");
    record(&directory, ADA, &["record", "-m", "base"]);

    let rendered = out(
        &directory,
        &["blame", "head", "notes.md", "--lines", "2..3"],
    );
    assert_eq!(
        rendered.lines().count(),
        2,
        "two lines and nothing else: {rendered}"
    );
    assert!(rendered.contains("  2  two"), "{rendered}");
    assert!(rendered.contains("  3  three"), "{rendered}");

    let past = run(
        &directory,
        ADA,
        &["blame", "head", "notes.md", "--lines", "9..10"],
    );
    assert!(!past.status.success());
    assert!(
        String::from_utf8_lossy(&past.stderr).contains("the file has 4 lines"),
        "{}",
        String::from_utf8_lossy(&past.stderr)
    );
}

/// Decision 0017 gives a file of bytes no lines, and a photograph has no
/// author per line.
#[test]
fn a_file_of_bytes_is_refused() {
    let directory = repository("bytes");
    fs::write(directory.join("pic.bin"), [0u8, 1, 2, 0]).expect("writing bytes");
    record(&directory, ADA, &["record", "-m", "a picture"]);

    let refused = run(&directory, ADA, &["blame", "head", "pic.bin"]);
    assert!(!refused.status.success());
    assert!(
        String::from_utf8_lossy(&refused.stderr).contains("file of bytes"),
        "{}",
        String::from_utf8_lossy(&refused.stderr)
    );
}
