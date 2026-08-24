//! `diff`, exercised as a person exercises it.
//!
//! Decision 0037. The claim under test is the one that distinguishes this
//! from every other tool's diff: a rename between two revisions is a fact the
//! store recorded (0008), and a rename in the folder is not a fact at all
//! (0011) — so the two are rendered differently on purpose.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

fn scratch(test: &str) -> PathBuf {
    let path = Path::new(env!("CARGO_TARGET_TMPDIR")).join(format!("diff-{test}"));
    let _ = fs::remove_dir_all(&path);
    fs::create_dir_all(&path).expect("a scratch directory");
    path
}

fn run(directory: &Path, arguments: &[&str]) -> Output {
    with(directory, arguments, &[])
}

fn with(directory: &Path, arguments: &[&str], environment: &[(&str, &str)]) -> Output {
    let mut command = Command::new(env!("CARGO_BIN_EXE_historica"));
    command
        .arg("-C")
        .arg(directory)
        .args(arguments)
        .env("HISTORICA_AUTHOR", "Adam Harris <adam@example.com>")
        // The test harness inherits whatever the person running it has set,
        // and `auto` reads this — so every run here says what it means.
        .env_remove("NO_COLOR");
    for (name, value) in environment {
        command.env(name, value);
    }
    command.output().expect("the binary this test crate builds")
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
    let file = directory.join(path);
    if let Some(parent) = file.parent() {
        fs::create_dir_all(parent).expect("a directory");
    }
    fs::write(file, text).expect("writing a file");
}

fn repository(test: &str) -> PathBuf {
    let directory = scratch(test);
    assert!(run(&directory, &["init"]).status.success());
    directory
}

/// The digest of the head, as `log` prints it.
fn head(directory: &Path) -> String {
    out(directory, &["log"])
        .lines()
        .find(|line| line.contains("(head"))
        .and_then(|line| line.split_whitespace().nth(1))
        .expect("a head")
        .to_owned()
}

#[test]
fn the_folder_against_the_position_is_what_status_counts() {
    let directory = repository("folder");
    write(&directory, "notes.md", "alpha\nbeta\ngamma\n");
    assert!(run(&directory, &["record", "-m", "base"]).status.success());
    assert_eq!(out(&directory, &["diff"]), "nothing differs\n");

    write(&directory, "notes.md", "alpha\nBETA\ngamma\n");
    let rendered = out(&directory, &["diff"]);
    assert_eq!(
        rendered,
        "--- a/notes.md\n\
         +++ b/notes.md\n\
         @@ -1,3 +1,3 @@\n\
         \x20alpha\n\
         -beta\n\
         +BETA\n\
         \x20gamma\n"
    );
}

/// The half decision 0008 pays for. Two revisions carry identifiers, so this
/// is read rather than guessed at — including with an edit in the same
/// revision, which resemblance could not have recovered.
#[test]
fn a_rename_between_two_revisions_is_stated() {
    let directory = repository("rename-recorded");
    write(&directory, "notes.md", "alpha\nbeta\ngamma\n");
    assert!(run(&directory, &["record", "-m", "base"]).status.success());

    fs::remove_file(directory.join("notes.md")).expect("removing it");
    write(&directory, "docs/notes.md", "alpha\nBETA\ngamma\n");
    assert!(
        run(
            &directory,
            &["record", "--move", "notes.md=docs/notes.md", "-m", "move"]
        )
        .status
        .success()
    );

    let rendered = out(&directory, &["diff", &head(&directory)]);
    assert!(rendered.contains("rename from notes.md"), "{rendered}");
    assert!(rendered.contains("rename to docs/notes.md"), "{rendered}");
    assert!(rendered.contains("--- a/notes.md"), "{rendered}");
    assert!(rendered.contains("+++ b/docs/notes.md"), "{rendered}");
    assert!(rendered.contains("-beta"), "{rendered}");
    assert!(rendered.contains("+BETA"), "{rendered}");
    // Not a drop and an add: one file, one row.
    assert!(!rendered.contains("new file"), "{rendered}");
    assert!(!rendered.contains("deleted file"), "{rendered}");
}

/// And the other half. The folder holds paths and no identifiers, so a
/// rename there is a drop and an add until somebody states it — inventing one
/// would be inventing a fact `record` would then not write down.
#[test]
fn a_rename_in_the_folder_is_a_drop_and_an_add() {
    let directory = repository("rename-folder");
    write(&directory, "notes.md", "alpha\nbeta\ngamma\n");
    assert!(run(&directory, &["record", "-m", "base"]).status.success());

    fs::remove_file(directory.join("notes.md")).expect("removing it");
    write(&directory, "docs/notes.md", "alpha\nbeta\ngamma\n");

    let rendered = out(&directory, &["diff"]);
    assert!(rendered.contains("deleted file notes.md"), "{rendered}");
    assert!(rendered.contains("new file docs/notes.md"), "{rendered}");
    assert!(!rendered.contains("rename"), "{rendered}");
}

/// Decision 0024's `file:` reaches through every rename between the sides,
/// which is the thing a path cannot spell.
#[test]
fn a_file_bookmark_follows_the_file_across_a_rename() {
    let directory = repository("bookmark");
    write(&directory, "notes.md", "alpha\n");
    assert!(run(&directory, &["record", "-m", "base"]).status.success());
    let root = head(&directory);

    fs::remove_file(directory.join("notes.md")).expect("removing it");
    write(&directory, "docs/notes.md", "alpha\nbeta\n");
    assert!(
        run(
            &directory,
            &["record", "--move", "notes.md=docs/notes.md", "-m", "move"]
        )
        .status
        .success()
    );
    let moved = head(&directory);
    assert!(
        run(&directory, &["name", "notes", &moved, "docs/notes.md"])
            .status
            .success()
    );

    // Named once, and it answers at a revision where the path was different.
    let rendered = out(&directory, &["diff", &moved, "file:notes", "--onto", &root]);
    assert!(rendered.contains("rename from notes.md"), "{rendered}");
    assert!(rendered.contains("+beta"), "{rendered}");
}

#[test]
fn one_argument_is_a_path_when_it_cannot_be_a_target() {
    let directory = repository("one-argument");
    write(&directory, "notes.md", "alpha\n");
    write(&directory, "other.md", "one\n");
    assert!(run(&directory, &["record", "-m", "base"]).status.success());
    write(&directory, "notes.md", "ALPHA\n");
    write(&directory, "other.md", "two\n");

    // 0001's disjoint alphabets: `notes.md` has a dot in it and so names no
    // change and no digest, which is what makes this unambiguous rather than
    // a guess between two readings.
    let rendered = out(&directory, &["diff", "notes.md"]);
    assert!(rendered.contains("notes.md"), "{rendered}");
    assert!(!rendered.contains("other.md"), "{rendered}");

    // A spelling that could be a target is one, and says so when it is not.
    let refused = run(&directory, &["diff", "kxryzmor"]);
    assert!(!refused.status.success());
    let complaint = String::from_utf8_lossy(&refused.stderr).into_owned();
    assert!(complaint.contains("kxryzmor"), "{complaint}");
}

#[test]
fn a_file_of_bytes_says_it_differs_rather_than_being_printed() {
    let directory = repository("binary");
    fs::write(directory.join("pic.png"), [0x89, b'P', b'N', b'G', 0, 1, 2])
        .expect("a file of bytes");
    assert!(run(&directory, &["record", "-m", "base"]).status.success());
    fs::write(directory.join("pic.png"), [0x89, b'P', b'N', b'G', 3, 4, 5]).expect("editing it");

    let rendered = out(&directory, &["diff"]);
    assert_eq!(
        rendered,
        "--- a/pic.png\n+++ b/pic.png\nbinary files differ\n"
    );
}

#[test]
fn a_mode_change_names_the_file_it_is_about() {
    let directory = repository("mode");
    write(&directory, "run.sh", "echo hello\n");
    write(&directory, "notes.md", "alpha\n");
    assert!(run(&directory, &["record", "-m", "base"]).status.success());

    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        let path = directory.join("run.sh");
        let mut mode = fs::metadata(&path).expect("metadata").permissions();
        mode.set_mode(0o755);
        fs::set_permissions(&path, mode).expect("chmod");

        // The whole of what changed, so nothing else names the file: two bare
        // `mode` lines would belong to no file at all.
        let rendered = out(&directory, &["diff"]);
        assert_eq!(rendered, "mode run.sh plain -> executable\n");
    }
}

#[test]
fn a_merge_says_which_side_it_wants_naming() {
    let directory = repository("merge");
    write(&directory, "f.md", "base\n");
    assert!(run(&directory, &["record", "-m", "base"]).status.success());
    let root = head(&directory);

    write(&directory, "a.md", "mine\n");
    assert!(run(&directory, &["record", "-m", "mine"]).status.success());
    let mine = head(&directory);
    fs::remove_file(directory.join("a.md")).expect("removing it");
    write(&directory, "b.md", "theirs\n");
    assert!(
        run(&directory, &["record", "--onto", &root, "-m", "theirs"])
            .status
            .success()
    );
    let theirs = out(&directory, &["log"])
        .lines()
        .find(|line| line.contains("(head") && !line.contains(&mine))
        .and_then(|line| line.split_whitespace().nth(1))
        .expect("the other head")
        .to_owned();

    assert!(run(&directory, &["merge"]).status.success());
    assert!(
        run(
            &directory,
            &["record", "--merge", &mine, "--merge", &theirs, "-m", "join"]
        )
        .status
        .success()
    );

    let refused = run(&directory, &["diff", &head(&directory)]);
    assert!(!refused.status.success());
    let complaint = String::from_utf8_lossy(&refused.stderr).into_owned();
    assert!(complaint.contains("is a merge"), "{complaint}");
    // And it prints commands that work, rather than describing them.
    let suggested: Vec<&str> = complaint
        .lines()
        .filter(|line| line.trim_start().starts_with("historica diff"))
        .collect();
    assert_eq!(suggested.len(), 2, "{complaint}");
    for line in suggested {
        let arguments: Vec<&str> = line.split_whitespace().skip(1).collect();
        assert!(
            run(&directory, &arguments).status.success(),
            "`{line}` should work"
        );
    }
}

#[test]
fn a_file_with_no_final_newline_says_so() {
    let directory = repository("terminator");
    write(&directory, "notes.md", "alpha\nbeta\n");
    assert!(run(&directory, &["record", "-m", "base"]).status.success());
    write(&directory, "notes.md", "alpha\nbeta");

    let rendered = out(&directory, &["diff"]);
    assert!(
        rendered.contains("\\ no newline at end of file"),
        "{rendered}"
    );
}

/// A repository whose one file has a line replaced, with words on either side
/// of the replacement that both versions share.
fn edited(test: &str) -> PathBuf {
    let directory = repository(test);
    write(&directory, "notes.md", "alpha\nbeta gamma delta\nepsilon\n");
    assert!(run(&directory, &["record", "-m", "base"]).status.success());
    write(&directory, "notes.md", "alpha\nbeta GAMMA delta\nepsilon\n");
    directory
}

/// Every escape sequence taken back out, which should leave the bytes the
/// undecorated run wrote.
fn undecorated(text: &str) -> String {
    let mut plain = String::with_capacity(text.len());
    let mut rest = text;
    while let Some(at) = rest.find('\x1b') {
        plain.push_str(&rest[..at]);
        let after = &rest[at..];
        assert!(after.starts_with("\x1b["), "a lone escape in {text:?}");
        let end = after
            .find(|character: char| character.is_ascii_alphabetic())
            .expect("an escape sequence ends in a letter");
        rest = &after[end + 1..];
    }
    plain.push_str(rest);
    plain
}

/// The property that makes colour a decoration rather than a change: a pipe
/// sees the bytes it saw before there was a `--color` at all, so
/// `historica diff | patch` is unaffected and no caller has to be told.
#[test]
fn a_pipe_is_never_decorated() {
    let directory = edited("piped");
    let piped = out(&directory, &["diff"]);
    assert!(!piped.contains('\x1b'), "{piped:?}");
    assert_eq!(out(&directory, &["diff", "--color", "never"]), piped);
    assert_eq!(out(&directory, &["diff", "--color=never"]), piped);
    assert_eq!(out(&directory, &["diff", "--color", "auto"]), piped);

    // And `NO_COLOR` settles `auto`, which is the only thing it can settle
    // here — a pipe has already settled it the same way.
    let output = with(&directory, &["diff"], &[("NO_COLOR", "1")]);
    assert!(output.status.success());
    assert_eq!(
        String::from_utf8(output.stdout).expect("printed text"),
        piped
    );
}

/// `always` is a person saying so, and `NO_COLOR` is a person not having said
/// anything — so the one that was said out loud wins.
#[test]
fn saying_always_outranks_no_color() {
    let directory = edited("no-color");
    for value in ["1", "true", ""] {
        let output = with(
            &directory,
            &["diff", "--color=always"],
            &[("NO_COLOR", value)],
        );
        assert!(output.status.success());
        let rendered = String::from_utf8(output.stdout).expect("printed text");
        // An empty `NO_COLOR` is not set as far as anyone is concerned, so
        // this holds for all three.
        assert!(rendered.contains("\x1b[31m"), "{rendered:?}");
    }
}

/// The conventions eyes trained on `git diff` already read: removals red,
/// arrivals green, hunk headers cyan, facts about the file bold.
#[test]
fn colour_is_the_one_every_other_tool_uses() {
    let directory = edited("always");
    let rendered = out(&directory, &["diff", "--color=always"]);
    assert!(
        rendered.contains("\x1b[1m--- a/notes.md\x1b[0m"),
        "{rendered:?}"
    );
    assert!(
        rendered.contains("\x1b[1m+++ b/notes.md\x1b[0m"),
        "{rendered:?}"
    );
    assert!(
        rendered.contains("\x1b[36m@@ -1,3 +1,3 @@\x1b[0m"),
        "{rendered:?}"
    );
    assert!(rendered.contains("\x1b[31m-beta "), "{rendered:?}");
    assert!(rendered.contains("\x1b[32m+beta "), "{rendered:?}");
    // A context line is not decorated, so it carries no reset either.
    assert!(rendered.contains("\n alpha\n"), "{rendered:?}");

    // Taking the escapes back out leaves what the pipe was given, byte for
    // byte: nothing here moves a line or alters one.
    assert_eq!(undecorated(&rendered), out(&directory, &["diff"]));
}

/// Emphasis inside the pair: what the two lines share stays plain and what
/// differs is drawn in inverse video, as `diff-highlight` has drawn it for a
/// decade. Display only — the hunks are still `crate::diff`'s decomposition,
/// which is why the escapes come back out to the same bytes.
#[test]
fn the_changed_words_inside_a_replaced_line_are_emphasised() {
    let directory = edited("intra-line");
    let rendered = out(&directory, &["diff", "--color=always"]);
    assert!(
        rendered.contains("\x1b[31m-beta \x1b[7mgamma\x1b[27m delta\x1b[0m"),
        "{rendered:?}"
    );
    assert!(
        rendered.contains("\x1b[32m+beta \x1b[7mGAMMA\x1b[27m delta\x1b[0m"),
        "{rendered:?}"
    );
    assert_eq!(undecorated(&rendered), out(&directory, &["diff"]));
}

/// Nothing shared means nothing worth emphasising: a line drawn entirely in
/// inverse video says only what its `-` already said.
#[test]
fn two_lines_with_nothing_in_common_stay_plain_inside() {
    let directory = repository("intra-line-plain");
    write(&directory, "notes.md", "alpha\nbeta\ngamma\n");
    assert!(run(&directory, &["record", "-m", "base"]).status.success());
    write(&directory, "notes.md", "alpha\nBETA\ngamma\n");

    let rendered = out(&directory, &["diff", "--color=always"]);
    assert!(rendered.contains("\x1b[31m-beta\x1b[0m"), "{rendered:?}");
    assert!(rendered.contains("\x1b[32m+BETA\x1b[0m"), "{rendered:?}");
    assert!(!rendered.contains("\x1b[7m"), "{rendered:?}");
}

#[test]
fn an_unknown_color_setting_says_what_the_three_are() {
    let directory = edited("color-usage");
    let refused = run(&directory, &["diff", "--color", "sometimes"]);
    assert_eq!(refused.status.code(), Some(2));
    let complaint = String::from_utf8_lossy(&refused.stderr).into_owned();
    assert!(complaint.contains("sometimes"), "{complaint}");
    for word in ["auto", "always", "never"] {
        assert!(complaint.contains(word), "{complaint}");
    }
}

/// `diff` renders; `show` is what prints the stored document. A rendering
/// that could be mistaken for the authority is the thing decision 0037 exists
/// to keep apart.
#[test]
fn what_diff_prints_is_not_what_the_store_holds() {
    let directory = repository("rendering");
    write(&directory, "notes.md", "alpha\n");
    assert!(run(&directory, &["record", "-m", "base"]).status.success());
    write(&directory, "notes.md", "alpha\nbeta\n");
    assert!(run(&directory, &["record", "-m", "more"]).status.success());

    let head = head(&directory);
    let rendered = out(&directory, &["diff", &head]);
    let stored = out(&directory, &["show", &head, "notes.md"]);
    assert!(rendered.contains("@@"), "{rendered}");
    assert!(!stored.contains("@@"), "{stored}");
    assert!(stored.starts_with("historica-v"), "{stored}");
}
