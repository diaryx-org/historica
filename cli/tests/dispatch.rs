//! Decision 0072: a command this tool does not have.
//!
//! What is being checked is that the fall-through is a spelling and nothing
//! more — the arguments arrive as given, the exit code comes back as the other
//! program set it, `-C` is the folder the child is run in, and a word that
//! names a position rather than a program is a typo rather than a thing to run.
#![cfg(unix)]

use std::fs;
use std::os::unix::fs::PermissionsExt as _;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

/// A fresh directory for one test, inside the target directory.
fn scratch(test: &str) -> PathBuf {
    let path = Path::new(env!("CARGO_TARGET_TMPDIR")).join(format!("dispatch-{test}"));
    let _ = fs::remove_dir_all(&path);
    fs::create_dir_all(&path).expect("a scratch directory");
    path
}

/// Write an executable shell script, and return the directory holding it.
fn program(at: &Path, name: &str, body: &str) -> PathBuf {
    fs::create_dir_all(at).expect("a directory for the program");
    let path = at.join(name);
    fs::write(&path, format!("#!/bin/sh\n{body}\n")).expect("the program");
    fs::set_permissions(&path, fs::Permissions::from_mode(0o755)).expect("it to be runnable");
    at.to_path_buf()
}

/// Run the binary with `path` prepended to `PATH`, from `directory`.
fn run(directory: &Path, path: &Path, arguments: &[&str]) -> Output {
    let inherited = std::env::var("PATH").unwrap_or_default();
    Command::new(env!("CARGO_BIN_EXE_historica"))
        .arg("-C")
        .arg(directory)
        .args(arguments)
        .env("PATH", format!("{}:{inherited}", path.display()))
        .current_dir(directory)
        .output()
        .expect("the binary this test crate builds")
}

#[test]
fn a_program_on_the_path_answers_for_the_word_that_names_it() {
    let base = scratch("found");
    let bin = program(&base.join("bin"), "historica-hello", "echo \"said $*\"");

    let output = run(&base, &bin, &["hello", "one", "--two"]);
    assert!(output.status.success());
    assert_eq!(
        String::from_utf8_lossy(&output.stdout),
        "said one --two\n",
        "the arguments cross as given, with nothing added or read"
    );
}

#[test]
fn the_other_programs_exit_code_is_this_ones() {
    let base = scratch("code");
    let bin = program(&base.join("bin"), "historica-cross", "exit 7");

    let output = run(&base, &bin, &["cross"]);
    assert_eq!(
        output.status.code(),
        Some(7),
        "a script wrapping `historica cross` sees what wrapping the tool would show it"
    );
}

#[test]
fn dash_c_is_the_directory_the_other_program_runs_in() {
    let base = scratch("directory");
    let bin = program(&base.join("bin"), "historica-where", "pwd");
    let elsewhere = base.join("elsewhere");
    fs::create_dir_all(&elsewhere).expect("somewhere else");

    let output = run(&elsewhere, &bin, &["where"]);
    assert!(output.status.success());
    let said = String::from_utf8_lossy(&output.stdout);
    assert!(
        // The scratch path goes through `/var` on macOS and is reported as
        // `/private/var`, so the tail is what can be compared.
        said.trim_end().ends_with("elsewhere"),
        "the side tool is handed the folder rather than told about a flag: {said}"
    );
}

#[test]
fn a_word_nothing_on_the_path_answers_to_is_the_plain_no_such_command() {
    let base = scratch("missing");
    let bin = program(&base.join("bin"), "historica-present", "echo here");

    let output = run(&base, &bin, &["absent"]);
    assert_eq!(output.status.code(), Some(2));
    let said = String::from_utf8_lossy(&output.stderr);
    assert!(
        said.contains("there is no `absent` command"),
        "a typo reads as a typo rather than as a failed spawn: {said}"
    );
}

#[test]
fn a_word_holding_a_separator_names_a_position_and_is_never_run() {
    let base = scratch("separator");
    // `historica-../evil`, resolved as a path from the working directory, is
    // this file. `Command::new` would run it without consulting `PATH` at all,
    // which is what the alphabet in `dispatchable` exists to refuse.
    let marker = base.join("ran");
    program(
        &base.join("historica-.."),
        "evil",
        &format!("touch {}", marker.display()),
    );

    let output = run(&base, &base.join("bin"), &["../evil"]);
    assert_eq!(output.status.code(), Some(2));
    assert!(
        String::from_utf8_lossy(&output.stderr).contains("there is no `../evil` command"),
        "a position is not a command name"
    );
    assert!(!marker.exists(), "nothing was run");
}

#[test]
fn a_word_outside_the_alphabet_is_refused_rather_than_looked_for() {
    let base = scratch("alphabet");
    let output = run(&base, &base.join("bin"), &["gít"]);
    assert_eq!(output.status.code(), Some(2));
    assert!(
        String::from_utf8_lossy(&output.stderr).contains("there is no `gít` command"),
        "the rule is a positive one, so anything outside it is simply absent"
    );
}
