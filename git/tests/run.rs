//! `write --wrote` on the command line — decision 0009's cheap case and its
//! refusal, which are decided before any store or repository is looked for.

use std::io::Write;
use std::process::{Command, Output, Stdio};

/// Run `historica-git write --wrote -` in an empty directory, with `input` on
/// standard input.
fn run(input: &str) -> Output {
    let nowhere = std::path::PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join("run-cli");
    let _ = std::fs::remove_dir_all(&nowhere);
    std::fs::create_dir_all(&nowhere).expect("a scratch directory");
    let mut child = Command::new(env!("CARGO_BIN_EXE_historica-git"))
        .args(["write", "--wrote", "-"])
        .current_dir(&nowhere)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("the binary runs");
    child
        .stdin
        .take()
        .expect("stdin was piped")
        .write_all(input.as_bytes())
        .expect("the statement is sent");
    child.wait_with_output().expect("the binary finishes")
}

#[test]
fn wrote_nothing_is_silent_and_succeeds_with_no_store_anywhere() {
    for input in ["historica-wrote-1\n", ""] {
        let out = run(input);
        assert!(out.status.success(), "{input:?}: {out:?}");
        assert!(out.stdout.is_empty(), "{input:?}: {out:?}");
        assert!(out.stderr.is_empty(), "{input:?}: {out:?}");
    }
}

#[test]
fn a_statement_this_build_does_not_read_is_refused_whole() {
    for input in [
        "historica-log-1\n",
        "historica-wrote-2\nrevision 00\n",
        "historica-wrote-1\nmoved main\n",
    ] {
        let out = run(input);
        assert!(!out.status.success(), "{input:?}: {out:?}");
        let said = String::from_utf8_lossy(&out.stderr);
        assert!(said.contains("nothing was written to git"), "{said}");
    }
}
