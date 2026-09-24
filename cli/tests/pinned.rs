//! `historica-pinned`, the test build whose clock and random source are fixed.
//!
//! Built only with `--features pinned`, so this file is empty without it. What
//! it holds the build to is the one thing the build is for: the same command,
//! the same folder and the same pins leave the same bytes on disk.
#![cfg(feature = "pinned")]

use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

fn scratch(test: &str) -> PathBuf {
    let path = Path::new(env!("CARGO_TARGET_TMPDIR")).join(format!("pinned-{test}"));
    let _ = fs::remove_dir_all(&path);
    fs::create_dir_all(&path).expect("a scratch directory");
    path
}

fn run(directory: &Path, seed: Option<&str>, arguments: &[&str]) -> Output {
    let mut command = Command::new(env!("CARGO_BIN_EXE_historica-pinned"));
    command
        .arg("-C")
        .arg(directory)
        .args(arguments)
        .env("HISTORICA_AUTHOR", "Adam Harris <adam@example.com>")
        .env("HISTORICA_PINNED_NOW", "2026-01-02T03:04:05+01:00");
    match seed {
        Some(seed) => command.env("HISTORICA_PINNED_SEED", seed),
        None => command.env_remove("HISTORICA_PINNED_SEED"),
    };
    command.output().expect("the binary this test crate builds")
}

/// Every file under the store but its cache, which holds modification times.
fn stored(directory: &Path) -> BTreeMap<PathBuf, Vec<u8>> {
    fn walk(at: &Path, under: &Path, out: &mut BTreeMap<PathBuf, Vec<u8>>) {
        for entry in fs::read_dir(at).expect("a directory") {
            let path = entry.expect("an entry").path();
            if path.ends_with("history/cache") {
                continue;
            }
            if path.is_dir() {
                walk(&path, under, out);
            } else {
                let name = path.strip_prefix(under).expect("beneath").to_path_buf();
                out.insert(name, fs::read(&path).expect("a file"));
            }
        }
    }
    let mut out = BTreeMap::new();
    walk(&directory.join("history"), directory, &mut out);
    out
}

fn recorded(test: &str, seed: &str) -> (BTreeMap<PathBuf, Vec<u8>>, String) {
    let directory = scratch(test);
    fs::write(directory.join("one.md"), "one\n").expect("a file");
    assert!(run(&directory, Some(seed), &["init"]).status.success());
    let output = run(&directory, Some(seed), &["record", "-m", "the first"]);
    assert!(output.status.success(), "{output:?}");
    (
        stored(&directory),
        String::from_utf8(output.stdout).expect("printed text"),
    )
}

#[test]
fn the_same_pins_record_the_same_bytes() {
    let (one, said) = recorded("same-one", "a seed");
    let (two, again) = recorded("same-two", "a seed");
    assert_eq!(said, again);
    assert_eq!(one, two);
    assert!(
        one.keys().any(|path| path.starts_with("history/revisions")),
        "a revision was written"
    );
}

#[test]
fn another_seed_mints_another_change() {
    let (_, said) = recorded("seed-one", "a seed");
    let (_, other) = recorded("seed-two", "another seed");
    assert_ne!(said, other);
}

#[test]
fn a_missing_pin_is_refused_rather_than_read_from_the_machine() {
    let directory = scratch("missing");
    let output = run(&directory, None, &["init"]);
    assert_eq!(output.status.code(), Some(2));
    assert!(
        String::from_utf8_lossy(&output.stderr).contains("HISTORICA_PINNED_SEED"),
        "{output:?}"
    );
}
