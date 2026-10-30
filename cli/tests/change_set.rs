//! `change-set`, as decision 0091 describes it: proposed, stepped on with
//! `record`, submitted, and decided by a merge or a tombstone.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

use historica::change_set::State;
use historica::store::Store;

fn scratch(test: &str) -> PathBuf {
    let path = Path::new(env!("CARGO_TARGET_TMPDIR")).join(format!("change-set-{test}"));
    let _ = fs::remove_dir_all(&path);
    fs::create_dir_all(&path).expect("a scratch directory");
    path
}

fn run(directory: &Path, author: &str, arguments: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_historica"))
        .env(
            "HISTORICA_CACHE_DIR",
            concat!(env!("CARGO_TARGET_TMPDIR"), "/caches"),
        )
        .env("HISTORICA_AUTHOR", author)
        .env_remove("VISUAL")
        .env_remove("EDITOR")
        .arg("-C")
        .arg(directory)
        .args(arguments)
        .output()
        .expect("the binary this test crate builds")
}

const PERSON: &str = "Adam Harris <adam@example.com>";
const AGENT: &str = "agent:claude-opus-5-5";

fn out_as(directory: &Path, author: &str, arguments: &[&str]) -> String {
    let output = run(directory, author, arguments);
    assert!(
        output.status.success(),
        "`{}` failed: {}",
        arguments.join(" "),
        String::from_utf8_lossy(&output.stderr)
    );
    String::from_utf8(output.stdout).expect("printed text")
}

fn out(directory: &Path, arguments: &[&str]) -> String {
    out_as(directory, PERSON, arguments)
}

fn failure(directory: &Path, arguments: &[&str]) -> String {
    let output = run(directory, PERSON, arguments);
    assert!(
        !output.status.success(),
        "`{}` succeeded",
        arguments.join(" ")
    );
    String::from_utf8(output.stderr).expect("printed text")
}

fn library(test: &str) -> PathBuf {
    let directory = scratch(test);
    out(&directory, &["init"]);
    fs::write(directory.join("notes.md"), "one\n").expect("a file");
    out(&directory, &["record", "-m", "Start a journal"]);
    out(&directory, &["name", "main", "head"]);
    directory
}

fn store(directory: &Path) -> Store {
    Store::open(directory.join("history")).expect("a store")
}

#[test]
fn a_change_set_is_proposed_stepped_submitted_and_accepted_by_a_merge() {
    let here = library("accept");
    let proposed = out_as(
        &here,
        AGENT,
        &["change-set", "propose", "-m", "Add a second thought"],
    );
    let id = store(&here).change_sets().unwrap()[0].id;
    let tip = format!("change-sets/{id}");
    assert!(proposed.contains(&tip), "{proposed}");

    fs::write(here.join("notes.md"), "one\ntwo\n").unwrap();
    out_as(
        &here,
        AGENT,
        &["record", "--onto", &tip, "-m", "A second thought"],
    );
    out_as(
        &here,
        AGENT,
        &["change-set", "submit", &id.to_string()[..6]],
    );

    let listed = out(&here, &["change-set"]);
    assert!(
        listed.contains("submitted") && listed.contains("1 step") && listed.contains(AGENT),
        "{listed}"
    );
    let shown = out(&here, &["change-set", "show", &tip]);
    assert!(shown.contains("title      Add a second thought"), "{shown}");
    assert!(shown.contains("A second thought"), "{shown}");

    // Accepting before anything merges it says how.
    let said = failure(&here, &["change-set", "accept", &tip]);
    assert!(said.contains("--merge"), "{said}");

    // The person's `main` did not move, so the merge joins the line to it.
    out(&here, &["update", &tip]);
    out(
        &here,
        &[
            "record",
            "--onto",
            "main",
            "--merge",
            &tip,
            "-m",
            "Accept it",
        ],
    );
    let accepted = out(&here, &["change-set", "accept", &tip]);
    assert!(accepted.starts_with("accepted"), "{accepted}");

    let change_set = store(&here).change_set(&id).unwrap();
    assert_eq!(change_set.state(), State::Accepted);
    // `main` followed the merge, and the tip stayed on the line.
    let main = out(&here, &["log", "main", "--limit", "1"]);
    assert!(main.contains("Accept it"), "{main}");
    assert_eq!(change_set.steps, vec![change_set.tip]);
    let checked = run(&here, PERSON, &["check"]);
    assert!(checked.status.success());
}

#[test]
fn a_declined_change_set_is_one_tombstone_and_a_reason() {
    let here = library("decline");
    out_as(
        &here,
        AGENT,
        &["change-set", "propose", "-m", "Rewrite everything"],
    );
    let id = store(&here).change_sets().unwrap()[0].id;
    let tip = format!("change-sets/{id}");
    fs::write(here.join("notes.md"), "everything\n").unwrap();
    out_as(
        &here,
        AGENT,
        &["record", "--onto", &tip, "-m", "Everything"],
    );

    // No reason and no editor is a refusal: the reason is what a tombstone is.
    failure(&here, &["change-set", "decline", &tip]);
    let declined = out(&here, &["change-set", "decline", &tip, "-m", "Not this"]);
    assert!(declined.starts_with("declined"), "{declined}");
    assert_eq!(
        store(&here).change_set(&id).unwrap().state(),
        State::Declined
    );
    let again = failure(&here, &["change-set", "submit", &tip]);
    assert!(again.contains("already declined"), "{again}");
}
