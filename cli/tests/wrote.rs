//! Decision 0074's comparison: every statement, against the store that made it.
//!
//! The claim under test is the one that makes `historica-wrote-1` safe to
//! have at all — **every line is a claim the store can be held to**. So
//! nothing here reads a statement and compares it with what the library
//! returned; that would be one implementation agreeing with itself. Every
//! assertion goes to the files: `revision <digest>` means a file under
//! `revisions/` hashes to that, `name <bookmark>` means a file under `names/`
//! has that path, `unname` means it does not, and `gone <digest>` means
//! nothing anywhere under the store hashes to it.
//!
//! That makes this the first end-to-end test of decision 0003's rule from the
//! writing side, which is what 0074 says it is for.

use std::collections::BTreeSet;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

use historica::core::RevisionId;
use historica::format::digest;
use historica::wrote::{HEADER, Line, Statement};

fn scratch(test: &str) -> PathBuf {
    let path = Path::new(env!("CARGO_TARGET_TMPDIR")).join(format!("wrote-{test}"));
    let _ = fs::remove_dir_all(&path);
    fs::create_dir_all(&path).expect("a scratch directory");
    path
}

fn run(directory: &Path, arguments: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_historica"))
        .arg("-C")
        .arg(directory)
        .args(arguments)
        .env("HISTORICA_AUTHOR", "Adam Harris <adam@example.com>")
        .output()
        .expect("the binary this test crate builds")
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

/// A store with one recorded revision and a bookmark that follows the work.
fn started(test: &str) -> PathBuf {
    let directory = scratch(test);
    fs::create_dir_all(directory.join("notes")).expect("a folder");
    fs::write(directory.join("notes/one.md"), "one\n").expect("a file");
    assert!(run(&directory, &["init"]).status.success());
    out(&directory, &["record", "-m", "the first"]);
    out(&directory, &["name", "main", "head"]);
    directory
}

/// Every file under the store, by path.
fn files_under(directory: &Path) -> Vec<PathBuf> {
    let mut found = Vec::new();
    let mut pending = vec![directory.join("history")];
    while let Some(next) = pending.pop() {
        let Ok(entries) = fs::read_dir(&next) else {
            continue;
        };
        for entry in entries.filter_map(Result::ok) {
            let path = entry.path();
            if path.is_dir() {
                pending.push(path);
            } else {
                found.push(path);
            }
        }
    }
    found
}

/// The digest of every file in one directory of the store.
fn digests_in(directory: &Path, which: &str) -> BTreeSet<RevisionId> {
    files_under(directory)
        .into_iter()
        .filter(|path| path.starts_with(directory.join("history").join(which)))
        .filter_map(|path| fs::read(&path).ok())
        .map(|bytes| digest(&bytes))
        .collect()
}

/// The digest of every file the store holds, wherever it sits.
fn every_digest(directory: &Path) -> BTreeSet<RevisionId> {
    files_under(directory)
        .into_iter()
        .filter_map(|path| fs::read(&path).ok())
        .map(|bytes| digest(&bytes))
        .collect()
}

/// Every bookmark, as its path below `names/` without the suffix — which is
/// what decision 0071 makes a name.
fn names_on_disk(directory: &Path) -> BTreeSet<String> {
    let root = directory.join("history").join("names");
    files_under(directory)
        .into_iter()
        .filter_map(|path| path.strip_prefix(&root).ok().map(Path::to_path_buf))
        .filter_map(|path| {
            let text = path.to_str()?.strip_suffix(".txt")?.to_owned();
            Some(text.replace(std::path::MAIN_SEPARATOR, "/"))
        })
        .collect()
}

/// Read a statement, and hold the store to every line of it.
///
/// This is the comparison 0074 asks for, and it is total: the vocabulary is
/// four kinds and each one is a question with a yes or no answer on disk.
fn held_to(directory: &Path, said: &str) -> Statement {
    let statement: Statement = said
        .parse()
        .unwrap_or_else(|error| panic!("a statement this tool wrote: {error}\n{said}"));

    let revisions = digests_in(directory, "revisions");
    let names = names_on_disk(directory);
    let everything = every_digest(directory);
    for line in statement.lines() {
        match line {
            Line::Revision(id) => assert!(
                revisions.contains(id),
                "`revision {id}` names nothing in revisions/"
            ),
            Line::Name(name) => assert!(
                names.contains(name),
                "`name {name}` names nothing in names/; there is {names:?}"
            ),
            Line::Unname(name) => assert!(
                !names.contains(name),
                "`unname {name}` says it is gone and names/ still has it"
            ),
            Line::Gone(id) => assert!(
                !everything.contains(id),
                "`gone {id}` says nothing is there and something is"
            ),
        }
    }
    statement
}

/// The lines of one kind, for a test that also cares what was said.
fn revisions_of(statement: &Statement) -> Vec<RevisionId> {
    statement
        .lines()
        .filter_map(|line| match line {
            Line::Revision(id) => Some(*id),
            _ => None,
        })
        .collect()
}

fn gone_in(statement: &Statement) -> Vec<RevisionId> {
    statement
        .lines()
        .filter_map(|line| match line {
            Line::Gone(id) => Some(*id),
            _ => None,
        })
        .collect()
}

#[test]
fn record_states_the_revision_it_wrote_and_the_bookmark_that_followed() {
    let directory = started("record");
    fs::write(directory.join("notes/one.md"), "one, again\n").expect("a change");

    let said = out(&directory, &["record", "--fields", "-m", "the second"]);
    let statement = held_to(&directory, &said);

    assert_eq!(revisions_of(&statement).len(), 1, "{said}");
    assert!(
        statement
            .lines()
            .any(|line| *line == Line::Name("main".to_owned())),
        "the bookmark followed the work forward: {said}"
    );
    // Nothing a document says is restated: no change ID, no message, no author.
    assert!(!said.contains("the second"), "{said}");
    assert!(!said.contains("@example.com"), "{said}");
}

#[test]
fn amend_states_the_revision_it_wrote_and_not_the_one_it_superseded() {
    let directory = started("amend");
    let before = digests_in(&directory, "revisions");
    fs::write(directory.join("notes/one.md"), "one, amended\n").expect("a change");

    let said = out(&directory, &["amend", "--fields", "-m", "reworded"]);
    let statement = held_to(&directory, &said);

    let written = revisions_of(&statement);
    assert_eq!(written.len(), 1, "{said}");
    assert!(!before.contains(&written[0]), "a new document: {said}");
    // Decision 0013: what it superseded is still in `revisions/`, and nothing
    // about it changed, so it is not a line.
    assert_eq!(
        digests_in(&directory, "revisions").len(),
        before.len() + 1,
        "the superseded revision is still here"
    );
}

#[test]
fn abandon_states_the_tombstone_and_leaves_what_it_superseded_alone() {
    let directory = started("abandon");
    fs::write(directory.join("notes/one.md"), "one, again\n").expect("a change");
    out(&directory, &["record", "-m", "the second"]);

    let said = out(&directory, &["abandon", "head", "--fields", "-m", "no"]);
    let statement = held_to(&directory, &said);

    assert_eq!(revisions_of(&statement).len(), 1, "the tombstone: {said}");
    // A tombstone is not a deletion, so nothing here is `gone`: `prune` is the
    // command that makes that true, and it has its own statement.
    assert!(gone_in(&statement).is_empty(), "{said}");
}

#[test]
fn carry_states_every_revision_it_restated() {
    let directory = started("carry");
    fs::write(directory.join("notes/one.md"), "one, again\n").expect("a change");
    out(&directory, &["record", "-m", "the second"]);
    fs::write(directory.join("notes/two.md"), "two\n").expect("another file");
    out(&directory, &["record", "-m", "the third"]);

    // `--onto` is the half of decision 0059 a person decides: the head, moved
    // to stand on the root instead of on what it was recorded against.
    let stack = out(&directory, &["log", "--fields"]);
    let digest = |line: &str| line.split(' ').next().expect("a digest").to_owned();
    let head = digest(stack.lines().nth(1).expect("the head"));
    let root = digest(stack.lines().last().expect("the root"));

    let said = out(&directory, &["carry", &head, "--onto", &root, "--fields"]);
    let statement = held_to(&directory, &said);
    // Whatever there was to carry, every line of it is a document on disk —
    // and where there was nothing, the header alone is the whole statement.
    assert!(said.starts_with(HEADER), "{said}");
    assert!(
        !revisions_of(&statement).is_empty(),
        "a carry a person asked for restates at least the revision named: {said}"
    );
}

#[test]
fn prune_states_what_is_gone_and_nothing_is_there() {
    let directory = started("prune");
    fs::write(directory.join("notes/one.md"), "one, again\n").expect("a change");
    out(&directory, &["record", "-m", "the second"]);
    out(&directory, &["abandon", "head", "-m", "no"]);

    let said = out(&directory, &["prune", "--fields"]);
    let statement = held_to(&directory, &said);

    assert!(
        !gone_in(&statement).is_empty(),
        "something was pruned: {said}"
    );
    // `gone` is the only kind pruning has: it destroys and writes nothing.
    assert_eq!(gone_in(&statement).len(), statement.len(), "{said}");
}

#[test]
fn forget_states_the_digests_that_stopped_being_readable() {
    let directory = started("forget");
    fs::write(directory.join("notes/one.md"), "a secret\n").expect("a change");
    out(&directory, &["record", "-m", "the second"]);

    let said = out(
        &directory,
        &[
            "forget",
            "head",
            "notes/one.md",
            "--lines",
            "1..1",
            "--fields",
        ],
    );
    let statement = held_to(&directory, &said);

    assert!(!gone_in(&statement).is_empty(), "{said}");
    // The stand-ins forgetting writes are documents in `operations/`, which
    // this vocabulary has no kind for, so they are not lines.
    assert_eq!(gone_in(&statement).len(), statement.len(), "{said}");
}

/// The case 0074 had to be amended for: decision 0071 makes a name a path that
/// may hold an interior space, so a reader splits the line once.
#[test]
fn name_states_a_bookmark_whose_name_holds_a_space() {
    let directory = started("name");

    let said = out(
        &directory,
        &["name", "feature/two words", "head", "--fields"],
    );
    let statement = held_to(&directory, &said);
    assert_eq!(
        statement.lines().collect::<Vec<_>>(),
        vec![&Line::Name("feature/two words".to_owned())],
        "{said}"
    );

    let said = out(
        &directory,
        &["name", "--delete", "feature/two words", "--fields"],
    );
    let statement = held_to(&directory, &said);
    assert_eq!(
        statement.lines().collect::<Vec<_>>(),
        vec![&Line::Unname("feature/two words".to_owned())],
        "{said}"
    );
}

#[test]
fn receive_states_the_revisions_and_bookmarks_that_arrived() {
    let there = started("receive-source");
    fs::write(there.join("notes/one.md"), "one, again\n").expect("a change");
    out(&there, &["record", "-m", "the second"]);

    let here = scratch("receive");
    assert!(run(&here, &["init"]).status.success());
    let said = out(
        &here,
        &["receive", there.to_str().expect("a path"), "--fields"],
    );
    let statement = held_to(&here, &said);

    assert_eq!(revisions_of(&statement).len(), 2, "{said}");
    assert!(
        statement
            .lines()
            .any(|line| *line == Line::Name("main".to_owned())),
        "the bookmark travelled: {said}"
    );
}

/// The most useful line in the format: a wrapper reading this does nothing at
/// all, and it is the one fact reading the store cannot recover.
#[test]
fn a_command_that_wrote_nothing_says_so_and_succeeds() {
    let directory = started("empty");
    assert_eq!(
        out(&directory, &["prune", "--fields"]),
        format!("{HEADER}\n")
    );
    assert_eq!(
        out(&directory, &["carry", "--fields"]),
        format!("{HEADER}\n")
    );
}

/// A command that stopped still leaves a statement, so the wrapper on the far
/// side of the pipe is never handed a truncated stream.
#[test]
fn a_command_that_failed_leaves_a_well_formed_statement() {
    let directory = started("failed");
    // Nothing differs from what is recorded, which `record` refuses.
    let output = run(&directory, &["record", "--fields", "-m", "nothing"]);

    assert!(!output.status.success());
    assert_eq!(
        String::from_utf8(output.stdout).expect("printed text"),
        format!("{HEADER}\n"),
        "the exit code carries the failure, and the statement is still one"
    );
}

/// A plan is not a claim the store can be held to, so the header is not lent
/// to one.
#[test]
fn a_plan_gets_no_statement() {
    let directory = started("planned");
    for command in [
        ["record", "--dry-run", "--fields", "-m", "x"].as_slice(),
        ["prune", "--dry-run", "--fields"].as_slice(),
        [
            "forget",
            "head",
            "notes/one.md",
            "--lines",
            "1..1",
            "-n",
            "--fields",
        ]
        .as_slice(),
    ] {
        let output = run(&directory, command);
        assert_eq!(output.status.code(), Some(2), "{command:?}");
        assert!(output.stdout.is_empty(), "{command:?}");
        let said = String::from_utf8_lossy(&output.stderr).to_string();
        assert!(said.contains("is not on disk"), "{said}");
    }
}

/// `merge` reads the store and writes the folder, so it is not on the roster:
/// the empty statement it could always make would be a lie told by a true
/// sentence.
#[test]
fn a_command_that_writes_no_store_refuses_the_flag() {
    let directory = started("roster");
    for command in [
        ["merge", "--fields"].as_slice(),
        ["update", "--fields"].as_slice(),
    ] {
        let output = run(&directory, command);
        assert!(!output.status.success(), "{command:?}");
        assert!(output.stdout.is_empty(), "{command:?}");
    }
}
