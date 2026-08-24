//! `export`, exercised as decision 0042 describes it.
//!
//! The claim under test throughout is the decision's central one: the copy is
//! *assembled*, not mirrored. So the assertions come in pairs — what the copy
//! holds, and what it cannot hold however the folder it was made from stood.
//! An unrecorded edit and a skipped file are in every fixture here for exactly
//! that reason, and the `wget -r` failure the decision names is what their
//! absence rules out.

use std::collections::BTreeSet;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

use historica::store::Store;

fn scratch(test: &str) -> PathBuf {
    let path = Path::new(env!("CARGO_TARGET_TMPDIR")).join(format!("export-{test}"));
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

/// Everything the command printed, having succeeded.
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

/// Everything the command printed, having been refused.
fn refused(directory: &Path, arguments: &[&str]) -> String {
    let output = run(directory, arguments);
    assert!(
        !output.status.success(),
        "`{}` should have been refused: {}",
        arguments.join(" "),
        String::from_utf8_lossy(&output.stdout)
    );
    String::from_utf8(output.stderr).expect("printed text")
}

fn write(directory: &Path, path: &str, text: &str) {
    let file = directory.join(path);
    if let Some(parent) = file.parent() {
        fs::create_dir_all(parent).expect("a directory");
    }
    fs::write(file, text).expect("writing a file");
}

/// An empty repository with a store in it.
fn repository(test: &str) -> PathBuf {
    let directory = scratch(test);
    assert!(run(&directory, &["init"]).status.success());
    directory
}

/// Every revision digest `log` names, in the order it prints them.
fn digests(directory: &Path) -> Vec<String> {
    out(directory, &["log"])
        .lines()
        .filter(|line| !line.starts_with(' ') && !line.is_empty())
        .filter_map(|line| line.split_whitespace().nth(1).map(str::to_owned))
        .collect()
}

/// The current head, as `log` abbreviates it.
fn head_of(directory: &Path) -> String {
    out(directory, &["log"])
        .lines()
        .find(|line| line.contains("(head") && !line.contains("superseded"))
        .and_then(|line| line.split_whitespace().nth(1).map(str::to_owned))
        .expect("a head")
}

/// Every file under a directory, said relative to it.
fn walk(root: &Path) -> Vec<String> {
    let mut found = Vec::new();
    let mut pending = vec![root.to_path_buf()];
    while let Some(directory) = pending.pop() {
        let Ok(entries) = fs::read_dir(&directory) else {
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

/// A repository with two revisions, a picture, a bookmark, a rule, and an
/// unrecorded file — one of everything the copy has to decide about.
fn furnished(test: &str) -> PathBuf {
    let directory = repository(test);
    write(&directory, "notes.md", "one\n");
    fs::create_dir_all(directory.join("notes")).expect("a directory");
    fs::write(directory.join("notes/photo.png"), [0u8, 1, 2, 255]).expect("a picture");
    out(&directory, &["record", "-m", "Start a journal"]);
    write(&directory, "notes.md", "one\ntwo\n");
    out(&directory, &["record", "-m", "A second thought"]);

    out(&directory, &["name", "main", "head"]);
    out(&directory, &["skip", "--suffix", ".tmp"]);
    write(&directory, "draft.tmp", "a file a rule keeps out\n");
    write(&directory, "notes.md", "one\ntwo\nunrecorded\n");
    directory
}

#[test]
fn an_export_is_a_repository_a_stranger_can_open() {
    let origin = furnished("round-trip");
    let copy = scratch("round-trip-copy").join("journal");

    let said = out(&origin, &["export", &copy.to_string_lossy()]);
    assert!(said.contains("exported 2 revisions"), "{said}");
    assert!(said.contains("made a copy of"), "{said}");

    // A complete, ordinary store: `check` is the first thing a stranger runs.
    assert!(
        out(&copy, &["check"]).ends_with("nothing to report\n"),
        "the copy does not check out"
    );
    // And the same history, revision for revision, because the digests are
    // the digests.
    assert_eq!(digests(&origin), digests(&copy));

    // The folder is the target's, byte for byte.
    assert_eq!(
        fs::read_to_string(copy.join("notes.md")).expect("the copy's file"),
        "one\ntwo\n",
        "the copy holds the recorded bytes rather than the folder's"
    );
    assert_eq!(
        fs::read(copy.join("notes/photo.png")).expect("the copy's picture"),
        [0u8, 1, 2, 255]
    );
    assert!(
        !copy.join("draft.tmp").exists(),
        "a file a `skip` rule names travelled: 0042's `wget -r` failure"
    );
    assert!(out(&copy, &["status"]).contains("nothing here differs"));

    // What is the exporter's stays with the exporter.
    assert!(
        out(&copy, &["names"]).contains("no bookmarks"),
        "the exporter's bookmarks travelled"
    );
    let rules = fs::read_to_string(copy.join("history/skipped.txt")).expect("a rule file");
    assert!(
        rules
            .lines()
            .all(|line| line.is_empty() || line.starts_with('#')),
        "the exporter's rules travelled: {rules}"
    );
    // A cache is nobody's, so none of the exporter's travels. What the copy
    // has in `cache/` is what it wrote for itself on the way: the note `init`
    // leaves, the catalogue saying where in its *own* `operations/` each
    // digest sits, and decision 0043's catalogue of its *own* folder. A cached
    // state is a file named by a digest, and there are none — the copy has
    // read nobody's files.
    let cache = walk(&copy.join("history/cache"));
    assert!(
        cache
            .iter()
            .all(|name| name == "README.txt" || name == "operations.txt" || name == "working.txt"),
        "the exporter's cache travelled: {cache:?}"
    );

    // Decision 0021: the copy explains itself to whoever opens it.
    let header = fs::read_to_string(copy.join("history/historica.txt")).expect("a header");
    assert!(header.contains("Identity comes from content"), "{header}");
    assert!(copy.join("history/format.txt").is_file());

    // Decision 0006's names, arrived at over what travelled: running
    // `arrange` in the copy has nothing to move.
    let arranged = out(&copy, &["arrange", "-n"]);
    assert!(
        !arranged.contains(" -> "),
        "the copy was written under names its own `arrange` disagrees with:\n{arranged}"
    );
    let revisions = walk(&copy.join("history/revisions"));
    assert!(
        revisions
            .iter()
            .any(|name| name.contains("Start a journal.rev.txt")),
        "the copy's files are not the readable ones: {revisions:?}"
    );
    assert!(
        walk(&copy.join("history/operations"))
            .iter()
            .any(|name| name.ends_with("Start a journal/notes/photo.png")),
        "decision 0018 files a path as a path, and the copy did not"
    );
}

#[test]
fn an_export_at_a_past_revision_ends_there() {
    let origin = repository("past");
    write(&origin, "notes.md", "one\n");
    out(&origin, &["record", "-m", "First"]);
    write(&origin, "notes.md", "one\ntwo\n");
    out(&origin, &["record", "-m", "Second"]);
    let second = head_of(&origin);
    write(&origin, "notes.md", "one\ntwo\nthree\n");
    out(&origin, &["record", "-m", "Third"]);

    let copy = scratch("past-copy").join("journal");
    out(&origin, &["export", &copy.to_string_lossy(), &second]);

    // Decision 0042: an export's history *ends* at the target, so the target
    // is its head and the folder and the store agree. No position is written
    // anywhere, which is why this is not the checkout-to-the-past 0030 still
    // refuses in place.
    let log = out(&copy, &["log"]);
    assert!(log.contains("Second"), "{log}");
    assert!(log.contains("First"), "{log}");
    assert!(!log.contains("Third"), "a later revision travelled: {log}");
    assert_eq!(head_of(&copy), second);
    assert_eq!(digests(&copy).len(), 2);
    assert_eq!(
        fs::read_to_string(copy.join("notes.md")).expect("the copy's file"),
        "one\ntwo\n"
    );
    assert!(out(&copy, &["update"]).contains("already holds"));
    assert!(out(&copy, &["check"]).ends_with("nothing to report\n"));
}

#[test]
fn forgetting_travels_and_what_it_destroyed_does_not() {
    let origin = repository("forgetting");
    write(&origin, "notes.md", "public\nthe secret\n");
    out(&origin, &["record", "-m", "A secret"]);
    let target = head_of(&origin);
    out(&origin, &["forget", &target, "notes.md", "--lines", "2"]);

    let copy = scratch("forgetting-copy").join("journal");
    let said = out(&origin, &["export", &copy.to_string_lossy()]);
    assert!(said.contains("exported 1 forgetting documents"), "{said}");

    // Decision 0014 always travels: the stand-in is what the copy reads, and
    // the destroyed text is nowhere in it.
    assert_eq!(
        out(&copy, &["cat", "head", "notes.md"]),
        "public\n\\ forgotten\n"
    );
    for file in walk(&copy.join("history")) {
        let bytes = fs::read(copy.join("history").join(&file)).expect("a stored file");
        assert!(
            !String::from_utf8_lossy(&bytes).contains("the secret"),
            "the copy holds the forgotten text, in {file}"
        );
    }

    // The copy reads exactly as the origin does, note and all: a destroyed
    // document with a stand-in is a recorded fact carried out, not a fault.
    let here = out(&origin, &["check"]);
    let there = out(&copy, &["check"]);
    assert!(there.contains("no errors, 1 note"), "{there}");
    assert!(here.contains("whose bytes were destroyed"), "{here}");
    assert!(there.contains("whose bytes were destroyed"), "{there}");
}

#[test]
fn a_merge_travels_with_the_documents_its_resolution_quotes() {
    // Decision 0032: a resolution is not self-contained prose — its `keep`
    // lines quote items of documents it names — so a closure that stopped at
    // the `edit` lines would ship a merge nothing could assemble.
    let origin = repository("merged");
    write(&origin, "notes.md", "one\ntwo\nthree\n");
    out(&origin, &["record", "-m", "Common root"]);
    let root = head_of(&origin);
    write(&origin, "notes.md", "MINE\ntwo\nthree\n");
    out(&origin, &["record", "-m", "Mine", "--onto", &root]);
    let mine = head_of(&origin);
    write(&origin, "notes.md", "one\ntwo\nTHEIRS\n");
    out(&origin, &["record", "-m", "Theirs", "--onto", &root]);
    let theirs = digests(&origin)
        .into_iter()
        .find(|digest| *digest != mine && *digest != root)
        .expect("the other head");

    out(&origin, &["merge", &mine, &theirs]);
    out(
        &origin,
        &[
            "record", "--merge", &mine, "--merge", &theirs, "-m", "Joined",
        ],
    );
    let joined = fs::read_to_string(origin.join("notes.md")).expect("the merged file");

    let copy = scratch("merged-copy").join("journal");
    out(&origin, &["export", &copy.to_string_lossy()]);
    assert!(out(&copy, &["check"]).ends_with("nothing to report\n"));
    assert_eq!(digests(&origin), digests(&copy));
    assert_eq!(out(&copy, &["cat", "head", "notes.md"]), joined);
    assert_eq!(
        fs::read_to_string(copy.join("notes.md")).expect("the copy's file"),
        joined
    );
}

#[test]
fn divergence_refuses_without_a_target_and_exports_with_one() {
    let origin = repository("divergent");
    write(&origin, "notes.md", "common\n");
    out(&origin, &["record", "-m", "Common root"]);
    let root = head_of(&origin);
    write(&origin, "notes.md", "common\nleft\n");
    out(&origin, &["record", "-m", "Left", "--onto", &root]);
    write(&origin, "notes.md", "common\nright\n");
    out(&origin, &["record", "-m", "Right", "--onto", &root]);

    // Decision 0042: an export of "the history" when there are two is a
    // choice somebody has to make out loud — refused with the heads
    // described, exactly as every other command refuses divergence.
    let copy = scratch("divergent-copy").join("journal");
    let complaint = refused(&origin, &["export", &copy.to_string_lossy()]);
    assert!(complaint.contains("2 heads"), "{complaint}");
    assert!(complaint.contains("Left"), "{complaint}");
    assert!(complaint.contains("Right"), "{complaint}");
    assert!(!copy.exists(), "a refused export wrote a directory");

    let left = digests(&origin)
        .into_iter()
        .find(|digest| {
            out(&origin, &["show", digest]).contains("\nLeft")
                || out(&origin, &["show", digest]).ends_with("Left")
        })
        .expect("the left head");
    out(&origin, &["export", &copy.to_string_lossy(), &left]);
    let log = out(&copy, &["log"]);
    assert!(log.contains("Left"), "{log}");
    assert!(!log.contains("Right"), "the other line of work travelled");
}

#[test]
fn an_export_refuses_a_destination_that_already_holds_something() {
    let origin = repository("occupied");
    write(&origin, "notes.md", "one\n");
    out(&origin, &["record", "-m", "First"]);

    let copy = scratch("occupied-copy").join("journal");
    fs::create_dir_all(&copy).expect("a directory");
    fs::write(copy.join("something.txt"), "already here\n").expect("a file");

    let complaint = refused(&origin, &["export", &copy.to_string_lossy()]);
    assert!(complaint.contains("already holds something"), "{complaint}");
    assert!(complaint.contains("`receive`"), "{complaint}");
    assert_eq!(walk(&copy), ["something.txt".to_owned()]);

    // An empty directory is not something: `mkdir` and then export is
    // ordinary, and refusing it would be pedantry.
    let empty = scratch("occupied-empty").join("journal");
    fs::create_dir_all(&empty).expect("a directory");
    out(&origin, &["export", &empty.to_string_lossy()]);
    assert!(empty.join("notes.md").is_file());
}

#[test]
fn an_export_refuses_a_store_check_calls_broken() {
    let origin = repository("broken");
    write(&origin, "notes.md", "one\n");
    out(&origin, &["record", "-m", "First"]);

    // A name that claims a digest and states the wrong one: the loader
    // ignores names entirely, so this is a store that opens and does not
    // check out — which is the state the refusal exists for.
    let revisions = origin.join("history/revisions");
    let held = fs::read_dir(&revisions)
        .expect("the directory")
        .filter_map(Result::ok)
        .map(|entry| entry.path())
        .flat_map(|path| {
            if path.is_dir() {
                fs::read_dir(&path)
                    .expect("the month")
                    .filter_map(Result::ok)
                    .map(|entry| entry.path())
                    .collect()
            } else {
                vec![path]
            }
        })
        .find(|path| path.to_string_lossy().ends_with(".rev.txt"))
        .expect("a revision document");
    fs::rename(&held, revisions.join(format!("{}.rev.txt", "0".repeat(64)))).expect("renaming");

    let copy = scratch("broken-copy").join("journal");
    let complaint = refused(&origin, &["export", &copy.to_string_lossy()]);
    assert!(complaint.contains("does not pass `check`"), "{complaint}");
    assert!(!copy.exists(), "a copy of a fault is two faults");
}

#[test]
fn receiving_the_origin_catches_a_copy_up() {
    let origin = repository("pull");
    write(&origin, "notes.md", "one\n");
    out(&origin, &["record", "-m", "First"]);

    let copy = scratch("pull-copy").join("journal");
    out(&origin, &["export", &copy.to_string_lossy()]);

    // Decision 0042: an export is a replica, so `receive` is its pull. It
    // shares every revision with its origin, which is 0029's relatedness on
    // the first try — no `--join-unrelated` anywhere.
    write(&origin, "notes.md", "one\ntwo\n");
    out(&origin, &["record", "-m", "Second"]);
    let received = out(&copy, &["receive", &origin.to_string_lossy()]);
    assert!(received.contains("received 1 revisions"), "{received}");
    out(&copy, &["update"]);
    assert_eq!(
        fs::read_to_string(copy.join("notes.md")).expect("the copy's file"),
        "one\ntwo\n"
    );
    assert_eq!(digests(&origin), digests(&copy));
    assert!(out(&copy, &["check"]).ends_with("nothing to report\n"));
}

#[test]
fn a_copy_keeps_a_supersedes_line_whose_other_end_it_does_not_hold() {
    // Decision 0042's own open question, settled against `check`'s existing
    // rules rather than new ones. An amendment supersedes a revision that is
    // not its ancestor, so exporting the amendment leaves that edge dangling
    // — and every rule the format already has says that is ordinary:
    //
    //   * `History::superseded` is explicit that a superseded revision need
    //     not be present locally, because the successor carries the evidence;
    //   * `check` has no finding for the missing predecessor;
    //   * head discovery — heads by parent edge, less what anything
    //     supersedes — reads the dangling edge exactly as it reads a
    //     delivered one.
    //
    // So the closure is parents and nothing else. If any of the three ever
    // stops being true, this is the test that says so.
    let origin = repository("supersedes");
    write(&origin, "notes.md", "one\n");
    out(&origin, &["record", "-m", "First"]);
    write(&origin, "notes.md", "one\ntwo\n");
    out(&origin, &["record", "-m", "Second"]);
    let superseded = head_of(&origin);
    write(&origin, "notes.md", "one\ntwo three\n");
    out(&origin, &["amend", "-m", "Second amended"]);
    let amendment = head_of(&origin);

    let copy = scratch("supersedes-copy").join("journal");
    out(&origin, &["export", &copy.to_string_lossy()]);

    let store = Store::open(copy.join("history")).expect("the copy opens");
    let held: BTreeSet<String> = store.iter().map(|(id, _)| id.abbreviate(8)).collect();
    assert!(held.contains(&amendment), "the amendment travelled");
    assert!(
        !held.contains(&superseded),
        "the superseded revision travelled: the closure chased a supersedes edge"
    );

    // The edge is there, and its other end is not.
    let history = store.history();
    let dangling: Vec<_> = history
        .superseded()
        .into_iter()
        .filter(|id| store.get(id).is_none())
        .collect();
    assert_eq!(dangling.len(), 1, "exactly one edge should dangle");
    assert_eq!(dangling[0].abbreviate(8), superseded);

    // And nothing minds. `check` reports nothing at all — not an error, not
    // even a note about it — and head discovery still names the amendment.
    let report = Store::check(store.root());
    assert!(
        report.is_ok(),
        "check calls a dangling supersedes edge broken"
    );
    assert!(
        report.findings().is_empty(),
        "check has something to say about it: {:?}",
        report
            .findings()
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>()
    );
    let heads: BTreeSet<_> = history
        .heads()
        .difference(&history.superseded())
        .map(|id| id.abbreviate(8))
        .collect();
    assert_eq!(heads, BTreeSet::from([amendment.clone()]));
    assert_eq!(head_of(&copy), amendment);
    assert!(out(&copy, &["update"]).contains("already holds"));
}

#[test]
fn the_copy_states_the_version_its_own_documents_come_to() {
    // Decision 0004, working in the other direction: the header states the
    // lowest version that expresses what the store holds, and what the copy
    // holds is not what the store it came from holds. The corpus is entirely
    // version 0 and `init` writes version 1, so a store that is a version 1
    // header over version 0 documents exports as the version 0 store it
    // actually is.
    let origin = repository("version");
    let corpus = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/corpus/tree");
    for (from, into) in [("revisions", "revisions"), ("operations", "operations")] {
        for entry in fs::read_dir(corpus.join(from))
            .expect("the corpus")
            .flatten()
        {
            let name = entry.file_name();
            fs::copy(entry.path(), origin.join("history").join(into).join(&name))
                .expect("copying a corpus file");
        }
    }
    assert_eq!(
        fs::read_to_string(origin.join("history/historica.txt"))
            .expect("a header")
            .lines()
            .next(),
        Some("historica-v1")
    );

    let copy = scratch("version-copy").join("journal");
    let said = out(&origin, &["export", &copy.to_string_lossy()]);
    assert!(said.contains("stating historica-v0"), "{said}");
    assert_eq!(
        fs::read_to_string(copy.join("history/historica.txt"))
            .expect("the copy's header")
            .lines()
            .next(),
        Some("historica-v0")
    );
    assert!(out(&copy, &["check"]).ends_with("nothing to report\n"));
}

#[test]
fn a_dry_run_and_the_export_describe_the_same_copy() {
    let origin = furnished("dry-run");
    let copy = scratch("dry-run-copy").join("journal");

    let planned = out(&origin, &["export", &copy.to_string_lossy(), "--dry-run"]);
    assert!(!copy.exists(), "a dry run wrote a copy");
    assert!(planned.contains("would export 2 revisions"), "{planned}");
    assert!(planned.contains("write   notes.md"), "{planned}");
    assert!(planned.contains("write   notes/photo.png"), "{planned}");

    let done = out(&origin, &["export", &copy.to_string_lossy()]);
    for line in planned.lines() {
        let said = line
            .trim_start_matches("would export ")
            .trim_start_matches("would make ");
        if line.starts_with("would export ") {
            assert!(done.contains(&format!("exported {said}")), "{done}");
        }
    }
    assert!(done.contains("wrote   notes.md"), "{done}");
    assert!(done.contains("wrote   notes/photo.png"), "{done}");
}
