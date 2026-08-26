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

use historica::fs::Disk;
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

/// A repository with two revisions, a picture, two bookmarks on decision
/// 0062's two axes, two rules on decision 0051's, and an unrecorded file —
/// one of everything the copy has to decide about.
fn furnished(test: &str) -> PathBuf {
    let directory = repository(test);
    write(&directory, "notes.md", "one\n");
    fs::create_dir_all(directory.join("notes")).expect("a directory");
    fs::write(directory.join("notes/photo.png"), [0u8, 1, 2, 255]).expect("a picture");
    out(&directory, &["record", "-m", "Start a journal"]);
    write(&directory, "notes.md", "one\ntwo\n");
    out(&directory, &["record", "-m", "A second thought"]);

    out(&directory, &["name", "main", "head"]);
    // The name is the leak the rule below could not reach: the revisions say
    // nothing about the client, because the files that would have are not
    // recorded.
    out(
        &directory,
        &["name", "--private", "fix-acme-layoffs", "head"],
    );
    out(&directory, &["skip", "--name", "*.tmp"]);
    out(&directory, &["skip", "--private", "clients/acme-layoffs/"]);
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

    // Decision 0062 supersedes the bookmarks half of 0042's sentence on 0051's
    // argument: the shared bookmark travels, and the private one does not.
    let names = out(&copy, &["names"]);
    assert!(
        names.contains("main"),
        "the shared bookmark stayed behind: {names}"
    );
    assert!(
        !names.contains("acme"),
        "a private bookmark's name reached the copy: {names}"
    );
    assert!(said.contains("exported 1 bookmarks"), "{said}");
    assert!(said.contains("held back 1 private bookmarks"), "{said}");
    // Decision 0051: the shared rules travel and the private ones do not. A
    // copy without `skip-name *.tmp` is a copy whose first `record` offers to
    // record the recipient's editor droppings, which is the failure 0011 wrote
    // rules to prevent, arriving because the rules did not.
    assert!(said.contains("exported 1 rules"), "{said}");
    assert!(said.contains("held back 1 private rules"), "{said}");
    let rules: Vec<String> = walk(&copy.join("history/skipped"))
        .into_iter()
        .filter_map(|label| fs::read_to_string(copy.join("history/skipped").join(&label)).ok())
        .filter(|text| !text.starts_with('#'))
        .collect();
    assert_eq!(
        rules,
        vec!["skip-name *.tmp\n".to_owned()],
        "the copy states the shared rule and only that"
    );
    // And it says so, as a rule the copy can act on: the recipient's own
    // `.tmp` files stay out of their history.
    write(&copy, "theirs.tmp", "an editor's dropping\n");
    assert!(!out(&copy, &["status"]).contains("theirs.tmp"));
    // A cache is nobody's, so none of the exporter's travels. What the copy
    // has in `cache/` is what it wrote for itself on the way: the note `init`
    // leaves, the catalogue saying where in its *own* `operations/` each
    // digest sits, decision 0043's catalogue of its *own* folder, and 0058's
    // copy of its *own* revision documents. A cached state is a file named by
    // a digest, and there are none — the copy has read nobody's files.
    let cache = walk(&copy.join("history/cache"));
    assert!(
        cache.iter().all(|name| {
            name == "README.txt"
                || name == "operations.txt"
                || name == "working.txt"
                || name == "revisions.txt"
        }),
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
    let held: BTreeSet<String> = store.revisions().map(|(id, _)| id.abbreviate(8)).collect();
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
        .filter(|id| !store.holds(id))
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
fn the_copy_carries_the_header_that_makes_it_a_store() {
    // Decision 0021: the copy explains itself to whoever opens it, so its
    // header comes from `init` — the format's one spelling, and the note
    // under it — rather than from the store it left.
    let origin = repository("version");
    let corpus = Path::new(env!("CARGO_MANIFEST_DIR")).join("../tests/corpus/tree");
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

    let copy = scratch("version-copy").join("journal");
    out(&origin, &["export", &copy.to_string_lossy()]);
    assert_eq!(
        fs::read_to_string(copy.join("history/historica.txt"))
            .expect("the copy's header")
            .lines()
            .next(),
        Some("historica")
    );
    assert!(out(&copy, &["check"]).ends_with("nothing to report\n"));
}

/// Decision 0053: a reserved directory travels by the class its reservation
/// declares, and export never learns whose it is. `claims/` travels and
/// unions, `trust/` never crosses a boundary, and the claims travel **whole**
/// rather than filtered to the ones naming exported revisions — which is what
/// the second claim here pins, since the copy's history stops before the
/// revision it vouches for.
#[test]
fn a_reserved_directory_travels_by_the_class_it_declares() {
    let origin = repository("reserved");
    write(&origin, "notes.md", "one\n");
    out(&origin, &["record", "-m", "First"]);
    let first = head_of(&origin);
    write(&origin, "notes.md", "one\ntwo\n");
    out(&origin, &["record", "-m", "Second"]);
    let second = head_of(&origin);

    // What historica-sign leaves in the two directories 0046 reserved. None
    // of it is read here or anywhere else in this crate, which is the point:
    // the bytes below are opaque, and the class is the whole of what export
    // consults.
    write(
        &origin,
        "history/claims/over-the-first.claim.txt",
        &format!("claim-0\nrevision {first}…\nrole author\n"),
    );
    write(
        &origin,
        "history/claims/over-the-first.claim.txt.minisig",
        "untrusted comment: signature from minisign secret key\n",
    );
    write(
        &origin,
        "history/claims/over-the-second.claim.txt",
        &format!("claim-0\nrevision {second}…\nrole author\n"),
    );
    write(
        &origin,
        "history/trust/adam.txt",
        "trust-0\nkey RWTd8LRCGA9i53mlYecO4IzT51TGPpvWucNSCh1CBM0QTaLn73Y7GFO3\n",
    );
    // Decision 0046's tolerance, unchanged: historica reads none of this and
    // reports none of it.
    assert!(out(&origin, &["check"]).ends_with("nothing to report\n"));

    let copy = scratch("reserved-copy").join("journal");
    let said = out(&origin, &["export", &copy.to_string_lossy(), &first]);
    assert!(
        said.contains("carried 3 files another tool wrote"),
        "{said}"
    );

    // Every file of the travelling directory, under the names it had, since
    // the names are what makes it union wherever the copy lands next.
    assert_eq!(
        walk(&copy.join("history/claims")),
        vec![
            "over-the-first.claim.txt".to_owned(),
            "over-the-first.claim.txt.minisig".to_owned(),
            "over-the-second.claim.txt".to_owned(),
        ]
    );
    assert_eq!(
        fs::read_to_string(copy.join("history/claims/over-the-second.claim.txt"))
            .expect("the claim over a revision the copy does not hold"),
        format!("claim-0\nrevision {second}…\nrole author\n"),
        "the copy holds the claim's bytes, byte for byte"
    );
    // Whole rather than filtered: the copy's history ends at the first
    // revision, and the claim over the second travelled anyway. A claim
    // covers everything its revision descends from (0046), so the claim over
    // a later head is the one that vouches for this copy.
    let log = out(&copy, &["log"]);
    assert!(!log.contains("Second"), "a later revision travelled: {log}");

    // Local only, in the one direction an export can be wrong in.
    assert!(
        !copy.join("history/trust").exists(),
        "0046's trust policy travelled: a store seeded with another's keys \
         verifies another's history"
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

// Decision 0052: exporting onto a copy this store already made.
//
// The claim under test throughout this half is that the copy is *diffed*
// rather than rebuilt, and that the diff runs in both directions. Every test
// below is one of the three outcomes a file can have — written, left, or
// withdrawn — and the withdrawals are the half worth the most, since a
// published copy that only ever grew would be a permanent record of
// everything the origin ever held.

/// A repository with one revision, exported to `copy`, ready to be exported
/// onto a second time.
fn published(test: &str) -> (PathBuf, PathBuf) {
    let origin = repository(test);
    write(&origin, "notes.md", "one\n");
    out(&origin, &["record", "-m", "First"]);
    let copy = scratch(&format!("{test}-copy")).join("journal");
    out(&origin, &["export", &copy.to_string_lossy()]);
    (origin, copy)
}

/// Every revision digest the store at this repository holds.
fn held(repository: &Path) -> BTreeSet<String> {
    let store = Store::open(repository.join("history")).expect("the store opens");
    store.revisions().map(|(id, _)| id.to_string()).collect()
}

#[test]
fn a_second_export_adds_exactly_what_the_copy_lacked() {
    let (origin, copy) = published("again");
    let before = walk(&copy.join("history/revisions"));

    write(&origin, "notes.md", "one\ntwo\n");
    out(&origin, &["record", "-m", "Second"]);
    let said = out(&origin, &["export", &copy.to_string_lossy()]);

    // The difference and nothing else: one revision, the document it edited,
    // and no payload, because the file it edits arrived with the first export
    // and is still exactly where that export put it.
    assert!(said.contains("exported 1 revisions"), "{said}");
    assert!(said.contains("exported 1 operation documents"), "{said}");
    assert!(said.contains("exported 0 payloads"), "{said}");
    assert!(
        !said.contains("withdrew"),
        "an addition withdrew something: {said}"
    );
    assert!(said.contains("updated the copy of"), "{said}");

    // Files are added and nothing moves, which is what makes a fetch in
    // flight during an addition-only run work from a subset rather than miss.
    let after = walk(&copy.join("history/revisions"));
    assert!(
        before.iter().all(|name| after.contains(name)),
        "a file the first export wrote moved: {before:?} then {after:?}"
    );
    assert_eq!(after.len(), before.len() + 1);

    assert_eq!(held(&origin), held(&copy));
    assert_eq!(digests(&origin), digests(&copy));
    assert_eq!(
        fs::read_to_string(copy.join("notes.md")).expect("the copy's file"),
        "one\ntwo\n",
        "the folder did not catch up, which is decision 0030's half"
    );
    assert!(out(&copy, &["check"]).ends_with("nothing to report\n"));
}

#[test]
fn a_forget_at_the_origin_destroys_the_bytes_in_the_copy() {
    let origin = repository("published-forget");
    write(&origin, "notes.md", "public\nthe secret\n");
    out(&origin, &["record", "-m", "A secret"]);
    let target = head_of(&origin);
    let copy = scratch("published-forget-copy").join("journal");
    out(&origin, &["export", &copy.to_string_lossy()]);
    assert!(
        walk(&copy.join("history"))
            .iter()
            .any(|file| fs::read(copy.join("history").join(file))
                .is_ok_and(|bytes| String::from_utf8_lossy(&bytes).contains("the secret"))),
        "the first export did not publish the text this test is about"
    );

    // Decision 0014's promise is that the bytes are gone, and the one copy
    // that is world-readable is the copy where that has to be true.
    out(&origin, &["forget", &target, "notes.md", "--lines", "2"]);
    let said = out(&origin, &["export", &copy.to_string_lossy()]);
    assert!(said.contains("exported 1 forgetting documents"), "{said}");
    assert!(said.contains("destroyed 1 forgotten originals"), "{said}");

    for file in walk(&copy.join("history")) {
        let bytes = fs::read(copy.join("history").join(&file)).expect("a stored file");
        assert!(
            !String::from_utf8_lossy(&bytes).contains("the secret"),
            "the copy still holds the forgotten text, in {file}"
        );
    }
    // And the folder too, which is the half a `wget -r` of the copy takes.
    assert_eq!(
        fs::read_to_string(copy.join("notes.md")).expect("the copy's file"),
        "public\n\\ forgotten\n"
    );
    assert_eq!(
        out(&copy, &["cat", "head", "notes.md"]),
        "public\n\\ forgotten\n"
    );
    assert!(out(&copy, &["check"]).contains("no errors, 1 note"));
}

#[test]
fn what_a_prune_removed_at_the_origin_is_gone_from_the_copy() {
    let origin = repository("published-prune");
    write(&origin, "notes.md", "one\n");
    out(&origin, &["record", "-m", "First"]);
    write(&origin, "notes.md", "one\ntwo\n");
    out(&origin, &["record", "-m", "Second"]);
    let copy = scratch("published-prune-copy").join("journal");
    out(&origin, &["export", &copy.to_string_lossy()]);
    let superseded = head_of(&origin);

    // An amendment leaves the superseded revision behind, and `prune` is what
    // deletes it. Both reach the copy by the same mechanism — the set is the
    // target's ancestry and the copy is diffed against it — which is the
    // whole of what decision 0052 means by a prune propagating.
    write(&origin, "notes.md", "one\ntwo three\n");
    out(&origin, &["amend", "-m", "Second amended"]);
    let pruned = out(&origin, &["prune"]);
    assert!(pruned.contains("removed history/revisions"), "{pruned}");

    let said = out(&origin, &["export", &copy.to_string_lossy()]);
    assert!(said.contains("withdrew"), "{said}");
    assert_eq!(
        held(&origin),
        held(&copy),
        "the copy is not the replica of a pruned store"
    );
    let log = out(&copy, &["log"]);
    assert!(
        !log.contains("\n    Second\n"),
        "the pruned revision survived: {log}"
    );
    assert!(
        !digests(&copy).contains(&superseded),
        "the copy still holds a revision the origin deleted"
    );
    assert!(out(&copy, &["check"]).ends_with("nothing to report\n"));
}

#[test]
fn a_target_moved_to_an_ancestor_withdraws_what_it_left_behind() {
    let origin = repository("published-back");
    write(&origin, "notes.md", "one\n");
    out(&origin, &["record", "-m", "First"]);
    let first = head_of(&origin);
    write(&origin, "notes.md", "one\ntwo\n");
    fs::create_dir_all(origin.join("notes")).expect("a directory");
    fs::write(origin.join("notes/photo.png"), [0u8, 1, 2, 255]).expect("a picture");
    out(&origin, &["record", "-m", "Second"]);

    let copy = scratch("published-back-copy").join("journal");
    out(&origin, &["export", &copy.to_string_lossy()]);
    assert!(copy.join("notes/photo.png").is_file());

    // The origin still holds every one of these. It is the *published set*
    // that shrank, and the copy is what the set says rather than a record of
    // what the set has ever said.
    let said = out(&origin, &["export", &copy.to_string_lossy(), &first]);
    assert!(said.contains("withdrew 3 files"), "{said}");
    assert_eq!(digests(&copy), vec![first.clone()]);
    assert_eq!(
        fs::read_to_string(copy.join("notes.md")).expect("the copy's file"),
        "one\n"
    );
    assert!(
        !copy.join("notes/photo.png").exists(),
        "the folder still holds a file the published revision never had"
    );
    assert!(
        !walk(&copy.join("history/operations"))
            .iter()
            .any(|name| name.ends_with("photo.png")),
        "the payload nothing published names is still in the copy"
    );
    assert!(out(&copy, &["check"]).ends_with("nothing to report\n"));
    assert!(out(&copy, &["update"]).contains("already holds"));
}

#[test]
fn withdrawals_descend_so_that_no_revision_ever_outlives_its_bytes() {
    // The interruption invariant, pinned as the order it comes from: a
    // revision document leaves before the documents it names, and those
    // before the payloads. Cut the run short anywhere in that sequence and
    // the copy understates what is reachable, which is what a fetch and a
    // receive are both already built to meet. The rule files come last,
    // because they are nothing's ancestor.
    let origin = repository("descend");
    write(&origin, "notes.md", "one\n");
    out(&origin, &["record", "-m", "First"]);
    let first = head_of(&origin);
    write(&origin, "notes.md", "one\ntwo\n");
    fs::create_dir_all(origin.join("notes")).expect("a directory");
    fs::write(origin.join("notes/photo.png"), [0u8, 1, 2, 255]).expect("a picture");
    out(&origin, &["record", "-m", "Second"]);
    out(&origin, &["skip", "--name", "*.tmp"]);

    let copy = scratch("descend-copy").join("journal");
    out(&origin, &["export", &copy.to_string_lossy()]);

    // The rule stops travelling, so its file is withdrawn too.
    for label in walk(&origin.join("history/skipped")) {
        if label != "README.txt" {
            fs::remove_file(origin.join("history/skipped").join(label)).expect("dropping a rule");
        }
    }

    let store = Store::open(origin.join("history")).expect("the origin opens");
    let target = store
        .revisions()
        .map(|(id, _)| *id)
        .find(|id| id.to_string().starts_with(&first))
        .expect("the first revision");
    let plan = store
        .export_plan_onto(&Disk, &copy, &target)
        .expect("a plan onto the copy");

    let ranked: Vec<usize> = plan
        .withdraws()
        .iter()
        .map(|path| {
            let path = path.to_string_lossy().replace('\\', "/");
            match () {
                _ if path.starts_with("revisions/") => 0,
                _ if path.starts_with("skipped/") => 3,
                _ if path.ends_with(".ops.txt") => 1,
                _ => 2,
            }
        })
        .collect();
    assert_eq!(
        ranked,
        vec![0, 1, 2, 3],
        "the withdrawal order is not revisions, documents, payloads, rules: {:?}",
        plan.withdraws()
    );

    // And the plan is what the run acts on, so the two cannot disagree.
    let said = out(&origin, &["export", &copy.to_string_lossy(), &first]);
    assert!(said.contains("withdrew 4 files"), "{said}");
    assert!(out(&copy, &["check"]).ends_with("nothing to report\n"));
}

#[test]
fn a_copy_somebody_recorded_in_is_refused_and_told_to_receive() {
    let (origin, copy) = published("recorded-in");

    // Decision 0052: export assembles, and the machinery for combining two
    // histories is a command that exists and should be run in the other
    // direction first.
    write(&copy, "notes.md", "one\ntheirs\n");
    out(&copy, &["record", "-m", "Recorded in the copy"]);
    let complaint = refused(&origin, &["export", &copy.to_string_lossy()]);
    assert!(
        complaint.contains("which this store does not"),
        "{complaint}"
    );
    assert!(complaint.contains("`historica receive`"), "{complaint}");

    // And nothing was written: the refusal is decided before the copy is
    // touched, which is what makes a dry run of it worth anything.
    assert_eq!(
        fs::read_to_string(copy.join("notes.md")).expect("the copy's file"),
        "one\ntheirs\n"
    );
    let planned = refused(&origin, &["export", &copy.to_string_lossy(), "--dry-run"]);
    assert!(planned.contains("`historica receive`"), "{planned}");

    // The named remedy works, and then the export does.
    out(&origin, &["receive", &copy.to_string_lossy()]);
    let said = out(&origin, &["export", &copy.to_string_lossy()]);
    assert!(said.contains("updated the copy of"), "{said}");
    assert_eq!(held(&origin), held(&copy));
}

#[test]
fn an_export_refuses_a_directory_holding_a_store_of_its_own() {
    let origin = repository("stranger");
    write(&origin, "notes.md", "one\n");
    out(&origin, &["record", "-m", "First"]);

    let stranger = scratch("stranger-elsewhere").join("journal");
    fs::create_dir_all(&stranger).expect("a directory");
    assert!(run(&stranger, &["init"]).status.success());
    write(&stranger, "theirs.md", "somebody else's\n");
    out(&stranger, &["record", "-m", "Elsewhere"]);

    let complaint = refused(&origin, &["export", &stranger.to_string_lossy()]);
    assert!(complaint.contains("shares no revision"), "{complaint}");
    assert!(
        fs::read_to_string(stranger.join("theirs.md")).is_ok(),
        "a refused export wrote into somebody else's repository"
    );

    // A store that does not check out is refused as its own thing, because a
    // copy built on a fault is two faults wherever the fault is.
    let broken = scratch("stranger-broken").join("journal");
    out(&origin, &["export", &broken.to_string_lossy()]);
    fs::write(
        broken.join("history/revisions/nonsense.rev.txt"),
        "not a revision\n",
    )
    .expect("breaking the copy");
    let complaint = refused(&origin, &["export", &broken.to_string_lossy()]);
    assert!(complaint.contains("does not pass `check`"), "{complaint}");
}

#[test]
fn a_rule_the_origin_made_private_is_withdrawn_from_the_copy() {
    let origin = repository("rule-withdrawn");
    write(&origin, "notes.md", "one\n");
    out(&origin, &["record", "-m", "First"]);
    out(&origin, &["skip", "--name", "*.tmp"]);
    let copy = scratch("rule-withdrawn-copy").join("journal");
    out(&origin, &["export", &copy.to_string_lossy()]);
    let stated = |repository: &Path| -> Vec<String> {
        walk(&repository.join("history/skipped"))
            .into_iter()
            .filter_map(|label| {
                fs::read_to_string(repository.join("history/skipped").join(&label)).ok()
            })
            .filter(|text| !text.starts_with('#'))
            .collect()
    };
    assert_eq!(stated(&copy), vec!["skip-name *.tmp\n".to_owned()]);

    // Decision 0051's travel axis at the one boundary that can be crossed
    // twice: the rule the copy was given is not the exporter's to leave there
    // once its text has become the disclosure a `private` rule is about.
    for label in walk(&origin.join("history/skipped")) {
        if label != "README.txt" {
            fs::remove_file(origin.join("history/skipped").join(label)).expect("dropping a rule");
        }
    }
    out(&origin, &["skip", "--private", "--name", "*.tmp"]);

    let said = out(&origin, &["export", &copy.to_string_lossy()]);
    assert!(said.contains("held back 1 private rules"), "{said}");
    assert!(said.contains("withdrew 1 files"), "{said}");
    assert!(
        stated(&copy).is_empty(),
        "the copy still states a rule the origin made private: {:?}",
        stated(&copy)
    );
    for file in walk(&copy.join("history/skipped")) {
        let text = fs::read_to_string(copy.join("history/skipped").join(&file)).expect("a file");
        assert!(
            !text.lines().any(|line| line.starts_with("private")),
            "the private rule's text travelled, in {file}"
        );
    }
    assert!(out(&copy, &["check"]).ends_with("nothing to report\n"));

    // And the other direction: a shared rule the origin gains is written.
    out(&origin, &["skip", "--name", "*.bak"]);
    out(&origin, &["export", &copy.to_string_lossy()]);
    assert_eq!(stated(&copy), vec!["skip-name *.bak\n".to_owned()]);
}

#[test]
fn a_file_already_in_the_copy_is_never_renamed_to_make_room() {
    // Decision 0052, on decision 0041's collision suffix: two revisions
    // written on one day under one summary would both take the suffix in a
    // fresh export, and the one already published keeps the plain name it was
    // fetched under instead. Renaming a published file breaks a fetch in
    // flight for no gain.
    let origin = repository("collision");
    write(&origin, "notes.md", "one\n");
    out(&origin, &["record", "-m", "Note"]);
    let copy = scratch("collision-copy").join("journal");
    out(&origin, &["export", &copy.to_string_lossy()]);
    let published: Vec<String> = walk(&copy.join("history/revisions"));
    assert_eq!(published.len(), 1);
    assert!(published[0].ends_with("Note.rev.txt"), "{published:?}");

    write(&origin, "notes.md", "one\ntwo\n");
    out(&origin, &["record", "-m", "Note"]);
    out(&origin, &["export", &copy.to_string_lossy()]);

    let after = walk(&copy.join("history/revisions"));
    assert_eq!(after.len(), 2, "{after:?}");
    assert!(
        after.contains(&published[0]),
        "the published file was renamed: {published:?} became {after:?}"
    );
    assert!(
        after
            .iter()
            .any(|name| name != &published[0] && name.contains("Note ")),
        "the newcomer did not take the collision suffix: {after:?}"
    );
    assert!(out(&copy, &["check"]).ends_with("nothing to report\n"));

    // The drift decision 0052 accepts, stated out loud: a fresh export of the
    // same history gives *both* revisions the suffix, because it resolves the
    // collision against a set that arrived all at once.
    let fresh = scratch("collision-fresh").join("journal");
    out(&origin, &["export", &fresh.to_string_lossy()]);
    assert!(
        walk(&fresh.join("history/revisions"))
            .iter()
            .all(|name| !name.ends_with("Note.rev.txt")),
        "a fresh export gave one of them the plain name after all"
    );
}

#[test]
fn a_bookmark_the_origin_made_private_is_withdrawn_from_the_copy() {
    let (origin, copy) = published("name-withdrawn");
    out(&origin, &["name", "acme-layoffs", "head"]);
    out(&origin, &["export", &copy.to_string_lossy()]);
    assert!(out(&copy, &["names"]).contains("acme-layoffs"));

    // Decision 0062 at the boundary decision 0052 makes crossable twice. The
    // name the copy was given is not the exporter's to leave in a
    // world-readable directory once it has become the disclosure the axis is
    // about — and an export that only ever added would publish a permanent
    // record of every name the origin ever had, which is 0052's own argument
    // for withdrawal.
    let said = out(&origin, &["name", "--private", "acme-layoffs", "head"]);
    assert!(said.contains("(private)"), "{said}");

    let said = out(&origin, &["export", &copy.to_string_lossy()]);
    assert!(said.contains("held back 1 private bookmarks"), "{said}");
    assert!(said.contains("withdrew 1 files"), "{said}");
    let names = out(&copy, &["names"]);
    assert!(!names.contains("acme-layoffs"), "{names}");
    assert!(
        !copy.join("history/names/acme-layoffs.txt").exists(),
        "the file outlived the bookmark"
    );
    assert!(out(&copy, &["check"]).ends_with("nothing to report\n"));
}

/// Decision 0071: a bookmark's name may have directories in it, and the copy
/// gets the name rather than the leaf. The withdrawal is the half worth
/// testing end to end — an empty `names/feature/` in a published copy says a
/// `feature/` bookmark is there when none is.
#[test]
fn a_nested_bookmark_travels_and_takes_its_directory_when_it_goes() {
    let (origin, copy) = published("name-nested");
    out(&origin, &["name", "feature/acme-layoffs", "head"]);
    out(&origin, &["name", "feature/other", "head"]);
    out(&origin, &["export", &copy.to_string_lossy()]);

    let names = out(&copy, &["names"]);
    assert!(names.contains("feature/acme-layoffs"), "{names}");
    assert!(
        copy.join("history/names/feature/acme-layoffs.txt")
            .is_file(),
        "the name is the path below `names/`"
    );

    // One goes private, and the copy loses that file and keeps the directory
    // its sibling still needs.
    out(
        &origin,
        &["name", "--private", "feature/acme-layoffs", "head"],
    );
    out(&origin, &["export", &copy.to_string_lossy()]);
    assert!(!copy.join("history/names/feature/acme-layoffs.txt").exists());
    assert!(
        copy.join("history/names/feature").is_dir(),
        "the sibling holds the directory up"
    );

    // The last one goes, and the directory goes with it.
    out(&origin, &["name", "--private", "feature/other", "head"]);
    out(&origin, &["export", &copy.to_string_lossy()]);
    assert!(
        !copy.join("history/names/feature").exists(),
        "an empty `names/feature/` says a bookmark is there when none is"
    );
    assert!(copy.join("history/names").is_dir());
    assert!(out(&copy, &["check"]).ends_with("nothing to report\n"));
}

#[test]
fn a_bookmark_pointing_past_the_target_stays_behind() {
    let origin = repository("name-beyond");
    write(&origin, "notes.md", "one\n");
    out(&origin, &["record", "-m", "First"]);
    let first = out(&origin, &["log"]);
    let first = first
        .lines()
        .find_map(|line| line.split_whitespace().next())
        .expect("a revision")
        .to_owned();
    write(&origin, "notes.md", "one\ntwo\n");
    out(&origin, &["record", "-m", "Second"]);
    out(&origin, &["name", "main", "head"]);
    out(&origin, &["name", "start", &first]);

    // Decision 0062: an export never manufactures a finding the origin did not
    // have. `main` names a change the copy does not hold, which would open the
    // copy on a `DanglingBookmark` — and, under 0052, name for good the change
    // that unexported work ends at, which is the disclosure the axis exists to
    // govern arriving through the spelling that is supposed to be safe.
    let copy = scratch("name-beyond-copy").join("journal");
    let said = out(&origin, &["export", &copy.to_string_lossy(), &first]);
    assert!(said.contains("exported 1 bookmarks"), "{said}");
    assert!(
        said.contains("left 1 bookmarks pointing past this target"),
        "{said}"
    );
    let names = out(&copy, &["names"]);
    assert!(names.contains("start"), "{names}");
    assert!(!names.contains("main"), "{names}");
    assert!(out(&copy, &["check"]).ends_with("nothing to report\n"));
}

#[test]
fn a_bookmark_made_in_the_copy_gives_way_to_the_origins() {
    let (origin, copy) = published("bookmarks");
    out(&copy, &["name", "theirs", "head"]);

    write(&origin, "notes.md", "one\ntwo\n");
    out(&origin, &["record", "-m", "Second"]);
    out(&origin, &["name", "mine", "head"]);
    out(&origin, &["export", &copy.to_string_lossy()]);

    // Decision 0062 reverses what 0052 said about this directory: the copy's
    // `names/` is the origin's output, so the origin's bookmark arrives and
    // one the copy made that the origin does not state goes. It has to be all
    // of them rather than only the ones a previous export wrote, because
    // nothing records which those were — and the alternative fails in the
    // direction this decision exists to prevent, leaving a name in a
    // world-readable copy after the origin made it `private`.
    let names = out(&copy, &["names"]);
    assert!(names.contains("mine"), "{names}");
    assert!(
        !names.contains("theirs"),
        "a bookmark the origin does not state stayed in the copy: {names}"
    );

    // `cache/` likewise: it is nobody's, and the copy's own is its own.
    let cache = walk(&copy.join("history/cache"));
    assert!(
        cache.iter().all(|name| {
            name == "README.txt"
                || name == "operations.txt"
                || name == "working.txt"
                || name == "revisions.txt"
        }),
        "the exporter's cache travelled: {cache:?}"
    );
    assert!(out(&copy, &["check"]).ends_with("nothing to report\n"));
}

#[test]
fn a_claim_the_origin_deleted_stays_in_the_published_copy() {
    // Decision 0054. `claims/` is `travels-and-unions`, and a union adds. A
    // name missing at the origin means "not yet arrived" rather than
    // "deleted", because deciding otherwise would be a merge rule over a
    // grammar 0046 promised historica would never learn — and because the one
    // directory built for several parties to write into is the one where an
    // absence at the origin is least likely to mean what mirroring would read
    // it as.
    let (origin, copy) = published("claims-union");
    write(
        &origin,
        "history/claims/over-the-first.claim.txt",
        "claim-0\nrole author\n",
    );
    let said = out(&origin, &["export", &copy.to_string_lossy()]);
    assert!(
        said.contains("carried 1 files another tool wrote"),
        "{said}"
    );

    // A second signer writes into the published copy, which is what the
    // directory is for.
    write(
        &copy,
        "history/claims/a-second-signer.claim.txt",
        "claim-0\nrole reviewer\n",
    );

    fs::remove_file(origin.join("history/claims/over-the-first.claim.txt")).expect("a deletion");
    write(
        &origin,
        "history/claims/over-the-first-again.claim.txt",
        "claim-0\nrole author\n",
    );
    let said = out(&origin, &["export", &copy.to_string_lossy()]);
    assert!(
        said.contains("carried 1 files another tool wrote"),
        "{said}"
    );

    assert_eq!(
        walk(&copy.join("history/claims")),
        vec![
            "a-second-signer.claim.txt".to_owned(),
            "over-the-first-again.claim.txt".to_owned(),
            "over-the-first.claim.txt".to_owned(),
        ],
        "an export withdrew a file it cannot read"
    );
    assert!(out(&copy, &["check"]).ends_with("nothing to report\n"));

    // A run that carries nothing new says nothing, rather than counting what
    // it offered.
    let said = out(&origin, &["export", &copy.to_string_lossy()]);
    assert!(!said.contains("another tool wrote"), "{said}");
}

#[test]
fn a_dry_run_of_an_update_names_what_would_leave_the_copy() {
    let origin = repository("update-dry-run");
    write(&origin, "notes.md", "one\n");
    out(&origin, &["record", "-m", "First"]);
    let first = head_of(&origin);
    write(&origin, "notes.md", "one\ntwo\n");
    out(&origin, &["record", "-m", "Second"]);
    let copy = scratch("update-dry-run-copy").join("journal");
    out(&origin, &["export", &copy.to_string_lossy()]);

    let planned = out(
        &origin,
        &["export", &copy.to_string_lossy(), &first, "--dry-run"],
    );
    assert!(planned.contains("would export 0 revisions"), "{planned}");
    assert!(
        planned.contains("would withdraw history/revisions/"),
        "{planned}"
    );
    assert!(planned.contains("would update the copy of"), "{planned}");
    assert_eq!(
        digests(&copy).len(),
        2,
        "a dry run withdrew something from the copy"
    );

    let done = out(&origin, &["export", &copy.to_string_lossy(), &first]);
    assert!(done.contains("exported 0 revisions"), "{done}");
    assert_eq!(
        done.matches("withdrew").count(),
        1,
        "the run and the dry run disagree about withdrawing: {done}"
    );
    assert!(
        done.contains(&format!(
            "withdrew {} files",
            planned.matches("would withdraw ").count()
        )),
        "the dry run named a different number of files than the run withdrew:\n{planned}\n{done}"
    );
}

// ── `--files-only`: the folder, and nothing under it ──────────────────────

/// A repository of two revisions, so that the past is a place to reach.
fn two_revisions(test: &str) -> (PathBuf, String, String) {
    let origin = repository(test);
    write(&origin, "notes.md", "one\n");
    out(&origin, &["record", "-m", "First"]);
    let root = digests(&origin).pop().expect("a root revision");
    write(&origin, "notes.md", "one\ntwo\n");
    out(&origin, &["record", "-m", "Second"]);
    let head = digests(&origin).first().expect("a head").clone();
    (origin, root, head)
}

#[test]
fn files_only_writes_the_folder_and_no_store() {
    let (origin, _, _) = two_revisions("files-only");
    let into = scratch("files-only-into").join("folder");

    let said = out(
        &origin,
        &["export", &into.to_string_lossy(), "--files-only"],
    );
    assert!(said.contains("wrote   notes.md"), "{said}");
    assert!(said.contains("no history beside it"), "{said}");

    assert_eq!(
        fs::read_to_string(into.join("notes.md")).unwrap(),
        "one\ntwo\n"
    );
    // The whole of what the flag means: there is no store under it, so nothing
    // there can be recorded into, fetched from or received.
    assert!(!into.join("history").exists(), "a store travelled");
    assert_eq!(walk(&into), vec!["notes.md".to_owned()]);
    assert!(!run(&into, &["log"]).status.success());
}

#[test]
fn files_only_reaches_a_revision_that_is_not_the_head() {
    let (origin, root, _) = two_revisions("files-only-past");
    let into = scratch("files-only-past-into").join("folder");

    out(
        &origin,
        &["export", &into.to_string_lossy(), &root, "--files-only"],
    );
    // The root's content rather than the head's, which is the question the
    // flag exists to answer cheaply.
    assert_eq!(fs::read_to_string(into.join("notes.md")).unwrap(), "one\n");
}

#[test]
fn the_folder_agrees_with_the_one_a_whole_export_writes() {
    // The contract that makes this a flag on `export` rather than a command of
    // its own: what it writes is what `export` writes, with the store left
    // out. A file of lines and a file of bytes, so decision 0017's two kinds
    // are both in the comparison.
    let (origin, _, _) = two_revisions("files-only-agrees");
    fs::write(origin.join("photo.png"), [0u8, 1, 2, 3]).expect("a picture");
    write(&origin, "under/deeper.md", "a file in a directory\n");
    out(&origin, &["record", "-m", "Third"]);

    let whole = scratch("files-only-agrees-whole").join("copy");
    let folder = scratch("files-only-agrees-folder").join("copy");
    out(&origin, &["export", &whole.to_string_lossy()]);
    out(
        &origin,
        &["export", &folder.to_string_lossy(), "--files-only"],
    );

    let mut theirs = walk(&whole);
    theirs.retain(|path| !path.starts_with("history/"));
    theirs.sort();
    let mut ours = walk(&folder);
    ours.sort();
    assert_eq!(ours, theirs, "the two folders hold different files");
    assert!(ours.len() >= 3, "the comparison is too thin: {ours:?}");
    for path in &ours {
        assert_eq!(
            fs::read(whole.join(path)).unwrap(),
            fs::read(folder.join(path)).unwrap(),
            "{path} differs between the two copies"
        );
    }
}

/// Decisions 0034 and 0040 arrive as themselves, which is the reason this goes
/// through `update` rather than writing the bytes out.
#[test]
#[cfg(unix)]
fn a_mode_and_a_link_arrive_in_a_files_only_copy() {
    use std::os::unix::fs::PermissionsExt as _;

    let (origin, _, _) = two_revisions("files-only-modes");
    write(&origin, "build.sh", "#!/bin/sh\necho hello\n");
    fs::set_permissions(origin.join("build.sh"), fs::Permissions::from_mode(0o755))
        .expect("making it runnable");
    std::os::unix::fs::symlink("notes.md", origin.join("current")).expect("a link");
    out(&origin, &["record", "-m", "Third"]);

    let folder = scratch("files-only-modes-into").join("copy");
    let said = out(
        &origin,
        &["export", &folder.to_string_lossy(), "--files-only"],
    );
    assert!(said.contains("mode"), "{said}");
    assert!(said.contains("linked"), "{said}");

    assert!(
        fs::symlink_metadata(folder.join("current"))
            .unwrap()
            .is_symlink(),
        "the link arrived as a plain file"
    );
    let mode = fs::metadata(folder.join("build.sh"))
        .unwrap()
        .permissions()
        .mode();
    assert!(
        mode & 0o111 != 0,
        "the runnable bit did not arrive: {mode:o}"
    );
}

#[test]
fn files_only_wants_a_directory_holding_nothing() {
    let (origin, _, _) = two_revisions("files-only-occupied");
    let into = scratch("files-only-occupied-into").join("folder");
    fs::create_dir_all(&into).expect("the directory");
    fs::write(into.join("theirs.txt"), "somebody's work\n").expect("their file");

    // Decision 0052 lets a whole export be written over a copy of this store,
    // because the copy's own history says what the last export put there. A
    // folder with no store beside it cannot answer that, so there is nothing
    // to diff and the destination has to be empty.
    let said = refused(
        &origin,
        &["export", &into.to_string_lossy(), "--files-only"],
    );
    assert!(said.contains("theirs.txt"), "{said}");
    assert!(said.contains("holding nothing"), "{said}");
    // And it left their file exactly where it was.
    assert_eq!(
        fs::read_to_string(into.join("theirs.txt")).unwrap(),
        "somebody's work\n"
    );
}

#[test]
fn a_files_only_dry_run_writes_nothing() {
    let (origin, _, _) = two_revisions("files-only-dry");
    let into = scratch("files-only-dry-into").join("folder");

    let said = out(
        &origin,
        &[
            "export",
            &into.to_string_lossy(),
            "--files-only",
            "--dry-run",
        ],
    );
    assert!(said.contains("write   notes.md"), "{said}");
    assert!(said.contains("would write the folder"), "{said}");
    assert!(walk(&into).is_empty(), "a dry run wrote something");
}
