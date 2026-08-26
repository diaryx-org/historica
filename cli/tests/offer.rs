//! `offer`, exercised as decisions 0048, 0052 and 0056 describe it.
//!
//! The claim under test throughout is that the manifest is a *listing*: every
//! file a fetch would take, at the path it is actually at, under the name of
//! the directory it will be fetched from — and nothing else the copy happens
//! to hold. So the assertions come in pairs here too, what is named and what
//! cannot be, and the second half is where the privacy 0051 and 0052 argued
//! for either survives or does not.

use std::collections::BTreeSet;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

use historica::format::digest;
use historica::store::OFFER_HEADER;

fn scratch(test: &str) -> PathBuf {
    let path = Path::new(env!("CARGO_TARGET_TMPDIR")).join(format!("offer-{test}"));
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

/// One line of a manifest, taken apart the way a fetcher takes it apart.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Line {
    kind: String,
    digest: String,
    forgets: String,
    path: String,
}

/// The manifest for a published copy, parsed.
///
/// Split from the left three times and no further, which is decision 0043's
/// convention read from the other side: the path is last, may hold spaces, and
/// nothing is escaped.
fn manifest(text: &str) -> (Vec<String>, Vec<Line>) {
    let mut lines = text.lines();
    assert_eq!(lines.next(), Some(OFFER_HEADER), "the header is the header");
    let mut heads = Vec::new();
    let mut entries = Vec::new();
    for line in lines {
        if let Some(head) = line.strip_prefix("head ") {
            assert!(
                entries.is_empty(),
                "a head line came after an entry: {line}"
            );
            heads.push(head.to_owned());
            continue;
        }
        let mut fields = line.splitn(4, ' ');
        let (Some(kind), Some(digest), Some(forgets), Some(path)) =
            (fields.next(), fields.next(), fields.next(), fields.next())
        else {
            panic!("a line with fewer than four fields: {line}");
        };
        entries.push(Line {
            kind: kind.to_owned(),
            digest: digest.to_owned(),
            forgets: forgets.to_owned(),
            path: path.to_owned(),
        });
    }
    (heads, entries)
}

/// A repository with one of everything a manifest has to decide about, and the
/// published copy of it.
fn published(test: &str) -> (PathBuf, PathBuf) {
    let origin = repository(test);
    write(&origin, "notes.md", "one\n");
    fs::create_dir_all(origin.join("notes")).expect("a directory");
    fs::write(origin.join("notes/photo.png"), [0u8, 1, 2, 255]).expect("a picture");
    out(&origin, &["record", "-m", "Start a journal"]);
    write(&origin, "notes.md", "one\ntwo\n");
    out(&origin, &["record", "-m", "A second thought"]);

    out(&origin, &["name", "main", "head"]);
    out(&origin, &["skip", "--name", "*.tmp"]);
    out(&origin, &["skip", "--private", "clients/acme-layoffs/"]);
    // What a signing tool leaves in the two directories 0046 reserved. Nothing
    // in this crate reads a byte of it, which is the point.
    write(
        &origin,
        "history/claims/over-the-head.claim.txt",
        "claim-0\nrole author\n",
    );
    write(
        &origin,
        "history/trust/adam.txt",
        "trust-0\nkey RWTd8LRCGA9i53mlYecO4IzT51TGPpvWucNSCh1CBM0QTaLn73Y7GFO3\n",
    );
    write(&origin, "draft.tmp", "a file a rule keeps out\n");

    let root = scratch(&format!("{test}-published"));
    let copy = root.join("store");
    out(&origin, &["export", &copy.to_string_lossy()]);
    (origin, root)
}

#[test]
fn an_offer_names_every_transferable_file_of_a_published_copy() {
    let (_origin, root) = published("listing");
    let copy = root.join("store");
    let text = out(&root, &["offer", "store"]);
    let (heads, entries) = manifest(&text);

    // Decision 0052: the copy's only head is the target it was written at, and
    // the heads answer relatedness rather than currency.
    assert_eq!(heads.len(), 1, "{text}");
    assert!(
        entries
            .iter()
            .any(|line| line.kind == "revision" && line.digest == heads[0]),
        "the head is not among the revisions offered: {text}"
    );

    // One of every kind, which is what the fixture was built for.
    let kinds: BTreeSet<&str> = entries.iter().map(|line| line.kind.as_str()).collect();
    assert_eq!(
        kinds,
        BTreeSet::from([
            "revision",
            "operation",
            "payload",
            "rule",
            "reserved",
            "name",
        ]),
        "{text}"
    );
    assert_eq!(
        entries
            .iter()
            .filter(|line| line.kind == "revision")
            .count(),
        2
    );
    assert_eq!(
        entries.iter().filter(|line| line.kind == "payload").count(),
        2,
        "the file and the picture are payloads: {text}"
    );

    // Decision 0052: every path resolves against the manifest's own directory,
    // so it begins with the exported directory's name and the store under it.
    for line in &entries {
        assert!(
            line.path.starts_with("store/history/"),
            "a path that does not resolve against the manifest's directory: {line:?}"
        );
        assert!(
            root.join(&line.path).is_file(),
            "the manifest names a file that is not there: {line:?}"
        );
    }

    // The digest is the digest of the file's bytes — hashed here rather than
    // taken from the store, because that claim is the whole of what a fetcher
    // verifies on arrival.
    for line in &entries {
        let bytes = fs::read(root.join(&line.path)).expect("a file the manifest names");
        assert_eq!(
            digest(&bytes).to_string(),
            line.digest,
            "the digest does not name the bytes at {}",
            line.path
        );
    }

    // And the listing is complete: every file the copy's `history/` holds is
    // either offered or one of the few things 0048 says is not.
    let named: BTreeSet<String> = entries
        .iter()
        .map(|line| line.path.trim_start_matches("store/history/").to_owned())
        .collect();
    let unnamed: Vec<String> = walk(&copy.join("history"))
        .into_iter()
        .filter(|file| !named.contains(file))
        // Decision 0035 makes everything here derived and deletable without
        // loss, and how much of it a copy happens to hold depends on what has
        // been read there. Nothing in it is ever offered, which the next test
        // pins from the other side.
        .filter(|file| !file.starts_with("cache/"))
        .collect();
    assert_eq!(
        unnamed,
        vec![
            "format.txt".to_owned(),
            "historica.txt".to_owned(),
            "skipped/README.txt".to_owned(),
        ],
        "something the copy holds is neither offered nor one of the exceptions"
    );
}

#[test]
fn the_files_a_store_keeps_to_itself_are_never_named() {
    let (_origin, root) = published("kept-back");
    let text = out(&root, &["offer", "store"]);

    // Decision 0048: a fetcher has a store already, with its own header and
    // its own copy of the format.
    for kept in ["historica.txt", "format.txt"] {
        assert!(!text.contains(kept), "`{kept}` was offered:\n{text}");
    }
    // Decision 0042 on `cache/`, unchanged and now alone in that sentence: a
    // cache is nobody's, and the directory is not even walked, so a listing
    // never names a file from it. `names/` is listed since decision 0062, and
    // `an_offer_names_every_transferable_file_of_a_published_copy` pins that.
    assert!(!text.contains("cache/"), "`cache/` was offered:\n{text}");
    // A file of `skipped/` that states no rule states nothing a recipient
    // needs, and the note `init` leaves is that file.
    assert!(
        !text.contains("skipped/README.txt"),
        "the rule note was offered:\n{text}"
    );
}

#[test]
fn a_private_rule_is_not_named_even_where_the_store_still_holds_one() {
    // Decision 0056 narrows 0052: an export's `skipped/` is shared-only by
    // construction, and `offer` takes a directory rather than a provenance, so
    // it applies 0051's axis itself. A rule file's name is derived from the
    // rule (0045), so naming one would publish the rule.
    let (origin, root) = published("private");

    let published = out(&root, &["offer", "store"]);
    let (_, entries) = manifest(&published);
    let rules: Vec<&str> = entries
        .iter()
        .filter(|line| line.kind == "rule")
        .map(|line| line.path.as_str())
        .collect();
    assert_eq!(rules.len(), 1, "{published}");

    // The same command, pointed at the live store it was published from, where
    // the private rule is genuinely there.
    let name = origin.file_name().expect("a directory name").to_owned();
    let beside = origin.parent().expect("a parent directory");
    let live = out(beside, &["offer", &name.to_string_lossy()]);
    let (_, entries) = manifest(&live);
    assert_eq!(
        entries.iter().filter(|line| line.kind == "rule").count(),
        1,
        "the private rule was listed:\n{live}"
    );
    assert!(
        !live.contains("acme-layoffs"),
        "a `private` rule's own text reached the manifest through its \
         filename:\n{live}"
    );
    assert!(
        origin
            .join("history/skipped/clients/acme-layoffs/all.txt")
            .is_file(),
        "the fixture no longer holds a private rule to withhold"
    );
    // And `trust/` never crosses a boundary, so nothing lists it either.
    assert!(
        !live.contains("trust/"),
        "0046's trust policy leaked:\n{live}"
    );
}

#[test]
fn what_a_document_forgets_is_stated_where_a_fetcher_reads_it() {
    // Decision 0014 travelling. A fetcher that took a plain set difference
    // would keep an original an arriving forgetting document destroys, so the
    // relationship is in the fourth field and nothing has to be opened.
    let origin = repository("forgetting");
    write(&origin, "notes.md", "public\nthe secret\n");
    out(&origin, &["record", "-m", "A secret"]);
    let target = out(&origin, &["log"])
        .lines()
        .find(|line| line.contains("(head"))
        .and_then(|line| line.split_whitespace().nth(1).map(str::to_owned))
        .expect("a head");
    write(&origin, "notes.md", "public\nthe secret\nmore\n");
    out(&origin, &["record", "-m", "More"]);
    let root = scratch("forgetting-published");
    let copy = root.join("store");
    out(&origin, &["export", &copy.to_string_lossy()]);

    // Before the redaction, nothing forgets anything. The bytes about to be
    // destroyed are the payload decision 0017 writes for a file's creation.
    let (_, before) = manifest(&out(&root, &["offer", "store"]));
    assert!(
        before.iter().all(|line| line.forgets == "-"),
        "something forgets something before anything has been forgotten"
    );
    let original = before
        .iter()
        .find(|line| line.kind == "payload")
        .expect("the payload the file was created as")
        .clone();

    out(&origin, &["forget", &target, "notes.md", "--lines", "2"]);
    out(&origin, &["export", &copy.to_string_lossy()]);

    let text = out(&root, &["offer", "store"]);
    let (_, after) = manifest(&text);
    // The stand-in is offered, and says what it destroyed.
    let standing: Vec<&Line> = after.iter().filter(|line| line.forgets != "-").collect();
    assert_eq!(standing.len(), 1, "{text}");
    assert_eq!(
        standing[0].forgets, original.digest,
        "the manifest does not say which digest was destroyed:\n{text}"
    );
    assert_eq!(standing[0].kind, "operation");

    // And the original is gone from the listing, because it is gone from the
    // copy: a forgetting document that arrives destroys what it stands in for.
    assert!(
        !after.iter().any(|line| line.digest == original.digest),
        "the forgotten original is still offered:\n{text}"
    );
    assert!(
        !text.contains("the secret"),
        "the destroyed text reached the manifest:\n{text}"
    );
}

#[test]
fn the_lines_are_ordered_so_that_a_fetcher_reading_from_the_top_is_safe() {
    let (_origin, root) = published("order");
    let text = out(&root, &["offer", "store"]);
    let (_, entries) = manifest(&text);

    // Decision 0056 fixes the order: payloads, documents, revisions, rules,
    // and the files of another tool — 0048's fetch order, so an interruption
    // understates what is reachable rather than leaving a revision naming
    // bytes that never arrived.
    // Decision 0062 puts bookmarks last, with the two kinds no revision names.
    let order = [
        "payload",
        "operation",
        "revision",
        "rule",
        "reserved",
        "name",
    ];
    let positions: Vec<usize> = entries
        .iter()
        .map(|line| {
            order
                .iter()
                .position(|kind| *kind == line.kind)
                .expect("a kind the grammar names")
        })
        .collect();
    assert!(
        positions.windows(2).all(|pair| pair[0] <= pair[1]),
        "the groups are out of order:\n{text}"
    );
    // And within a group, the path's order, so that one copy is one manifest.
    for kind in order {
        let paths: Vec<&str> = entries
            .iter()
            .filter(|line| line.kind == kind)
            .map(|line| line.path.as_str())
            .collect();
        let mut sorted = paths.clone();
        sorted.sort_unstable();
        assert_eq!(paths, sorted, "`{kind}` lines are not in path order");
    }

    // A copy nothing has changed produces a manifest nothing has changed,
    // which is what makes republishing on a timer a no-op.
    assert_eq!(text, out(&root, &["offer", "store"]));
}

#[test]
fn an_offer_writes_nothing_anywhere() {
    // Decision 0048: an enumeration living in `history/` would be derived
    // mutable state going stale beside the thing it describes. This is a
    // rendering, with the standing `log` and `status` have.
    let (_origin, root) = published("writes-nothing");
    // Once first, so that whatever reading a store does for itself — the
    // catalogue in `cache/`, which 0035 makes disposable and every reading
    // command refreshes — has already happened and is not mistaken for the
    // manifest being written down.
    out(&root, &["offer", "store"]);

    let before = walk(&root);
    out(&root, &["offer", "store"]);
    assert_eq!(before, walk(&root), "`offer` wrote a file");
    assert!(
        !root.join("offer.txt").exists(),
        "`offer` wrote the manifest itself; the redirect is the publisher's"
    );
}

#[test]
fn every_file_is_named_at_the_path_it_is_actually_at() {
    // Decision 0056's reason for taking the catalogue's pass rather than the
    // catalogue: 0036 keys it by digest, so two files holding one set of bytes
    // collapse to whichever path sorts first — which is right for a lookup and
    // wrong for a listing, whose paths are the only addresses a fetcher has.
    let (_origin, root) = published("duplicates");
    let copy = root.join("store");
    let text = out(&root, &["offer", "store"]);
    let (_, entries) = manifest(&text);
    let picture = entries
        .iter()
        .find(|line| line.path.ends_with("photo.png"))
        .expect("the picture")
        .clone();

    // The same bytes at a second path, which is what a store that was
    // received into from two differently arranged sources ends up holding.
    let second = copy.join("history/operations/a second copy of the picture");
    fs::copy(root.join(&picture.path), &second).expect("a second copy");

    let text = out(&root, &["offer", "store"]);
    let (_, entries) = manifest(&text);
    let both: Vec<&Line> = entries
        .iter()
        .filter(|line| line.digest == picture.digest)
        .collect();
    assert_eq!(both.len(), 2, "one of the two files went unnamed:\n{text}");
    assert!(
        both.iter().any(|line| line.path.ends_with("picture")),
        "the second path is not the one it is at:\n{text}"
    );
    assert!(both.iter().all(|line| line.kind == "payload"));
}

#[test]
fn every_head_is_named_where_a_store_has_more_than_one() {
    // 0048 puts a head line above the entries for each head the store has, and
    // 0052 says what they are for: relatedness, which is a question about the
    // graph rather than about which line of work a person is on.
    let origin = repository("heads");
    write(&origin, "notes.md", "one\n");
    out(&origin, &["record", "-m", "Root"]);
    let root_revision = out(&origin, &["log"])
        .lines()
        .find(|line| line.contains("(head"))
        .and_then(|line| line.split_whitespace().nth(1).map(str::to_owned))
        .expect("a head");
    write(&origin, "notes.md", "one\nmine\n");
    out(&origin, &["record", "-m", "Mine", "--onto", &root_revision]);
    write(&origin, "notes.md", "one\ntheirs\n");
    out(
        &origin,
        &["record", "-m", "Theirs", "--onto", &root_revision],
    );

    let name = origin.file_name().expect("a directory name").to_owned();
    let beside = origin.parent().expect("a parent directory");
    let text = out(beside, &["offer", &name.to_string_lossy()]);
    let (heads, entries) = manifest(&text);
    assert_eq!(heads.len(), 2, "{text}");
    for head in &heads {
        assert!(
            entries
                .iter()
                .any(|line| line.kind == "revision" && &line.digest == head),
            "a head with no revision offered: {head}"
        );
    }
}

#[test]
fn offer_refuses_what_is_not_a_published_copy() {
    let (_origin, root) = published("refusals");

    let said = refused(&root, &["offer"]);
    assert!(
        said.contains("wants the directory of the published copy"),
        "{said}"
    );

    let said = refused(&root, &["offer", "nowhere"]);
    assert!(said.contains("holds no `history/historica.txt`"), "{said}");
    assert!(
        said.contains("the directory `export` wrote"),
        "the refusal does not say what to point at instead: {said}"
    );

    // Pointed at the store rather than at the copy around it. Taking the
    // latitude `check` takes would silently write every path twice under
    // `history/`, which is the one thing about a manifest that must be right.
    let said = refused(&root, &["offer", "store/history"]);
    assert!(said.contains("holds no `history/historica.txt`"), "{said}");

    let said = refused(&root, &["offer", "store", "head"]);
    assert!(said.contains("takes one directory"), "{said}");
    let said = refused(&root, &["offer", "--all"]);
    assert!(said.contains("not an argument `offer` takes"), "{said}");
}
