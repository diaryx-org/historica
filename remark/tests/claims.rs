//! Which of a store's reserved directories travels with it.
//!
//! Nothing in this crate arranges any of this — historica carries a reserved
//! directory by its class (decision 0053), and its registry says `claims/`
//! travels and `trust/` does not. The test is here anyway, because the whole
//! reason a remark can reach a third reader as *its author's* depends on
//! exactly this pair of facts, and a change to either would break that
//! silently and a long way from here.
//!
//! What it pins:
//!
//! - a claim and the signature beside it arrive, **listed in the offer**, so
//!   the fetch verifies them by digest like everything else;
//! - `trust/` does not arrive, at any hop;
//! - and neither does this crate's own notes directory, which is unreserved
//!   and therefore local-only.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use historica::format::Timestamp;
use historica::record::{self, Kinds, Platform, Recording, Restriction};
use historica::store::{STORE_DIR, Store};
use historica::working::Working;

use historica_remark::Repo;
use historica_remark::layer::{Layers, MANIFEST_PATH, NOTES_DIR};

fn scratch(tag: &str) -> PathBuf {
    let stamp = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let dir = std::env::temp_dir().join(format!("historica-remark-{tag}-{stamp}"));
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

/// A chain with one remark in it.
fn chain(root: &Path) {
    std::fs::create_dir_all(root).unwrap();
    Store::init(root.join(STORE_DIR)).unwrap();
    std::fs::write(root.join("note.md"), "---\ntarget: doc:1\n---\n\nhm\n").unwrap();
    let mut store = Store::open(root.join(STORE_DIR)).unwrap();
    let working = Working::read(root, store.skipped()).unwrap();
    record::record(
        &mut store,
        &working,
        &Recording {
            parents: Vec::new(),
            author: "Mom".into(),
            when: "2026-01-01T00:00:00+00:00".parse::<Timestamp>().unwrap(),
            message: "one".into(),
            moves: Vec::new(),
            at: Vec::new(),
            accepted: Default::default(),
            only: Restriction::Everything,
            kinds: Kinds::default(),
            extensions: BTreeMap::new(),
        },
        &mut Platform,
    )
    .unwrap();
}

fn claims_dir(root: &Path) -> PathBuf {
    historica_minisign::layout::claims(&root.join(STORE_DIR))
}

fn trust_dir(root: &Path) -> PathBuf {
    historica_minisign::layout::trust(&root.join(STORE_DIR))
}

/// Every file under a directory, by path relative to it, in name order.
fn under(dir: &Path) -> Vec<String> {
    fn walk(dir: &Path, prefix: &str, out: &mut Vec<String>) {
        let Ok(entries) = std::fs::read_dir(dir) else {
            return;
        };
        for entry in entries.flatten() {
            let name = entry.file_name().to_string_lossy().into_owned();
            let relative = match prefix.is_empty() {
                true => name,
                false => format!("{prefix}/{name}"),
            };
            match entry.path().is_dir() {
                true => walk(&entry.path(), &relative, out),
                false => out.push(relative),
            }
        }
    }
    let mut out = Vec::new();
    walk(dir, "", &mut out);
    out.sort();
    out
}

#[test]
fn claims_travel_with_the_chain_and_trust_stays_home() {
    let dir = scratch("claims");
    let origin = dir.join("mom");
    chain(&origin);

    // A claim and the signature beside it. Their pairing is the two
    // filenames, which is why a reserved directory travels whole.
    std::fs::create_dir_all(claims_dir(&origin).join("2026-01")).unwrap();
    std::fs::write(
        claims_dir(&origin).join("2026-01/one.claim.txt"),
        "claim-0\nrevision aa\n",
    )
    .unwrap();
    std::fs::write(
        claims_dir(&origin).join("2026-01/one.claim.txt.minisig"),
        "untrusted comment: x\n",
    )
    .unwrap();

    // One key this copy believes. It must not leave: a copy seeded with a
    // stranger's key verifies the stranger's history.
    std::fs::create_dir_all(trust_dir(&origin)).unwrap();
    std::fs::write(trust_dir(&origin).join("adam.txt"), "RWTd8LRCGA9i53m\n").unwrap();

    let export = Repo::at(&origin).export("mom").unwrap().unwrap();

    // In the offer, by digest — which is what makes the fetch verify them.
    let listed: Vec<&str> = export
        .manifest
        .lines()
        .filter(|line| line.starts_with("reserved "))
        .collect();
    assert_eq!(listed.len(), 2, "{}", export.manifest);
    assert!(listed.iter().all(|line| line.contains("/claims/")));
    assert!(
        !export.manifest.contains("/trust/"),
        "trust is local-only and has no business in an offer:\n{}",
        export.manifest
    );

    // ── one hop ────────────────────────────────────────────────────────────
    let layers = Layers::at(dir.join("kept"));
    layers.keep("mom", "Mom", &export, MANIFEST_PATH).unwrap();
    let kept = layers.layer("mom").unwrap().root().to_path_buf();

    assert_eq!(
        under(&claims_dir(&kept)),
        ["2026-01/one.claim.txt", "2026-01/one.claim.txt.minisig"],
    );
    assert!(
        !trust_dir(&kept).exists(),
        "believing a key is a person on this machine deciding, and nothing else",
    );
    // The notes this crate keeps are unreserved, so they are local-only too:
    // the origin's copy stayed at the origin, and what is here was written
    // here.
    assert_eq!(
        under(&kept.join(STORE_DIR).join(NOTES_DIR)),
        ["origin.txt", "sender.txt"],
    );

    // ── and a second hop, which is the one the design needs ────────────────
    // Dad fetches Mom's chain from the store that kept it, and gets Mom's
    // claims — not the keeper's word that they were once seen.
    let carried = layers.layer("mom").unwrap().export("mom").unwrap().unwrap();
    let dad = Layers::at(dir.join("dad"));
    dad.keep("mom", "Mom", &carried, MANIFEST_PATH).unwrap();
    let dads = dad.layer("mom").unwrap().root().to_path_buf();

    assert_eq!(
        under(&claims_dir(&dads)),
        ["2026-01/one.claim.txt", "2026-01/one.claim.txt.minisig"],
    );
    assert_eq!(
        std::fs::read_to_string(claims_dir(&dads).join("2026-01/one.claim.txt")).unwrap(),
        "claim-0\nrevision aa\n",
        "byte for byte what Mom wrote",
    );
    assert!(!trust_dir(&dads).exists());

    let _ = std::fs::remove_dir_all(&dir);
}

/// A chain nobody has vouched for carries no claims, which is most chains and
/// is not a fault.
#[test]
fn a_chain_with_no_claims_is_not_a_broken_one() {
    let dir = scratch("unvouched");
    let origin = dir.join("mom");
    chain(&origin);

    let export = Repo::at(&origin).export("mom").unwrap().unwrap();
    assert!(
        !export.manifest.contains("reserved "),
        "{}",
        export.manifest
    );

    let layers = Layers::at(dir.join("kept"));
    let got = layers.keep("mom", "Mom", &export, MANIFEST_PATH).unwrap();
    assert_eq!(got.files, 1, "the chain still arrived");
    assert!(!claims_dir(layers.layer("mom").unwrap().root()).exists());

    let _ = std::fs::remove_dir_all(&dir);
}

/// An export answers for the manifest and for what the manifest lists, and
/// for nothing else — so there is no path over which it could serve a byte
/// with no digest to check it against.
#[test]
fn an_export_serves_nothing_the_offer_does_not_name() {
    use historica::store::Source;

    let dir = scratch("named");
    let origin = dir.join("mom");
    chain(&origin);
    std::fs::create_dir_all(trust_dir(&origin)).unwrap();
    std::fs::write(trust_dir(&origin).join("adam.txt"), "RWTsecret\n").unwrap();

    let export = Repo::at(&origin).export("mom").unwrap().unwrap();
    assert!(export.get(MANIFEST_PATH).unwrap().is_some());
    for unlisted in [
        "store/history/trust/adam.txt",
        "trust/adam.txt",
        "claims.txt",
        "claims/2026-01/one.claim.txt",
        "../../../etc/passwd",
        "",
    ] {
        assert!(
            export.get(unlisted).unwrap().is_none(),
            "{unlisted:?} is not in the offer and must not be served",
        );
    }

    let _ = std::fs::remove_dir_all(&dir);
}
