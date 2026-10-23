//! The loop, end to end: an author publishes, a reader remarks, the remark
//! comes back, and a third reader sees it — as the remark's own chain, not as
//! a copy the author made of somebody else's words.
//!
//! This is the whole reason the crate has a transport half. Everything below
//! runs on real historica stores on a real disk, with no workspace engine
//! above them, which is also the check that the extraction is complete: if
//! anything here still needed a vault, it would not compile.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use historica::format::Timestamp;
use historica::record::{self, Kinds, Platform, Recording, Restriction};
use historica::store::{STORE_DIR, Store};
use historica::working::Working;

use historica_remark::layer::{Layers, MANIFEST_PATH};
use historica_remark::{Annotation, Motivation, Reader, Repo, Selector};

// ---------------------------------------------------------------------------
// A chain, without a workspace engine to make one
// ---------------------------------------------------------------------------

/// A store with a working folder, at a directory of its own.
struct Chain {
    root: PathBuf,
}

impl Chain {
    fn new(root: impl Into<PathBuf>) -> Self {
        let root = root.into();
        std::fs::create_dir_all(&root).unwrap();
        Store::init(root.join(STORE_DIR)).unwrap();
        Chain { root }
    }

    fn write(&self, path: &str, text: &str) {
        let full = self.root.join(path);
        if let Some(parent) = full.parent() {
            std::fs::create_dir_all(parent).unwrap();
        }
        std::fs::write(full, text).unwrap();
    }

    /// Snapshot whatever is in the folder. Returns the new head.
    fn record(&self, author: &str, when: &str, message: &str) -> String {
        let mut store = Store::open(self.root.join(STORE_DIR)).unwrap();
        let parents: Vec<_> = store.history().heads().into_iter().collect();
        let working = Working::read(&self.root, store.skipped()).unwrap();
        let recording = Recording {
            parents,
            author: author.to_string(),
            when: when.parse::<Timestamp>().unwrap(),
            message: message.to_string(),
            moves: Vec::new(),
            at: Vec::new(),
            accepted: Default::default(),
            only: Restriction::Everything,
            kinds: Kinds::default(),
            extensions: BTreeMap::new(),
        };
        let recorded = record::record(&mut store, &working, &recording, &mut Platform).unwrap();
        recorded.revision.to_string()
    }

    /// The chain, ready to leave — what a publish seals and a fetch takes
    /// from. Reached through [`Repo`] because that is the shape this crate
    /// carries: files at the head, store beside them, which is what a
    /// recorded folder already is.
    fn export(&self, label: &str) -> historica_remark::Export {
        Repo::at(&self.root).export(label).unwrap().unwrap()
    }
}

fn scratch(tag: &str) -> PathBuf {
    let stamp = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let dir = std::env::temp_dir().join(format!("historica-remark-{tag}-{stamp}"));
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

const LETTER: &str = "\
---
id: dxk7f2q9wl
title: The lake
---

That winter we had no idea the lake would freeze and Dad laughed.
";

/// One remark, as the reader's own document. Written with
/// [`Annotation::render`] rather than by hand, so the test exercises the
/// writing side the way a caller with no document machinery of its own would.
fn remark_document(target: &str, at: &str) -> String {
    let mut note = Annotation::new(target, Motivation::Questioning);
    note.at = Some(at.to_string());
    note.selector = Some(Selector::in_context(
        "the lake would freeze",
        "we had no idea ",
        " and Dad laughed",
    ));
    note.body = "Which lake?".into();
    note.render().unwrap()
}

// ---------------------------------------------------------------------------

/// Grandpa writes a letter and publishes it. Mom fetches it, remarks on it in
/// a chain of her own, and publishes that. Grandpa keeps her chain as a layer
/// beside his own and carries it, so Dad — any reader — fetches Mom's remark
/// from Grandpa and reads it as *Mom's*.
#[test]
fn a_remark_travels_reader_to_author_to_every_other_reader() {
    let dir = scratch("loop");
    let reader = Reader::new();

    // ── Grandpa writes, and publishes ──────────────────────────────────────
    let grandpa = Chain::new(dir.join("grandpa"));
    grandpa.write("letter.md", LETTER);
    let letter_at = grandpa.record("Grandpa", "2026-01-01T00:00:00+00:00", "The lake");

    // ── Mom fetches it ─────────────────────────────────────────────────────
    let moms_copy = Repo::at(dir.join("mom/copy"));
    let got = moms_copy
        .receive("grandpa", &grandpa.export("grandpa"), MANIFEST_PATH)
        .unwrap();
    assert_eq!(got.head.as_deref(), Some(letter_at.as_str()));
    assert_eq!(got.files, 1);
    moms_copy.note_sender("Grandpa").unwrap();
    moms_copy.note_origin("dxk7f2q9wl").unwrap();

    // The letter is on Mom's disk as a file, not only in a store.
    let letter = moms_copy.root().join("letter.md");
    assert!(letter.is_file(), "the head is materialised");
    assert!(
        std::fs::read_to_string(&letter).unwrap().contains("froze")
            || std::fs::read_to_string(&letter).unwrap().contains("freeze")
    );
    assert_eq!(moms_copy.sender().as_deref(), Some("Grandpa"));
    assert_eq!(moms_copy.origin().as_deref(), Some("dxk7f2q9wl"));

    // ── Mom remarks, in a chain of her own ─────────────────────────────────
    let mom = Chain::new(dir.join("mom/remarks"));
    mom.write(
        "on-the-lake.md",
        &remark_document("ark:mom/dxk7f2q9wl", &letter_at),
    );
    mom.record("Mom", "2026-01-02T00:00:00+00:00", "Which lake?");

    // ── Grandpa keeps her chain as a layer ─────────────────────────────────
    let grandpas_layers = Layers::at(grandpa.root.join(STORE_DIR).join("remarks"));
    grandpas_layers
        .keep("mom", "Mom", &mom.export("mom"), MANIFEST_PATH)
        .unwrap();
    assert_eq!(grandpas_layers.names().unwrap(), vec!["mom"]);
    assert_eq!(grandpas_layers.sender("mom"), "Mom");

    let kept = grandpas_layers.layer("mom").unwrap();
    let found = kept.remarks(&reader, "Mom", None).unwrap();
    assert_eq!(found.len(), 1, "{found:?}");
    assert_eq!(found[0].annotation.body.trim(), "Which lake?");
    assert_eq!(found[0].annotation.motivation, Motivation::Questioning);
    assert_eq!(found[0].annotation.at.as_deref(), Some(letter_at.as_str()));

    // ── and carries it, so Dad gets Mom's chain from Grandpa ───────────────
    let carried = kept.export("mom").unwrap().unwrap();
    let dads_layers = Layers::at(dir.join("dad/layers"));
    dads_layers
        .keep("mom", "Mom", &carried, MANIFEST_PATH)
        .unwrap();

    let dad_sees = dads_layers
        .layer("mom")
        .unwrap()
        .remarks(&reader, "Mom", None)
        .unwrap();
    assert_eq!(dad_sees.len(), 1);
    assert_eq!(dad_sees[0].annotation, found[0].annotation);
    assert_eq!(
        dad_sees[0].from, "Mom",
        "it arrived through Grandpa and is still Mom's"
    );

    // The remark Dad holds is the same *chain* Mom wrote, not a copy of her
    // words in Grandpa's: same head, digest for digest.
    assert_eq!(
        dads_layers.layer("mom").unwrap().head().unwrap(),
        kept.head().unwrap(),
    );

    // ── narrowing by target ────────────────────────────────────────────────
    let of_letter = kept
        .remarks(&reader, "Mom", Some("ark:mom/dxk7f2q9wl"))
        .unwrap();
    assert_eq!(of_letter.len(), 1);
    assert!(
        kept.remarks(&reader, "Mom", Some("ark:mom/somethingelse"))
            .unwrap()
            .is_empty()
    );

    // ── and it anchors on the text as Grandpa's letter now stands ──────────
    let text = std::fs::read_to_string(grandpa.root.join("letter.md")).unwrap();
    let selector = found[0].annotation.selector.as_ref().unwrap();
    let anchor = historica_remark::anchor(selector, &text).unwrap();
    assert_eq!(&text[anchor.start..anchor.end], "the lake would freeze");
    assert!(anchor.certain);

    clean(&dir);
}

/// Receiving again takes only what arrived since, and a document the writer
/// dropped is gone from the copy — the copy is the chain as it stands, not
/// an accumulation of everything it ever held.
#[test]
fn receiving_again_follows_the_writer() {
    let dir = scratch("again");
    let reader = Reader::new();

    let mom = Chain::new(dir.join("mom"));
    mom.write("first.md", &remark_document("doc:1", "3f9c"));
    mom.write("second.md", &remark_document("doc:2", "3f9c"));
    mom.record("Mom", "2026-01-01T00:00:00+00:00", "two");

    let layers = Layers::at(dir.join("kept"));
    layers
        .keep("mom", "Mom", &mom.export("mom"), MANIFEST_PATH)
        .unwrap();
    let kept = layers.layer("mom").unwrap();
    assert_eq!(kept.remarks(&reader, "Mom", None).unwrap().len(), 2);

    // Mom withdraws one and records again.
    std::fs::remove_file(mom.root.join("second.md")).unwrap();
    mom.record("Mom", "2026-01-03T00:00:00+00:00", "one");

    let again = layers
        .keep("mom", "Mom", &mom.export("mom"), MANIFEST_PATH)
        .unwrap();
    assert_eq!(again.revisions, 1, "only what arrived since");
    let now = kept.remarks(&reader, "Mom", None).unwrap();
    assert_eq!(now.len(), 1, "{now:?}");
    assert_eq!(now[0].path, "first.md");
    assert!(
        !kept.root().join("second.md").exists(),
        "the copy is the chain as it stands"
    );

    clean(&dir);
}

/// Suppression is the keeper's whole editorial power: a path left out of what
/// they show, and put back as easily. Nothing about the chain changes either
/// way, which is why nothing has to be fetched back.
#[test]
fn suppression_hides_and_lifts_without_touching_the_chain() {
    let dir = scratch("suppress");
    let reader = Reader::new();

    let mom = Chain::new(dir.join("mom"));
    mom.write("kind.md", &remark_document("doc:1", "3f9c"));
    mom.write("blunt.md", &remark_document("doc:2", "3f9c"));
    mom.record("Mom", "2026-01-01T00:00:00+00:00", "two");

    let layers = Layers::at(dir.join("kept"));
    layers
        .keep("mom", "Mom", &mom.export("mom"), MANIFEST_PATH)
        .unwrap();
    let kept = layers.layer("mom").unwrap();
    let head_before = kept.head().unwrap();

    assert!(layers.suppressed("mom").unwrap().is_empty());
    layers.suppress("mom", "blunt.md").unwrap();
    layers.suppress("mom", "blunt.md").unwrap(); // idempotent
    assert_eq!(layers.suppressed("mom").unwrap(), vec!["blunt.md"]);

    // What the keeper shows is the caller's to filter, and this is what they
    // filter by. The document is still in the chain and still on disk.
    let hidden = layers.suppressed("mom").unwrap();
    let shown: Vec<_> = kept
        .remarks(&reader, "Mom", None)
        .unwrap()
        .into_iter()
        .filter(|remark| !hidden.contains(&remark.path))
        .collect();
    assert_eq!(shown.len(), 1);
    assert_eq!(shown[0].path, "kind.md");
    assert!(kept.root().join("blunt.md").is_file(), "nothing destroyed");
    assert_eq!(kept.head().unwrap(), head_before, "the chain is untouched");

    layers.unsuppress("mom", "blunt.md").unwrap();
    layers.unsuppress("mom", "blunt.md").unwrap(); // idempotent
    assert!(layers.suppressed("mom").unwrap().is_empty());
    assert_eq!(kept.remarks(&reader, "Mom", None).unwrap().len(), 2);

    clean(&dir);
}

/// A name that is about to be a directory, and a chain that is not there.
#[test]
fn a_layer_name_is_a_path_segment_and_an_absent_one_is_not_an_error() {
    let dir = scratch("names");
    let layers = Layers::at(dir.join("kept"));

    for bad in ["", ".", "..", "a/b", "a\\b", ".hidden"] {
        assert!(layers.layer(bad).is_err(), "{bad:?} named a layer");
    }
    assert!(layers.layer("mom").is_ok());

    // Nothing kept yet is an empty answer, not a missing directory.
    assert!(layers.names().unwrap().is_empty());
    assert!(layers.suppressed("mom").unwrap().is_empty());
    let absent = Repo::at(dir.join("nowhere"));
    assert!(!absent.exists());
    assert!(absent.documents().unwrap().is_empty());
    assert_eq!(absent.head().unwrap(), None);
    assert!(absent.export("nowhere").unwrap().is_none());
    assert_eq!(absent.sender(), None);

    clean(&dir);
}

/// A chain full of documents that are not remarks is a chain with no remarks
/// in it, and one document nobody can read does not cost the answer about the
/// others.
#[test]
fn documents_that_are_not_remarks_are_passed_over() {
    let dir = scratch("mixed");
    let reader = Reader::new();

    let mom = Chain::new(dir.join("mom"));
    mom.write("plain.md", "---\ntitle: Groceries\n---\n\nmilk\n");
    mom.write("prose.md", "no metadata at all\n");
    mom.write("unterminated.md", "---\ntitle: oops\n\nstill going\n");
    mom.write(
        "odd.md",
        "---\ntarget: doc:1\nmotivation: vibing\n---\n\nhm\n",
    );
    mom.write("good.md", &remark_document("doc:1", "3f9c"));
    mom.record("Mom", "2026-01-01T00:00:00+00:00", "a mixed bag");

    let layers = Layers::at(dir.join("kept"));
    layers
        .keep("mom", "Mom", &mom.export("mom"), MANIFEST_PATH)
        .unwrap();
    let kept = layers.layer("mom").unwrap();

    assert_eq!(kept.documents().unwrap().len(), 5);
    let found = kept.remarks(&reader, "Mom", None).unwrap();
    assert_eq!(found.len(), 1, "{found:?}");
    assert_eq!(found[0].path, "good.md");

    clean(&dir);
}

/// The tests write into the system temp directory; leaving a store there per
/// run would be leaving a store there per run forever.
fn clean(dir: &Path) {
    let _ = std::fs::remove_dir_all(dir);
}
