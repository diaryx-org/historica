//! A layer held in memory, from the writer's record to the reader's
//! suppression, with no directory on any disk.
//!
//! `loop.rs` drives the same machinery on a real disk, which is the check that
//! it works where people keep their histories. This is the check that it
//! works *only* through historica's `Filesystem`: every chain below — the
//! writer's own, the copy kept of it, the copy carried onward — lives in one
//! [`Memory`], and if anything in the crate still reached `std::fs` behind the
//! seam, a receive here would find nothing where it looked, or leave something
//! on the disk where it should not.
//!
//! It is also the shape a caller's own tests are meant to take: a
//! [`Layers::on`] or [`Repo::on`] over an `Arc<Memory>`, and no temporary
//! directory to make, clean, or wait on.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::sync::Arc;

use historica::format::Timestamp;
use historica::fs::Filesystem;
use historica::record::{self, Kinds, Platform, Recording, Restriction};
use historica::store::{STORE_DIR, Store};
use historica::working::Working;

use historica_remark::layer::{Layers, MANIFEST_PATH, Memory};
use historica_remark::{Annotation, Motivation, Reader, Repo, Selector};

/// A store with a working folder, in memory.
struct Chain {
    files: Arc<Memory>,
    root: PathBuf,
}

impl Chain {
    fn new(files: &Arc<Memory>, root: &str) -> Self {
        let root = PathBuf::from(root);
        files.create_directory(&root).unwrap();
        Store::init_on(Arc::clone(files), root.join(STORE_DIR)).unwrap();
        Chain {
            files: Arc::clone(files),
            root,
        }
    }

    fn write(&self, path: &str, text: &str) {
        let full = self.root.join(path);
        self.files.create_directory(full.parent().unwrap()).unwrap();
        self.files.write(&full, text.as_bytes()).unwrap();
    }

    fn remove(&self, path: &str) {
        self.files.remove_file(&self.root.join(path)).unwrap();
    }

    fn record(&self, when: &str, message: &str) -> String {
        let mut store = Store::open_on(Arc::clone(&self.files), self.root.join(STORE_DIR)).unwrap();
        let parents: Vec<_> = store.history().heads().into_iter().collect();
        let working =
            Working::read_on(Arc::clone(&self.files), &self.root, store.skipped()).unwrap();
        let recording = Recording {
            parents,
            author: "Mom".to_string(),
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

    /// The chain, ready to leave, read through the same seam as the copies.
    fn export(&self) -> historica_remark::Export {
        Repo::on(Arc::clone(&self.files), &self.root)
            .export("mom")
            .unwrap()
            .unwrap()
    }
}

fn remark_document(target: &str) -> String {
    let mut note = Annotation::new(target, Motivation::Questioning);
    note.at = Some("3f9c".to_string());
    note.selector = Some(Selector::quoting("the lake"));
    note.body = format!("On {target}?");
    note.render().unwrap()
}

fn read(files: &Memory, path: &Path) -> Option<String> {
    historica::fs::read_to_string(files, path).ok()
}

/// Keep, read, carry, receive again after the writer withdrew a document, and
/// suppress — all of it over one `Memory`, and none of it on the disk.
#[test]
fn a_layer_lives_and_travels_in_memory() {
    let files = Arc::new(Memory::default());
    let reader = Reader::new();

    // A nested document, so laying the head out again has a directory to
    // clear and not only files.
    let mom = Chain::new(&files, "/mom");
    mom.write("first.md", &remark_document("doc:1"));
    mom.write("deeper/second.md", &remark_document("doc:2"));
    let first_head = mom.record("2026-01-01T00:00:00+00:00", "two");

    let layers = Layers::on(Arc::clone(&files), "/grandpa/history/remarks");
    let got = layers
        .keep("mom", "Mom", &mom.export(), MANIFEST_PATH)
        .unwrap();
    assert_eq!(got.head.as_deref(), Some(first_head.as_str()));
    assert_eq!(got.files, 2);
    assert_eq!(layers.names().unwrap(), vec!["mom"]);
    assert_eq!(layers.sender("mom"), "Mom");

    let kept = layers.layer("mom").unwrap();
    assert!(kept.exists());
    assert_eq!(kept.origin().as_deref(), Some("mom"));
    assert_eq!(kept.remarks(&reader, "Mom", None).unwrap().len(), 2);
    assert!(
        read(&files, &kept.root().join("deeper/second.md")).is_some(),
        "the head is laid out as files, in memory"
    );

    // Carried onward to a third reader, still in memory, still Mom's chain.
    let carried = kept.export("mom").unwrap().unwrap();
    let dad = Repo::on(Arc::clone(&files), "/dad/mom");
    dad.receive("mom", &carried, MANIFEST_PATH).unwrap();
    assert_eq!(dad.head().unwrap(), kept.head().unwrap());

    // Mom withdraws the nested one; receiving again clears it from the head,
    // directory and all, and leaves the store and its notes where they were.
    mom.remove("deeper/second.md");
    mom.record("2026-01-02T00:00:00+00:00", "one");
    let again = layers
        .keep("mom", "Mom", &mom.export(), MANIFEST_PATH)
        .unwrap();
    assert_eq!(again.files, 1);
    assert_eq!(
        kept.documents()
            .unwrap()
            .into_iter()
            .map(|(path, _)| path)
            .collect::<Vec<_>>(),
        vec!["first.md"]
    );
    assert_eq!(
        files.look(&kept.root().join("deeper")).unwrap(),
        None,
        "the withdrawn document's directory went with it"
    );
    assert_eq!(kept.sender().as_deref(), Some("Mom"));

    // Suppression is a note on the same filesystem.
    layers.suppress("mom", "first.md").unwrap();
    assert_eq!(layers.suppressed("mom").unwrap(), vec!["first.md"]);
    layers.unsuppress("mom", "first.md").unwrap();
    assert!(layers.suppressed("mom").unwrap().is_empty());

    for held in ["/mom", "/grandpa", "/dad"] {
        assert!(
            !Path::new(held).exists(),
            "{held} reached the disk, so something went around the seam"
        );
    }
}

/// An absent root and an absent repository answer emptily over memory exactly
/// as they do over a disk.
#[test]
fn nothing_kept_in_memory_is_an_empty_answer() {
    let files = Arc::new(Memory::default());
    let layers = Layers::on(Arc::clone(&files), "/kept");
    assert!(layers.names().unwrap().is_empty());
    assert!(layers.suppressed("mom").unwrap().is_empty());

    let absent = Repo::on(Arc::clone(&files), "/nowhere");
    assert!(!absent.exists());
    assert_eq!(absent.head().unwrap(), None);
    assert!(absent.documents().unwrap().is_empty());
    assert!(absent.export("nowhere").unwrap().is_none());
    assert_eq!(absent.sender(), None);
}
