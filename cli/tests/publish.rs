//! What one snapshot costs a published copy, at two lengths of history.
//!
//! The measurement the task *An export restates its indexes whole* was written
//! against, kept as a test: a store published once, one file added and
//! recorded, the copy exported onto and the manifest kept again. Two numbers
//! come out — how many files of the published directory the run added or
//! rewrote, and how many bytes of listing a fetcher that was current reads to
//! take the change — and neither may grow with the history. Before decision
//! 0078 the first was seven, three of them whole rewrites of indexes; before
//! decision 0080 the second was the whole listing, 12.7 KB at 40 revisions
//! and 120 KB at 400.

use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::io;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

use historica::format::digest;
use historica::record::{Clock as _, Platform, Recording, Restriction, record};
use historica::store::{Source, Store, Unreachable};
use historica::working::Working;

const MANIFEST: &str = "offer.txt";

fn scratch(test: &str) -> PathBuf {
    let path = Path::new(env!("CARGO_TARGET_TMPDIR")).join(format!("publish-{test}"));
    let _ = fs::remove_dir_all(&path);
    fs::create_dir_all(&path).expect("a scratch directory");
    path
}

fn out(directory: &Path, arguments: &[&str]) -> String {
    let output: Output = Command::new(env!("CARGO_BIN_EXE_historica"))
        .env(
            "HISTORICA_CACHE_DIR",
            concat!(env!("CARGO_TARGET_TMPDIR"), "/caches"),
        )
        .arg("-C")
        .arg(directory)
        .args(arguments)
        .env("HISTORICA_AUTHOR", "Adam Harris <adam@example.com>")
        .output()
        .expect("the binary this test crate builds");
    assert!(
        output.status.success(),
        "`{}` failed: {}",
        arguments.join(" "),
        String::from_utf8_lossy(&output.stderr)
    );
    String::from_utf8(output.stdout).expect("printed text")
}

/// One revision recorded from the folder as it stands, through the library:
/// four hundred of them through the binary would be most of this test's time.
fn record_folder(store: &mut Store, base: &Path, message: &str) {
    let mut platform = Platform;
    let working = Working::read(base, store.skipped()).expect("the folder");
    let parents = store.history().heads().into_iter().collect();
    record(
        store,
        &working,
        &Recording {
            parents,
            author: "Adam Harris <adam@example.com>".to_owned(),
            when: platform.now().expect("a clock"),
            message: message.to_owned(),
            moves: Vec::new(),
            at: Vec::new(),
            accepted: BTreeSet::new(),
            only: Restriction::Everything,
            kinds: Default::default(),
            extensions: Default::default(),
        },
        &mut platform,
    )
    .expect("recording");
}

/// Every file under a directory, by its path relative to it, with its digest.
fn snapshot(root: &Path) -> BTreeMap<String, String> {
    let mut found = BTreeMap::new();
    let mut pending = vec![root.to_path_buf()];
    while let Some(directory) = pending.pop() {
        for entry in fs::read_dir(&directory)
            .expect("a directory")
            .filter_map(Result::ok)
        {
            let path = entry.path();
            if path.is_dir() {
                pending.push(path);
            } else {
                let bytes = fs::read(&path).expect("a file");
                found.insert(
                    path.strip_prefix(root)
                        .expect("under the root")
                        .to_string_lossy()
                        .replace('\\', "/"),
                    digest(&bytes).to_string(),
                );
            }
        }
    }
    found
}

/// A published root read as a fetcher reads it, counting the bytes of listing
/// it was handed: the manifest and its pages.
struct Counting {
    root: PathBuf,
    listing: RefCell<usize>,
}

impl Source for Counting {
    fn get(&self, path: &str) -> Result<Option<Vec<u8>>, Unreachable> {
        match fs::read(self.root.join(path)) {
            Ok(bytes) => {
                if path == MANIFEST || path.starts_with("offer-pages/") {
                    *self.listing.borrow_mut() += bytes.len();
                }
                Ok(Some(bytes))
            }
            Err(error) if error.kind() == io::ErrorKind::NotFound => Ok(None),
            Err(error) => Err(Unreachable::saying(error)),
        }
    }
}

/// Files the one-file publish added or rewrote, and bytes of listing a current
/// fetcher read, at one length of history.
fn one_snapshot_published(revisions: usize) -> (Vec<String>, usize) {
    let base = scratch(&format!("{revisions}"));
    let origin = base.join("origin");
    fs::create_dir_all(&origin).expect("a repository");
    out(&origin, &["init"]);
    let mut store = Store::open(origin.join("history")).expect("the store");
    for file in 0..5 {
        fs::write(origin.join(format!("f{file}.md")), "begun\n").expect("a file");
    }
    for revision in 0..revisions {
        let file = origin.join(format!("f{}.md", revision % 5));
        let mut text = fs::read_to_string(&file).expect("a file");
        text.push_str(&format!("line {revision}\n"));
        fs::write(&file, text).expect("an edit");
        if revision % 8 == 7 {
            fs::write(origin.join(format!("n{revision}.md")), "new\n").expect("a new file");
        }
        record_folder(&mut store, &origin, &format!("revision {revision}"));
    }
    drop(store);

    let root = base.join("published");
    fs::create_dir_all(&root).expect("a published root");
    out(&origin, &["export", &root.join("store").to_string_lossy()]);
    out(&root, &["offer", "store", "--into", MANIFEST]);
    let here = base.join("here");
    fs::create_dir_all(&here).expect("a repository");
    out(&here, &["init"]);
    let fetcher =
        || Store::open_caching(here.join("history"), base.join("here-caches")).expect("the store");
    fetcher()
        .fetch(
            &Counting {
                root: root.clone(),
                listing: RefCell::new(0),
            },
            MANIFEST,
            false,
        )
        .expect("the first fetch");

    let before = snapshot(&root);
    fs::write(origin.join("added.md"), "a new 17-byte fi\n").expect("the one change");
    let mut store = Store::open(origin.join("history")).expect("the store");
    record_folder(&mut store, &origin, "one file added");
    drop(store);
    out(&origin, &["export", &root.join("store").to_string_lossy()]);
    out(&root, &["offer", "store", "--into", MANIFEST]);
    let after = snapshot(&root);
    let changed: Vec<String> = after
        .iter()
        .filter(|(path, digest)| before.get(*path) != Some(*digest))
        .map(|(path, _)| path.clone())
        .collect();

    let source = Counting {
        root: root.clone(),
        listing: RefCell::new(0),
    };
    let fetched = fetcher()
        .fetch(&source, MANIFEST, false)
        .expect("the fetch after the change");
    assert_eq!(fetched.revisions.len(), 1);
    let listing = *source.listing.borrow();
    (changed, listing)
}

#[test]
fn one_snapshot_costs_a_published_copy_the_same_at_any_length() {
    let (short, short_listing) = one_snapshot_published(40);
    let (long, long_listing) = one_snapshot_published(400);
    eprintln!("40 revisions: {short:?}, {short_listing} bytes of listing");
    eprintln!("400 revisions: {long:?}, {long_listing} bytes of listing");

    for changed in [&short, &long] {
        // The revision, the content file, the folder's copy of the file, the
        // manifest, and the page — and nothing under a `cache/`.
        assert_eq!(changed.len(), 5, "{changed:?}");
        assert!(
            changed.iter().all(|path| !path.contains("/cache/")),
            "{changed:?}"
        );
        assert!(changed.contains(&MANIFEST.to_owned()), "{changed:?}");
        assert!(
            changed.iter().any(|path| path.starts_with("offer-pages/")),
            "{changed:?}"
        );
    }
    // Within a constant of each other: the manifest names the same pages at
    // both lengths, and only the path of the added file differs in length.
    assert!(
        short_listing.abs_diff(long_listing) <= 64,
        "{short_listing} against {long_listing}"
    );
    assert!(long_listing < 2048, "{long_listing}");
}
