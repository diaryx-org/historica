//! History held elsewhere, decision 0089.
//!
//! A copy that took the history without the content, or the content of one
//! line, holds every revision and not every file's text. These tests hold
//! the library's fetch to what it leaves and takes, the record survey to
//! reading a file it lacks as held elsewhere rather than deleted, and the
//! CLI's reading commands to fetching what they lack from the copy they came
//! from, over a real HTTP connection, and to refusing whole when they cannot.

use std::collections::BTreeSet;
use std::fs;
use std::io::{self, BufRead as _, BufReader, Write as _};
use std::net::{TcpListener, TcpStream};
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};
use std::thread::JoinHandle;

use historica::core::RevisionId;
use historica::store::{FetchError, Fetching, Source, Store, Unreachable};

const MANIFEST: &str = "offer.txt";

fn scratch(test: &str) -> PathBuf {
    let path = Path::new(env!("CARGO_TARGET_TMPDIR")).join(format!("elsewhere-{test}"));
    let _ = fs::remove_dir_all(&path);
    let _ = fs::remove_dir_all(caches(&path));
    fs::create_dir_all(&path).expect("a scratch directory");
    path
}

/// Run the binary with a cache directory of the test's own, so what it
/// remembers about where it fetched from is this test's.
fn run(directory: &Path, arguments: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_historica"))
        .env("HISTORICA_CACHE_DIR", caches(directory))
        .env("HISTORICA_AUTHOR", "Adam Harris <adam@example.com>")
        .arg("-C")
        .arg(directory)
        .args(arguments)
        .output()
        .expect("the binary this test crate builds")
}

/// Where a repository's caches are kept: beside it, so `record` never sees
/// them.
fn caches(directory: &Path) -> PathBuf {
    directory.with_extension("caches")
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

fn refused(directory: &Path, arguments: &[&str]) -> String {
    let output = run(directory, arguments);
    assert!(
        !output.status.success(),
        "`{}` succeeded: {}",
        arguments.join(" "),
        String::from_utf8_lossy(&output.stdout)
    );
    String::from_utf8(output.stderr).expect("printed text")
}

fn write(directory: &Path, path: &str, text: &str) {
    fs::write(directory.join(path), text).expect("writing a file");
}

fn repository(test: &str) -> PathBuf {
    let directory = scratch(test);
    out(&directory, &["init"]);
    directory
}

fn store(repository: &Path) -> Store {
    // The directory the binary uses for this store: the base, and the store's
    // own directory below it, which is not this test's to name. So the
    // library opens without one, and the binary keeps its own.
    Store::open(repository.join("history")).expect("a store")
}

/// A history of two files over two revisions, `first` pinned to the first
/// and `main` on the second, published at the returned root with a paged
/// manifest.
fn published(test: &str) -> (PathBuf, PathBuf) {
    let origin = repository(test);
    write(&origin, "notes.md", "one\n");
    write(&origin, "other.md", "other\n");
    out(&origin, &["record", "-m", "Start"]);
    out(&origin, &["name", "--revision", "first", "head"]);
    write(&origin, "notes.md", "one\ntwo\n");
    out(&origin, &["record", "-m", "A second thought"]);
    out(&origin, &["name", "main", "head"]);

    let root = scratch(&format!("{test}-published"));
    out(&origin, &["export", &root.join("store").to_string_lossy()]);
    out(&root, &["offer", "store", "--into", MANIFEST]);
    (origin, root)
}

/// A published root read from the disk, as decision 0048 allows.
struct Directory(PathBuf);

impl Source for Directory {
    fn get(&self, path: &str) -> Result<Option<Vec<u8>>, Unreachable> {
        match fs::read(self.0.join(path)) {
            Ok(bytes) => Ok(Some(bytes)),
            Err(error) if error.kind() == io::ErrorKind::NotFound => Ok(None),
            Err(error) => Err(Unreachable::saying(error)),
        }
    }
}

/// Every file under `operations/`, by digest.
fn content_held(repository: &Path) -> BTreeSet<RevisionId> {
    let mut held = BTreeSet::new();
    let mut walking = vec![repository.join("history/operations")];
    while let Some(directory) = walking.pop() {
        let Ok(entries) = fs::read_dir(&directory) else {
            continue;
        };
        for entry in entries {
            let path = entry.expect("an entry").path();
            if path.is_dir() {
                walking.push(path);
            } else {
                held.insert(historica::format::digest(&fs::read(&path).expect("a file")));
            }
        }
    }
    held
}

fn head(store: &Store) -> RevisionId {
    let tips = store.history().tips();
    assert_eq!(tips.len(), 1, "one line");
    tips.into_iter().next().expect("the head")
}

/// The revision a bookmark pins.
fn pinned(store: &Store, name: &str) -> RevisionId {
    match store.name(name) {
        Some(historica::store::Name::Revision(id)) => id,
        other => panic!("`{name}` pins nothing: {other:?}"),
    }
}

#[test]
fn history_alone_takes_every_revision_and_no_content() {
    let (origin, root) = published("history");
    let here = repository("history-here");
    let fetched = store(&here)
        .fetch_with(
            &Directory(root.clone()),
            MANIFEST,
            Fetching::default().leaving_content(true),
        )
        .expect("a fetch of the history");
    assert_eq!(fetched.revisions.len(), 2);
    assert_eq!(fetched.payloads, 0);
    assert_eq!(fetched.documents, 0);
    assert!(fetched.left > 0);
    assert!(content_held(&here).is_empty(), "content arrived");
    assert_eq!(out(&here, &["log"]), out(&origin, &["log"]));

    // The store is legal, and not whole.
    out(&here, &["check"]);
    refused(&here, &["check", "--complete"]);

    // Every file at main lacks its content, and taking what it names makes
    // the file readable.
    let mut store = store(&here);
    let main = head(&store);
    let elsewhere = store
        .text_elsewhere(&[main], None)
        .expect("what main lacks");
    assert_eq!(
        elsewhere.paths().collect::<Vec<_>>(),
        ["notes.md", "other.md"]
    );
    let wanted: Vec<RevisionId> = elsewhere.digests().into_iter().collect();
    store
        .fetch_content(&Directory(root), MANIFEST, &wanted)
        .expect("the content main names");
    let store = Store::open(here.join("history")).expect("the store again");
    assert!(
        store
            .text_elsewhere(&[main], None)
            .expect("what main lacks")
            .is_empty()
    );
    assert_eq!(out(&here, &["cat", "main", "notes.md"]), "one\ntwo\n");
}

#[test]
fn naming_a_bookmark_takes_the_content_of_its_line_only() {
    let (_, root) = published("named");
    let here = repository("named-here");
    let fetched = store(&here)
        .fetch_with(
            &Directory(root),
            MANIFEST,
            Fetching::default().naming("first"),
        )
        .expect("a fetch of first's line");
    assert_eq!(fetched.revisions.len(), 2, "every revision arrives");
    assert_eq!(fetched.left, 1, "the second revision's edit was left");

    let store = store(&here);
    let first = pinned(&store, "first");
    assert!(
        store
            .text_elsewhere(&[first], None)
            .expect("what first lacks")
            .is_empty(),
        "first's line is held whole"
    );
    let lacking = store
        .text_elsewhere(&[head(&store)], None)
        .expect("what main lacks");
    assert_eq!(lacking.paths().collect::<Vec<_>>(), ["notes.md"]);
    // Readable offline, since nothing it needs is elsewhere.
    assert_eq!(out(&here, &["cat", "first", "notes.md"]), "one\n");
    assert_eq!(out(&here, &["cat", "first", "other.md"]), "other\n");
}

#[test]
fn naming_a_bookmark_the_copy_does_not_state_is_refused() {
    let (_, root) = published("unnamed");
    let here = repository("unnamed-here");
    let error = store(&here)
        .fetch_with(
            &Directory(root),
            MANIFEST,
            Fetching::default().naming("nowhere"),
        )
        .expect_err("no such bookmark");
    assert!(matches!(error, FetchError::NoSuchName { .. }), "{error}");
    assert!(content_held(&here).is_empty());
}

/// A plain fetch after a fetch of the history takes what it left, documents
/// as well as payloads, from where the pages said they were.
#[test]
fn a_plain_fetch_takes_the_content_a_fetch_of_the_history_left() {
    let (_, root) = published("then-whole");
    let here = repository("then-whole-here");
    store(&here)
        .fetch_with(
            &Directory(root.clone()),
            MANIFEST,
            Fetching::default().leaving_content(true),
        )
        .expect("a fetch of the history");
    let fetched = store(&here)
        .fetch(&Directory(root), MANIFEST, false)
        .expect("a plain fetch");
    assert_eq!(fetched.revisions.len(), 0);
    assert!(fetched.documents > 0 && fetched.payloads > 0, "{fetched:?}");
    out(&here, &["check", "--complete"]);
}

/// The survey reads a file of lines whose content is held elsewhere, and
/// which the folder lacks, as held elsewhere and not as deleted.
#[test]
fn record_does_not_drop_a_file_whose_content_is_elsewhere() {
    let (_, root) = published("record");
    let here = repository("record-here");
    store(&here)
        .fetch_with(
            &Directory(root),
            MANIFEST,
            Fetching::default().leaving_content(true),
        )
        .expect("a fetch of the history");
    let status = out(&here, &["status"]);
    assert!(status.contains("absent  notes.md"), "{status}");
    assert!(!status.contains("dropped"), "{status}");

    write(&here, "new.md", "new\n");
    let said = out(&here, &["record", "-m", "A file of my own"]);
    assert!(said.contains("added   new.md"), "{said}");
    assert!(!said.contains("dropped"), "{said}");
    let files = out(&here, &["files", "head"]);
    assert!(
        files.contains("notes.md") && files.contains("other.md"),
        "{files}"
    );
}

// ── Over HTTP: the CLI fetches what a command lacks ─────────────────────────

/// A directory served over HTTP/1.1 on a loopback port, until stopped.
struct Server {
    port: u16,
    stop: Arc<AtomicBool>,
    thread: Option<JoinHandle<()>>,
}

impl Server {
    fn serving(root: &Path) -> Self {
        let listener = TcpListener::bind("127.0.0.1:0").expect("a loopback port");
        let port = listener.local_addr().expect("an address").port();
        let stop = Arc::new(AtomicBool::new(false));
        let stopping = Arc::clone(&stop);
        let root = root.to_path_buf();
        let thread = std::thread::spawn(move || {
            for stream in listener.incoming() {
                if stopping.load(Ordering::SeqCst) {
                    break;
                }
                if let Ok(stream) = stream {
                    let _ = answer(&root, stream);
                }
            }
        });
        Self {
            port,
            stop,
            thread: Some(thread),
        }
    }

    fn url(&self) -> String {
        format!("http://127.0.0.1:{}/{MANIFEST}", self.port)
    }

    /// Stop answering and close the port, so a request is refused.
    fn stop(&mut self) {
        self.stop.store(true, Ordering::SeqCst);
        let _ = TcpStream::connect(("127.0.0.1", self.port));
        if let Some(thread) = self.thread.take() {
            thread.join().expect("the server thread");
        }
    }
}

impl Drop for Server {
    fn drop(&mut self) {
        self.stop();
    }
}

/// One request, answered with the file at its path or a 404.
fn answer(root: &Path, stream: TcpStream) -> io::Result<()> {
    let mut reader = BufReader::new(stream.try_clone()?);
    let mut line = String::new();
    reader.read_line(&mut line)?;
    loop {
        let mut header = String::new();
        if reader.read_line(&mut header)? == 0 || header == "\r\n" {
            break;
        }
    }
    let path = line.split_whitespace().nth(1).unwrap_or("/");
    let path = path.trim_start_matches('/').replace("%20", " ");
    let mut stream = stream;
    match fs::read(root.join(path)) {
        Ok(body) => {
            write!(
                stream,
                "HTTP/1.1 200 OK\r\nContent-Length: {}\r\nConnection: close\r\n\r\n",
                body.len()
            )?;
            stream.write_all(&body)?;
        }
        Err(_) => {
            write!(
                stream,
                "HTTP/1.1 404 Not Found\r\nContent-Length: 0\r\nConnection: close\r\n\r\n"
            )?;
        }
    }
    stream.flush()
}

#[test]
fn a_command_fetches_the_content_it_lacks_and_refuses_whole_without_the_copy() {
    let (_, root) = published("http");
    let mut server = Server::serving(&root);
    let here = repository("http-here");
    let said = out(&here, &["fetch", "--history", &server.url()]);
    assert!(said.contains("fetched 2 revisions"), "{said}");
    assert!(content_held(&here).is_empty());

    // `cat` fetches one file's content, and nothing else's.
    assert_eq!(out(&here, &["cat", "main", "notes.md"]), "one\ntwo\n");
    let held = content_held(&here);
    assert!(!held.is_empty());
    let main = head(&store(&here));
    let lacking = store(&here)
        .text_elsewhere(&[main], None)
        .expect("what main lacks");
    assert_eq!(lacking.paths().collect::<Vec<_>>(), ["other.md"]);

    // Without the copy, a command that needs content refuses, names the file
    // and the fetch, and writes nothing.
    server.stop();
    let said = refused(&here, &["cat", "main", "other.md"]);
    assert!(said.contains("other.md"), "{said}");
    assert!(said.contains("held elsewhere"), "{said}");
    assert!(
        said.contains(&format!("historica fetch {}", server.url())),
        "{said}"
    );
    let said = refused(&here, &["update", "main"]);
    assert!(said.contains("other.md"), "{said}");
    assert!(
        !here.join("notes.md").exists(),
        "update wrote part of a head"
    );
    assert_eq!(content_held(&here), held);

    // Without the cache, the copy is not remembered: a refusal, and nothing
    // else.
    fs::remove_dir_all(caches(&here)).expect("the cache gone");
    let said = refused(&here, &["cat", "main", "other.md"]);
    assert!(said.contains("does not remember"), "{said}");
    assert!(said.contains("historica fetch <url> other.md"), "{said}");

    // Back online, `fetch <url> <path>` brings a file of lines' content, and
    // `update` then writes the whole head.
    let server = Server::serving(&root);
    let said = out(&here, &["fetch", &server.url(), "other.md"]);
    assert!(
        said.contains("content documents") || said.contains("payloads"),
        "{said}"
    );
    out(&here, &["update", "main"]);
    assert_eq!(
        fs::read_to_string(here.join("other.md")).expect("other.md"),
        "other\n"
    );
}
