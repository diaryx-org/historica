//! The C ABI `main.bend`'s effects call.
//!
//! Every function takes byte strings as `(pointer, length)` pairs, returns
//! `0` and a buffer in `out` on success, or an errno-style code and a message
//! in `out` on failure. Rust owns every buffer it hands out: the caller
//! returns it through [`hist_free`] with the length it was given, and nothing
//! else. No panic crosses the boundary — `catch_unwind` turns one into `EIO`.
//!
//! Only reading is here. Nothing in this library decides anything about a
//! store; that is what the Bend side is for. The two lookups answer *where*
//! bytes are and *what* bytes are, and the Bend side reads, hashes and
//! parses every document it goes on to believe anything about.

use std::collections::{BTreeMap, BTreeSet};
use std::ffi::c_char;
use std::fs;
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::path::{Path, PathBuf};
use std::slice;

use sha2::{Digest, Sha256};

const STORE_DIR: &str = "history";
const HEADER_FILE: &str = "historica.txt";

/// The directories whose files are documents: everything under them is
/// named by its own digest, and nothing else in a store is.
const DOCUMENT_DIRS: [&str; 2] = ["revisions", "operations"];
/// Every directory `Store.list` walks when asked: the documents, and the
/// bookmarks, which are not documents — nothing names one by its digest —
/// and so are listed only by a caller that asks for them.
const LISTED_DIRS: [&str; 3] = ["revisions", "operations", "names"];

/// Where a store keeps what it can rebuild, and what decision 0036's
/// catalogue of `operations/` is called inside it.
const CACHE_DIR: &str = "cache";
const CATALOGUE_FILE: &str = "operations.txt";
/// The line a catalogue this reader understands starts with.
const CATALOGUE_HEADER: &str = "historica-catalogue-1";
/// Characters a digest is spelled in, which is how a catalogue line is
/// recognised without parsing it.
const DIGEST_CHARS: usize = 64;

const EIO: i32 = 5;
const EINVAL: i32 = 22;
const ENOENT: i32 = 2;

/// Where the store is: the `history` directory holding a `historica.txt`,
/// here or in an ancestor of `from`. Empty `from` means the current directory.
///
/// # Safety
///
/// `from` is `from_len` readable bytes, or null with `from_len` zero; `out`
/// and `out_len` are writable.
#[no_mangle]
pub unsafe extern "C" fn hist_store_locate(
    from: *const c_char,
    from_len: usize,
    out: *mut *mut c_char,
    out_len: *mut usize,
) -> i32 {
    answer(out, out_len, || {
        let from = text(from, from_len)?;
        let from = if from.is_empty() { "." } else { from };
        locate(Path::new(from)).map(|root| root.to_string_lossy().into_owned())
    })
}

/// Every document a store holds: the files under `revisions/` and
/// `operations/`, as paths relative to `root`, sorted, one per line.
///
/// The argument is the root, then — if the caller wants other than every
/// document — one directory per line, and only those are walked: a document
/// directory, or `names`. A command that reads the graph asks for
/// `revisions`, and is not handed the thousands of payload paths it would
/// only throw away.
///
/// # Safety
///
/// As [`hist_store_locate`].
#[no_mangle]
pub unsafe extern "C" fn hist_store_list(
    query: *const c_char,
    query_len: usize,
    out: *mut *mut c_char,
    out_len: *mut usize,
) -> i32 {
    answer(out, out_len, || {
        let (root, asked) = split(text(query, query_len)?);
        let root = Path::new(root);
        let mut dirs = Vec::new();
        for dir in asked {
            match LISTED_DIRS.iter().find(|known| **known == dir) {
                Some(known) if !dirs.contains(known) => dirs.push(*known),
                Some(_) => {}
                None => return Err((EINVAL, format!("`{dir}` is not a directory this lists"))),
            }
        }
        if dirs.is_empty() {
            dirs.extend(DOCUMENT_DIRS);
        }
        let mut paths = Vec::new();
        for dir in dirs {
            walk(root, &root.join(dir), &mut paths)?;
        }
        paths.sort();
        Ok(paths.join("\n"))
    })
}

/// Where the bytes with each digest are: one path per digest asked for,
/// relative to `root`, or `-` where the store holds no such document.
///
/// The argument is the root, then one digest — or an unambiguous prefix of
/// one — per line. This is decision 0036's question, and it is answered the
/// way `crate::store::catalogue` answers it: `cache/operations.txt` accounts
/// for the paths it names that the directory still holds, and every path it
/// does not account for is read and hashed. A missing, stale or garbled
/// catalogue therefore costs a pass and changes no answer.
///
/// Nothing here is believed on the Bend side. What comes back is a path; the
/// caller opens it, hashes what it finds, and refuses it where the bytes are
/// not the bytes it asked for.
///
/// # Safety
///
/// As [`hist_store_locate`].
#[no_mangle]
pub unsafe extern "C" fn hist_store_at(
    query: *const c_char,
    query_len: usize,
    out: *mut *mut c_char,
    out_len: *mut usize,
) -> i32 {
    answer(out, out_len, || {
        let query = text(query, query_len)?;
        let (root, wanted) = split(query);
        let at = index(Path::new(root))?;
        Ok(wanted
            .map(|digest| located(&at, digest).unwrap_or(MISSING))
            .collect::<Vec<_>>()
            .join("\n"))
    })
}

/// The digest and the byte count of each file asked for: `<digest> <size>`
/// per line, or `- 0` where the file will not be read.
///
/// The argument is the root, then one path relative to it per line. Every
/// file named is opened and hashed — `cache/` is not consulted — because the
/// one caller is `check`, which exists to do the work rather than to have
/// the answer.
///
/// # Safety
///
/// As [`hist_store_locate`].
#[no_mangle]
pub unsafe extern "C" fn hist_store_digests(
    query: *const c_char,
    query_len: usize,
    out: *mut *mut c_char,
    out_len: *mut usize,
) -> i32 {
    answer(out, out_len, || {
        let query = text(query, query_len)?;
        let (root, paths) = split(query);
        let root = Path::new(root);
        Ok(paths
            .map(|path| match fs::read(root.join(path)) {
                Ok(bytes) => format!("{} {}", digest(&bytes), bytes.len()),
                Err(_) => format!("{MISSING} 0"),
            })
            .collect::<Vec<_>>()
            .join("\n"))
    })
}

/// Return a buffer [`hist_store_locate`] or [`hist_store_list`] handed out.
///
/// # Safety
///
/// `p` came from this library with this `len`, and is freed once.
#[no_mangle]
pub unsafe extern "C" fn hist_free(p: *mut c_char, len: usize) {
    if p.is_null() {
        return;
    }
    // Allocated as `len + 1` bytes by `hand_out`, the terminator included.
    drop(Box::from_raw(std::ptr::slice_from_raw_parts_mut(
        p as *mut u8,
        len + 1,
    )));
}

fn locate(from: &Path) -> Result<PathBuf, (i32, String)> {
    let start = from
        .canonicalize()
        .map_err(|error| (code(&error), format!("{}: {error}", from.display())))?;
    for directory in start.ancestors() {
        let candidate = directory.join(STORE_DIR);
        if candidate.join(HEADER_FILE).is_file() {
            return Ok(candidate);
        }
    }
    Err((
        ENOENT,
        format!(
            "no `{STORE_DIR}` directory here or above {}; `historica init` makes one",
            start.display()
        ),
    ))
}

fn walk(root: &Path, dir: &Path, paths: &mut Vec<String>) -> Result<(), (i32, String)> {
    let entries = match fs::read_dir(dir) {
        Ok(entries) => entries,
        // A store with nothing recorded has no `operations/` yet.
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => return Ok(()),
        Err(error) => return Err((code(&error), format!("{}: {error}", dir.display()))),
    };
    for entry in entries {
        let entry = entry.map_err(|error| (code(&error), format!("{}: {error}", dir.display())))?;
        let path = entry.path();
        if path.is_dir() {
            walk(root, &path, paths)?;
            continue;
        }
        let relative = path.strip_prefix(root).unwrap_or(&path);
        let spelled = relative.to_string_lossy();
        // One path per line, so a name holding a newline cannot be listed.
        if !spelled.contains('\n') {
            paths.push(spelled.into_owned());
        }
    }
    Ok(())
}

/// The answer to a lookup the store cannot make.
///
/// A path under a document directory always begins `operations/` or
/// `revisions/`, so this names no file and needs no escaping.
const MISSING: &str = "-";

/// A one-shot argument: the root, and then a line each for the rest.
fn split(query: &str) -> (&str, impl Iterator<Item = &str>) {
    let mut lines = query.split('\n');
    let root = lines.next().unwrap_or_default();
    (root, lines)
}

/// Every document this store holds, by the digest of its bytes.
///
/// A digest two paths share resolves to the lesser path, which is the first
/// one a sorted listing reaches — so this and a reader walking the listing
/// itself answer alike.
fn index(root: &Path) -> Result<BTreeMap<String, String>, (i32, String)> {
    let mut paths = Vec::new();
    for dir in DOCUMENT_DIRS {
        walk(root, &root.join(dir), &mut paths)?;
    }
    let held: BTreeSet<&str> = paths.iter().map(String::as_str).collect();

    // What the catalogue accounts for: the paths it names that are still
    // there. A path it has lost is dropped, and a path it never named is
    // read below, which is the whole of the condition decision 0036 states.
    let mut at = BTreeMap::new();
    let mut accounted = BTreeSet::new();
    let catalogue = fs::read_to_string(root.join(CACHE_DIR).join(CATALOGUE_FILE)).unwrap_or_default();
    let mut lines = catalogue.lines();
    if lines.next() == Some(CATALOGUE_HEADER) {
        for line in lines {
            let mut fields = line.splitn(3, ' ');
            let (Some(digest), Some(_forgets), Some(path)) =
                (fields.next(), fields.next(), fields.next())
            else {
                continue;
            };
            if digest.len() != DIGEST_CHARS || !held.contains(path) {
                continue;
            }
            remember(&mut at, digest, path);
            accounted.insert(path.to_owned());
        }
    }

    for path in &paths {
        if accounted.contains(path.as_str()) {
            continue;
        }
        // A file that will not open is one this store cannot answer about,
        // which is what `-` says; there is nothing to report it to here.
        let Ok(bytes) = fs::read(root.join(path)) else {
            continue;
        };
        remember(&mut at, &digest(&bytes), path);
    }
    Ok(at)
}

fn remember(at: &mut BTreeMap<String, String>, digest: &str, path: &str) {
    match at.get_mut(digest) {
        Some(held) if path < held.as_str() => *held = path.to_owned(),
        Some(_) => {}
        None => {
            at.insert(digest.to_owned(), path.to_owned());
        }
    }
}

/// The path for a digest, or for the one digest a prefix names.
fn located<'a>(at: &'a BTreeMap<String, String>, wanted: &str) -> Option<&'a str> {
    if wanted.is_empty() {
        return None;
    }
    if let Some(path) = at.get(wanted) {
        return Some(path);
    }
    at.range(wanted.to_owned()..)
        .take_while(|(digest, _)| digest.starts_with(wanted))
        .map(|(_, path)| path.as_str())
        .min()
}

fn digest(bytes: &[u8]) -> String {
    let mut spelled = String::with_capacity(DIGEST_CHARS);
    for byte in Sha256::digest(bytes) {
        spelled.push_str(&format!("{byte:02x}"));
    }
    spelled
}

// The boundary
// ------------

/// Run `f` and hand its answer or its complaint out through `out`.
unsafe fn answer(
    out: *mut *mut c_char,
    out_len: *mut usize,
    f: impl FnOnce() -> Result<String, (i32, String)>,
) -> i32 {
    let (code, text) = match catch_unwind(AssertUnwindSafe(f)) {
        Ok(Ok(text)) => (0, text),
        Ok(Err((code, text))) => (code, text),
        Err(_) => (EIO, "historica-bend-ffi: internal error".to_owned()),
    };
    hand_out(out, out_len, text);
    code
}

/// Give the caller a buffer: the bytes, then a NUL the length does not count,
/// so C may read it either way.
unsafe fn hand_out(out: *mut *mut c_char, out_len: *mut usize, text: String) {
    let mut bytes = text.into_bytes();
    bytes.push(0);
    let len = bytes.len() - 1;
    let boxed: Box<[u8]> = bytes.into_boxed_slice();
    *out_len = len;
    *out = Box::into_raw(boxed) as *mut c_char;
}

unsafe fn text<'a>(p: *const c_char, len: usize) -> Result<&'a str, (i32, String)> {
    if p.is_null() {
        return Ok("");
    }
    std::str::from_utf8(slice::from_raw_parts(p as *const u8, len))
        .map_err(|_| (EINVAL, "a path that is not UTF-8".to_owned()))
}

fn code(error: &std::io::Error) -> i32 {
    error.raw_os_error().unwrap_or(EIO)
}

#[cfg(test)]
mod tests {
    //! The boundary, exercised as C would: raw pointers in, a buffer out,
    //! and the buffer given back. Under Miri or ASan a leak or a bad free
    //! here is a failure; without them, the answers are.
    use super::*;
    use std::ffi::CStr;

    /// Call one of the two entry points and take ownership of the answer.
    fn call(
        f: unsafe extern "C" fn(*const c_char, usize, *mut *mut c_char, *mut usize) -> i32,
        arg: &[u8],
    ) -> (i32, String) {
        let mut out: *mut c_char = std::ptr::null_mut();
        let mut len = 0usize;
        let code = unsafe { f(arg.as_ptr() as *const c_char, arg.len(), &mut out, &mut len) };
        assert!(!out.is_null(), "an answer is always handed out");
        // The NUL after `len` bytes is there for a C caller that wants it.
        let text = unsafe { CStr::from_ptr(out) }.to_str().unwrap().to_owned();
        assert_eq!(text.len(), len);
        unsafe { hist_free(out, len) };
        (code, text)
    }

    fn store(root: &Path) {
        let history = root.join("history");
        fs::create_dir_all(history.join("revisions/2026-09")).unwrap();
        fs::create_dir_all(history.join("operations/2026-09/x")).unwrap();
        fs::write(history.join("historica.txt"), "historica\n\n").unwrap();
        fs::write(history.join("revisions/2026-09/b.rev.txt"), "historica\n").unwrap();
        fs::write(history.join("revisions/2026-09/a.rev.txt"), "historica\n").unwrap();
        fs::write(history.join("operations/2026-09/x/notes.txt"), "one\n").unwrap();
        // Not a document directory: never listed.
        fs::create_dir_all(history.join("cache")).unwrap();
        fs::write(history.join("cache/README.txt"), "").unwrap();
    }

    #[test]
    fn locates_from_below_and_lists_sorted() {
        let dir = tempfile::tempdir().unwrap();
        store(dir.path());
        let below = dir.path().join("deep/er");
        fs::create_dir_all(&below).unwrap();

        let (code, root) = call(hist_store_locate, below.to_str().unwrap().as_bytes());
        assert_eq!(code, 0);
        assert!(root.ends_with("/history"), "{root}");

        let (code, listing) = call(hist_store_list, root.as_bytes());
        assert_eq!(code, 0);
        assert_eq!(
            listing,
            "operations/2026-09/x/notes.txt\nrevisions/2026-09/a.rev.txt\nrevisions/2026-09/b.rev.txt"
        );

        // Asked for one directory, only that one is walked; asked for one
        // that holds no documents, the answer is a refusal, not a listing.
        let (code, listing) = call(hist_store_list, format!("{root}\nrevisions").as_bytes());
        assert_eq!(code, 0);
        assert_eq!(listing, "revisions/2026-09/a.rev.txt\nrevisions/2026-09/b.rev.txt");
        let (code, text) = call(hist_store_list, format!("{root}\ncache").as_bytes());
        assert_eq!(code, EINVAL);
        assert_eq!(text, "`cache` is not a directory this lists");

        // `names` is walked when asked for, at any depth, and never by default.
        fs::create_dir_all(dir.path().join("history/names/feature")).unwrap();
        fs::write(dir.path().join("history/names/feature/x.txt"), "change k\n").unwrap();
        let (code, listing) = call(hist_store_list, format!("{root}\nnames").as_bytes());
        assert_eq!(code, 0);
        assert_eq!(listing, "names/feature/x.txt");
        let (_, listing) = call(hist_store_list, root.as_bytes());
        assert!(!listing.contains("names/"), "{listing}");
    }

    #[test]
    fn a_folder_called_history_without_the_header_is_not_a_store() {
        let dir = tempfile::tempdir().unwrap();
        fs::create_dir_all(dir.path().join("history")).unwrap();
        let (code, text) = call(hist_store_locate, dir.path().to_str().unwrap().as_bytes());
        assert_eq!(code, ENOENT);
        assert!(
            text.starts_with("no `history` directory here or above"),
            "{text}"
        );
        assert!(text.ends_with("`historica init` makes one"), "{text}");
    }

    #[test]
    fn a_missing_start_is_the_os_error() {
        let dir = tempfile::tempdir().unwrap();
        let gone = dir.path().join("gone");
        let (code, text) = call(hist_store_locate, gone.to_str().unwrap().as_bytes());
        assert_eq!(code, ENOENT);
        assert!(text.starts_with(gone.to_str().unwrap()), "{text}");
    }

    #[test]
    fn an_empty_store_lists_nothing() {
        let dir = tempfile::tempdir().unwrap();
        let history = dir.path().join("history");
        fs::create_dir_all(&history).unwrap();
        let (code, listing) = call(hist_store_list, history.to_str().unwrap().as_bytes());
        assert_eq!(code, 0);
        assert_eq!(listing, "");
    }

    #[test]
    fn malformed_arguments_are_refused_not_read() {
        let (code, text) = call(hist_store_list, b"\xff\xfe");
        assert_eq!(code, EINVAL);
        assert_eq!(text, "a path that is not UTF-8");

        let mut out: *mut c_char = std::ptr::null_mut();
        let mut len = 0usize;
        // A null argument of length zero is the current directory, which
        // exists, so this either finds a store or says there is none.
        let code = unsafe { hist_store_locate(std::ptr::null(), 0, &mut out, &mut len) };
        assert!(code == 0 || code == ENOENT);
        unsafe { hist_free(out, len) };
        // Freeing nothing is allowed, as C's `free` allows it.
        unsafe { hist_free(std::ptr::null_mut(), 0) };
    }

    /// The digest of `one\n`, which is what the store above files as a
    /// payload — worked out by this library and checked against `sha2` here
    /// rather than written down twice.
    fn one_digest() -> String {
        digest(b"one\n")
    }

    #[test]
    fn a_digest_finds_the_file_holding_those_bytes() {
        let dir = tempfile::tempdir().unwrap();
        store(dir.path());
        let root = dir.path().join("history");
        let wanted = one_digest();
        let query = format!("{}\n{wanted}", root.display());
        let (code, answer) = call(hist_store_at, query.as_bytes());
        assert_eq!(code, 0);
        assert_eq!(answer, "operations/2026-09/x/notes.txt");

        // A prefix names the same file, and a digest nothing holds is `-`.
        let query = format!("{}\n{}\n{}\n", root.display(), &wanted[..8], "0".repeat(64));
        let (code, answer) = call(hist_store_at, query.as_bytes());
        assert_eq!(code, 0);
        assert_eq!(
            answer,
            "operations/2026-09/x/notes.txt\n-\n-",
            "the empty last line is a digest too, and names nothing"
        );
    }

    #[test]
    fn two_revisions_of_one_text_resolve_to_the_lesser_path() {
        // Both revision documents above hold `historica\n`, so one digest has
        // two files. A sorted listing reaches `a` first, and so does this.
        let dir = tempfile::tempdir().unwrap();
        store(dir.path());
        let root = dir.path().join("history");
        let query = format!("{}\n{}", root.display(), digest(b"historica\n"));
        let (_, answer) = call(hist_store_at, query.as_bytes());
        assert_eq!(answer, "revisions/2026-09/a.rev.txt");
    }

    #[test]
    fn the_catalogue_is_believed_about_where_and_never_about_what() {
        // Decision 0036's condition, from the outside: an entry for a path the
        // directory still holds is taken without the file being read, which is
        // exactly why the Bend side hashes what it opens. An entry for a path
        // that is gone accounts for nothing.
        let dir = tempfile::tempdir().unwrap();
        store(dir.path());
        let root = dir.path().join("history");
        let invented = "f".repeat(64);
        let stale = "e".repeat(64);
        fs::write(
            root.join("cache/operations.txt"),
            format!(
                "historica-catalogue-1\n{invented} - operations/2026-09/x/notes.txt\n{stale} - operations/2026-09/x/gone.txt\n"
            ),
        )
        .unwrap();

        let query = format!("{}\n{invented}\n{stale}\n{}", root.display(), one_digest());
        let (code, answer) = call(hist_store_at, query.as_bytes());
        assert_eq!(code, 0);
        let lines: Vec<&str> = answer.split('\n').collect();
        assert_eq!(lines[0], "operations/2026-09/x/notes.txt", "believed");
        assert_eq!(lines[1], "-", "a path the directory has lost");
        // The file the catalogue accounted for is not hashed, so its own
        // digest is no longer an answer this can give.
        assert_eq!(lines[2], "-");
    }

    #[test]
    fn a_catalogue_of_another_version_is_discarded_whole() {
        let dir = tempfile::tempdir().unwrap();
        store(dir.path());
        let root = dir.path().join("history");
        fs::write(
            root.join("cache/operations.txt"),
            format!("historica-catalogue-9\n{} - operations/nowhere\n", "f".repeat(64)),
        )
        .unwrap();
        let query = format!("{}\n{}", root.display(), one_digest());
        let (_, answer) = call(hist_store_at, query.as_bytes());
        assert_eq!(answer, "operations/2026-09/x/notes.txt");
    }

    #[test]
    fn a_payload_is_named_without_its_bytes_leaving_here() {
        let dir = tempfile::tempdir().unwrap();
        store(dir.path());
        let root = dir.path().join("history");
        let query = format!(
            "{}\noperations/2026-09/x/notes.txt\noperations/2026-09/x/gone.txt",
            root.display()
        );
        let (code, answer) = call(hist_store_digests, query.as_bytes());
        assert_eq!(code, 0);
        assert_eq!(answer, format!("{} 4\n- 0", one_digest()));
    }

    #[test]
    fn a_lookup_with_nothing_to_look_up_is_an_empty_answer() {
        let dir = tempfile::tempdir().unwrap();
        store(dir.path());
        let root = dir.path().join("history");
        let query = format!("{}", root.display());
        assert_eq!(call(hist_store_at, query.as_bytes()), (0, String::new()));
        assert_eq!(call(hist_store_digests, query.as_bytes()), (0, String::new()));
    }

    #[test]
    fn repeated_calls_answer_the_same() {
        let dir = tempfile::tempdir().unwrap();
        store(dir.path());
        let arg = dir.path().to_str().unwrap().as_bytes();
        let first = call(hist_store_locate, arg);
        let query = format!("{}/history\n{}", dir.path().display(), one_digest());
        let found = call(hist_store_at, query.as_bytes());
        for _ in 0..100 {
            assert_eq!(call(hist_store_locate, arg), first);
            assert_eq!(call(hist_store_at, query.as_bytes()), found);
        }
    }
}
