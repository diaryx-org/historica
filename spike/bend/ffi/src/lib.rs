//! The C ABI `main.bend`'s effects call.
//!
//! Every function takes byte strings as `(pointer, length)` pairs, returns
//! `0` and a buffer in `out` on success, or an errno-style code and a message
//! in `out` on failure. Rust owns every buffer it hands out: the caller
//! returns it through [`hist_free`] with the length it was given, and nothing
//! else. No panic crosses the boundary — `catch_unwind` turns one into `EIO`.
//!
//! Reading is here, and the writes: the rename `record --move` makes in
//! the folder, a bookmark written and removed, and `init`'s directories. Nothing in this library
//! decides anything about a store; that is what the Bend side is for. The two lookups answer *where*
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
/// bookmarks and the rules of what recording skips, which are not documents
/// — nothing names one by its digest — and so are listed only by a caller
/// that asks for them.
const LISTED_DIRS: [&str; 4] = ["revisions", "operations", "names", "skipped"];

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

/// One directory of the folder beside the store, as the working copy's walk
/// sees it: an entry a line, in name order, each saying what it is without
/// following it.
///
/// - `d <name>`: a directory;
/// - `f <x> <size> <name>`: a regular file, `x` `1` where any execute bit
///   is set, and its length in bytes;
/// - `l <name>`, then its target on the next line: a symbolic link, read and
///   not followed;
/// - `L <name>`: a link whose target is not UTF-8, or cannot be one line;
/// - `o <name>`: anything else — a socket, a device;
/// - `u`: a name that is not UTF-8, which cannot be spelled.
///
/// A name holding a newline cannot be a line and is left out; the working
/// copy refuses such a path anyway, so nothing it would have tracked is lost.
/// Nothing here decides what is tracked: the rules of `skipped/`, the store's
/// own directory, and whether a path is one the format can hold are the Bend
/// side's, which asks for a directory only once it has decided to walk it.
///
/// # Safety
///
/// As [`hist_store_locate`].
#[no_mangle]
pub unsafe extern "C" fn hist_folder_list(
    query: *const c_char,
    query_len: usize,
    out: *mut *mut c_char,
    out_len: *mut usize,
) -> i32 {
    answer(out, out_len, || folder(Path::new(text(query, query_len)?)))
}

fn folder(dir: &Path) -> Result<String, (i32, String)> {
    use std::os::unix::fs::PermissionsExt as _;

    let failed = |at: &Path, error: std::io::Error| (code(&error), format!("{}: {error}", at.display()));
    let mut entries = Vec::new();
    for entry in fs::read_dir(dir).map_err(|error| failed(dir, error))? {
        let entry = entry.map_err(|error| failed(dir, error))?;
        let kind = entry.file_type().map_err(|error| failed(dir, error))?;
        entries.push((entry.path(), kind));
    }
    // The order the working copy's walk sorts its entries in.
    entries.sort_by(|a, b| a.0.cmp(&b.0));
    let mut lines = Vec::new();
    for (path, kind) in entries {
        let Some(name) = path.file_name().and_then(|name| name.to_str()) else {
            lines.push("u".to_owned());
            continue;
        };
        if name.contains('\n') {
            continue;
        }
        if kind.is_symlink() {
            let target = fs::read_link(&path).map_err(|error| failed(&path, error))?;
            match target.to_str() {
                Some(target) if !target.contains('\n') => {
                    lines.push(format!("l {name}"));
                    lines.push(target.to_owned());
                }
                _ => lines.push(format!("L {name}")),
            }
        } else if kind.is_dir() {
            lines.push(format!("d {name}"));
        } else if kind.is_file() {
            let metadata = fs::symlink_metadata(&path).map_err(|error| failed(&path, error))?;
            let runs = metadata.permissions().mode() & 0o111 != 0;
            lines.push(format!("f {} {} {name}", u8::from(runs), metadata.len()));
        } else {
            lines.push(format!("o {name}"));
        }
    }
    Ok(lines.join("\n"))
}

/// Whether this process's standard output is a terminal: `1` or `0`.
///
/// What `--color auto` asks, and nothing else: whether to decorate is the
/// Bend side's, which also reads `NO_COLOR`. The argument is ignored.
///
/// # Safety
///
/// As [`hist_store_locate`].
#[no_mangle]
pub unsafe extern "C" fn hist_stdout_terminal(
    query: *const c_char,
    query_len: usize,
    out: *mut *mut c_char,
    out_len: *mut usize,
) -> i32 {
    use std::io::IsTerminal as _;

    let _ = (query, query_len);
    answer(out, out_len, || Ok(if std::io::stdout().is_terminal() { "1" } else { "0" }.to_owned()))
}

/// A rename a person stated, done in the folder: `record --move`'s one write
/// before anything is surveyed, which `record --dry-run` does too.
///
/// The argument is the folder, then the old path and the new, a line each,
/// relative to it. Whether each is there is asked as the Rust tool asks it —
/// following links, so a link to nothing is not there — and the answer says
/// which of the four it was: `moved`, having made the new path's directory
/// and renamed the old to it; `there`, the new being there and the old not,
/// so nothing is left to do; `both` or `neither`, where nothing is done and
/// the Bend side says why. A failure is the Rust tool's own sentence for it.
///
/// # Safety
///
/// As [`hist_store_locate`].
#[no_mangle]
pub unsafe extern "C" fn hist_folder_move(
    query: *const c_char,
    query_len: usize,
    out: *mut *mut c_char,
    out_len: *mut usize,
) -> i32 {
    answer(out, out_len, || {
        let mut lines = text(query, query_len)?.split('\n');
        let (Some(folder), Some(from), Some(to), None) = (lines.next(), lines.next(), lines.next(), lines.next()) else {
            return Err((EINVAL, "a move is a folder, an old path and a new one".to_owned()));
        };
        let (old, new) = (Path::new(folder).join(from), Path::new(folder).join(to));
        Ok(match (old.exists(), new.exists()) {
            (true, false) => {
                if let Some(directory) = new.parent() {
                    fs::create_dir_all(directory)
                        .map_err(|error| (code(&error), format!("{}: {error}", directory.display())))?;
                }
                fs::rename(&old, &new).map_err(|error| (code(&error), format!("{from} -> {to}: {error}")))?;
                "moved"
            }
            (false, true) => "there",
            (true, true) => "both",
            (false, false) => "neither",
        }
        .to_owned())
    })
}

/// A bookmark written: `name`'s one write.
///
/// The argument is the file's path, then its bytes after the first newline.
/// Its directory is made first — a name with structure in it is a file in a
/// directory that may not be there yet — and the bytes land as the Rust
/// tool lands them: staged in a sibling, flushed, and renamed over the file,
/// so a reader sees the old bookmark or the new one and never half of
/// either. A failure is the Rust tool's own sentence for it.
///
/// # Safety
///
/// As [`hist_store_locate`].
#[no_mangle]
pub unsafe extern "C" fn hist_store_write(
    query: *const c_char,
    query_len: usize,
    out: *mut *mut c_char,
    out_len: *mut usize,
) -> i32 {
    use std::io::Write as _;

    answer(out, out_len, || {
        let Some((path, bytes)) = text(query, query_len)?.split_once('\n') else {
            return Err((EINVAL, "a write is a path, then its bytes".to_owned()));
        };
        let path = Path::new(path);
        let failed = |at: &Path, error: std::io::Error| (code(&error), format!("{}: {error}", at.display()));
        let (Some(directory), Some(name)) = (path.parent(), path.file_name()) else {
            return Err((EINVAL, format!("{}: not a file", path.display())));
        };
        fs::create_dir_all(directory).map_err(|error| failed(directory, error))?;
        let mut staged = name.to_owned();
        staged.push(format!(".{}.staged", std::process::id()));
        let staged = directory.join(staged);
        let landed = (|| {
            let mut file = fs::File::create(&staged)?;
            file.write_all(bytes.as_bytes())?;
            file.sync_all()?;
            fs::rename(&staged, path)?;
            fs::File::open(directory)?.sync_all()
        })();
        if let Err(error) = landed {
            let _ = fs::remove_file(&staged);
            return Err(failed(path, error));
        }
        Ok(String::new())
    })
}

/// A bookmark deleted: `name --delete`'s one write.
///
/// The argument is the directory removal stops at, then the file. The file
/// is removed, then each directory above it that the removal left empty, up
/// to and never including the first line's: a `names/feature/` holding
/// nothing says a `feature/` bookmark is here when none is. The answer is
/// `removed`, or `absent` for a file that was not there.
///
/// # Safety
///
/// As [`hist_store_locate`].
#[no_mangle]
pub unsafe extern "C" fn hist_store_remove(
    query: *const c_char,
    query_len: usize,
    out: *mut *mut c_char,
    out_len: *mut usize,
) -> i32 {
    answer(out, out_len, || {
        let Some((boundary, path)) = text(query, query_len)?.split_once('\n') else {
            return Err((EINVAL, "a removal is where it stops, then the file".to_owned()));
        };
        let (boundary, path) = (Path::new(boundary), Path::new(path));
        match fs::remove_file(path) {
            Ok(()) => {}
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => return Ok("absent".to_owned()),
            Err(error) => return Err((code(&error), format!("{}: {error}", path.display()))),
        }
        let mut empty = path.parent();
        while let Some(directory) = empty {
            if directory == boundary || fs::remove_dir(directory).is_err() {
                break;
            }
            empty = directory.parent();
        }
        Ok("removed".to_owned())
    })
}

/// Where a path really is: the current directory for an empty argument,
/// and otherwise the path with every link and `.` and `..` resolved — which
/// only a path that exists has, so a failure is also `init`'s answer to
/// whether its header is already there.
///
/// # Safety
///
/// As [`hist_store_locate`].
#[no_mangle]
pub unsafe extern "C" fn hist_path_real(
    query: *const c_char,
    query_len: usize,
    out: *mut *mut c_char,
    out_len: *mut usize,
) -> i32 {
    answer(out, out_len, || {
        let path = text(query, query_len)?;
        let found = if path.is_empty() {
            std::env::current_dir().map_err(|error| (code(&error), format!("$PWD: {error}")))?
        } else {
            fs::canonicalize(path).map_err(|error| (code(&error), format!("{path}: {error}")))?
        };
        found
            .into_os_string()
            .into_string()
            .map_err(|_| (EINVAL, "a path that is not UTF-8".to_owned()))
    })
}

/// Each directory named, a line each, made with every parent it lacks: the
/// layout `init` lays down. A failure is the Rust tool's own sentence for it.
///
/// # Safety
///
/// As [`hist_store_locate`].
#[no_mangle]
pub unsafe extern "C" fn hist_dirs_make(
    query: *const c_char,
    query_len: usize,
    out: *mut *mut c_char,
    out_len: *mut usize,
) -> i32 {
    answer(out, out_len, || {
        for path in text(query, query_len)?.split('\n').filter(|path| !path.is_empty()) {
            fs::create_dir_all(path).map_err(|error| (code(&error), format!("{path}: {error}")))?;
        }
        Ok(String::new())
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
    fn a_test_run_is_not_writing_to_a_terminal() {
        let (code, answer) = call(hist_stdout_terminal, b"");
        assert_eq!(code, 0);
        assert!(answer == "0" || answer == "1", "{answer}");
    }

    #[test]
    fn a_folder_is_listed_one_directory_at_a_time_without_following_links() {
        use std::os::unix::fs::PermissionsExt as _;

        let dir = tempfile::tempdir().unwrap();
        let root = dir.path();
        fs::create_dir_all(root.join("notes/deep")).unwrap();
        fs::write(root.join("notes/deep/hidden.txt"), "x").unwrap();
        fs::write(root.join("b.txt"), "four").unwrap();
        fs::write(root.join("run.sh"), "#!/bin/sh\n").unwrap();
        fs::set_permissions(root.join("run.sh"), fs::Permissions::from_mode(0o755)).unwrap();
        std::os::unix::fs::symlink("notes", root.join("a-link")).unwrap();
        fs::write(root.join("two\nlines"), "").unwrap();

        let (code, listed) = call(hist_folder_list, root.to_str().unwrap().as_bytes());
        assert_eq!(code, 0, "{listed}");
        assert_eq!(listed, "l a-link\nnotes\nf 0 4 b.txt\nd notes\nf 1 10 run.sh");

        let (code, message) = call(hist_folder_list, root.join("gone").to_str().unwrap().as_bytes());
        assert_eq!(code, ENOENT);
        assert!(message.contains("gone"), "{message}");
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
    fn a_move_says_which_of_the_four_it_was() {
        let dir = tempfile::tempdir().unwrap();
        let root = dir.path();
        fs::write(root.join("a.md"), "one\n").unwrap();
        fs::write(root.join("c.md"), "two\n").unwrap();
        let asked = |from: &str, to: &str| call(hist_folder_move, format!("{}\n{from}\n{to}", root.display()).as_bytes());

        assert_eq!(asked("a.md", "deep/er/b.md"), (0, "moved".to_owned()));
        assert_eq!(fs::read_to_string(root.join("deep/er/b.md")).unwrap(), "one\n");
        assert!(!root.join("a.md").exists());
        assert_eq!(asked("a.md", "deep/er/b.md"), (0, "there".to_owned()));
        assert_eq!(asked("c.md", "deep/er/b.md"), (0, "both".to_owned()));
        assert_eq!(asked("x.md", "y.md"), (0, "neither".to_owned()));
        // Followed, as the Rust tool follows it: a link to nothing is not there.
        std::os::unix::fs::symlink("nowhere", root.join("dangling")).unwrap();
        assert_eq!(asked("dangling", "z.md"), (0, "neither".to_owned()));
    }

    #[test]
    fn a_move_that_cannot_happen_says_why_and_moves_nothing() {
        let dir = tempfile::tempdir().unwrap();
        let root = dir.path();
        fs::write(root.join("a.md"), "one\n").unwrap();
        fs::write(root.join("file"), "").unwrap();
        let query = format!("{}\na.md\nfile/b.md", root.display());
        let (code, answer) = call(hist_folder_move, query.as_bytes());
        assert_ne!(code, 0);
        assert!(answer.starts_with(&format!("{}: ", root.join("file").display())), "{answer}");
        assert!(root.join("a.md").exists());
        assert_eq!(call(hist_folder_move, b"only one line").0, EINVAL);
    }

    #[test]
    fn a_bookmark_is_written_whole_where_its_name_puts_it() {
        let dir = tempfile::tempdir().unwrap();
        let names = dir.path().join("names");
        fs::create_dir(&names).unwrap();
        let file = names.join("feature/deep/x.txt");
        let query = format!("{}\nchange {}\nprivate\n", file.display(), "k".repeat(24));
        assert_eq!(call(hist_store_write, query.as_bytes()), (0, String::new()));
        assert_eq!(fs::read_to_string(&file).unwrap(), format!("change {}\nprivate\n", "k".repeat(24)));
        // Written over, and nothing staged left beside it.
        let query = format!("{}\nrevision {}\n", file.display(), "0".repeat(64));
        assert_eq!(call(hist_store_write, query.as_bytes()), (0, String::new()));
        assert_eq!(fs::read_to_string(&file).unwrap(), format!("revision {}\n", "0".repeat(64)));
        assert_eq!(fs::read_dir(file.parent().unwrap()).unwrap().count(), 1);

        fs::write(names.join("plain"), "").unwrap();
        let (code, answer) = call(hist_store_write, format!("{}\nx\n", names.join("plain/y.txt").display()).as_bytes());
        assert_ne!(code, 0);
        assert!(answer.starts_with(&format!("{}: ", names.join("plain").display())), "{answer}");
        assert_eq!(call(hist_store_write, b"no newline").0, EINVAL);
    }

    #[test]
    fn a_removal_tidies_what_it_empties_and_stops_at_names() {
        let dir = tempfile::tempdir().unwrap();
        let names = dir.path().join("names");
        fs::create_dir_all(names.join("a/b")).unwrap();
        fs::create_dir_all(names.join("a/kept")).unwrap();
        fs::write(names.join("a/b/x.txt"), "").unwrap();
        fs::write(names.join("a/kept/y.txt"), "").unwrap();
        fs::write(names.join("top.txt"), "").unwrap();
        let asked = |file: &str| call(hist_store_remove, format!("{}\n{}", names.display(), names.join(file).display()).as_bytes());

        assert_eq!(asked("a/b/x.txt"), (0, "removed".to_owned()));
        assert!(!names.join("a/b").exists());
        assert!(names.join("a/kept").exists());
        assert_eq!(asked("a/kept/y.txt"), (0, "removed".to_owned()));
        assert!(!names.join("a").exists());
        assert_eq!(asked("top.txt"), (0, "removed".to_owned()));
        assert!(names.is_dir(), "names/ itself stays");
        assert_eq!(asked("top.txt"), (0, "absent".to_owned()));
        assert_eq!(call(hist_store_remove, b"no newline").0, EINVAL);
    }

    #[test]
    fn a_path_is_found_where_it_really_is_and_only_where_it_is() {
        let dir = tempfile::tempdir().unwrap();
        let real = fs::canonicalize(dir.path()).unwrap();
        fs::create_dir(real.join("a")).unwrap();
        std::os::unix::fs::symlink(real.join("a"), real.join("link")).unwrap();
        let asked = format!("{}/link/../a/.", real.display());
        assert_eq!(call(hist_path_real, asked.as_bytes()), (0, real.join("a").display().to_string()));
        let (code, answer) = call(hist_path_real, real.join("gone").display().to_string().as_bytes());
        assert_eq!(code, ENOENT);
        assert!(answer.starts_with(&format!("{}: ", real.join("gone").display())), "{answer}");
        let (code, here) = call(hist_path_real, b"");
        assert_eq!(code, 0);
        assert_eq!(here, std::env::current_dir().unwrap().display().to_string());
    }

    #[test]
    fn directories_are_made_with_their_parents_or_the_first_failure_said() {
        let dir = tempfile::tempdir().unwrap();
        let root = dir.path();
        let query = format!("{}\n{}\n", root.join("h/revisions").display(), root.join("h/names").display());
        assert_eq!(call(hist_dirs_make, query.as_bytes()), (0, String::new()));
        assert!(root.join("h/revisions").is_dir() && root.join("h/names").is_dir());
        // Made again, nothing is wrong.
        assert_eq!(call(hist_dirs_make, query.as_bytes()), (0, String::new()));
        fs::write(root.join("file"), "").unwrap();
        let (code, answer) = call(hist_dirs_make, root.join("file/h").display().to_string().as_bytes());
        assert_ne!(code, 0);
        assert!(answer.starts_with(&format!("{}: ", root.join("file/h").display())), "{answer}");
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
