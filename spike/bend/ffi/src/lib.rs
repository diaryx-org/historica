//! The C ABI `main.bend`'s effects call.
//!
//! Every function takes byte strings as `(pointer, length)` pairs, returns
//! `0` and a buffer in `out` on success, or an errno-style code and a message
//! in `out` on failure. Rust owns every buffer it hands out: the caller
//! returns it through [`hist_free`] with the length it was given, and nothing
//! else. No panic crosses the boundary — `catch_unwind` turns one into `EIO`.
//!
//! Only reading is here. Nothing in this library decides anything about a
//! store; that is what the Bend side is for.

use std::ffi::c_char;
use std::fs;
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::path::{Path, PathBuf};
use std::slice;

const STORE_DIR: &str = "history";
const HEADER_FILE: &str = "historica.txt";

/// The directories whose files are documents: everything under them is
/// named by its own digest, and nothing else in a store is.
const DOCUMENT_DIRS: [&str; 2] = ["revisions", "operations"];

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
/// # Safety
///
/// As [`hist_store_locate`].
#[no_mangle]
pub unsafe extern "C" fn hist_store_list(
    root: *const c_char,
    root_len: usize,
    out: *mut *mut c_char,
    out_len: *mut usize,
) -> i32 {
    answer(out, out_len, || {
        let root = Path::new(text(root, root_len)?);
        let mut paths = Vec::new();
        for dir in DOCUMENT_DIRS {
            walk(root, &root.join(dir), &mut paths)?;
        }
        paths.sort();
        Ok(paths.join("\n"))
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

    #[test]
    fn repeated_calls_answer_the_same() {
        let dir = tempfile::tempdir().unwrap();
        store(dir.path());
        let arg = dir.path().to_str().unwrap().as_bytes();
        let first = call(hist_store_locate, arg);
        for _ in 0..100 {
            assert_eq!(call(hist_store_locate, arg), first);
        }
    }
}
