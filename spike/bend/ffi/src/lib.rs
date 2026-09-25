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
/// — nothing names one by its digest — and `cache/`, whose copies `forget`
/// destroys with what they copy; each listed only by a caller that asks.
const LISTED_DIRS: [&str; 5] = ["revisions", "operations", "names", "skipped", "cache"];

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
/// Where the first line after the root is `forgets`, the digests after it
/// are answered the same way, and then each document that says it forgets
/// one of them follows, a line each, as `<digest> <path>` in path order:
/// decision 0014's question for bytes a store still holds, which the Rust
/// store asks of the same catalogue — its `forgets` column for a path it
/// accounts for, and a document's first header for one it does not. That
/// too is a path: the caller reads the document and asks it again.
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
        let mut wanted = wanted.peekable();
        let standing = wanted.peek() == Some(&FORGETS);
        if standing {
            wanted.next();
        }
        let (at, forgetting) = index(Path::new(root))?;
        let wanted: Vec<&str> = wanted.collect();
        let mut lines: Vec<String> = wanted
            .iter()
            .map(|digest| located(&at, digest).unwrap_or(MISSING).to_owned())
            .collect();
        if standing {
            let mut beside: Vec<(&str, &str)> = Vec::new();
            for digest in &wanted {
                for path in forgetting.get(*digest).into_iter().flatten() {
                    beside.push((path.as_str(), digest));
                }
            }
            beside.sort();
            beside.dedup();
            lines.extend(beside.into_iter().map(|(path, digest)| format!("{digest} {path}")));
        }
        Ok(lines.join("\n"))
    })
}

/// The line after the root that asks `Store.at` for the documents standing
/// in for each digest as well.
const FORGETS: &str = "forgets";

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
/// - `u <name>`: a name that is not UTF-8, spelled as `to_string_lossy`
///   spells it — data for the refusal the Bend side words, which names it
///   so, and nothing to open by.
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
            let lossy = path.file_name().map(|name| name.to_string_lossy()).unwrap_or_default();
            if !lossy.contains('\n') {
                lines.push(format!("u {lossy}"));
            }
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
/// nothing says a `feature/` bookmark is here when none is. A third line,
/// where there is one, is where tidying starts instead of the file: `update`
/// removes a file where the folder spells it and tidies above the path as
/// the tree spells it, as the Rust tool does (decision 0033). The answer is
/// `removed`, or `absent` for a file that was not there.
///
/// The path may name an empty directory instead, which is removed the same
/// way — `forget`'s sweep of what `operations/` holds empty, which the Rust
/// store makes after every forgetting. One that is not empty is refused.
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
        let (path, tidy) = path.split_once('\n').unwrap_or((path, path));
        let (boundary, path, tidy) = (Path::new(boundary), Path::new(path), Path::new(tidy));
        let directory = fs::symlink_metadata(path).is_ok_and(|entry| entry.is_dir());
        let removed = if directory { fs::remove_dir(path) } else { fs::remove_file(path) };
        match removed {
            Ok(()) => {}
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => return Ok("absent".to_owned()),
            Err(error) => return Err((code(&error), format!("{}: {error}", path.display()))),
        }
        let mut empty = tidy.parent();
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

// Recording
// ---------

/// The environment variable that fixes the clock, and the one that fixes
/// the minting: `historica-pinned`'s two, read here the same way so that
/// `check.py` can hold both writers to one store's bytes. Unset, the machine
/// answers, as it does for `historica`.
const PINNED_NOW: &str = "HISTORICA_PINNED_NOW";
const PINNED_SEED: &str = "HISTORICA_PINNED_SEED";

/// What time it is, spelled as the format spells one: the pinned moment
/// where there is one, and otherwise the system clock in the offset the
/// platform reports for it, to the second — `record::Platform`'s spelling.
/// The argument is ignored.
///
/// # Safety
///
/// As [`hist_store_locate`].
#[no_mangle]
pub unsafe extern "C" fn hist_clock_now(
    query: *const c_char,
    query_len: usize,
    out: *mut *mut c_char,
    out_len: *mut usize,
) -> i32 {
    answer(out, out_len, || {
        text(query, query_len)?;
        if let Ok(pinned) = std::env::var(PINNED_NOW) {
            return Ok(pinned);
        }
        Ok(jiff::Zoned::now().strftime("%Y-%m-%dT%H:%M:%S%:z").to_string())
    })
}

/// Where the pinned stream has got to: the next block, and what is left of
/// the last. One program mints from one stream, so this is the process's.
static DRAWN: std::sync::Mutex<(u64, Vec<u8>)> = std::sync::Mutex::new((0, Vec::new()));

/// Bytes nothing can predict, as lowercase hex: the count asked for, in
/// decimal. With a seed pinned, the stream `historica-pinned` draws —
/// SHA-256 of the seed then an eight-byte big-endian block counter, digest
/// after digest — carried on from wherever the last call left it.
///
/// # Safety
///
/// As [`hist_store_locate`].
#[no_mangle]
pub unsafe extern "C" fn hist_entropy_fill(
    query: *const c_char,
    query_len: usize,
    out: *mut *mut c_char,
    out_len: *mut usize,
) -> i32 {
    use std::io::Read as _;

    answer(out, out_len, || {
        let asked = text(query, query_len)?;
        let count: usize = asked
            .parse()
            .map_err(|_| (EINVAL, format!("`{asked}` is not a count of bytes")))?;
        let mut bytes = vec![0u8; count];
        match std::env::var(PINNED_SEED) {
            Ok(seed) => {
                let mut drawn = DRAWN.lock().unwrap_or_else(|poisoned| poisoned.into_inner());
                for byte in &mut bytes {
                    if drawn.1.is_empty() {
                        let mut hash = Sha256::new();
                        hash.update(seed.as_bytes());
                        hash.update(drawn.0.to_be_bytes());
                        drawn.0 += 1;
                        drawn.1 = hash.finalize().iter().rev().copied().collect();
                    }
                    *byte = drawn.1.pop().expect("a block just drawn");
                }
            }
            Err(_) => {
                let source = "/dev/urandom";
                fs::File::open(source)
                    .and_then(|mut random| random.read_exact(&mut bytes))
                    .map_err(|error| {
                        (
                            code(&error),
                            format!(
                                "the operating system's random source refused, so no change ID can be minted: {error}"
                            ),
                        )
                    })?;
            }
        }
        Ok(bytes.iter().map(|byte| format!("{byte:02x}")).collect())
    })
}

/// Bytes filed once under a name, as the store files a document: the path,
/// then the bytes after the first newline. The directory is made first. A
/// file already there is left alone where it holds these bytes and refused
/// where it does not, since a document's name is a promise about its bytes.
///
/// # Safety
///
/// As [`hist_store_locate`].
#[no_mangle]
pub unsafe extern "C" fn hist_store_once(
    query: *const c_char,
    query_len: usize,
    out: *mut *mut c_char,
    out_len: *mut usize,
) -> i32 {
    answer(out, out_len, || {
        let Some((path, bytes)) = text(query, query_len)?.split_once('\n') else {
            return Err((EINVAL, "a write is a path, then its bytes".to_owned()));
        };
        once(Path::new(path), bytes.as_bytes())
    })
}

/// A file of the folder's filed once in the store: where it is, where it
/// goes, and the digest the survey found it to have, a line each. Bytes
/// that no longer hash to that are refused and nothing is written.
///
/// # Safety
///
/// As [`hist_store_locate`].
#[no_mangle]
pub unsafe extern "C" fn hist_store_copy(
    query: *const c_char,
    query_len: usize,
    out: *mut *mut c_char,
    out_len: *mut usize,
) -> i32 {
    answer(out, out_len, || {
        let mut lines = text(query, query_len)?.split('\n');
        let (Some(from), Some(to), Some(wanted), None) =
            (lines.next(), lines.next(), lines.next(), lines.next())
        else {
            return Err((EINVAL, "a copy is a path, where it goes, and its digest".to_owned()));
        };
        let bytes = fs::read(from).map_err(|error| (code(&error), format!("{from}: {error}")))?;
        let found = digest(&bytes);
        if found != wanted {
            return Err((
                EIO,
                format!(
                    "the content for {to} hashes to {found} rather than {wanted}, so nothing \
                     was written; it changed while it was being copied"
                ),
            ));
        }
        once(Path::new(to), &bytes)
    })
}

fn once(path: &Path, bytes: &[u8]) -> Result<String, (i32, String)> {
    use std::io::Write as _;

    let failed = |at: &Path, error: std::io::Error| (code(&error), format!("{}: {error}", at.display()));
    if let Some(directory) = path.parent() {
        fs::create_dir_all(directory).map_err(|error| failed(directory, error))?;
    }
    match fs::OpenOptions::new().write(true).create_new(true).open(path) {
        Ok(mut file) => {
            file.write_all(bytes)
                .and_then(|()| file.sync_all())
                .map_err(|error| failed(path, error))?;
            Ok("written".to_owned())
        }
        Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => {
            let existing = fs::read(path).map_err(|error| failed(path, error))?;
            if existing != bytes {
                return Err((
                    EIO,
                    format!("{} is named for a digest its bytes do not have", path.display()),
                ));
            }
            Ok("there".to_owned())
        }
        Err(error) => Err(failed(path, error)),
    }
}

// Laying the folder out
// ---------------------

/// Stage bytes beside `path` and rename them over it, making its directory
/// first: the landing every write into the folder shares, so a reader sees
/// what stood there or the new file and never half of either. `keep` says
/// whether a regular file standing there keeps its permissions — a file of
/// lines written over is the same file with new bytes, as the Rust tool's
/// `write_if` leaves it, and a payload laid down is a new file.
fn landed(path: &Path, bytes: &[u8], keep: bool) -> Result<(), (i32, String)> {
    use std::io::Write as _;

    let failed = |at: &Path, error: std::io::Error| (code(&error), format!("{}: {error}", at.display()));
    let (Some(directory), Some(name)) = (path.parent(), path.file_name()) else {
        return Err((EINVAL, format!("{}: not a file", path.display())));
    };
    fs::create_dir_all(directory).map_err(|error| failed(directory, error))?;
    let mut staged = name.to_owned();
    staged.push(format!(".{}.staged", std::process::id()));
    let staged = directory.join(staged);
    let held = match fs::symlink_metadata(path) {
        Ok(metadata) if keep && metadata.is_file() => Some(metadata.permissions()),
        _ => None,
    };
    let done = (|| {
        let mut file = fs::File::create(&staged)?;
        file.write_all(bytes)?;
        if let Some(permissions) = held {
            file.set_permissions(permissions)?;
        }
        file.sync_all()?;
        fs::rename(&staged, path)
    })();
    if let Err(error) = done {
        let _ = fs::remove_file(&staged);
        return Err(failed(path, error));
    }
    Ok(())
}

/// A file of lines written into the folder: `update`'s write of text a
/// revision records. The argument is the path, then the text after
/// the first newline. Its directory is made, the text lands staged and
/// renamed over whatever file stood there, and that file's permissions are
/// kept. The answer is `written`.
///
/// # Safety
///
/// As [`hist_store_locate`].
#[no_mangle]
pub unsafe extern "C" fn hist_folder_put(
    query: *const c_char,
    query_len: usize,
    out: *mut *mut c_char,
    out_len: *mut usize,
) -> i32 {
    answer(out, out_len, || {
        let Some((path, text)) = text(query, query_len)?.split_once('\n') else {
            return Err((EINVAL, "a write is a path, then its text".to_owned()));
        };
        landed(Path::new(path), text.as_bytes(), true)?;
        Ok("written".to_owned())
    })
}

/// A file of lines written in place: the path, then the text after the
/// first newline. Its directory is made, and the text is written as
/// `std::fs::write` writes — through a link standing at the path, to the
/// file it names, and into a file already there without replacing it —
/// which is how the Rust tool's `merge` lays a file of lines down. The
/// answer is `written`.
///
/// # Safety
///
/// As [`hist_store_locate`].
#[no_mangle]
pub unsafe extern "C" fn hist_folder_through(
    query: *const c_char,
    query_len: usize,
    out: *mut *mut c_char,
    out_len: *mut usize,
) -> i32 {
    answer(out, out_len, || {
        let Some((path, text)) = text(query, query_len)?.split_once('\n') else {
            return Err((EINVAL, "a write is a path, then its text".to_owned()));
        };
        let path = Path::new(path);
        if let Some(directory) = path.parent() {
            fs::create_dir_all(directory).map_err(|error| (code(&error), format!("{}: {error}", directory.display())))?;
        }
        fs::write(path, text).map_err(|error| (code(&error), format!("{}: {error}", path.display())))?;
        Ok("written".to_owned())
    })
}

/// A payload laid into the folder: where the store holds it, where it goes,
/// and the digest it must have, a line each. The bytes are read, hashed, and
/// refused where they are not that digest, with nothing written; otherwise
/// they land staged and renamed over whatever stood there, a new file, as
/// the Rust tool's `copy_payload_to` lays one. The answer is `written`.
///
/// # Safety
///
/// As [`hist_store_locate`].
#[no_mangle]
pub unsafe extern "C" fn hist_folder_lay(
    query: *const c_char,
    query_len: usize,
    out: *mut *mut c_char,
    out_len: *mut usize,
) -> i32 {
    answer(out, out_len, || {
        let mut lines = text(query, query_len)?.split('\n');
        let (Some(from), Some(to), Some(wanted), None) =
            (lines.next(), lines.next(), lines.next(), lines.next())
        else {
            return Err((EINVAL, "a payload laid is where it is, where it goes, and its digest".to_owned()));
        };
        let bytes = fs::read(from).map_err(|error| (code(&error), format!("{from}: {error}")))?;
        let found = digest(&bytes);
        if found != wanted {
            return Err((EIO, format!("{from} holds {found} rather than {wanted}")));
        }
        landed(Path::new(to), &bytes, false)?;
        Ok("written".to_owned())
    })
}

/// A link made in the folder: its path, then where it points. Its directory
/// is made, and the link is made at a sibling and renamed over whatever
/// stood there, so there is no moment the path names nothing. The answer is
/// `linked`.
///
/// # Safety
///
/// As [`hist_store_locate`].
#[no_mangle]
pub unsafe extern "C" fn hist_folder_link(
    query: *const c_char,
    query_len: usize,
    out: *mut *mut c_char,
    out_len: *mut usize,
) -> i32 {
    answer(out, out_len, || {
        let Some((path, target)) = text(query, query_len)?.split_once('\n') else {
            return Err((EINVAL, "a link is a path, then where it points".to_owned()));
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
        let done = std::os::unix::fs::symlink(target, &staged).and_then(|()| fs::rename(&staged, path));
        if let Err(error) = done {
            let _ = fs::remove_file(&staged);
            return Err(failed(path, error));
        }
        Ok("linked".to_owned())
    })
}

/// A file's execute bit set: its path, then `1` or `0`. The bit is asked of
/// the path itself, a link standing there included, as the Rust tool's
/// `executable` asks it; only where that differs is anything set, and then
/// on what the path names, the execute bits following its read bits, as
/// the Rust tool's `set_executable` sets them — so a file its group may read
/// its group may run and a private file stays private. The answer is what
/// the bit was before, `1` or `0`: whether that is a change a person is told
/// of is the Bend side's.
///
/// # Safety
///
/// As [`hist_store_locate`].
#[no_mangle]
pub unsafe extern "C" fn hist_folder_chmod(
    query: *const c_char,
    query_len: usize,
    out: *mut *mut c_char,
    out_len: *mut usize,
) -> i32 {
    use std::os::unix::fs::PermissionsExt as _;

    answer(out, out_len, || {
        let (path, runs) = match text(query, query_len)?.split_once('\n') {
            Some((path, "1")) => (path, true),
            Some((path, "0")) => (path, false),
            _ => return Err((EINVAL, "a mode is a path, then `1` or `0`".to_owned())),
        };
        let failed = |error: std::io::Error| (code(&error), format!("{path}: {error}"));
        let was = fs::symlink_metadata(path).map_err(failed)?.permissions().mode() & 0o111 != 0;
        if was != runs {
            let mut permissions = fs::metadata(path).map_err(failed)?.permissions();
            let held = permissions.mode();
            let mode = if runs { held | ((held & 0o444) >> 2) } else { held & !0o111 };
            if mode != held {
                permissions.set_mode(mode);
                fs::set_permissions(path, permissions).map_err(failed)?;
            }
        }
        Ok(if was { "1" } else { "0" }.to_owned())
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

/// Every document this store holds, by the digest of its bytes; and the
/// paths of the documents that say they forget each digest.
///
/// A digest two paths share resolves to the lesser path, which is the first
/// one a sorted listing reaches — so this and a reader walking the listing
/// itself answer alike.
fn index(root: &Path) -> Result<(BTreeMap<String, String>, BTreeMap<String, Vec<String>>), (i32, String)> {
    let mut paths = Vec::new();
    for dir in DOCUMENT_DIRS {
        walk(root, &root.join(dir), &mut paths)?;
    }
    let held: BTreeSet<&str> = paths.iter().map(String::as_str).collect();

    // What the catalogue accounts for: the paths it names that are still
    // there. A path it has lost is dropped, and a path it never named is
    // read below, which is the whole of the condition decision 0036 states.
    let mut at = BTreeMap::new();
    let mut forgetting: BTreeMap<String, Vec<String>> = BTreeMap::new();
    let mut accounted = BTreeSet::new();
    let catalogue = fs::read_to_string(root.join(CACHE_DIR).join(CATALOGUE_FILE)).unwrap_or_default();
    let mut lines = catalogue.lines();
    if lines.next() == Some(CATALOGUE_HEADER) {
        for line in lines {
            let mut fields = line.splitn(3, ' ');
            let (Some(digest), Some(forgets), Some(path)) =
                (fields.next(), fields.next(), fields.next())
            else {
                continue;
            };
            if digest.len() != DIGEST_CHARS || !held.contains(path) {
                continue;
            }
            remember(&mut at, digest, path);
            if forgets.len() == DIGEST_CHARS {
                forgetting.entry(forgets.to_owned()).or_default().push(path.to_owned());
            }
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
        if let Some(forgets) = forgets_of(&bytes) {
            forgetting.entry(forgets.to_owned()).or_default().push(path.to_owned());
        }
    }
    Ok((at, forgetting))
}

/// The digest a document's first header says it forgets, in any of the
/// three grammars: every forgetting document opens `historica`, then
/// `forgets` and a digest. Whether it is one is the reader's to decide.
fn forgets_of(bytes: &[u8]) -> Option<&str> {
    const OPENING: &[u8] = b"historica\nforgets ";
    let rest = bytes.strip_prefix(OPENING)?;
    let digest = rest.get(..DIGEST_CHARS)?;
    if rest.get(DIGEST_CHARS) != Some(&b'\n') || !digest.iter().all(|b| b.is_ascii_hexdigit() && !b.is_ascii_uppercase()) {
        return None;
    }
    std::str::from_utf8(digest).ok()
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
        use std::os::unix::ffi::OsStrExt as _;
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
        // A name that is not UTF-8 is listed as its lossy spelling, in the
        // order its bytes sort in: after `run.sh`, as 0xff is after `r`.
        fs::write(root.join(std::ffi::OsStr::from_bytes(b"x\xff.md")), "").unwrap();

        let (code, listed) = call(hist_folder_list, root.to_str().unwrap().as_bytes());
        assert_eq!(code, 0, "{listed}");
        assert_eq!(listed, "l a-link\nnotes\nf 0 4 b.txt\nd notes\nf 1 10 run.sh\nu x\u{fffd}.md");

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
        let (code, text) = call(hist_store_list, format!("{root}\nworking").as_bytes());
        assert_eq!(code, EINVAL);
        assert_eq!(text, "`working` is not a directory this lists");

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
    fn a_destroyed_payload_takes_its_emptied_directory_and_leaves_operations() {
        // `forget` destroys a document or a payload through the same removal
        // a bookmark goes through: the file, and each directory it leaves
        // empty up to `operations/`, which stays.
        let dir = tempfile::tempdir().unwrap();
        let operations = dir.path().join("operations");
        fs::create_dir_all(operations.join("2026-09/2026-09-24 first")).unwrap();
        fs::create_dir_all(operations.join("2026-09/2026-09-24 second")).unwrap();
        fs::write(operations.join("2026-09/2026-09-24 first/photo.bin"), b"\x00\x01").unwrap();
        fs::write(operations.join("2026-09/2026-09-24 second/notes.md.ops.txt"), "historica\n").unwrap();
        fs::write(operations.join("2026-09/2026-09-24 second/photo.bin"), b"\x00\x02").unwrap();
        let asked = |file: &str| call(hist_store_remove, format!("{}\n{}", operations.display(), operations.join(file).display()).as_bytes());

        assert_eq!(asked("2026-09/2026-09-24 second/notes.md.ops.txt"), (0, "removed".to_owned()));
        assert!(operations.join("2026-09/2026-09-24 second/photo.bin").exists());
        assert_eq!(asked("2026-09/2026-09-24 first/photo.bin"), (0, "removed".to_owned()));
        assert!(!operations.join("2026-09/2026-09-24 first").exists());
        assert!(operations.join("2026-09").is_dir());
        assert_eq!(asked("2026-09/2026-09-24 second/photo.bin"), (0, "removed".to_owned()));
        assert!(!operations.join("2026-09").exists());
        assert!(operations.is_dir(), "operations/ itself stays");
    }

    #[test]
    fn an_empty_directory_is_removed_and_one_holding_anything_refused() {
        let dir = tempfile::tempdir().unwrap();
        let operations = dir.path().join("operations");
        fs::create_dir_all(operations.join("2026-09/empty/deeper")).unwrap();
        fs::create_dir_all(operations.join("2026-09/held")).unwrap();
        fs::write(operations.join("2026-09/held/notes.md"), "one\n").unwrap();
        let asked = |path: &str| call(hist_store_remove, format!("{}\n{}", operations.display(), operations.join(path).display()).as_bytes());

        assert_eq!(asked("2026-09/held").0 != 0, true, "a directory holding a file stays");
        assert!(operations.join("2026-09/held/notes.md").exists());
        assert_eq!(asked("2026-09/empty/deeper"), (0, "removed".to_owned()));
        assert!(!operations.join("2026-09/empty").exists(), "the directory it emptied goes with it");
        assert!(operations.join("2026-09/held").is_dir());
        assert_eq!(asked("2026-09/gone"), (0, "absent".to_owned()));
    }

    #[test]
    fn a_digest_is_answered_with_what_forgets_it_when_asked() {
        let dir = tempfile::tempdir().unwrap();
        let root = dir.path();
        store(root);
        let history = root.join("history");
        let original = "one\n";
        let target = digest(original.as_bytes());
        let standing = format!("historica\nforgets {target}\n\ninsert 0\n\\ forgotten\n");
        fs::write(history.join("operations/b.ops.txt"), &standing).unwrap();
        fs::write(history.join("operations/a.ops.txt"), format!("historica\nforgets {target}\nlength 4\n")).unwrap();
        let plain = format!("{}\n{target}", history.display());
        let (code, at) = call(hist_store_at, plain.as_bytes());
        assert_eq!((code, at.as_str()), (0, "operations/2026-09/x/notes.txt"));
        let asked = format!("{}\nforgets\n{target}\n{}", history.display(), "0".repeat(64));
        let (code, at) = call(hist_store_at, asked.as_bytes());
        assert_eq!(code, 0, "{at}");
        assert_eq!(at, format!("operations/2026-09/x/notes.txt\n-\n{target} operations/a.ops.txt\n{target} operations/b.ops.txt"));

        // A catalogue's `forgets` column is taken for a path it accounts for,
        // as the Rust store takes it: here it says the stand-in forgets nothing.
        fs::write(
            history.join("cache/operations.txt"),
            format!("historica-catalogue-1\n{} - operations/b.ops.txt\n", digest(standing.as_bytes())),
        )
        .unwrap();
        let (_, at) = call(hist_store_at, asked.as_bytes());
        assert_eq!(at, format!("operations/2026-09/x/notes.txt\n-\n{target} operations/a.ops.txt"));
    }

    #[test]
    fn the_cache_is_listed_only_when_asked_for() {
        let dir = tempfile::tempdir().unwrap();
        let root = dir.path();
        store(root);
        let history = root.join("history");
        fs::write(history.join("cache").join("0".repeat(64)), "a state\n").unwrap();
        let (code, listed) = call(hist_store_list, format!("{}\ncache", history.display()).as_bytes());
        assert_eq!(code, 0, "{listed}");
        assert_eq!(listed, format!("cache/{}\ncache/README.txt", "0".repeat(64)));
        let (code, listed) = call(hist_store_list, history.display().to_string().as_bytes());
        assert_eq!(code, 0, "{listed}");
        assert!(!listed.contains("cache/"), "{listed}");
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

        // Tidying from another spelling of the path: the file goes, and the
        // directory it was in stays where the other spelling names nothing.
        fs::create_dir_all(names.join("de\u{301}j")).unwrap();
        fs::write(names.join("de\u{301}j/z.txt"), "").unwrap();
        let (file, tidy) = (names.join("de\u{301}j/z.txt"), names.join("d\u{e9}j/z.txt"));
        let query = format!("{}\n{}\n{}", names.display(), file.display(), tidy.display());
        assert_eq!(call(hist_store_remove, query.as_bytes()), (0, "removed".to_owned()));
        assert!(!file.exists());
        assert!(names.join("de\u{301}j").is_dir());
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

    #[test]
    fn a_pinned_seed_is_drawn_as_historica_pinned_draws_it() {
        // One test owns the process's environment and its stream: the
        // others here never set either variable.
        std::env::set_var(PINNED_SEED, "a seed");
        std::env::set_var(PINNED_NOW, "2026-01-02T03:04:05+01:00");
        let mut expected = Vec::new();
        for block in 0u64..2 {
            let mut hash = Sha256::new();
            hash.update(b"a seed");
            hash.update(block.to_be_bytes());
            expected.extend(hash.finalize());
        }
        let hex: String = expected.iter().map(|byte| format!("{byte:02x}")).collect();
        // Twelve bytes, then twenty-four: the second call carries on across
        // the block boundary where the first stopped.
        assert_eq!(call(hist_entropy_fill, b"12"), (0, hex[..24].to_owned()));
        assert_eq!(call(hist_entropy_fill, b"24"), (0, hex[24..72].to_owned()));
        assert_eq!(call(hist_clock_now, b""), (0, "2026-01-02T03:04:05+01:00".to_owned()));
        std::env::remove_var(PINNED_SEED);
        std::env::remove_var(PINNED_NOW);
    }

    #[test]
    fn a_count_that_is_not_one_is_refused() {
        assert_eq!(call(hist_entropy_fill, b"twelve").0, EINVAL);
    }

    #[test]
    fn a_document_is_filed_once_and_its_name_is_held_to_its_bytes() {
        let dir = tempfile::tempdir().unwrap();
        let file = dir.path().join("operations/2026-01/a b/one.txt");
        let query = format!("{}\none\n", file.display());
        assert_eq!(call(hist_store_once, query.as_bytes()), (0, "written".to_owned()));
        assert_eq!(fs::read_to_string(&file).unwrap(), "one\n");
        assert_eq!(call(hist_store_once, query.as_bytes()), (0, "there".to_owned()));
        let other = format!("{}\ntwo\n", file.display());
        let (code, said) = call(hist_store_once, other.as_bytes());
        assert_eq!(code, EIO);
        assert!(said.ends_with("is named for a digest its bytes do not have"), "{said}");
        assert_eq!(fs::read_to_string(&file).unwrap(), "one\n");
    }

    #[test]
    fn a_copy_is_refused_when_the_bytes_moved_on() {
        let dir = tempfile::tempdir().unwrap();
        let from = dir.path().join("photo.bin");
        fs::write(&from, b"\x00\xff").unwrap();
        let to = dir.path().join("history/operations/x/photo.bin");
        let query = format!("{}\n{}\n{}", from.display(), to.display(), digest(b"\x00\xff"));
        assert_eq!(call(hist_store_copy, query.as_bytes()), (0, "written".to_owned()));
        assert_eq!(fs::read(&to).unwrap(), b"\x00\xff");
        let stale = format!("{}\n{}.2\n{}", from.display(), to.display(), digest(b"other"));
        let (code, said) = call(hist_store_copy, stale.as_bytes());
        assert_eq!(code, EIO);
        assert!(said.contains("changed while it was being copied"), "{said}");
        assert!(!dir.path().join("history/operations/x/photo.bin.2").exists());
    }

    #[test]
    fn a_file_of_lines_is_written_over_keeping_its_bit_and_a_new_one_is_plain() {
        use std::os::unix::fs::PermissionsExt as _;

        let dir = tempfile::tempdir().unwrap();
        let run = dir.path().join("run.sh");
        fs::write(&run, "old\n").unwrap();
        fs::set_permissions(&run, fs::Permissions::from_mode(0o750)).unwrap();
        let query = format!("{}\nnew\nlines\n", run.display());
        assert_eq!(call(hist_folder_put, query.as_bytes()), (0, "written".to_owned()));
        assert_eq!(fs::read_to_string(&run).unwrap(), "new\nlines\n");
        assert_eq!(fs::metadata(&run).unwrap().permissions().mode() & 0o777, 0o750);

        let deep = dir.path().join("a/b/new.md");
        assert_eq!(call(hist_folder_put, format!("{}\n", deep.display()).as_bytes()), (0, "written".to_owned()));
        assert_eq!(fs::read(&deep).unwrap(), b"");
        assert_eq!(fs::metadata(&deep).unwrap().permissions().mode() & 0o111, 0);
        assert_eq!(fs::read_dir(dir.path().join("a/b")).unwrap().count(), 1, "nothing staged is left");
        assert_eq!(call(hist_folder_put, b"no newline").0, EINVAL);
    }

    #[test]
    fn a_payload_is_laid_as_a_new_file_and_refused_where_its_bytes_differ() {
        use std::os::unix::fs::PermissionsExt as _;

        let dir = tempfile::tempdir().unwrap();
        let from = dir.path().join("history/operations/x/photo.bin");
        fs::create_dir_all(from.parent().unwrap()).unwrap();
        fs::write(&from, b"\x00\xff").unwrap();
        let to = dir.path().join("photo.bin");
        fs::write(&to, b"old").unwrap();
        fs::set_permissions(&to, fs::Permissions::from_mode(0o755)).unwrap();
        let query = format!("{}\n{}\n{}", from.display(), to.display(), digest(b"\x00\xff"));
        assert_eq!(call(hist_folder_lay, query.as_bytes()), (0, "written".to_owned()));
        assert_eq!(fs::read(&to).unwrap(), b"\x00\xff");
        assert_eq!(fs::metadata(&to).unwrap().permissions().mode() & 0o111, 0);

        let other = dir.path().join("other.bin");
        let stale = format!("{}\n{}\n{}", from.display(), other.display(), digest(b"other"));
        let (code, said) = call(hist_folder_lay, stale.as_bytes());
        assert_eq!(code, EIO);
        assert!(said.contains("rather than"), "{said}");
        assert!(!other.exists());
    }

    #[test]
    fn a_link_is_made_over_whatever_stood_there() {
        let dir = tempfile::tempdir().unwrap();
        let at = dir.path().join("sub/current");
        let query = format!("{}\n../notes.md", at.display());
        assert_eq!(call(hist_folder_link, query.as_bytes()), (0, "linked".to_owned()));
        assert_eq!(fs::read_link(&at).unwrap(), Path::new("../notes.md"));
        fs::remove_file(&at).unwrap();
        fs::write(&at, "a file\n").unwrap();
        let query = format!("{}\n/etc/hosts", at.display());
        assert_eq!(call(hist_folder_link, query.as_bytes()), (0, "linked".to_owned()));
        assert_eq!(fs::read_link(&at).unwrap(), Path::new("/etc/hosts"));
        assert_eq!(fs::read_dir(dir.path().join("sub")).unwrap().count(), 1, "nothing staged is left");
    }

    #[test]
    fn a_bit_is_set_as_the_read_bits_say_and_what_it_was_is_answered() {
        use std::os::unix::fs::PermissionsExt as _;

        let dir = tempfile::tempdir().unwrap();
        let file = dir.path().join("run.sh");
        fs::write(&file, "#!/bin/sh\n").unwrap();
        fs::set_permissions(&file, fs::Permissions::from_mode(0o640)).unwrap();
        let on = format!("{}\n1", file.display());
        assert_eq!(call(hist_folder_chmod, on.as_bytes()), (0, "0".to_owned()));
        assert_eq!(fs::metadata(&file).unwrap().permissions().mode() & 0o777, 0o750);
        assert_eq!(call(hist_folder_chmod, on.as_bytes()), (0, "1".to_owned()));
        let off = format!("{}\n0", file.display());
        assert_eq!(call(hist_folder_chmod, off.as_bytes()), (0, "1".to_owned()));
        assert_eq!(fs::metadata(&file).unwrap().permissions().mode() & 0o777, 0o640);
        assert_eq!(call(hist_folder_chmod, format!("{}\n2", file.display()).as_bytes()).0, EINVAL);
        assert_eq!(call(hist_folder_chmod, format!("{}\n1", dir.path().join("gone").display()).as_bytes()).0, ENOENT);

        // A bit already as asked is left, however the read bits stand.
        fs::set_permissions(&file, fs::Permissions::from_mode(0o744)).unwrap();
        assert_eq!(call(hist_folder_chmod, on.as_bytes()), (0, "1".to_owned()));
        assert_eq!(fs::metadata(&file).unwrap().permissions().mode() & 0o777, 0o744);

        // A link is asked about itself, and what it names is what is set.
        let link = dir.path().join("link");
        std::os::unix::fs::symlink("run.sh", &link).unwrap();
        fs::set_permissions(&file, fs::Permissions::from_mode(0o644)).unwrap();
        assert_eq!(call(hist_folder_chmod, format!("{}\n1", link.display()).as_bytes()), (0, "1".to_owned()));
        assert_eq!(fs::metadata(&file).unwrap().permissions().mode() & 0o777, 0o644);
        assert_eq!(call(hist_folder_chmod, format!("{}\n0", link.display()).as_bytes()), (0, "1".to_owned()));
        assert_eq!(fs::metadata(&file).unwrap().permissions().mode() & 0o777, 0o644);
    }

    #[test]
    fn a_file_of_lines_is_written_through_a_link_and_in_place() {
        use std::os::unix::fs::PermissionsExt as _;

        let dir = tempfile::tempdir().unwrap();
        let real = dir.path().join("real");
        fs::create_dir_all(&real).unwrap();
        fs::write(real.join("f.txt"), "old\n").unwrap();
        let at = dir.path().join("f.md");
        std::os::unix::fs::symlink("real/f.txt", &at).unwrap();
        let query = format!("{}\nnew\n", at.display());
        assert_eq!(call(hist_folder_through, query.as_bytes()), (0, "written".to_owned()));
        assert_eq!(fs::read_link(&at).unwrap(), Path::new("real/f.txt"));
        assert_eq!(fs::read(real.join("f.txt")).unwrap(), b"new\n");

        let dangling = dir.path().join("g.md");
        std::os::unix::fs::symlink("real/g.txt", &dangling).unwrap();
        assert_eq!(call(hist_folder_through, format!("{}\ng\n", dangling.display()).as_bytes()), (0, "written".to_owned()));
        assert_eq!(fs::read(real.join("g.txt")).unwrap(), b"g\n");

        let plain = dir.path().join("sub/run.sh");
        fs::create_dir_all(plain.parent().unwrap()).unwrap();
        fs::write(&plain, "x").unwrap();
        fs::set_permissions(&plain, fs::Permissions::from_mode(0o750)).unwrap();
        assert_eq!(call(hist_folder_through, format!("{}\ny\n", plain.display()).as_bytes()), (0, "written".to_owned()));
        assert_eq!(fs::read(&plain).unwrap(), b"y\n");
        assert_eq!(fs::metadata(&plain).unwrap().permissions().mode() & 0o777, 0o750);

        let deep = dir.path().join("a/b/new.md");
        assert_eq!(call(hist_folder_through, format!("{}\n", deep.display()).as_bytes()), (0, "written".to_owned()));
        assert_eq!(fs::read(&deep).unwrap(), b"");
        assert_eq!(call(hist_folder_through, b"no newline").0, EINVAL);
    }
}
