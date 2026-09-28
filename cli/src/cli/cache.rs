//! Where this machine keeps what a store has already read.
//!
//! Decision 0078 takes caches out of the store and gives them to the host,
//! and a store opened with nowhere named caches nothing. The command line is a
//! host, and it names one directory per store below a base it finds in this
//! order:
//!
//! 1. `--cache-dir <dir>`, before the command
//! 2. `HISTORICA_CACHE_DIR`
//! 3. `XDG_CACHE_HOME/historica` — honored on every platform, because a user
//!    who has set it has said where caches go
//! 4. `~/Library/Caches/historica` on macOS, `~/.cache/historica` elsewhere
//! 5. nowhere, if none of those can be determined — the store caches nothing
//!
//! Below the base, a store's directory is named by the digest of the path it
//! was found at. A store that moves starts again with nothing kept, which costs
//! one slow command; two stores never share a directory, which is the one
//! thing `Store::open_caching_on` asks of its caller.

use std::env;
use std::path::{Path, PathBuf};
use std::sync::Mutex;

use historica::format::digest;
use historica::store::{Store, StoreError};
use historica::working::{Working, WorkingError};

/// The base the command line decided on, for this run.
///
/// A lock rather than a `OnceLock` because [`super::run`] may be called more
/// than once in one process, and each call decides afresh.
static BASE: Mutex<Option<PathBuf>> = Mutex::new(None);

/// Decide the base for this run, from the flag if it was given.
pub(super) fn init(flag: Option<PathBuf>) {
    let base = flag
        .or_else(|| given("HISTORICA_CACHE_DIR"))
        .or_else(|| {
            given("XDG_CACHE_HOME")
                .filter(|path| path.is_absolute())
                .map(|path| path.join("historica"))
        })
        .or_else(platform)
        .map(|path| match path.is_absolute() {
            true => path,
            false => env::current_dir().map_or(path.clone(), |here| here.join(&path)),
        });
    *BASE.lock().unwrap_or_else(|poisoned| poisoned.into_inner()) = base;
}

/// An environment variable that holds a path, where it holds anything.
fn given(name: &str) -> Option<PathBuf> {
    env::var_os(name)
        .filter(|value| !value.is_empty())
        .map(PathBuf::from)
}

#[cfg(target_os = "macos")]
fn platform() -> Option<PathBuf> {
    given("HOME").map(|home| home.join("Library/Caches/historica"))
}

#[cfg(not(target_os = "macos"))]
fn platform() -> Option<PathBuf> {
    given("HOME").map(|home| home.join(".cache/historica"))
}

/// The directory one store's caches go in, or `None` where there is no base.
pub(super) fn for_store(root: &Path) -> Option<PathBuf> {
    let base = BASE
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner())
        .clone()?;
    // Canonical, so that `offer .` and a command run from a subdirectory name
    // the same store by the same path, and so the same directory.
    let root = root.canonicalize().unwrap_or_else(|_| root.to_path_buf());
    let named = digest(root.as_os_str().as_encoded_bytes()).to_string();
    Some(base.join(&named[..16]))
}

/// Open the store at `root`, caching where this run decided.
pub(super) fn open(root: &Path) -> Result<Store, StoreError> {
    match for_store(root) {
        Some(cache) => Store::open_caching(root, cache),
        None => Store::open(root),
    }
}

/// Walk the folder beside `store`, keeping what it hashes where `store` keeps
/// its own caches.
pub(super) fn working(repository: &Path, store: &Store) -> Result<Working, WorkingError> {
    match store.cache_directory() {
        Some(cache) => Working::read_caching(repository, store.skipped(), cache),
        None => Working::read(repository, store.skipped()),
    }
}
