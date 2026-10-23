//! A historica [`Filesystem`] made of two maps.
//!
//! historica reaches a folder only through its `Filesystem` trait (its
//! decision 0025), and so does everything in [`crate::layer`]. Two things here
//! want a folder that is not on a disk.
//!
//! **The export.** An export is a store *written* somewhere, and where the
//! somewhere is a set of objects about to be sealed and handed to a stranger,
//! there is no directory on disk that should hold the plaintext even briefly —
//! so the export is written here, read back as bytes, and dropped. That is
//! the one place the crate chooses this over historica's `disk` for itself.
//!
//! **A caller's tests.** historica publishes its trait and [`Disk`], and no
//! filesystem that is not one: its own in-memory implementation lives in its
//! test suite. A caller that keeps layers and wants to drive them without a
//! temporary directory — every receive on a real disk pays for historica's
//! durable writes, which is most of what such a test spends its time on —
//! would otherwise have to write this file again. So it is public, and a
//! [`Repo`](super::Repo) or [`Layers`](super::Layers) opened `_on` an
//! `Arc<Memory>` is the whole of a layer held in memory.
//!
//! Nine methods over two `BTreeMap`s, after the implementation historica's
//! own test suite drives a whole history through. Paths are keys exactly as
//! they arrive; nothing is canonicalised because nothing asks for it. It is
//! more forgiving than a disk in one way worth knowing: a file may be written
//! under a directory nobody made, so a caller's own code that forgot to make
//! one is not caught here.
//!
//! [`Disk`]: historica::fs::Disk

use std::collections::{BTreeMap, BTreeSet};
use std::io;
use std::path::{Path, PathBuf};
use std::sync::Mutex;

use historica::fs::{Entry, Filesystem, Kind};

/// Files and directories in memory, and nothing else.
///
/// Shared by holding it in an `Arc` — `Arc<Memory>` is itself a
/// [`Filesystem`], and cloning it is how one set of files is handed to every
/// [`Repo`](super::Repo) and store that should see the same folder:
///
/// ```
/// use std::sync::Arc;
/// use historica_remark::layer::{Layers, Memory};
///
/// let files = Arc::new(Memory::default());
/// let layers = Layers::on(Arc::clone(&files), "/kept");
/// assert!(layers.names()?.is_empty());
/// # Ok::<(), historica_remark::Error>(())
/// ```
#[derive(Debug, Default)]
pub struct Memory {
    held: Mutex<Held>,
}

#[derive(Debug, Default)]
struct Held {
    files: BTreeMap<PathBuf, Vec<u8>>,
    directories: BTreeSet<PathBuf>,
}

fn missing(path: &Path) -> io::Error {
    io::Error::new(io::ErrorKind::NotFound, format!("{}", path.display()))
}

impl Filesystem for Memory {
    fn read(&self, path: &Path) -> io::Result<Vec<u8>> {
        let held = self.held.lock().expect("the lock");
        held.files.get(path).cloned().ok_or_else(|| missing(path))
    }

    fn write(&self, path: &Path, bytes: &[u8]) -> io::Result<()> {
        let mut held = self.held.lock().expect("the lock");
        held.files.insert(path.to_path_buf(), bytes.to_vec());
        Ok(())
    }

    fn create_new(&self, path: &Path, bytes: &[u8]) -> io::Result<()> {
        let mut held = self.held.lock().expect("the lock");
        if held.files.contains_key(path) {
            return Err(io::Error::new(
                io::ErrorKind::AlreadyExists,
                format!("{}", path.display()),
            ));
        }
        held.files.insert(path.to_path_buf(), bytes.to_vec());
        Ok(())
    }

    fn create_directory(&self, path: &Path) -> io::Result<()> {
        let mut held = self.held.lock().expect("the lock");
        for ancestor in path.ancestors() {
            held.directories.insert(ancestor.to_path_buf());
        }
        Ok(())
    }

    fn entries(&self, path: &Path) -> io::Result<Vec<Entry>> {
        let held = self.held.lock().expect("the lock");
        if !held.directories.contains(path) {
            return Err(missing(path));
        }
        let mut found = BTreeMap::new();
        let children = held
            .files
            .keys()
            .map(|file| (file, Kind::File))
            .chain(held.directories.iter().map(|dir| (dir, Kind::Directory)));
        for (candidate, kind) in children {
            if candidate == path {
                continue;
            }
            let Ok(relative) = candidate.strip_prefix(path) else {
                continue;
            };
            let mut components = relative.components();
            let Some(first) = components.next() else {
                continue;
            };
            let here = path.join(first);
            let kind = match components.next().is_some() {
                true => Kind::Directory,
                false => kind,
            };
            found.insert(here, kind);
        }
        Ok(found
            .into_iter()
            .map(|(path, kind)| Entry { path, kind })
            .collect())
    }

    fn look(&self, path: &Path) -> io::Result<Option<Kind>> {
        let held = self.held.lock().expect("the lock");
        if held.files.contains_key(path) {
            return Ok(Some(Kind::File));
        }
        if held.directories.contains(path) {
            return Ok(Some(Kind::Directory));
        }
        Ok(None)
    }

    fn rename(&self, from: &Path, to: &Path) -> io::Result<()> {
        let mut held = self.held.lock().expect("the lock");
        let bytes = held.files.remove(from).ok_or_else(|| missing(from))?;
        held.files.insert(to.to_path_buf(), bytes);
        Ok(())
    }

    fn remove_file(&self, path: &Path) -> io::Result<()> {
        let mut held = self.held.lock().expect("the lock");
        held.files
            .remove(path)
            .map(|_| ())
            .ok_or_else(|| missing(path))
    }

    fn remove_directory(&self, path: &Path) -> io::Result<()> {
        let mut held = self.held.lock().expect("the lock");
        if !held.directories.contains(path) {
            return Err(missing(path));
        }
        let occupied = held
            .files
            .keys()
            .chain(held.directories.iter())
            .any(|held| held != path && held.starts_with(path));
        if occupied {
            return Err(io::Error::new(
                io::ErrorKind::DirectoryNotEmpty,
                format!("{}", path.display()),
            ));
        }
        held.directories.remove(path);
        Ok(())
    }
}
