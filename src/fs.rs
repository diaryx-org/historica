//! The filesystem historica asks for, and the one it ships.
//!
//! Everything this crate persists is files in a folder, and decision 0003 is
//! emphatic that this is the point: a store is readable without the tool
//! because it is a directory a person can open. None of that says the
//! directory has to be `std::fs`. An application that holds its documents
//! through a document provider — iCloud, a security-scoped bookmark, an
//! Android content URI — has a folder in every sense the format cares about
//! and no `std::fs` path that reaches it.
//!
//! So the library asks for [`Filesystem`] and the binary supplies [`Disk`].
//!
//! ```
//! use historica::fs::Disk;
//! use historica::store::Store;
//! use std::sync::Arc;
//!
//! # fn main() -> Result<(), Box<dyn std::error::Error>> {
//! # let root = std::env::temp_dir().join("historica-doc-example");
//! # let _ = std::fs::remove_dir_all(&root);
//! let store = Store::init_on(Arc::new(Disk), &root)?;
//! assert!(store.is_empty());
//! # let _ = std::fs::remove_dir_all(&root);
//! # Ok(())
//! # }
//! ```
//!
//! # Where the type parameter is, and why
//!
//! [`Store`](crate::store::Store) and [`Working`](crate::working::Working) each
//! carry the filesystem as a type parameter, defaulting to [`Disk`]. That is
//! not primarily about dispatch — it is about **not asking implementations for
//! capabilities they may not have**. A trait behind an `Arc` has to require
//! `Debug + Send + Sync`, because that is what makes a store holding one
//! `Debug` and `Send`; a type parameter makes those derived implementations
//! conditional instead, so a host whose filesystem is a Swift object or a
//! `JsValue` gets a `Store` with exactly the capabilities its own filesystem
//! has, and never has to write `unsafe impl Send` to be allowed in.
//!
//! Dynamic dispatch is still available, and is a choice rather than the
//! architecture: `Arc<T>`, `Box<T>`, `Rc<T>` and `&T` are all filesystems when
//! `T` is, so `Store<Arc<dyn Filesystem>>` is a store that decided its
//! filesystem at run time.
//!
//! # What is abstracted, and what is not
//!
//! **Operations are.** Reading bytes, creating a file that must not already
//! exist, listing a directory without following what it links to.
//!
//! **Naming is not.** A path is still [`std::path::Path`], which decision 0018
//! already argued for from the other side: a path is filed as a path, with
//! real directories for real components, because the filesystem already has a
//! separator. An implementation backed by something that is not a filesystem
//! is free to treat the path as an opaque key — it is a sequence of components
//! and this crate never asks it for anything else. `std::path` is not
//! `std::fs`, and a target that lacks the second still has the first.
//!
//! **Errors are not.** [`std::io::Error`] is the currency, because the two
//! kinds this crate reasons about — [`NotFound`] and [`AlreadyExists`] — are
//! the whole of the vocabulary it needs, and inventing a parallel error type
//! would make every implementation translate into it and every caller
//! translate back out.
//!
//! [`NotFound`]: std::io::ErrorKind::NotFound
//! [`AlreadyExists`]: std::io::ErrorKind::AlreadyExists

use std::io;
use std::path::{Path, PathBuf};

/// What something in a directory turned out to be.
///
/// Looked at **without following symbolic links**, which is the distinction
/// the whole enum exists for: decision 0011 refuses a link in the working
/// copy and the store walk refuses one too, and a `Kind` that had already
/// followed it would report the thing at the other end as a file of this
/// store.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[non_exhaustive]
pub enum Kind {
    /// A regular file.
    File,
    /// A directory.
    Directory,
    /// A symbolic link, whatever it points at.
    Symlink,
    /// Something else a platform has and this format has no use for.
    Other,
}

impl Kind {
    /// Whether this is a regular file.
    pub fn is_file(self) -> bool {
        self == Kind::File
    }

    /// Whether this is a directory.
    pub fn is_directory(self) -> bool {
        self == Kind::Directory
    }

    /// Whether this is a symbolic link.
    pub fn is_symlink(self) -> bool {
        self == Kind::Symlink
    }
}

/// One thing found in a directory.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Entry {
    /// Where it is, as the directory's path with the entry's name pushed onto
    /// it — so an entry can be read without rebuilding the path it came from.
    pub path: PathBuf,
    /// What it is, having followed nothing.
    pub kind: Kind,
}

/// The folder a store lives in, whoever is holding it.
///
/// Eight methods, and the fewest that the store, the working copy, and `check`
/// between them actually perform. Every one takes `&self`, because a store
/// reads through its filesystem while handing out references to its own
/// documents — so an implementation that needs mutable state of its own keeps
/// it behind a cell or a lock.
///
/// **No supertraits.** Not `Send`, not `Sync`, not `Debug`. Whatever this is,
/// a [`Store`](crate::store::Store) holding it is exactly as capable: a
/// filesystem that is `Send` makes a store that is, and one that is not makes
/// one that is not. Nothing here needs a host to promise something about a
/// handle it did not choose the shape of.
///
/// # What an implementation must get right
///
/// **The two error kinds.** This crate branches on
/// [`NotFound`](io::ErrorKind::NotFound) and
/// [`AlreadyExists`](io::ErrorKind::AlreadyExists) and on nothing else. An
/// absent file must report the first, from every method that can meet one, and
/// [`create_new`](Filesystem::create_new) must report the second. An
/// implementation that returns [`Other`](io::ErrorKind::Other) for a missing
/// file turns "this store has no `skipped.txt`", which is ordinary, into an
/// error that stops a store opening.
///
/// **`create_new` is one operation.** It is the whole of this format's
/// concurrency story. Decision 0003 makes a store append-only and names every
/// file by the digest of its bytes, so two writers that produce one revision
/// produce one file and neither has to win — but only if the create and the
/// test-for-existence cannot be split. An implementation that checks and then
/// writes has a window in it, and the thing that fits in the window is a
/// half-written document under a name that promises its digest.
///
/// **Nothing follows a link.** [`entries`](Filesystem::entries) and
/// [`look`](Filesystem::look) report [`Kind::Symlink`] and stop. This is what
/// makes an unbounded walk safe: a tree of real directories cannot contain
/// itself, so there is no loop to guard against and no depth to cap.
///
/// **Order is not promised.** [`entries`](Filesystem::entries) may return a
/// directory in any order; this crate sorts what it needs sorted, because two
/// replicas loading one store must agree and a `readdir` order is not
/// something either of them chose.
pub trait Filesystem {
    /// Every byte of one file.
    fn read(&self, path: &Path) -> io::Result<Vec<u8>>;

    /// Write a file, replacing whatever was there.
    ///
    /// Used only for the store's mutable files — the version header, a
    /// bookmark, `skipped.txt` — which decision 0003 counts on one hand and
    /// calls the store's entire conflict surface. Everything else is written
    /// with [`create_new`](Filesystem::create_new).
    fn write(&self, path: &Path, bytes: &[u8]) -> io::Result<()>;

    /// Write a file that must not already exist, indivisibly.
    ///
    /// Fails with [`AlreadyExists`](io::ErrorKind::AlreadyExists) if it does,
    /// and the caller then reads what is there and confirms it is the same
    /// bytes — which it must be, since the name is the digest.
    fn create_new(&self, path: &Path, bytes: &[u8]) -> io::Result<()>;

    /// Make a directory and every directory above it, succeeding if it is
    /// already there.
    fn create_directory(&self, path: &Path) -> io::Result<()>;

    /// What one directory holds, in no promised order, following nothing.
    ///
    /// The paths are `path` with each name pushed onto it.
    fn entries(&self, path: &Path) -> io::Result<Vec<Entry>>;

    /// What is at a path, or `None` if nothing is.
    ///
    /// Absence is `Ok(None)` rather than an error, because every caller here
    /// is asking whether something is there and none of them treat "no" as a
    /// fault. An error means the question could not be answered.
    fn look(&self, path: &Path) -> io::Result<Option<Kind>>;

    /// Remove one file.
    fn remove_file(&self, path: &Path) -> io::Result<()>;

    /// Remove one directory, **failing if it is not empty**.
    ///
    /// The refusal is the feature. `arrange` and `prune` tidy the directories
    /// they empty by walking upwards until one refuses, which is a correct
    /// stop only because a directory holding anything says so. An
    /// implementation that removed a directory recursively here would delete a
    /// person's history one level at a time.
    fn remove_directory(&self, path: &Path) -> io::Result<()>;
}

/// A reference to a filesystem is a filesystem.
impl<T: Filesystem + ?Sized> Filesystem for &T {
    fn read(&self, path: &Path) -> io::Result<Vec<u8>> {
        (**self).read(path)
    }
    fn write(&self, path: &Path, bytes: &[u8]) -> io::Result<()> {
        (**self).write(path, bytes)
    }
    fn create_new(&self, path: &Path, bytes: &[u8]) -> io::Result<()> {
        (**self).create_new(path, bytes)
    }
    fn create_directory(&self, path: &Path) -> io::Result<()> {
        (**self).create_directory(path)
    }
    fn entries(&self, path: &Path) -> io::Result<Vec<Entry>> {
        (**self).entries(path)
    }
    fn look(&self, path: &Path) -> io::Result<Option<Kind>> {
        (**self).look(path)
    }
    fn remove_file(&self, path: &Path) -> io::Result<()> {
        (**self).remove_file(path)
    }
    fn remove_directory(&self, path: &Path) -> io::Result<()> {
        (**self).remove_directory(path)
    }
}

/// Forward every method to whatever is inside the pointer.
///
/// This is what keeps dynamic dispatch a choice: `Arc<dyn Filesystem>` is
/// itself a `Filesystem`, so `Store<Arc<dyn Filesystem>>` is the store that
/// decided at run time, and it is spelled in the type rather than imposed on
/// everybody.
macro_rules! forwarding {
    ($holder:ty) => {
        impl<T: Filesystem + ?Sized> Filesystem for $holder {
            fn read(&self, path: &Path) -> io::Result<Vec<u8>> {
                (**self).read(path)
            }
            fn write(&self, path: &Path, bytes: &[u8]) -> io::Result<()> {
                (**self).write(path, bytes)
            }
            fn create_new(&self, path: &Path, bytes: &[u8]) -> io::Result<()> {
                (**self).create_new(path, bytes)
            }
            fn create_directory(&self, path: &Path) -> io::Result<()> {
                (**self).create_directory(path)
            }
            fn entries(&self, path: &Path) -> io::Result<Vec<Entry>> {
                (**self).entries(path)
            }
            fn look(&self, path: &Path) -> io::Result<Option<Kind>> {
                (**self).look(path)
            }
            fn remove_file(&self, path: &Path) -> io::Result<()> {
                (**self).remove_file(path)
            }
            fn remove_directory(&self, path: &Path) -> io::Result<()> {
                (**self).remove_directory(path)
            }
        }
    };
}

forwarding!(std::sync::Arc<T>);
forwarding!(std::rc::Rc<T>);
forwarding!(Box<T>);

/// Read a file as text, refusing bytes that are not UTF-8.
///
/// `std::fs::read_to_string` decides this inside the read and reports
/// [`InvalidData`](io::ErrorKind::InvalidData); the trait has no such method,
/// because a decoding rule is not a filesystem's business and an
/// implementation should not have to know that this one exists. So the rule
/// lives here, once, and every caller gets the same error kind it used to.
pub fn read_to_string<F: Filesystem + ?Sized>(files: &F, path: &Path) -> io::Result<String> {
    let bytes = files.read(path)?;
    String::from_utf8(bytes).map_err(|error| io::Error::new(io::ErrorKind::InvalidData, error))
}

/// Whether anything is at this path.
pub fn exists<F: Filesystem + ?Sized>(files: &F, path: &Path) -> io::Result<bool> {
    Ok(files.look(path)?.is_some())
}

/// Whether a regular file is at this path, following nothing.
pub fn is_file<F: Filesystem + ?Sized>(files: &F, path: &Path) -> io::Result<bool> {
    Ok(files.look(path)?.is_some_and(Kind::is_file))
}

/// The filesystem the operating system is offering.
///
/// A unit struct, because `std::fs` is ambient: there is nothing to configure
/// and nothing to hold. Construct it as `Disk` and hand it to whichever `_on`
/// constructor wants it — or use the shorter constructors, which are this and
/// nothing more.
///
/// **Only a `Filesystem` with the `disk` feature**, which is on by default.
/// The type is named unconditionally so that it can be the default type
/// parameter of [`Store`](crate::store::Store) — a build without `disk` that
/// says `Store` rather than `Store<MyFilesystem>` is told, exactly, that
/// `Disk: Filesystem` is not satisfied.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct Disk;

#[cfg(feature = "disk")]
impl Filesystem for Disk {
    fn read(&self, path: &Path) -> io::Result<Vec<u8>> {
        std::fs::read(path)
    }

    fn write(&self, path: &Path, bytes: &[u8]) -> io::Result<()> {
        std::fs::write(path, bytes)
    }

    fn create_new(&self, path: &Path, bytes: &[u8]) -> io::Result<()> {
        use io::Write as _;

        let mut file = std::fs::OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(path)?;
        file.write_all(bytes)
    }

    fn create_directory(&self, path: &Path) -> io::Result<()> {
        std::fs::create_dir_all(path)
    }

    fn entries(&self, path: &Path) -> io::Result<Vec<Entry>> {
        let mut found = Vec::new();
        for entry in std::fs::read_dir(path)? {
            let entry = entry?;
            // `file_type` from a directory entry describes the link itself,
            // which is what this trait promises; `metadata` would follow it.
            found.push(Entry {
                path: entry.path(),
                kind: kind_of(entry.file_type()?),
            });
        }
        Ok(found)
    }

    fn look(&self, path: &Path) -> io::Result<Option<Kind>> {
        match std::fs::symlink_metadata(path) {
            Ok(metadata) => Ok(Some(kind_of(metadata.file_type()))),
            Err(error) if error.kind() == io::ErrorKind::NotFound => Ok(None),
            Err(error) => Err(error),
        }
    }

    fn remove_file(&self, path: &Path) -> io::Result<()> {
        std::fs::remove_file(path)
    }

    fn remove_directory(&self, path: &Path) -> io::Result<()> {
        std::fs::remove_dir(path)
    }
}

/// The order matters: a symlink to a directory is a symlink.
#[cfg(feature = "disk")]
fn kind_of(kind: std::fs::FileType) -> Kind {
    if kind.is_symlink() {
        Kind::Symlink
    } else if kind.is_dir() {
        Kind::Directory
    } else if kind.is_file() {
        Kind::File
    } else {
        Kind::Other
    }
}
