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
//! **Operations are.** Reading bytes, atomically replacing a mutable file,
//! creating a file that must not already exist, listing a directory without
//! following what it links to, moving one to the name a person would rather
//! read.
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
use std::time::SystemTime;

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

/// What a directory already says about a file, without it being opened.
///
/// Decision 0043, and the whole of what a catalogue of the working folder
/// needs: two numbers that change when a file's bytes change, so that a digest
/// worked out once can be believed a second time. Nothing here is ever an
/// answer — it only ever says *whether the answer already known still stands* —
/// which is why a filesystem that cannot report it loses nothing but time.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Stamp {
    /// How many bytes the file holds.
    pub size: u64,
    /// When it was last written, as the platform reports it.
    pub modified: SystemTime,
}

/// A modification time as a whole number of nanoseconds either side of the
/// Unix epoch.
///
/// A readable integer, because everything in this repository that a person may
/// have to look at is readable — and one that compares as an instant does,
/// because the racy rule decisions 0043 and 0058 share is a comparison. `None`
/// for a time so far from the epoch that it does not fit, which is not a time
/// any file has.
pub(crate) fn nanoseconds(time: SystemTime) -> Option<i128> {
    match time.duration_since(SystemTime::UNIX_EPOCH) {
        Ok(since) => i128::try_from(since.as_nanos()).ok(),
        Err(before) => i128::try_from(before.duration().as_nanos())
            .ok()
            .map(|nanos| -nanos),
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
/// Nine methods, and the fewest that the store, the working copy, `check` and
/// `arrange` between them actually perform. Every one takes `&self`, because a store
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
/// **`write` replaces atomically.** Mutable files are the store's conflict
/// surface, but a conflict must be between two complete values. The old bytes
/// remain readable until all the new bytes can replace them in one operation;
/// a truncate followed by writes does not satisfy this contract.
///
/// **Nothing follows a link.** [`entries`](Filesystem::entries) and
/// [`look`](Filesystem::look) report [`Kind::Symlink`] and stop, and
/// [`link_target`](Filesystem::link_target) reads the link rather than what it
/// points at. This is what makes an unbounded walk safe: a tree of real
/// directories cannot contain itself, so there is no loop to guard against and
/// no depth to cap — and decision 0040, which writes links down, does not
/// relax it. Reading a link is what makes recording one safe; following one
/// would make a link pointing at `/` enumerate the machine.
///
/// **A mode is answered or declined, never guessed.**
/// [`executable`](Filesystem::executable) returns `None` where the filesystem
/// has no such bit, and an implementation that cannot see one must say so
/// rather than answer `false` — decision 0034 turns on the difference.
/// [`link_target`](Filesystem::link_target) is the same promise for decision
/// 0040, spelled the other way round: `Ok(None)` is reserved for a filesystem
/// that models no links at all, so an implementation that models them answers
/// with a target or with an error and never with `None`.
///
/// **A capability declined costs time and never an answer.**
/// [`stamp`](Filesystem::stamp) and
/// [`read_in_pieces`](Filesystem::read_in_pieces) are decision 0043's, and
/// they are the two methods here that nothing is allowed to *mean* anything
/// by. Both default to `None`; a filesystem that takes the default makes every
/// command read what it would have read before either existed, and gets the
/// same answers in the same words. That is what lets the trait offer a size
/// and a modification time at all, which decision 0025 kept out of it for the
/// good reason that identity comes from content — nothing here decides
/// anything by a clock, it only declines to re-read a file the directory says
/// nobody has written to.
///
/// **Order is not promised.** [`entries`](Filesystem::entries) may return a
/// directory in any order; this crate sorts what it needs sorted, because two
/// replicas loading one store must agree and a `readdir` order is not
/// something either of them chose.
pub trait Filesystem {
    /// Every byte of one file.
    fn read(&self, path: &Path) -> io::Result<Vec<u8>>;

    /// Write a file, atomically replacing whatever was there.
    ///
    /// Used for the store's mutable files — the version header, a bookmark,
    /// `skipped.txt` — which decision 0003 counts on one hand and calls the
    /// store's entire conflict surface, and for the working files an `update`
    /// replaces, which decision 0030 holds to the same contract: a reader
    /// mid-update meets a complete old file or a complete new one. Every
    /// store document is written with [`create_new`](Filesystem::create_new)
    /// instead. Until replacement commits, a reader must see the complete old
    /// file; afterwards it must see the complete new one, never a missing or
    /// partially written destination.
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

    /// Move a file to another name, replacing nothing.
    ///
    /// Only `arrange` renames. Decision 0019 is why nothing else does: *a
    /// writer names the file it is creating rather than renaming it
    /// afterwards*, so a rename here is always presentation being tidied, and
    /// never a document being written.
    ///
    /// `to`'s parent is made first by the caller, so an implementation is not
    /// required to create directories. Whether an occupied `to` is replaced is
    /// not relied on: `arrange` looks before it moves and leaves a name that
    /// is taken.
    fn rename(&self, from: &Path, to: &Path) -> io::Result<()>;

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

    /// Whether a regular file can be run, or `None` where that is not a thing
    /// this filesystem has.
    ///
    /// Decision 0034, and `None` is the load-bearing answer. A filesystem that
    /// cannot observe the bit — Windows, an in-memory map, a document provider
    /// handing over opaque blobs — must not report `false`, because a recorder
    /// would then state `mode <file> plain` for every executable file in the
    /// history and a person's two machines would take turns flipping the bit
    /// off and on forever. Saying "I do not model this" is what stops that,
    /// and it is the default, so an implementation that has no opinion is
    /// already correct.
    fn executable(&self, path: &Path) -> io::Result<Option<bool>> {
        let _ = path;
        Ok(None)
    }

    /// Make a regular file runnable, or not.
    ///
    /// A filesystem whose [`executable`](Filesystem::executable) is `None` has
    /// nothing to set, and the default does nothing. Nothing else about the
    /// file changes: this is one bit, not a mode.
    fn set_executable(&self, path: &Path, executable: bool) -> io::Result<()> {
        let (_, _) = (path, executable);
        Ok(())
    }

    /// What the symbolic link at a path points at, **read rather than
    /// followed**.
    ///
    /// Decision 0040, and `Ok(None)` is the load-bearing answer, on 0034's
    /// terms doing the same work: it means *this filesystem does not model
    /// links at all*, and a recorder that gets it states nothing and leaves
    /// the recorded target standing — because two machines, one blind to the
    /// fact, must not take turns rewriting it.
    ///
    /// That makes `Ok(None)` the default's answer and **never an
    /// implementation's**. A filesystem that does model links answers with the
    /// target, or with an error where the path holds no link — which is what
    /// `readlink` already does, and what lets one question settle whether a
    /// folder can hold a link at all.
    ///
    /// A target that is not UTF-8 is [`InvalidData`](io::ErrorKind::InvalidData):
    /// this store is UTF-8 text, and the honest answer is that the string
    /// cannot be written down rather than a lossy rendering of it.
    fn link_target(&self, path: &Path) -> io::Result<Option<String>> {
        let _ = path;
        Ok(None)
    }

    /// Make a symbolic link at a path, pointing at a target.
    ///
    /// Whatever is at the path is replaced by the link — decision 0026's
    /// atomic-rename path included, because a link is removed and remade
    /// rather than written through. Nothing here opens the target: a received
    /// store may say `link kx.. ../../etc/passwd` and the only consequence is
    /// an honest symlink, pointing where symlinks are allowed to point.
    ///
    /// The default refuses, because a filesystem with no links has nowhere to
    /// put one and writing a plain file holding the target would invent
    /// content no revision stated. `update` asks
    /// [`link_target`](Filesystem::link_target) first and refuses by name, so
    /// this is the answer to a caller that went round it.
    fn set_link(&self, path: &Path, target: &str) -> io::Result<()> {
        let (_, _) = (path, target);
        Err(io::Error::new(
            io::ErrorKind::Unsupported,
            "this filesystem does not model symbolic links",
        ))
    }

    /// What this directory already says about a file, or `None` where it says
    /// nothing.
    ///
    /// Decision 0043, on 0034's terms doing 0034's work. Decision 0025 keeps
    /// this trait free of metadata for a reason that still holds — *identity
    /// comes from content*, and a store that decided anything by a clock would
    /// be deciding it by something two replicas disagree about. So nothing here
    /// is ever consulted for an answer. It is consulted for whether an answer
    /// already worked out may be taken again instead of worked out afresh, and
    /// `None` means only that a command reads what it would have read anyway.
    ///
    /// Answered about the link itself where a path holds one, like everything
    /// else this trait reports.
    fn stamp(&self, path: &Path) -> io::Result<Option<Stamp>> {
        let _ = path;
        Ok(None)
    }

    /// Hand one file's bytes over in pieces, or `None` to be asked for it
    /// whole.
    ///
    /// Decision 0043's other half. A caller that only wants a file's digest
    /// has no use for the file, and a photograph read whole to be hashed is a
    /// buffer the size of the photograph held for the length of a SHA-256.
    /// This is the same bytes in the same order, arriving in whatever runs the
    /// implementation finds convenient — the reader concatenating them gets
    /// exactly [`read`](Filesystem::read)'s answer.
    ///
    /// `Ok(None)` is reserved for *this filesystem hands a file over whole*,
    /// and an implementation answering it **must have called `each` no times**:
    /// the caller falls back to [`read`](Filesystem::read), and a partial feed
    /// followed by a whole one would hash a file with a prefix of itself in
    /// front. A filesystem that does read in pieces answers `Ok(Some(()))`, or
    /// an error — an absent file is [`NotFound`](io::ErrorKind::NotFound) here
    /// as everywhere.
    fn read_in_pieces(&self, path: &Path, each: &mut dyn FnMut(&[u8])) -> io::Result<Option<()>> {
        let (_, _) = (path, each);
        Ok(None)
    }
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
    fn rename(&self, from: &Path, to: &Path) -> io::Result<()> {
        (**self).rename(from, to)
    }
    fn remove_file(&self, path: &Path) -> io::Result<()> {
        (**self).remove_file(path)
    }
    fn remove_directory(&self, path: &Path) -> io::Result<()> {
        (**self).remove_directory(path)
    }
    fn executable(&self, path: &Path) -> io::Result<Option<bool>> {
        (**self).executable(path)
    }
    fn set_executable(&self, path: &Path, executable: bool) -> io::Result<()> {
        (**self).set_executable(path, executable)
    }
    fn link_target(&self, path: &Path) -> io::Result<Option<String>> {
        (**self).link_target(path)
    }
    fn set_link(&self, path: &Path, target: &str) -> io::Result<()> {
        (**self).set_link(path, target)
    }
    fn stamp(&self, path: &Path) -> io::Result<Option<Stamp>> {
        (**self).stamp(path)
    }
    fn read_in_pieces(&self, path: &Path, each: &mut dyn FnMut(&[u8])) -> io::Result<Option<()>> {
        (**self).read_in_pieces(path, each)
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
            fn rename(&self, from: &Path, to: &Path) -> io::Result<()> {
                (**self).rename(from, to)
            }
            fn remove_file(&self, path: &Path) -> io::Result<()> {
                (**self).remove_file(path)
            }
            fn remove_directory(&self, path: &Path) -> io::Result<()> {
                (**self).remove_directory(path)
            }
            // Forwarded like everything else, because a capability that
            // disappears behind an `Arc` is worse than one that was never
            // there: the default answers "this filesystem models no modes and
            // no links", and a wrapper answering that of a `Disk` would drop
            // every bit and every target the folder actually holds.
            fn executable(&self, path: &Path) -> io::Result<Option<bool>> {
                (**self).executable(path)
            }
            fn set_executable(&self, path: &Path, executable: bool) -> io::Result<()> {
                (**self).set_executable(path, executable)
            }
            fn link_target(&self, path: &Path) -> io::Result<Option<String>> {
                (**self).link_target(path)
            }
            fn set_link(&self, path: &Path, target: &str) -> io::Result<()> {
                (**self).set_link(path, target)
            }
            fn stamp(&self, path: &Path) -> io::Result<Option<Stamp>> {
                (**self).stamp(path)
            }
            fn read_in_pieces(
                &self,
                path: &Path,
                each: &mut dyn FnMut(&[u8]),
            ) -> io::Result<Option<()>> {
                (**self).read_in_pieces(path, each)
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

/// The digest of a file's bytes, without holding them.
///
/// Decision 0043. Identity comes from content, so a great deal of this crate
/// asks a file only what it hashes to — which path holds a payload, whether a
/// document is one this store may delete, whether the folder still holds what
/// was recorded. None of those wants the file, and every one of them used to
/// read it whole to find out. This is the same SHA-256, taken over the pieces
/// [`Filesystem::read_in_pieces`] hands over, falling back to reading the file
/// whole where that is all a filesystem offers — so the answer never depends
/// on which of the two happened.
pub fn digest_of<F: Filesystem + ?Sized>(
    files: &F,
    path: &Path,
) -> io::Result<crate::core::RevisionId> {
    let mut hasher = crate::format::Hasher::new();
    let streamed = files.read_in_pieces(path, &mut |piece| hasher.update(piece))?;
    if streamed.is_none() {
        hasher.update(&files.read(path)?);
    }
    Ok(hasher.finish())
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
        use fs_transaction::fs::Storage as _;

        // Decision 0026's atomic replacement, with the flushes it always
        // implied: the bytes are staged in a temporary sibling, barriered so
        // the rename cannot be seen before what it publishes, renamed over the
        // destination, and the directory entry is flushed durable. `write` is
        // what lands the store's mutable files — a bookmark, the marker — and
        // those are the writes that *name* documents, so this durable landing
        // is also the drain that caps every barrier `create_new` left behind:
        // once a record's own write returns, nothing it names can be lost to a
        // power cut it survived.
        fs_transaction::exec::block_on(fs_transaction::StdFs.write_atomic(path, bytes))
    }

    fn create_new(&self, path: &Path, bytes: &[u8]) -> io::Result<()> {
        use fs_transaction::fs::{Durability, Storage as _};
        use fs_transaction::{OrderedBatch, StdFs, exec::block_on};

        // The store is append-only and content-addressed, so a half-written
        // batch is a legal state — what it cannot tolerate is a *name* that
        // survives a crash the bytes it stands for did not. So every document
        // lands as one tier of an ordered batch with `Ordered` finality: the
        // exclusive create (the whole concurrency story, unchanged), then a
        // barrier on the file and on every directory that gained an entry,
        // freshly minted parents included. Nothing here drains the drive; the
        // batch's own landing may still go with a crash, wholly or in part,
        // and the tree it leaves is one the store already reads. What turns
        // the barriers durable is the next mutable write — the bookmark or
        // marker that *names* this document lands through
        // [`write`](Filesystem::write)'s durable flush, which carries
        // everything barriered before it.
        let directory = path.parent().filter(|held| !held.as_os_str().is_empty());
        let (Some(directory), Some(name)) = (directory, path.file_name()) else {
            // A bare relative name has no directory to root a batch in; the
            // port's own create and barrier are the same first tier.
            return block_on(async {
                StdFs.create_new(path, bytes).await?;
                StdFs.sync(path, Durability::Ordered).await
            });
        };
        let mut batch = OrderedBatch::new();
        batch.create_new(name, bytes);
        block_on(batch.apply(&StdFs, directory, Durability::Ordered)).map_err(io_error)
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

    fn rename(&self, from: &Path, to: &Path) -> io::Result<()> {
        std::fs::rename(from, to)
    }

    fn remove_file(&self, path: &Path) -> io::Result<()> {
        std::fs::remove_file(path)
    }

    fn remove_directory(&self, path: &Path) -> io::Result<()> {
        std::fs::remove_dir(path)
    }

    #[cfg(unix)]
    fn executable(&self, path: &Path) -> io::Result<Option<bool>> {
        use std::os::unix::fs::PermissionsExt as _;

        // The link itself, like everything else this trait answers. A symlink
        // is refused by the working copy before its mode is anybody's
        // question, and following one here would report the target's.
        let metadata = std::fs::symlink_metadata(path)?;
        Ok(Some(metadata.permissions().mode() & 0o111 != 0))
    }

    /// Windows has no such bit, which is a true fact about Windows rather than
    /// a limitation to work around: `None` is the accurate answer, and it is
    /// what keeps a store carried between the two from losing the bit.
    #[cfg(not(unix))]
    fn executable(&self, path: &Path) -> io::Result<Option<bool>> {
        let _ = path;
        Ok(None)
    }

    #[cfg(unix)]
    fn set_executable(&self, path: &Path, executable: bool) -> io::Result<()> {
        use std::os::unix::fs::PermissionsExt as _;

        let mut permissions = std::fs::metadata(path)?.permissions();
        let held = permissions.mode();
        // Every bit the person's own umask chose is theirs. Decision 0034
        // carries one bit, and this sets one bit: the execute bits follow the
        // read bits, so a file readable by its group becomes runnable by its
        // group and a private file stays private.
        let mode = if executable {
            held | ((held & 0o444) >> 2)
        } else {
            held & !0o111
        };
        if mode == held {
            return Ok(());
        }
        permissions.set_mode(mode);
        std::fs::set_permissions(path, permissions)
    }

    #[cfg(not(unix))]
    fn set_executable(&self, path: &Path, executable: bool) -> io::Result<()> {
        let (_, _) = (path, executable);
        Ok(())
    }

    #[cfg(unix)]
    fn link_target(&self, path: &Path) -> io::Result<Option<String>> {
        // `read_link` reads the link and does not follow it, which is the
        // whole of what decision 0040 asks of this: a link pointing at `/`
        // hands back a string, and never makes anything enumerate a machine.
        // It errors where the path holds no link, which is what keeps
        // `Ok(None)` meaning "this filesystem has no such thing".
        let target = std::fs::read_link(path)?;
        match target.to_str() {
            Some(target) => Ok(Some(target.to_owned())),
            None => Err(io::Error::new(
                io::ErrorKind::InvalidData,
                format!(
                    "{} points at a name that is not UTF-8, and this store is UTF-8 text",
                    path.display()
                ),
            )),
        }
    }

    /// Windows has symbolic links and does not hand them out: creating one
    /// wants a privilege an ordinary account does not have, so the honest
    /// answer is that this filesystem does not model them, and a store carried
    /// between the two keeps every target it arrived with.
    #[cfg(not(unix))]
    fn link_target(&self, path: &Path) -> io::Result<Option<String>> {
        let _ = path;
        Ok(None)
    }

    #[cfg(unix)]
    fn set_link(&self, path: &Path, target: &str) -> io::Result<()> {
        // Removed and remade rather than written through — decision 0040's
        // standing rule, and the reason the atomic-replace path of 0026 is not
        // reached here: every write this performs addresses the entry itself,
        // never the entry's referent.
        match std::fs::remove_file(path) {
            Ok(()) => {}
            Err(error) if error.kind() == io::ErrorKind::NotFound => {}
            Err(error) => return Err(error),
        }
        std::os::unix::fs::symlink(target, path)
    }

    #[cfg(not(unix))]
    fn set_link(&self, path: &Path, target: &str) -> io::Result<()> {
        let (_, _) = (path, target);
        Err(io::Error::new(
            io::ErrorKind::Unsupported,
            "this host does not hand out symbolic links",
        ))
    }

    fn stamp(&self, path: &Path) -> io::Result<Option<Stamp>> {
        // The link itself, as every other question this trait answers is: a
        // stamp read through a link would describe the file at the other end,
        // and the walk that asks for one has already refused to follow it.
        let metadata = std::fs::symlink_metadata(path)?;
        // A platform with no modification time is one this cannot speak for,
        // and saying so costs a command the read it would have done anyway.
        let Ok(modified) = metadata.modified() else {
            return Ok(None);
        };
        Ok(Some(Stamp {
            size: metadata.len(),
            modified,
        }))
    }

    fn read_in_pieces(&self, path: &Path, each: &mut dyn FnMut(&[u8])) -> io::Result<Option<()>> {
        use io::Read as _;

        let mut file = std::fs::File::open(path)?;
        // One buffer, reused, and the only memory a fifty-megabyte photograph
        // costs a command that wanted its digest.
        let mut buffer = vec![0u8; PIECE];
        loop {
            let read = file.read(&mut buffer)?;
            if read == 0 {
                return Ok(Some(()));
            }
            each(&buffer[..read]);
        }
    }
}

/// What a one-op batch failed with, said in this trait's currency.
///
/// [`std::io::Error`] is the vocabulary here, and a batch of one write can
/// only fail as its one write — so the wrapper comes off, and the kinds the
/// crate branches on ([`AlreadyExists`](io::ErrorKind::AlreadyExists) above
/// all) arrive exactly as the filesystem said them. The other variants are
/// journal and path machinery a single created file never reaches; a bare
/// file name cannot escape the directory it is rooted in.
#[cfg(feature = "disk")]
fn io_error(error: fs_transaction::Error) -> io::Error {
    match error {
        fs_transaction::Error::Io(error) => error,
        other => io::Error::other(other),
    }
}

/// How much of a file `Disk` holds at once while reading it in pieces.
///
/// Large enough that the per-read overhead is not the cost and small enough to
/// be nothing at all next to a file worth streaming. Nothing depends on the
/// number: the digest of a file is the digest of a file however it arrived.
#[cfg(feature = "disk")]
const PIECE: usize = 64 * 1024;

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
