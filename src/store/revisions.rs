//! Every revision document this store has read, so that reading them again
//! costs one open.
//!
//! Decision 0058. 0036 removed the cost of *finding* a digest in
//! `operations/` and 0043 removed the cost of *taking* one; neither touched
//! the directory every command reads before it does anything at all.
//! [`Store::open`](crate::store::Store::open) walks `revisions/` and performs
//! one read and one parse per file it finds, and since a revision document
//! holds the whole of the graph there is no command that does not pay it —
//! `names` opens six hundred files to print four lines.
//!
//! What that costs is the opens rather than the bytes. Six hundred documents
//! are 688 KB, and 688 KB is one fifth of a millisecond to read out of one
//! file and nine milliseconds to read out of six hundred — a hundred and
//! eleven from a cold page cache, which is what a store opens at after a
//! `receive`, a reboot, or somebody else's morning.
//!
//! # What it holds
//!
//! The documents themselves, verbatim, in one file with a byte count in front
//! of each:
//!
//! ```text
//! historica-revisions-1
//! <digest> <size> <modified> <path>
//! <size bytes of the document>
//! ```
//!
//! Bytes rather than facts, which is the decision's centre. A cache of parsed
//! facts would be a second grammar for the revision document, kept in step
//! with the first by hand, and it would have to be *believed*: there is
//! nothing to check a claim about a document's parents against except the
//! document. Bytes cannot lie. An entry states the digest it is, and hashing
//! what it holds settles whether it is that — 0.30 ms for the whole file
//! above, which is the cheapest verification in this crate and the only one
//! that makes a cache incapable of inventing a history.
//!
//! # When an entry is believed
//!
//! Three conditions, and anything else is a file this store opens:
//!
//! - its bytes hash to the digest it claims, which is what keeps a garbled
//!   cache from being read as a history;
//! - the directory reports the same size and the same modification time the
//!   entry recorded, which is 0043's rule and is the whole of the link
//!   between the entry and the file it stands for;
//! - and the entry's recorded time is strictly older than the cache file's
//!   own, which is 0043's racy-mtime rule, taken here for the reason it was
//!   taken there.
//!
//! The stamps are what a store of immutable files could be argued not to
//! need: documents are written with `create_new` and never overwritten, and
//! 0036 already infers as much about what a document forgets. They are here
//! because the readable files are the authority and a person is invited to
//! open them. Somebody who edits a message by hand has made that file a
//! different revision — a corruption `check` reports, and one every command
//! notices today because every command reads the file. A cache believed on
//! immutability alone would go on printing the old message, which is the tool
//! saying one thing while the file says another.
//!
//! Completeness is 0036's condition unchanged: **the set of paths the file
//! names is the set the directory holds**. The walk happens anyway, every
//! path it finds that the file does not account for is opened, and every path
//! the file names that the directory has lost is dropped.
//!
//! # What it is not
//!
//! **Not an index of the graph.** Nothing derived is written down. Parents,
//! heads, ancestry and supersession are computed from the documents on every
//! command exactly as they were; this changed where the documents come from
//! and not one thing concluded from them.
//!
//! **Not a source of truth.** Delete it, truncate it, fill it with lies, or
//! fill it with valid documents this store does not hold, and every command
//! answers as it did — having opened `revisions/`, which is what it would
//! have done anyway.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use crate::core::RevisionId;
use crate::format::{self, digest};
use crate::fs::{Filesystem, Stamp, nanoseconds};

use super::{CACHE_DIR, REVISION_SUFFIXES, REVISIONS_DIR, StoreError, files_claiming};

/// What `cache/` calls this file.
///
/// A fixed name rather than a digest, for 0036's reason: it is not content and
/// there is nothing to look it up by. Still disposable, still ignored where it
/// fails to read, still correct to delete.
const HELD_FILE: &str = "revisions.txt";

/// The line it starts with.
///
/// So that one written by a version spelling this differently is discarded
/// whole rather than half-understood, which is the only failure mode a fixed
/// name introduces that a digest-named entry does not have.
const HELD_HEADER: &str = "historica-revisions-1";

/// One document, as the file holds it.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Held {
    size: u64,
    /// Nanoseconds either side of the Unix epoch, which is how a modification
    /// time is written down and compared here.
    modified: i128,
    /// What the entry says its bytes are.
    digest: RevisionId,
    /// The document, verbatim.
    bytes: Vec<u8>,
}

/// One document, as this pass knows it, ready to be written back.
struct Entry {
    path: String,
    size: u64,
    modified: i128,
    digest: RevisionId,
    bytes: Vec<u8>,
}

/// Read every revision document, taking what `cache/` already holds.
///
/// `cached` is false for the one caller that must not take it: `check` exists
/// to do the work rather than to have the answer.
pub(super) fn load<F: Filesystem + ?Sized>(
    files: &F,
    root: &Path,
    cached: bool,
) -> Result<BTreeMap<RevisionId, super::Document>, StoreError> {
    // The directory as it stands, which is names and no contents. This is the
    // walk opening performed anyway, and it is what every belief below is
    // checked against.
    let paths = files_claiming(files, root, REVISIONS_DIR, &REVISION_SUFFIXES)?;

    let (held, written) = if cached {
        held_documents(files, root)
    } else {
        (BTreeMap::new(), None)
    };

    let mut documents = BTreeMap::new();
    // The paths this pass did not have to open, and the ones it did. Kept
    // apart because what is written back is only built where the two of them
    // disagree with the file: rewriting the whole of it on a store nobody has
    // touched would be the cache's own bytes for no change at all, on every
    // command. The bytes stay in `held` until this file is rewritten from
    // them; what the store keeps is a copy, because decision 0061 leaves most
    // of every document unparsed and the bytes are where the rest of it is.
    let mut taken: Vec<&Path> = Vec::new();
    let mut opened: Vec<Entry> = Vec::new();

    for path in &paths {
        let relative = match path.strip_prefix(root) {
            Ok(relative) => relative,
            Err(_) => path.as_path(),
        };
        // What the directory says without the file being opened. An error is
        // silence: a filesystem that will not answer is one whose entries are
        // all unverifiable, and the consequence is a command reading what it
        // would have read anyway.
        let stamp = files.stamp(path).ok().flatten();
        let entry = stamp
            .and_then(|stamp| believed(&held, relative, stamp, written))
            // A held document that will not read is not an error to raise
            // from here: the file is right there, and a cache must never turn
            // a store that reads into a store that does not. It costs one
            // read, and the error that follows names the file.
            .and_then(|entry| {
                // The digest `believed` just checked these bytes against,
                // which is the one the revision is named by.
                let revision = format::revision_named(&entry.bytes, entry.digest).ok()?;
                Some((entry, revision))
            });

        match entry {
            Some((entry, revision)) => {
                // Two files with identical bytes are one revision stored
                // twice, which is harmless. Identical digests with differing
                // bytes cannot happen, and if they ever did it would mean a
                // broken read.
                documents.insert(
                    entry.digest,
                    super::Document::new(revision, entry.bytes.clone(), path.clone()),
                );
                taken.push(relative);
            }
            None => {
                let bytes = files
                    .read(path)
                    .map_err(|error| StoreError::io(path, error))?;
                let id = digest(&bytes);
                let revision =
                    format::revision_named(&bytes, id).map_err(|error| StoreError::Unparsable {
                        file: path.clone(),
                        error,
                    })?;
                documents.insert(
                    id,
                    super::Document::new(revision, bytes.clone(), path.clone()),
                );
                // A path this cannot write down is one the next reader has to
                // open, and leaving it out here is what keeps that from being
                // mistaken for a directory that changed. A newline would end
                // the line early; a path that is not UTF-8 cannot be written
                // to a readable file; a stamp the directory will not report is
                // a line the reader would have to discard.
                if let Some(stamp) = stamp
                    && let Some(modified) = nanoseconds(stamp.modified)
                    && let Some(path) = relative.to_str()
                    && !path.contains('\n')
                {
                    opened.push(Entry {
                        path: path.to_owned(),
                        size: stamp.size,
                        modified,
                        digest: id,
                        bytes,
                    });
                }
            }
        }
    }

    // Written when this pass and the file disagreed: a path it had to open, or
    // one the file named and the directory has since lost.
    if cached && (!opened.is_empty() || taken.len() != held.len()) {
        write(files, root, &held, &taken, &opened);
    }
    Ok(documents)
}

/// The entry for this path, if everything about it still stands.
///
/// Borrowed rather than taken: a believed document is parsed where it lies,
/// and copying every one of them out would be a copy of the whole store for
/// the sake of a file that is usually not going to be rewritten.
fn believed<'a>(
    held: &'a BTreeMap<PathBuf, Held>,
    path: &Path,
    stamp: Stamp,
    written: Option<i128>,
) -> Option<&'a Held> {
    let entry = held.get(path)?;
    if entry.size != stamp.size || Some(entry.modified) != nanoseconds(stamp.modified) {
        return None;
    }
    // The racy-mtime rule, and the only comparison here that is about time
    // rather than about equality. A file written twice inside one tick of the
    // filesystem's clock would report a stamp that has not moved while
    // holding bytes nobody hashed.
    if entry.modified >= written? {
        return None;
    }
    // What keeps a garbled file from being read as a history. Everything above
    // is about the file this entry stands for; this is about the entry itself.
    if digest(&entry.bytes) != entry.digest {
        return None;
    }
    Some(entry)
}

/// What `cache/` holds, by path, and when it was written.
///
/// Every failure is silence, and silence is a store that opens its documents.
fn held_documents<F: Filesystem + ?Sized>(
    files: &F,
    root: &Path,
) -> (BTreeMap<PathBuf, Held>, Option<i128>) {
    let path = root.join(CACHE_DIR).join(HELD_FILE);
    // The file's own write time, read from the same directory that reports
    // every entry's. A filesystem that will not say loses the cache rather
    // than the rule, which is the safe half of the trade.
    let written = files
        .stamp(&path)
        .ok()
        .flatten()
        .and_then(|stamp| nanoseconds(stamp.modified));
    let Ok(bytes) = files.read(&path) else {
        return (BTreeMap::new(), written);
    };
    (parse(&bytes), written)
}

/// One file's bytes, read back.
///
/// Separated from the reading so that what this file *is* can be tested
/// without a filesystem to hold it: a total function from bytes to what a
/// store may believe, where every way of failing returns nothing at all.
fn parse(bytes: &[u8]) -> BTreeMap<PathBuf, Held> {
    let empty = BTreeMap::new();
    let Some((header, mut rest)) = split_line(bytes) else {
        return empty;
    };
    if header != HELD_HEADER.as_bytes() {
        return empty;
    }

    let mut held = BTreeMap::new();
    while !rest.is_empty() {
        let Some((line, after)) = split_line(rest) else {
            return empty;
        };
        let Ok(line) = std::str::from_utf8(line) else {
            return empty;
        };
        // `<digest> <size> <modified> <path>`, the path last because a path is
        // the one field that may hold a space.
        let mut fields = line.splitn(4, ' ');
        let (Some(id), Some(size), Some(modified), Some(path)) =
            (fields.next(), fields.next(), fields.next(), fields.next())
        else {
            return empty;
        };
        let (Ok(id), Ok(size), Ok(modified)) = (
            id.parse::<RevisionId>(),
            size.parse::<u64>(),
            modified.parse::<i128>(),
        ) else {
            return empty;
        };
        if path.is_empty() {
            return empty;
        }
        // Exactly that many bytes, and then the newline that ends them. A
        // count that runs past the end of the file, or one whose bytes are not
        // followed by a newline, is a file this version cannot read rather
        // than one it reads approximately.
        let Ok(length) = usize::try_from(size) else {
            return empty;
        };
        let Some(document) = after.get(..length) else {
            return empty;
        };
        if after.get(length) != Some(&b'\n') {
            return empty;
        }
        rest = &after[length + 1..];

        held.insert(
            PathBuf::from(path),
            Held {
                size,
                modified,
                digest: id,
                bytes: document.to_vec(),
            },
        );
    }
    held
}

/// One line, and everything after it.
fn split_line(bytes: &[u8]) -> Option<(&[u8], &[u8])> {
    let end = bytes.iter().position(|byte| *byte == b'\n')?;
    Some((&bytes[..end], &bytes[end + 1..]))
}

/// Write down what this pass read, and say nothing about whether it worked.
///
/// 0035's rule, unchanged: a store on a read-only filesystem, a full disk, and
/// a `cache/` somebody deleted mid-command are all conditions under which
/// reading a store must still succeed. Nothing is lost when this fails — the
/// next command opens the documents, as this one just did.
fn write<F: Filesystem + ?Sized>(
    files: &F,
    root: &Path,
    held: &BTreeMap<PathBuf, Held>,
    taken: &[&Path],
    opened: &[Entry],
) {
    // Replaced rather than created: 0026 makes replacement atomic, so a reader
    // never meets half of one. A half-read file would be discarded anyway;
    // this means it never has to be.
    let _ = files.create_directory(&root.join(CACHE_DIR));
    let _ = files.write(
        &root.join(CACHE_DIR).join(HELD_FILE),
        &render(held, taken, opened),
    );
}

/// This pass as the bytes `cache/` holds.
///
/// What was believed comes back out of `held`, unchanged and uncopied until
/// here; what was opened comes from this pass. Ordered by path, so that two
/// stores holding one history write one set of bytes rather than two
/// orderings of one.
fn render(held: &BTreeMap<PathBuf, Held>, taken: &[&Path], opened: &[Entry]) -> Vec<u8> {
    enum Line<'a> {
        Taken(&'a str, &'a Held),
        Opened(&'a Entry),
    }

    let mut lines: Vec<(&str, Line<'_>)> = Vec::with_capacity(taken.len() + opened.len());
    for path in taken {
        // A path that is not UTF-8 was never written down and cannot be now,
        // which costs the next command one read of that file.
        if let Some(text) = path.to_str()
            && let Some(entry) = held.get(*path)
        {
            lines.push((text, Line::Taken(text, entry)));
        }
    }
    for entry in opened {
        lines.push((entry.path.as_str(), Line::Opened(entry)));
    }
    lines.sort_by_key(|(path, _)| *path);

    let mut bytes = Vec::from(HELD_HEADER.as_bytes());
    bytes.push(b'\n');
    for (_, line) in lines {
        let (digest, size, modified, path, document) = match line {
            Line::Taken(path, entry) => {
                (entry.digest, entry.size, entry.modified, path, &entry.bytes)
            }
            Line::Opened(entry) => (
                entry.digest,
                entry.size,
                entry.modified,
                entry.path.as_str(),
                &entry.bytes,
            ),
        };
        bytes.extend_from_slice(format!("{digest} {size} {modified} {path}\n").as_bytes());
        bytes.extend_from_slice(document);
        bytes.push(b'\n');
    }
    bytes
}

#[cfg(test)]
mod tests {
    use std::time::{Duration, SystemTime};

    use super::*;

    fn entry(path: &str, bytes: &[u8], modified: i128) -> Entry {
        Entry {
            path: path.to_owned(),
            size: bytes.len() as u64,
            modified,
            digest: digest(bytes),
            bytes: bytes.to_vec(),
        }
    }

    /// What this pass would write, having opened everything.
    fn rendered(opened: &[Entry]) -> Vec<u8> {
        render(&BTreeMap::new(), &[], opened)
    }

    fn stamp(size: u64, modified: i128) -> Stamp {
        Stamp {
            size,
            modified: SystemTime::UNIX_EPOCH + Duration::from_nanos(modified as u64),
        }
    }

    /// A document with blank lines and a trailing newline in it survives the
    /// round trip, because an entry is counted rather than delimited. Every
    /// revision document has both — 0002 puts a blank line before the message.
    #[test]
    fn a_document_with_newlines_in_it_round_trips() {
        let document = b"historica\nchange abc\n\nA message\nover two lines\n";
        let held = parse(&rendered(&[entry("revisions/a.rev.txt", document, 3_000)]));

        let found = held
            .get(Path::new("revisions/a.rev.txt"))
            .expect("an entry");
        assert_eq!(found.bytes, document);
        assert_eq!(found.digest, digest(document));
        assert_eq!(found.size, document.len() as u64);
        assert_eq!(found.modified, 3_000);
    }

    /// A path with a space in it survives too, because the path is the last
    /// field on the line. Decision 0019 writes one for every revision whose
    /// summary has a space in it, which is nearly all of them.
    #[test]
    fn a_path_with_a_space_round_trips() {
        let document = b"historica\n";
        let path = "revisions/2026-08/2026-08-25 Start a journal.rev.txt";
        let held = parse(&rendered(&[entry(path, document, 1)]));
        assert_eq!(
            held.get(Path::new(path)).map(|held| held.bytes.as_slice()),
            Some(document.as_slice())
        );
    }

    /// A file older than the epoch is a file, and a store may hold one.
    #[test]
    fn a_time_before_the_epoch_round_trips() {
        let held = parse(&rendered(&[entry(
            "revisions/old.rev.txt",
            b"historica\n",
            -5_000,
        )]));
        assert_eq!(
            held.get(Path::new("revisions/old.rev.txt"))
                .map(|held| held.modified),
            Some(-5_000)
        );
    }

    /// Several entries in one file, which is the ordinary case, and each one
    /// comes back as itself rather than as a prefix of the next.
    #[test]
    fn every_entry_comes_back_as_itself() {
        let held = parse(&rendered(&[
            entry("revisions/a.rev.txt", b"first\n", 1),
            entry("revisions/b.rev.txt", b"second, and longer\n", 2),
            entry("revisions/c.rev.txt", b"", 3),
        ]));

        assert_eq!(held.len(), 3);
        assert_eq!(
            held.get(Path::new("revisions/b.rev.txt")).unwrap().bytes,
            b"second, and longer\n"
        );
        // A document of no bytes at all is still an entry, and still ends with
        // the newline that separates it from the line after.
        assert_eq!(
            held.get(Path::new("revisions/c.rev.txt")).unwrap().bytes,
            b""
        );
    }

    /// A file this pass believed is written back out of what was already held,
    /// which is the copy the whole shape exists to avoid: the bytes are never
    /// taken out of the file until there is a reason to write one.
    #[test]
    fn what_was_believed_is_written_back_unchanged() {
        let first = rendered(&[
            entry("revisions/a.rev.txt", b"historica\nchange one\n", 1),
            entry("revisions/b.rev.txt", b"historica\nchange two\n", 2),
        ]);
        let held = parse(&first);

        // One of them believed and the other opened again, which is what a
        // store that gained a revision looks like on the next command.
        let taken = [Path::new("revisions/a.rev.txt")];
        let opened = [entry("revisions/b.rev.txt", b"historica\nchange two\n", 2)];
        assert_eq!(render(&held, &taken, &opened), first);
    }

    /// A file whose header is not this one is a file this version does not
    /// have. Discarding it whole is what a fixed name costs.
    #[test]
    fn a_file_from_another_version_is_discarded() {
        assert!(parse(b"historica-revisions-0\n").is_empty());
        assert!(parse(b"").is_empty());
        assert!(parse(b"not a cache at all\n").is_empty());
    }

    /// A count that does not match what follows it discards the whole file
    /// rather than the entry. What is being claimed is an account of a
    /// directory, and a partial one is not a smaller account — it is a wrong
    /// one, with the directory right there to be read instead.
    #[test]
    fn a_count_that_runs_off_the_end_discards_the_file() {
        let good = rendered(&[entry("revisions/a.rev.txt", b"historica\n", 1)]);
        assert_eq!(parse(&good).len(), 1);

        let header = format!("{HELD_HEADER}\n");
        let id = digest(b"historica\n");
        for bad in [
            // A size longer than the bytes that follow.
            format!("{header}{id} 400 1 revisions/a.rev.txt\nhistorica\n"),
            // A size that stops short, so no newline follows the document.
            format!("{header}{id} 4 1 revisions/a.rev.txt\nhistorica\n"),
            // Fields missing.
            format!("{header}{id} 10 revisions/a.rev.txt\nhistorica\n"),
            // A path that is not there.
            format!("{header}{id} 10 1 \nhistorica\n"),
            // Numbers that are not numbers.
            format!("{header}{id} ten 1 revisions/a.rev.txt\nhistorica\n"),
            format!("{header}not-a-digest 10 1 revisions/a.rev.txt\nhistorica\n"),
            // Trailing rubbish after a well-formed entry.
            format!("{header}{id} 10 1 revisions/a.rev.txt\nhistorica\noh dear\n"),
        ] {
            assert!(
                parse(bad.as_bytes()).is_empty(),
                "should have been discarded: {bad:?}"
            );
        }
    }

    /// The three conditions, one at a time. Each of them alone is enough to
    /// send a reader to the file.
    #[test]
    fn an_entry_is_believed_only_where_everything_still_stands() {
        let path = PathBuf::from("revisions/a.rev.txt");
        let document = b"historica\n";
        let size = document.len() as u64;
        let held = |bytes: &[u8]| {
            BTreeMap::from([(
                path.clone(),
                Held {
                    size,
                    modified: 1_000,
                    digest: digest(document),
                    bytes: bytes.to_vec(),
                },
            )])
        };

        // Everything agrees, and the entry is taken.
        assert!(believed(&held(document), &path, stamp(size, 1_000), Some(2_000)).is_some());
        // The size moved.
        assert!(believed(&held(document), &path, stamp(99, 1_000), Some(2_000)).is_none());
        // The time moved.
        assert!(believed(&held(document), &path, stamp(size, 1_001), Some(2_000)).is_none());
        // The entry is not strictly older than the file holding it.
        assert!(believed(&held(document), &path, stamp(size, 1_000), Some(1_000)).is_none());
        // Nothing said when the file was written.
        assert!(believed(&held(document), &path, stamp(size, 1_000), None).is_none());
        // The entry does not hold what it says it holds.
        assert!(
            believed(
                &held(b"something else"),
                &path,
                stamp(size, 1_000),
                Some(2_000)
            )
            .is_none()
        );
        // A path the file does not name.
        assert!(
            believed(
                &held(document),
                Path::new("revisions/b.rev.txt"),
                stamp(size, 1_000),
                Some(2_000)
            )
            .is_none()
        );
    }
}
