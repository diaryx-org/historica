//! What the folder hashed to last time, and when it is allowed to be believed.
//!
//! Decision 0043, on the terms decision 0036 already set for `operations/`.
//! Identity comes from content, so `status` and `record` answer every question
//! about a tracked file by hashing it — which means a folder holding a
//! fifty-megabyte photograph reads and hashes fifty megabytes to be told
//! nothing has changed, on every command, forever.
//!
//! A catalogue is the way out. It lives in `history/cache/working.txt`, it
//! holds one line per tracked path — the digest of that file's bytes, and the
//! size and modification time the directory reported at the moment those bytes
//! were hashed — and it is believed **per entry**, on the condition that the
//! directory still reports the same size and the same modification time. An
//! entry that matches supplies a digest without the file being opened.
//! Everything else — a path the catalogue does not name, a size that moved, a
//! time that moved, a catalogue that will not parse, a catalogue that is not
//! there — is read and hashed exactly as before.
//!
//! ## The racy-mtime rule
//!
//! A modification time is not a version number. A file written twice inside
//! one tick of the filesystem's clock, the second time after this catalogue
//! was written, would still report the size and time the catalogue recorded
//! while holding bytes it never hashed. Git has the same exposure and the same
//! answer, and this takes it: **an entry whose recorded time is not strictly
//! older than the catalogue's own write time is unverifiable, and its file is
//! read and hashed.** The catalogue's write time is the modification time of
//! the catalogue file itself, which is the one clock reading that comes from
//! the same place every entry's does.
//!
//! What that leaves is a file rewritten in the same tick as the catalogue, to
//! the same length — and the next command past that tick believes nothing
//! about it, because the entry it wrote is no longer strictly older than a
//! catalogue that has since been rewritten. Nothing about a store's contents
//! is at stake either way: the worst a wrong entry can do is make one command
//! describe a file as unchanged, and the file itself is untouched, unrecorded,
//! and still there to be described correctly by the next one.
//!
//! ## What it is not
//!
//! **Not an index.** Decision 0011 refuses one and 0039 says why: an index
//! holds a version of a file that is in neither the folder nor the history.
//! Nothing here holds content. Every line is a claim about a file that is
//! present, in the folder, exactly as the folder has it, and the claim is
//! checked against the directory before it is used.
//!
//! **Not a source of truth.** Delete it, truncate it, or fill it with lies and
//! every command answers exactly as it did — having read the folder, which is
//! what it would have done anyway.

use std::collections::BTreeMap;
use std::path::Path;

use crate::core::RevisionId;
use crate::fs::{Filesystem, Stamp, nanoseconds};
use crate::store::CACHE_DIR;

/// What `cache/` calls this catalogue.
///
/// A fixed name rather than a digest, for decision 0036's reason: a catalogue
/// is not content and there is nothing to look it up by. It is still
/// disposable, still ignored where it fails to read, and still correct to
/// delete.
pub(super) const CATALOGUE_FILE: &str = "working.txt";

/// The line a catalogue starts with.
///
/// So that one written by a version spelling this differently is discarded
/// whole rather than half-understood — the only failure mode a fixed name
/// introduces that a digest-named entry does not have.
const CATALOGUE_HEADER: &str = "historica-working-1";

/// One line of the file: what a path held, and what the directory said.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Held {
    size: u64,
    /// Nanoseconds either side of the Unix epoch, which is how a modification
    /// time is written down and compared here.
    modified: i128,
    digest: RevisionId,
}

/// What may be believed about the folder, by path.
///
/// `stamps` is what the walk that just happened saw. An entry survives only
/// where the directory agrees with it in both numbers and where its time is
/// strictly older than the catalogue's own — so a folder nobody has touched
/// comes back whole, and a folder somebody has been working in comes back
/// missing exactly the files they touched.
pub(super) fn believed<F: Filesystem + ?Sized>(
    files: &F,
    store: &Path,
    stamps: &BTreeMap<String, Stamp>,
) -> BTreeMap<String, RevisionId> {
    let empty = BTreeMap::new();
    if stamps.is_empty() {
        return empty;
    }
    let path = store.join(CACHE_DIR).join(CATALOGUE_FILE);
    // The catalogue's own write time, read from the same directory that
    // reports every entry's. A filesystem that will not say loses the
    // catalogue rather than the rule, which is the safe half of the trade.
    let Ok(Some(written)) = files.stamp(&path) else {
        return empty;
    };
    let Some(written) = nanoseconds(written.modified) else {
        return empty;
    };
    let Ok(bytes) = files.read(&path) else {
        return empty;
    };
    let Ok(text) = std::str::from_utf8(&bytes) else {
        return empty;
    };

    let mut believed = BTreeMap::new();
    for (path, held) in parse(text) {
        let Some(stamp) = stamps.get(&path) else {
            // A path the folder no longer offers is not a file anybody is
            // about to ask about, and the entry goes with it.
            continue;
        };
        if stamp.size != held.size || nanoseconds(stamp.modified) != Some(held.modified) {
            continue;
        }
        // The racy-mtime rule, and the only line of this file that is about
        // time rather than about equality.
        if held.modified >= written {
            continue;
        }
        believed.insert(path, held.digest);
    }
    believed
}

/// One catalogue's text, read back.
///
/// Separated from the reading so that what a catalogue *is* can be tested
/// without a filesystem to hold it: a total function from a string to what the
/// folder may believe, where every way of failing returns nothing at all.
fn parse(text: &str) -> BTreeMap<String, Held> {
    let mut lines = text.lines();
    if lines.next() != Some(CATALOGUE_HEADER) {
        return BTreeMap::new();
    }
    let mut held = BTreeMap::new();
    for line in lines {
        // `<digest> <size> <modified> <path>`, path last because a path is the
        // one field that may hold a space.
        let mut fields = line.splitn(4, ' ');
        let (Some(digest), Some(size), Some(modified), Some(path)) =
            (fields.next(), fields.next(), fields.next(), fields.next())
        else {
            return BTreeMap::new();
        };
        let (Ok(digest), Ok(size), Ok(modified)) = (
            digest.parse::<RevisionId>(),
            size.parse::<u64>(),
            modified.parse::<i128>(),
        ) else {
            return BTreeMap::new();
        };
        if path.is_empty() {
            return BTreeMap::new();
        }
        held.insert(
            path.to_owned(),
            Held {
                size,
                modified,
                digest,
            },
        );
    }
    held
}

/// Write down what this pass knows, and say nothing about whether it worked.
///
/// Decision 0035's rule, unchanged: a folder on a read-only filesystem, a full
/// disk, and a `cache/` somebody deleted mid-command are all conditions under
/// which reading a folder must still succeed. Nothing is lost when this fails
/// — the next command hashes the files, as this one just did.
pub(super) fn write<F: Filesystem + ?Sized>(
    files: &F,
    store: &Path,
    digests: &BTreeMap<String, RevisionId>,
    stamps: &BTreeMap<String, Stamp>,
) {
    let _ = files.create_directory(&store.join(CACHE_DIR));
    let _ = files.write(
        &store.join(CACHE_DIR).join(CATALOGUE_FILE),
        render(digests, stamps).as_bytes(),
    );
}

/// One catalogue as the bytes `cache/` holds.
fn render(digests: &BTreeMap<String, RevisionId>, stamps: &BTreeMap<String, Stamp>) -> String {
    let mut text = String::from(CATALOGUE_HEADER);
    text.push('\n');
    // By path, which a `BTreeMap` already is, so that a folder nobody has
    // touched writes one set of bytes twice rather than two orderings of one.
    for (path, digest) in digests {
        // A path whose stamp the directory would not report is one nothing can
        // be believed about later, so writing the line down would be writing a
        // line the reader must discard. A newline in a path would end the line
        // early, and `check_path` has already refused one — this is the belt
        // for that brace, and it costs the next command one read.
        let Some(stamp) = stamps.get(path) else {
            continue;
        };
        let Some(modified) = nanoseconds(stamp.modified) else {
            continue;
        };
        if path.contains('\n') {
            continue;
        }
        text.push_str(&format!("{digest} {} {modified} {path}\n", stamp.size));
    }
    text
}

#[cfg(test)]
mod tests {
    use std::time::SystemTime;

    use super::*;
    use crate::format::digest;
    use std::time::Duration;

    fn stamp(size: u64, modified: i128) -> Stamp {
        let modified = if modified >= 0 {
            SystemTime::UNIX_EPOCH + Duration::from_nanos(modified as u64)
        } else {
            SystemTime::UNIX_EPOCH - Duration::from_nanos(-modified as u64)
        };
        Stamp { size, modified }
    }

    /// A path with a space in it survives the round trip, because the path is
    /// the last field on the line and everything after the third space is read
    /// as the path. A folder is full of them.
    #[test]
    fn a_path_with_a_space_round_trips() {
        let id = digest(b"one");
        let path = "notes/a thought, written down.md";
        let digests = BTreeMap::from([(path.to_owned(), id)]);
        let stamps = BTreeMap::from([(path.to_owned(), stamp(12, 3_000))]);

        let held = parse(&render(&digests, &stamps));
        assert_eq!(
            held.get(path),
            Some(&Held {
                size: 12,
                modified: 3_000,
                digest: id
            })
        );
    }

    /// A file older than the epoch is a file, and a folder may hold one.
    #[test]
    fn a_time_before_the_epoch_round_trips() {
        let id = digest(b"ancient");
        let digests = BTreeMap::from([("old.md".to_owned(), id)]);
        let stamps = BTreeMap::from([("old.md".to_owned(), stamp(1, -5_000))]);

        let held = parse(&render(&digests, &stamps));
        assert_eq!(held.get("old.md").map(|held| held.modified), Some(-5_000));
    }

    /// A catalogue whose header is not this one is a catalogue this version
    /// does not have. Discarding it whole is what a fixed name costs.
    #[test]
    fn a_catalogue_from_another_version_is_discarded() {
        assert!(parse("historica-working-0\n").is_empty());
        assert!(parse("").is_empty());
    }

    /// One malformed line discards the whole catalogue rather than the line.
    /// A catalogue that could not be written down completely is one whose
    /// remaining lines nobody has checked, and the folder is right there.
    #[test]
    fn a_line_that_does_not_parse_discards_the_catalogue() {
        let id = digest(b"one");
        let good = format!("{CATALOGUE_HEADER}\n{id} 12 3000 notes.md\n");
        assert_eq!(parse(&good).len(), 1);

        for bad in [
            format!("{CATALOGUE_HEADER}\nnot-a-digest 12 3000 notes.md\n"),
            format!("{CATALOGUE_HEADER}\n{id} enormous 3000 notes.md\n"),
            format!("{CATALOGUE_HEADER}\n{id} 12 whenever notes.md\n"),
            format!("{CATALOGUE_HEADER}\n{id} 12 3000\n"),
            format!("{CATALOGUE_HEADER}\n{id} 12 3000 \n"),
            format!("{good}oh dear\n"),
        ] {
            assert!(parse(&bad).is_empty(), "should have been discarded: {bad}");
        }
    }

    /// A path the directory reports no stamp for is left out rather than
    /// written down with a made-up one, since a line nothing can check is a
    /// line the reader has to throw away.
    #[test]
    fn a_path_with_no_stamp_is_left_out() {
        let digests = BTreeMap::from([
            ("seen.md".to_owned(), digest(b"seen")),
            ("unseen.md".to_owned(), digest(b"unseen")),
        ]);
        let stamps = BTreeMap::from([("seen.md".to_owned(), stamp(4, 1))]);

        let held = parse(&render(&digests, &stamps));
        assert_eq!(held.len(), 1);
        assert!(held.contains_key("seen.md"));
    }
}
