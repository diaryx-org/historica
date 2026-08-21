//! The names a store's files are written under, which nothing reads.
//!
//! Specified by decisions 0006, 0016, 0018 and 0019. One rule from 0003
//! governs everything here:
//!
//! > Identity comes from content. Filenames are presentation.
//!
//! So nothing in this module is load-bearing: a store whose files are all
//! named by digest is a correct store, and [`crate::store::Store::open`] could
//! not tell the difference. What it is for is the folder a person opens, which
//! 0019 makes the one they get by default rather than the one they get by
//! running a command.
//!
//! ```text
//! revisions/2026-08-20 File the photograph.rev
//! operations/2026-08-20 File the photograph/notes/photo.png
//! operations/2026-08-20 Say more/src/cli/mod.rs.ops
//! ```
//!
//! The one hard rule is determinism. Two replicas arranging one history must
//! produce one set of filenames, or sync sees two files per document and a
//! scheme meant to make a folder readable fills it with conflicted copies.
//! That is why a collision appends a change ID rather than a counter: a
//! counter depends on what else is in the directory, and a content-derived
//! suffix does not.

use std::collections::{BTreeMap, BTreeSet};

use crate::core::{ChangeId, RevisionId};
use crate::format::{RevisionDocument, Timestamp};
use crate::store::OPERATION_SUFFIX;

/// Characters of summary a filename carries, cut at a word boundary.
///
/// Sixty leaves room for a date, an extension, and a two-word suffix inside
/// the 255 bytes every filesystem in use allows, even where the summary is
/// entirely non-ASCII.
pub const SUMMARY_CHARS: usize = 60;
/// Change ID characters where a name needs one.
pub const CHANGE_CHARS: usize = 8;
/// Digest characters where two revisions of one change would still collide.
pub const DIGEST_CHARS: usize = 12;

/// The stem every revision is filed under, by digest.
///
/// Decision 0006's scheme, over a whole store: the date the author
/// experienced, the first line of the message, and a suffix only where two
/// would otherwise meet.
pub fn stems<'a>(
    documents: impl IntoIterator<Item = (&'a RevisionId, &'a RevisionDocument)>,
) -> BTreeMap<RevisionId, String> {
    let mut by_base: BTreeMap<String, Vec<(RevisionId, &RevisionDocument)>> = BTreeMap::new();
    for (id, document) in documents {
        by_base
            .entry(base(document))
            .or_default()
            .push((*id, document));
    }

    let mut out = BTreeMap::new();
    for (base, sharing) in by_base {
        if let [(id, _)] = sharing.as_slice() {
            out.insert(*id, base);
            continue;
        }

        // A collision appends the change ID, which distinguishes two changes
        // that happened to be written on one day under one summary.
        let mut by_change: BTreeMap<String, Vec<(RevisionId, &RevisionDocument)>> = BTreeMap::new();
        for (id, document) in sharing {
            let name = format!("{base} {}", document.change.abbreviate(CHANGE_CHARS));
            by_change.entry(name).or_default().push((id, document));
        }
        for (name, sharing) in by_change {
            if let [(id, _)] = sharing.as_slice() {
                out.insert(*id, name);
                continue;
            }
            // Two revisions *of one change* under one summary — an amendment
            // that reworded nothing. Only the digest tells them apart, and it
            // is the thing that differs by definition.
            for (id, _) in sharing {
                out.insert(id, format!("{name} {}", id.abbreviate(DIGEST_CHARS)));
            }
        }
    }
    out
}

/// The stem one revision takes as it is written, given the store it joins.
///
/// Decision 0019: a writer names the file it is creating rather than renaming
/// it afterwards, which means it needs the answer before the document exists.
/// It has everything the answer needs — the time, the message, and the change
/// ID are supplied to a recording rather than derived from it.
///
/// Where this collides with a revision already on disk, the new one takes its
/// change ID and the one already there keeps the plain name it was written
/// under, because a writer that renames is the thing 0016 warned about.
/// [`stems`] gives both a suffix, so `arrange` will move the older one if it
/// is ever run; both spellings are unambiguous in the meantime.
pub fn stem_for<'a>(
    when: &Timestamp,
    message: &str,
    change: &ChangeId,
    existing: impl IntoIterator<Item = &'a RevisionDocument>,
) -> String {
    let base = compose(when, message, change);
    let taken: BTreeSet<String> = existing.into_iter().map(base_of).collect();
    match taken.contains(&base) {
        false => base,
        true => format!("{base} {}", change.abbreviate(CHANGE_CHARS)),
    }
}

/// One thing filed inside a revision's directory.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Filing {
    /// The digest of the file being filed, which is its identity.
    pub held: RevisionId,
    /// The path the file had at that revision.
    pub path: String,
    /// Whether this is an operation document rather than a payload.
    pub document: bool,
}

/// What each of one revision's files is called, inside its directory.
///
/// Decision 0018 files a path as a path, so two different paths can no longer
/// produce one name. Two things can still meet, and both are parted here by a
/// digest suffix rather than by a counter: a payload and a document one path
/// apart — a file called `x.ops` beside a document for `x` — and a file at a
/// path that is another file's directory, which 0008 permits and no filesystem
/// can hold.
pub fn filed(filings: &[Filing]) -> BTreeMap<RevisionId, String> {
    let mut sharing: Vec<(&Filing, String)> = filings
        .iter()
        .map(|filing| {
            let path = scrubbed(&filing.path);
            let name = if filing.document {
                format!("{path}{OPERATION_SUFFIX}")
            } else if last(&path).ends_with(OPERATION_SUFFIX) {
                // A payload never carries a suffix that says "document",
                // whether or not a document is there to collide with. A person
                // whose repository holds a file called `notes.ops` would
                // otherwise have it filed under a name the loader hands to the
                // parser, which refuses it — a store that wrote something it
                // could not read back. Decision 0021 leaves one suffix to
                // avoid, so a repository file called `notes.ops` keeps its own
                // name and only `notes.ops.txt` yields.
                suffixed(&path, &filing.held, false)
            } else {
                path
            };
            (filing, name)
        })
        .collect();
    sharing.sort_by(|(one, left), (other, right)| (one.held, left).cmp(&(other.held, right)));

    // Every directory these names need. A name that *is* one of them is a file
    // where another file needs a directory.
    let mut directories: BTreeSet<&str> = BTreeSet::new();
    for (_, name) in &sharing {
        let mut rest = name.as_str();
        while let Some(cut) = rest.rfind('/') {
            rest = &rest[..cut];
            directories.insert(rest);
        }
    }

    let mut counts: BTreeMap<&str, usize> = BTreeMap::new();
    for (_, name) in &sharing {
        *counts.entry(name.as_str()).or_default() += 1;
    }
    let taken: BTreeMap<String, bool> = counts
        .into_iter()
        .map(|(name, count)| (name.to_owned(), count > 1))
        .collect();

    let mut out = BTreeMap::new();
    for (filing, name) in &sharing {
        let held = filing.held;
        // Whether this is a document is carried, never read back off the name:
        // a payload for a path that ends in `.ops` is a payload, and a rename
        // that made it look like a document would hand it to the parser, which
        // is the one thing a disambiguator may not do.
        let name = if directories.contains(name.as_str()) {
            // The file at the shorter path yields, and keeps its digest name
            // at the top of the revision's directory, where nothing can be a
            // directory over it.
            match filing.document {
                true => format!("{held}{OPERATION_SUFFIX}"),
                false => held.to_string(),
            }
        } else if taken.get(name.as_str()).copied().unwrap_or(false) {
            suffixed(name, &held, filing.document)
        } else {
            name.clone()
        };
        out.insert(held, name);
    }
    out
}

/// A name with the digest that parts it from another, on its last component.
///
/// Inside the extension for a document and outside it for a payload, because a
/// document that lost `.ops` would stop being one and a payload that gained it
/// would start.
fn suffixed(name: &str, held: &RevisionId, document: bool) -> String {
    let (head, last) = match name.rfind('/') {
        Some(cut) => name.split_at(cut + 1),
        None => ("", name),
    };
    let suffix = held.abbreviate(DIGEST_CHARS);
    match document {
        true => {
            let last = last.strip_suffix(OPERATION_SUFFIX).unwrap_or(last);
            format!("{head}{last} {suffix}{OPERATION_SUFFIX}")
        }
        false => format!("{head}{last} {suffix}"),
    }
}

/// The last component of a path, which is where a name is decided.
fn last(path: &str) -> &str {
    match path.rfind('/') {
        Some(cut) => &path[cut + 1..],
        None => path,
    }
}

/// A path, as the store files it.
///
/// Decision 0018: the separator is the separator, and the components are
/// directories, so there is nothing here to translate — a path that named a
/// file in somebody's folder names one here. What is left is the one thing a
/// filesystem cannot be asked to hold: a control character in a name, which
/// 0008's path rules permit and no directory entry should carry. A backslash
/// is left alone, because on the platforms this runs on it is an ordinary
/// character in a name rather than a separator.
pub fn scrubbed(path: &str) -> String {
    path.chars()
        .map(|character| match character {
            character if character.is_control() => ' ',
            character => character,
        })
        .collect()
}

/// A revision's name before any collision suffix.
fn base_of(document: &RevisionDocument) -> String {
    base(document)
}

fn base(document: &RevisionDocument) -> String {
    compose(&document.when, &document.message, &document.change)
}

/// The date and the summary, which is what a revision is called.
///
/// The date comes from `when` as written, so it is the date in the offset the
/// author experienced. Decision 0002 keeps timestamps out of identity and
/// ordering, which is exactly what frees them for this.
fn compose(when: &Timestamp, message: &str, change: &ChangeId) -> String {
    let date: String = when.as_str().chars().take(10).collect();
    format!("{date} {}", summary(message, change))
}

fn summary(message: &str, change: &ChangeId) -> String {
    let first = message.lines().next().unwrap_or_default();
    let replaced: String = first
        .chars()
        .map(|character| match character {
            // Decision 0006 names `/` and control characters. A backslash is
            // here for the same reason on the systems that separate with it,
            // and adding it costs nothing: no reader looks at these names.
            '/' | '\\' => ' ',
            character if character.is_control() => ' ',
            character => character,
        })
        .collect();

    // Non-ASCII is preserved: this is a filename shown to a person, not an
    // identifier, and a journal is written in its author's own language.
    let collapsed = replaced.split_whitespace().collect::<Vec<_>>().join(" ");
    let trimmed = clip(collapsed.trim_start_matches('.').trim(), SUMMARY_CHARS);

    if trimmed.is_empty() {
        // Decision 0001 calls a change ID prefix the name a person can learn,
        // which makes it the right fallback for a message that says nothing.
        change.abbreviate(CHANGE_CHARS)
    } else {
        trimmed
    }
}

/// Cut to `limit` characters, at a word boundary where there is one.
fn clip(text: &str, limit: usize) -> String {
    if text.chars().count() <= limit {
        return text.to_owned();
    }
    let cut: String = text.chars().take(limit).collect();
    match cut.rsplit_once(' ') {
        Some((words, _)) if !words.is_empty() => words.to_owned(),
        _ => cut.trim_end().to_owned(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::format::RevisionDocument;

    /// A document with one message, one date, and one change ID.
    fn document(change: &str, when: &str, message: &str) -> RevisionDocument {
        let headers =
            format!("historica-v0\nchange {change}\nauthor A <a@example.com>\nwhen {when}\n");
        // A document with nothing to say ends at its headers: the blank line
        // is a separator, and the parser refuses one with nothing after it.
        let text = if message.is_empty() {
            headers
        } else {
            format!("{headers}\n{message}")
        };
        RevisionDocument::parse(text.as_bytes()).expect("a document the parser accepts")
    }

    fn arranged(documents: &[RevisionDocument]) -> Vec<String> {
        let ids: Vec<RevisionId> = documents.iter().map(RevisionDocument::id).collect();
        let named = stems(ids.iter().zip(documents.iter()));
        ids.iter().map(|id| named[id].clone()).collect()
    }

    #[test]
    fn a_name_is_the_date_it_carries_and_the_summary_it_states() {
        let document = document(
            "qpvuntsmwlrkzxonmvtplsyq",
            "2025-08-19T00:47:11-06:00",
            "Start a journal\n\nA second paragraph the filename does not want.\n",
        );
        assert_eq!(base(&document), "2025-08-19 Start a journal");
    }

    #[test]
    fn a_path_is_filed_as_a_path() {
        // Decision 0018: nothing stands in for the separator, because the
        // separator is what a directory separates. Five files are called
        // `mod.rs` and the directories are what tell them apart — here as
        // directories, rather than as a character that resembles one.
        assert_eq!(scrubbed("src/cli/mod.rs"), "src/cli/mod.rs");
        assert_eq!(scrubbed("README.md"), "README.md");
    }

    #[test]
    fn a_long_path_is_not_clipped_because_it_no_longer_has_to_be() {
        // The 255-byte limit is per component, and every component here
        // already named a file on somebody's disk.
        let path = "tests/corpus/diffs/final-newline-gained/and/deeper/still/child.txt";
        assert_eq!(scrubbed(path), path);
        assert!(
            path.split('/').all(|component| component.len() < 255),
            "each component fits by construction"
        );
    }

    #[test]
    fn a_control_character_is_the_one_thing_a_name_may_not_carry() {
        // 0008's path rules permit it and no directory entry should hold one.
        assert_eq!(scrubbed("notes/a\u{7}b.md"), "notes/a b.md");
    }

    #[test]
    fn the_date_is_the_one_the_author_experienced() {
        // 01:00 on the 20th at +13:00 is the 19th in UTC, and the filename
        // says the 20th, because that is the day the person had.
        let document = document(
            "qpvuntsmwlrkzxonmvtplsyq",
            "2025-08-20T01:00:00+13:00",
            "Late\n",
        );
        assert_eq!(base(&document), "2025-08-20 Late");
    }

    #[test]
    fn a_summary_gives_up_its_separators_and_its_extra_space() {
        let document = document(
            "qpvuntsmwlrkzxonmvtplsyq",
            "2025-08-19T00:47:11-06:00",
            "File  docs/README.md  under docs\n",
        );
        assert_eq!(base(&document), "2025-08-19 File docs README.md under docs");
    }

    #[test]
    fn a_leading_dot_does_not_hide_the_file() {
        let document = document(
            "qpvuntsmwlrkzxonmvtplsyq",
            "2025-08-19T00:47:11-06:00",
            ".hidden would be a hidden file\n",
        );
        assert!(base(&document).ends_with("hidden would be a hidden file"));
    }

    #[test]
    fn a_long_summary_is_cut_between_words() {
        let long = "one two three four five six seven eight nine ten eleven twelve thirteen";
        let document = document(
            "qpvuntsmwlrkzxonmvtplsyq",
            "2025-08-19T00:47:11-06:00",
            &format!("{long}\n"),
        );
        let name = base(&document);
        let summary = name.strip_prefix("2025-08-19 ").expect("the date");
        assert!(summary.chars().count() <= SUMMARY_CHARS);
        assert!(long.starts_with(summary));
        assert!(!summary.ends_with(' '));
    }

    #[test]
    fn an_empty_message_falls_back_to_the_change_id() {
        let document = document("qpvuntsmwlrkzxonmvtplsyq", "2025-08-19T00:47:11-06:00", "");
        assert_eq!(base(&document), "2025-08-19 qpvuntsm");
    }

    #[test]
    fn two_changes_under_one_summary_are_told_apart_by_change_id() {
        let one = document(
            "qpvuntsmwlrkzxonmvtplsyq",
            "2025-08-19T00:47:11-06:00",
            "Notes\n",
        );
        let two = document(
            "mzvwutklopqrsnyxwkltvmzu",
            "2025-08-19T09:00:00-06:00",
            "Notes\n",
        );
        assert_eq!(
            arranged(&[one, two]),
            [
                "2025-08-19 Notes qpvuntsm".to_owned(),
                "2025-08-19 Notes mzvwutkl".to_owned()
            ]
        );
    }

    #[test]
    fn two_revisions_of_one_change_fall_through_to_the_digest() {
        let one = document(
            "qpvuntsmwlrkzxonmvtplsyq",
            "2025-08-19T00:47:11-06:00",
            "Notes\n",
        );
        let two = document(
            "qpvuntsmwlrkzxonmvtplsyq",
            "2025-08-19T09:00:00-06:00",
            "Notes\n",
        );
        let names = arranged(&[one.clone(), two.clone()]);
        assert_ne!(names[0], names[1]);
        for (name, document) in names.iter().zip([&one, &two]) {
            assert!(name.starts_with("2025-08-19 Notes qpvuntsm "));
            assert!(name.ends_with(&document.id().abbreviate(DIGEST_CHARS)));
        }
    }

    #[test]
    fn arranging_is_the_same_on_every_machine() {
        let documents = [
            document(
                "qpvuntsmwlrkzxonmvtplsyq",
                "2025-08-19T00:47:11-06:00",
                "A\n",
            ),
            document(
                "mzvwutklopqrsnyxwkltvmzu",
                "2025-08-20T08:14:33-06:00",
                "B\n",
            ),
        ];
        let forwards = arranged(&documents);
        let mut backwards = documents;
        backwards.reverse();
        let mut backwards = arranged(&backwards);
        backwards.reverse();
        assert_eq!(forwards, backwards);
    }
}
