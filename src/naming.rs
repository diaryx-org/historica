//! The names a store's files are written under, which nothing reads.
//!
//! Specified by decisions 0006, 0016, 0018, 0019 and 0041. One rule from 0003
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
//! revisions/2026-08/2026-08-20 File the photograph.rev.txt
//! operations/2026-08/2026-08-20 File the photograph/notes/photo.png
//! operations/2026-08/2026-08-20 Say more/src/cli/mod.rs.ops.txt
//! ```
//!
//! Decision 0041 is the `2026-08/` in front. The names already began with a
//! date, and a store kept the way a journal is kept passes ten thousand
//! entries without ever having been large; a directory of five thousand is not
//! a folder a person opens, which is the whole thing these names exist for.
//! The month comes from the revision's own `when` as spelled — the wall clock
//! in its own offset, exactly as the date in the filename already is — so no
//! replica consults its own clock or zone for any part of a name.
//!
//! The one hard rule is determinism. Two replicas arranging one history must
//! produce one set of filenames, or sync sees two files per document and a
//! scheme meant to make a folder readable fills it with conflicted copies.
//! That is why a collision appends a change ID rather than a counter: a
//! counter depends on what else is in the directory, and a content-derived
//! suffix does not. The month directory is the scope a collision is judged in
//! now, which changes nothing about the rule, since a suffix that does not
//! depend on the directory does not depend on which one either.

use std::collections::{BTreeMap, BTreeSet};

use crate::core::{ChangeId, RevisionId};
use crate::format::{RevisionDocument, Timestamp};
use crate::store::{OPERATION_SUFFIX, platform_name};

/// Characters of summary a filename carries, cut at a word boundary.
///
/// Sixty leaves room for a date, an extension, and a two-word suffix inside
/// the 255 bytes every filesystem in use allows, even where the summary is
/// entirely non-ASCII.
pub const SUMMARY_CHARS: usize = 60;
/// Change ID characters where a name needs one.
pub const CHANGE_CHARS: usize = 8;
/// Characters of a timestamp that spell its month: `2026-08`.
///
/// Decision 0041's directory. A [`Timestamp`] has exactly one spelling and it
/// is ASCII of a fixed width, so this is a prefix rather than a parse.
const MONTH_CHARS: usize = 7;
/// Characters of a timestamp that spell its date: `2026-08-20`.
const DATE_CHARS: usize = 10;
/// Digest characters where two revisions of one change would still collide.
pub const DIGEST_CHARS: usize = 12;

/// The stem every revision is filed under, by digest.
///
/// Decision 0006's scheme, over a whole store: the date the author
/// experienced, the first line of the message, and a suffix only where two
/// would otherwise meet — under the month directory decision 0041 files it in,
/// so a stem carries a `/` and names two components rather than one.
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
///
/// Two revisions only collide if they share a date, and two revisions that
/// share a date share a month, so decision 0041's directory neither creates a
/// collision nor hides one: `existing` is the whole store either way, and the
/// month is part of the base being compared.
///
/// The three tiers are [`stems`]'s, and the third had no caller until decision
/// 0023: two revisions *of one change* under one summary is what an amendment
/// that reworded nothing produces, and only the digest tells those apart. That
/// is why this needs the digest of the revision it is naming — which it can
/// have, because a revision document says nothing about what it is called.
pub fn stem_for<'a>(
    when: &Timestamp,
    message: &str,
    change: &ChangeId,
    id: &RevisionId,
    existing: impl IntoIterator<Item = &'a RevisionDocument>,
) -> String {
    let base = compose(when, message, change);
    let (mut sharing_base, mut sharing_change) = (false, false);
    for document in existing {
        if base_of(document) != base {
            continue;
        }
        sharing_base = true;
        sharing_change |= document.change == *change;
    }

    if !sharing_base {
        return base;
    }
    let named = format!("{base} {}", change.abbreviate(CHANGE_CHARS));
    if !sharing_change {
        return named;
    }
    format!("{named} {}", id.abbreviate(DIGEST_CHARS))
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
            } else if last(&path).ends_with(OPERATION_SUFFIX) || platform_name(last(&path)) {
                // A payload never carries a suffix that says "document",
                // whether or not a document is there to collide with. A person
                // whose repository holds a file called `notes.ops` would
                // otherwise have it filed under a name the loader hands to the
                // parser, which refuses it — a store that wrote something it
                // could not read back. Decision 0021 leaves one suffix to
                // avoid, so a repository file called `notes.ops` keeps its own
                // name and only `notes.ops.txt` yields — and decision 0022
                // adds the names the platform writes, because a file browser
                // that puts its own `.DS_Store` where a payload sits destroys
                // it without being asked.
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

/// The month directory, the date, and the summary — where a revision is filed
/// and what it is called there.
///
/// Both halves come from `when` as written, so they are the month and the date
/// in the offset the author experienced. Decision 0002 keeps timestamps out of
/// identity and ordering, which is exactly what frees them for this, and it is
/// the document's own spelling rather than any clock this process can read,
/// which is what makes two replicas file one history alike.
///
/// The filename keeps the whole date, so a file separated from its folder
/// still says when it is from and a name that sorted correctly flat still
/// does. The prefix is the one thing decision 0041 adds; the `SUMMARY_CHARS`
/// arithmetic below is untouched by it, because a directory component and a
/// filename are measured separately by every filesystem in use.
fn compose(when: &Timestamp, message: &str, change: &ChangeId) -> String {
    let spelled = when.as_str();
    let month: String = spelled.chars().take(MONTH_CHARS).collect();
    let date: String = spelled.chars().take(DATE_CHARS).collect();
    format!("{month}/{date} {}", summary(message, change))
}

/// Characters a stem gives up at either end, because a filesystem takes them.
///
/// Whitespace was always trimmed and a leading `.` always was, so that a
/// summary does not hide the file. A trailing `.` joins them for 0006's
/// `## Since` reason: this stem is a *directory* name in `operations/`, and
/// Windows drops a trailing dot from one silently, so two stems that differed
/// only there would arrive as one folder and the determinism the scheme is
/// held to would be broken by the copy rather than by the scheme.
fn spare(character: char) -> bool {
    character == '.' || character.is_whitespace()
}

fn summary(message: &str, change: &ChangeId) -> String {
    let first = message.lines().next().unwrap_or_default();
    let replaced: String = first
        .chars()
        .map(|character| match character {
            // Decision 0006 names `/` and control characters, and its
            // `## Since` adds the rest of what a filesystem reserves: a
            // backslash separates on the systems that use one, and `:*?"<>|`
            // are refused outright by FAT, exFAT and NTFS — which is to say
            // by the media a store travels on. A message reading `Fix: the
            // parser?` would otherwise compose a stem no copy onto a memory
            // card could write. Spending a character costs nothing, because
            // no reader looks at these names.
            '/' | '\\' | ':' | '*' | '?' | '"' | '<' | '>' | '|' => ' ',
            character if character.is_control() => ' ',
            character => character,
        })
        .collect();

    // Non-ASCII is preserved: this is a filename shown to a person, not an
    // identifier, and a journal is written in its author's own language.
    let collapsed = replaced.split_whitespace().collect::<Vec<_>>().join(" ");
    // Trimmed on both sides of the clip: before, so a leading dot does not
    // spend the budget, and after, because a cut at a word boundary can land
    // on the full stop that ended a sentence.
    let clipped = clip(collapsed.trim_matches(spare), SUMMARY_CHARS);
    let trimmed = clipped.trim_end_matches(spare);

    if trimmed.is_empty() {
        // Decision 0001 calls a change ID prefix the name a person can learn,
        // which makes it the right fallback for a message that says nothing.
        change.abbreviate(CHANGE_CHARS)
    } else {
        trimmed.to_owned()
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
            format!("historica\nchange {change}\nauthor A <a@example.com>\nwhen {when}\n");
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
        assert_eq!(base(&document), "2025-08/2025-08-19 Start a journal");
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
        assert_eq!(base(&document), "2025-08/2025-08-20 Late");
    }

    #[test]
    fn a_summary_gives_up_its_separators_and_its_extra_space() {
        let document = document(
            "qpvuntsmwlrkzxonmvtplsyq",
            "2025-08-19T00:47:11-06:00",
            "File  docs/README.md  under docs\n",
        );
        assert_eq!(
            base(&document),
            "2025-08/2025-08-19 File docs README.md under docs"
        );
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
    fn a_summary_gives_up_what_a_filesystem_reserves() {
        // 0006's `## Since`. Every one of these is a character FAT, exFAT or
        // NTFS refuses in a name, and a colon and a question mark are what an
        // ordinary message actually holds.
        let document = document(
            "qpvuntsmwlrkzxonmvtplsyq",
            "2025-08-19T00:47:11-06:00",
            "Fix: the parser? <yes> \"quoted\" | piped *star*\n",
        );
        assert_eq!(
            base(&document),
            "2025-08/2025-08-19 Fix the parser yes quoted piped star"
        );
    }

    #[test]
    fn a_trailing_dot_goes_the_way_the_leading_one_does() {
        // The stem is a directory name in `operations/`, and Windows drops a
        // trailing dot from one without saying so — which would land two
        // stems in one folder and break the determinism the scheme is held to.
        let document = document(
            "qpvuntsmwlrkzxonmvtplsyq",
            "2025-08-19T00:47:11-06:00",
            "Say what the parser refuses...\n",
        );
        assert_eq!(
            base(&document),
            "2025-08/2025-08-19 Say what the parser refuses"
        );
    }

    #[test]
    fn a_summary_of_nothing_a_filesystem_takes_falls_back_to_the_change() {
        // Every character replaced leaves an empty summary, which is the
        // state 0001's abbreviation already answers.
        let document = document(
            "qpvuntsmwlrkzxonmvtplsyq",
            "2025-08-19T00:47:11-06:00",
            "?*|\n",
        );
        assert_eq!(base(&document), "2025-08/2025-08-19 qpvuntsm");
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
        let summary = name
            .strip_prefix("2025-08/2025-08-19 ")
            .expect("the month and the date");
        assert!(summary.chars().count() <= SUMMARY_CHARS);
        assert!(long.starts_with(summary));
        assert!(!summary.ends_with(' '));
    }

    #[test]
    fn an_empty_message_falls_back_to_the_change_id() {
        let document = document("qpvuntsmwlrkzxonmvtplsyq", "2025-08-19T00:47:11-06:00", "");
        assert_eq!(base(&document), "2025-08/2025-08-19 qpvuntsm");
    }

    #[test]
    fn a_revision_is_filed_under_the_month_the_author_experienced() {
        // Decision 0041, on 0006's terms: the month is the date's own first
        // seven characters, read from `when` as spelled, so 01:00 on the 1st
        // at +13:00 is filed in the month the person had rather than the month
        // it was in UTC — and no clock this process could read comes into it.
        let document = document(
            "qpvuntsmwlrkzxonmvtplsyq",
            "2025-09-01T01:00:00+13:00",
            "Late\n",
        );
        assert_eq!(base(&document), "2025-09/2025-09-01 Late");
    }

    #[test]
    fn two_months_are_two_directories_and_the_filename_still_says_the_date() {
        // The filename carries the whole date, so a file separated from its
        // folder still says when it is from, and a name that sorted correctly
        // flat still does.
        let documents = [
            document(
                "qpvuntsmwlrkzxonmvtplsyq",
                "2025-08-31T23:00:00-06:00",
                "August\n",
            ),
            document(
                "mzvwutklopqrsnyxwkltvmzu",
                "2025-09-01T01:00:00-06:00",
                "September\n",
            ),
        ];
        assert_eq!(
            arranged(&documents),
            [
                "2025-08/2025-08-31 August".to_owned(),
                "2025-09/2025-09-01 September".to_owned()
            ]
        );
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
                "2025-08/2025-08-19 Notes qpvuntsm".to_owned(),
                "2025-08/2025-08-19 Notes mzvwutkl".to_owned()
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
            assert!(name.starts_with("2025-08/2025-08-19 Notes qpvuntsm "));
            // Both tiers of suffix land on the filename. A collision is two
            // names meeting in one directory, and decision 0041 made that
            // directory the month — which is the one place a suffix must not
            // go, or the two would be parted by living in different folders.
            assert_eq!(name.matches('/').count(), 1, "{name}");
            assert!(name.ends_with(&document.id().abbreviate(DIGEST_CHARS)));
        }
    }

    #[test]
    fn a_writer_reaches_the_same_three_tiers_arranging_does() {
        // Decision 0019 wrote two of them, because two revisions of one change
        // could only arrive from another replica. Decision 0023 made the third
        // reachable from the writing side: an amendment that reworded nothing
        // wants exactly the name its predecessor already has.
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
        let again = document(
            "mzvwutklopqrsnyxwkltvmzu",
            "2025-08-19T11:30:00-06:00",
            "Notes\n",
        );

        let named = |document: &RevisionDocument, existing: &[&RevisionDocument]| {
            stem_for(
                &document.when,
                &document.message,
                &document.change,
                &document.id(),
                existing.iter().copied(),
            )
        };
        assert_eq!(named(&one, &[]), "2025-08/2025-08-19 Notes");
        assert_eq!(named(&two, &[&one]), "2025-08/2025-08-19 Notes mzvwutkl");
        assert_eq!(
            named(&again, &[&one, &two]),
            format!(
                "2025-08/2025-08-19 Notes mzvwutkl {}",
                again.id().abbreviate(DIGEST_CHARS)
            )
        );
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
