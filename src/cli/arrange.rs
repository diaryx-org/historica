//! `arrange`: the advisory names decision 0006 made deterministic.
//!
//! Identity comes from content, so a revision's filename means nothing to the
//! reader and everything to the person browsing the folder. This renames each
//! `.rev` file to `YYYY-MM-DD summary.rev` and nothing else — no file's bytes
//! are touched, so no identity moves and no reference dangles.
//!
//! The one hard rule is determinism. Two replicas arranging the same history
//! must produce the same filenames, or sync sees two files per revision and a
//! scheme meant to make a folder readable fills it with conflicted copies.
//! That is why a collision appends a change ID rather than a counter: a
//! counter depends on what else is in the directory, and a content-derived
//! suffix does not.

use std::collections::BTreeMap;
use std::fs;
use std::io::{self, Write as _};
use std::path::Path;

use historica::core::RevisionId;
use historica::format::{RevisionDocument, digest};
use historica::store::{REVISION_EXT, REVISIONS_DIR, Store};

use super::Failure;

/// Characters of summary a filename carries, cut at a word boundary.
///
/// Sixty leaves room for a date, an extension, and a two-word suffix inside
/// the 255 bytes every filesystem in use allows, even where the summary is
/// entirely non-ASCII.
const SUMMARY_CHARS: usize = 60;
/// Change ID characters where a name needs one.
const CHANGE_CHARS: usize = 8;
/// Digest characters where two revisions of one change would still collide.
const DIGEST_CHARS: usize = 12;

/// Rename every revision file to its arranged name.
pub fn arrange(root: &Path, dry_run: bool) -> Result<u8, Failure> {
    // Opening first means a store that does not parse is refused before
    // anything is renamed, and refused in the parser's own words.
    let store = Store::open(root)?;
    let wanted = names(store.iter());

    let directory = root.join(REVISIONS_DIR);
    let mut paths: Vec<_> = fs::read_dir(&directory)
        .map_err(|error| Failure::error(format!("{}: {error}", directory.display())))?
        .filter_map(Result::ok)
        .map(|entry| entry.path())
        .filter(|path| path.extension().is_some_and(|found| found == REVISION_EXT))
        .collect();
    paths.sort();

    // What this says is a running commentary on what it is doing; a reader
    // who walks away must not stop a rename half-done, so write errors are
    // ignored here rather than raised.
    let mut out = io::stdout().lock();
    let mut renamed = 0usize;
    let mut already = 0usize;
    let mut duplicates = 0usize;

    for path in paths {
        let bytes = fs::read(&path)
            .map_err(|error| Failure::error(format!("{}: {error}", path.display())))?;
        let id = digest(&bytes);
        let Some(stem) = wanted.get(&id) else {
            // Only reachable if the directory changed under us: `Store::open`
            // read these same files a moment ago.
            return Err(Failure::error(format!(
                "{} changed while it was being arranged",
                path.display()
            )));
        };

        let target = directory.join(format!("{stem}.{REVISION_EXT}"));
        if path == target {
            already += 1;
            continue;
        }
        if target.exists() {
            // Two files holding one revision is a note in `check` and a
            // no-op here: the arranged name is taken by the same bytes.
            duplicates += 1;
            let _ = writeln!(
                out,
                "left {}: {} already holds this revision",
                shown(&path),
                shown(&target)
            );
            continue;
        }

        let _ = writeln!(
            out,
            "{} {}  ->  {}",
            if dry_run { "would rename" } else { "renamed" },
            shown(&path),
            shown(&target)
        );
        if !dry_run {
            fs::rename(&path, &target).map_err(|error| {
                Failure::error(format!("{} -> {}: {error}", shown(&path), shown(&target)))
            })?;
        }
        renamed += 1;
    }

    let _ = writeln!(
        out,
        "{}: {renamed} {}, {already} already arranged{}",
        directory.display(),
        if dry_run { "to rename" } else { "renamed" },
        if duplicates > 0 {
            format!(", {duplicates} left as duplicates")
        } else {
            String::new()
        }
    );
    Ok(0)
}

/// The arranged filename stem for every revision, collisions resolved.
///
/// Collisions are resolved against the whole set rather than against whatever
/// happens to be on disk, so the answer depends only on the history.
fn names<'a>(
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

/// `YYYY-MM-DD summary`, before any collision is resolved.
fn base(document: &RevisionDocument) -> String {
    // The date comes from `when` as written, so it is the date in the offset
    // the author experienced. Decision 0002 keeps timestamps out of identity
    // and ordering, which is exactly what frees them for this.
    let date: String = document.when.as_str().chars().take(10).collect();
    format!("{date} {}", summary(document))
}

/// The message's first line, made into something a folder can hold.
fn summary(document: &RevisionDocument) -> String {
    let first = document.message.lines().next().unwrap_or_default();
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
        document.change.abbreviate(CHANGE_CHARS)
    } else {
        trimmed
    }
}

/// At most `limit` characters, cut at a word boundary where there is one.
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

/// A path as its filename, which is the part a rename changes.
fn shown(path: &Path) -> String {
    path.file_name()
        .map(|name| name.to_string_lossy().into_owned())
        .unwrap_or_else(|| path.display().to_string())
}

#[cfg(test)]
mod tests {
    use super::*;

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
        let named = names(ids.iter().zip(documents.iter()));
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
