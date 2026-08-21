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

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::io::{self, Write as _};
use std::path::Path;

use historica::core::RevisionId;
use historica::format::{RevisionDocument, digest};
use historica::store::{OPERATION_EXT, OPERATIONS_DIR, REVISION_EXT, REVISIONS_DIR, Store};

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

/// Rename every document to its arranged name.
pub fn arrange(root: &Path, dry_run: bool) -> Result<u8, Failure> {
    // Opening first means a store that does not parse is refused before
    // anything is renamed, and refused in the parser's own words.
    let store = Store::open(root)?;
    let wanted = names(store.iter());
    let operations = operation_names(&store, &wanted)?;

    // What this says is a running commentary on what it is doing; a reader
    // who walks away must not stop a rename half-done, so write errors are
    // ignored here rather than raised.
    let mut out = io::stdout().lock();

    let mut revisions = Tally::default();
    // The store's own walk, so `arrange` handles exactly the files the loader
    // read a moment ago — including any a person has already filed into
    // directories of their own, which decision 0016 lets them do.
    let directory = root.join(REVISIONS_DIR);
    let mut paths = historica::store::walk(root, REVISIONS_DIR)?.files;
    paths.retain(|path| path.extension().is_some_and(|found| found == REVISION_EXT));
    for path in paths {
        let id = digest_of(&path)?;
        let Some(stem) = wanted.get(&id) else {
            // Only reachable if the directory changed under us: `Store::open`
            // read these same files a moment ago.
            return Err(Failure::error(format!(
                "{} changed while it was being arranged",
                path.display()
            )));
        };

        // Renamed where it sits, never moved. A revision is one file, so
        // there is nothing for a directory to group, and a person who filed
        // one somewhere meant to.
        let target = path
            .parent()
            .unwrap_or(&directory)
            .join(format!("{stem}.{REVISION_EXT}"));
        place(
            &mut out,
            &path,
            &target,
            &directory,
            dry_run,
            &mut revisions,
            "revision",
        )?;
    }
    let _ = writeln!(out, "{}", revisions.line(&directory, dry_run));

    let mut documents = Tally::default();
    let directory = root.join(OPERATIONS_DIR);
    // Every file, not only the documents: decision 0017 puts payloads here
    // too, and a payload's whole point is that it carries the file's own name
    // rather than an extension of the format's.
    let paths = historica::store::walk(root, OPERATIONS_DIR)?.files;
    for path in paths {
        let id = digest_of(&path)?;
        let Some((stem, name)) = operations.get(&id) else {
            // A document no revision names — left where it is, and left
            // rather than reported as a fault. 0013's prune is what removes
            // one, and until it runs the document is simply unreferenced.
            documents.left += 1;
            continue;
        };

        // Here a document *is* moved, which is the whole of the nesting: the
        // directory carries the revision, so a document in the wrong one is
        // in the wrong place rather than merely misnamed. Decision 0018: the
        // rest of the name is the path, as directories.
        let mut target = directory.join(stem);
        for component in name.split('/') {
            target.push(component);
        }
        if path != target
            && !dry_run
            && let Some(parent) = target.parent()
        {
            fs::create_dir_all(parent)
                .map_err(|error| Failure::error(format!("{}: {error}", parent.display())))?;
        }
        let from = path.parent().map(Path::to_path_buf);
        if place(
            &mut out,
            &path,
            &target,
            &directory,
            dry_run,
            &mut documents,
            "document",
        )? && !dry_run
            && let Some(from) = from
        {
            // Tidying the directories this document was the last thing in.
            // Upwards, because decision 0018 files a path as directories, so
            // emptying one can empty the one above it — and `remove_dir`
            // refuses a directory holding anything, which is the guard: a
            // directory a person put something else in survives, and so does
            // everything above it.
            let mut empty = from.as_path();
            while empty != directory && fs::remove_dir(empty).is_ok() {
                match empty.parent() {
                    Some(parent) => empty = parent,
                    None => break,
                }
            }
        }
    }
    let _ = writeln!(out, "{}", documents.line(&directory, dry_run));

    Ok(0)
}

/// What arranging one directory came to.
#[derive(Default)]
struct Tally {
    renamed: usize,
    already: usize,
    duplicates: usize,
    left: usize,
}

impl Tally {
    /// The line printed after a directory is done.
    fn line(&self, directory: &Path, dry_run: bool) -> String {
        let mut line = format!(
            "{}: {} {}, {} already arranged",
            directory.display(),
            self.renamed,
            if dry_run { "to rename" } else { "renamed" },
            self.already
        );
        if self.duplicates > 0 {
            line.push_str(&format!(", {} left as duplicates", self.duplicates));
        }
        if self.left > 0 {
            line.push_str(&format!(", {} named by no revision", self.left));
        }
        line
    }
}

/// Put one document at the name it should have, saying what it did.
///
/// Returns whether the file actually moved, which is what tells the caller
/// there may be an empty directory behind it.
fn place(
    out: &mut io::StdoutLock<'static>,
    path: &Path,
    target: &Path,
    within: &Path,
    dry_run: bool,
    tally: &mut Tally,
    kind: &str,
) -> Result<bool, Failure> {
    if path == target {
        tally.already += 1;
        return Ok(false);
    }
    if target.exists() {
        // Two files holding one document is a note in `check` and a no-op
        // here: the arranged name is taken by the same bytes.
        tally.duplicates += 1;
        let _ = writeln!(
            out,
            "left {}: {} already holds this {kind}",
            shown(path, within),
            shown(target, within)
        );
        return Ok(false);
    }

    let _ = writeln!(
        out,
        "{} {}  ->  {}",
        if dry_run { "would rename" } else { "renamed" },
        shown(path, within),
        shown(target, within)
    );
    if !dry_run {
        fs::rename(path, target).map_err(|error| {
            Failure::error(format!(
                "{} -> {}: {error}",
                shown(path, within),
                shown(target, within)
            ))
        })?;
    }
    tally.renamed += 1;
    Ok(!dry_run)
}

/// What a file on disk hashes to, which is what it is.
fn digest_of(path: &Path) -> Result<RevisionId, Failure> {
    let bytes =
        fs::read(path).map_err(|error| Failure::error(format!("{}: {error}", path.display())))?;
    Ok(digest(&bytes))
}

/// Where everything in `operations/` belongs: a directory, and a path.
///
/// Decision 0016. The directory is the revision's own arranged stem, so
/// `revisions/2026-08-20 Initial state.rev` and
/// `operations/2026-08-20 Initial state/` are visibly the same thing, and what
/// is left to say is the path — which decision 0018 says as a path, in real
/// directories, rather than spelling one into a filename. So a revision's
/// folder is the subtree of the repository that revision touched, and
/// `notes/photo.png` inside it opens as a picture from a folder called
/// `notes`.
///
/// Decision 0017 puts payloads in the same directory and gives them the same
/// name without the `.{OPERATION_EXT}`, because a payload's name is the file's
/// own. The extension is what tells a document from a payload, so it is part
/// of the name a collision is decided on, and a document keeps it whatever
/// else happens.
///
/// The path is not in the revision document for an `edit`, so the tree at each
/// revision has to be materialised to find it. That is real work `arrange` did
/// not previously do, and it is affordable for one reason: `arrange` is a
/// manual tidying command that nothing runs in a loop.
fn operation_names(
    store: &Store,
    stems: &BTreeMap<RevisionId, String>,
) -> Result<BTreeMap<RevisionId, (String, String)>, Failure> {
    // A document is one document however many files arrive at its content, so
    // the same digest can be claimed by several paths and several revisions.
    // It can only live in one directory, so one claim has to win: the smallest
    // revision digest, then the smallest path. Both halves are content-derived,
    // so two replicas choose alike, and neither depends on what else is on
    // disk. It is arbitrary from a person's point of view — the winning
    // revision need not be the one where the content first appeared — and it
    // is deterministic, which is the property that matters.
    let mut claims: BTreeMap<RevisionId, (RevisionId, String, bool)> = BTreeMap::new();
    for (id, document) in store.iter() {
        if document.edited.is_empty() && document.text.is_empty() && document.bytes.is_empty() {
            continue;
        }
        let tree = store
            .merged_tree_of(&[*id])
            .map_err(|error| Failure::error(error.to_string()))?
            .tree;
        let named = document
            .edited
            .iter()
            .map(|(file, held)| (file, held, true))
            .chain(document.text.iter().map(|(file, held)| (file, held, false)))
            .chain(
                document
                    .bytes
                    .iter()
                    .map(|(file, held)| (file, held, false)),
            );
        for (file, held, is_document) in named {
            // `added` covers the revision that brought the file into being,
            // where the tree has it too; between them a path is always found.
            let Some(path) = tree
                .path(file)
                .or_else(|| document.added.get(file).map(String::as_str))
            else {
                continue;
            };
            let claim = (*id, path.to_owned(), is_document);
            claims
                .entry(*held)
                .and_modify(|held| {
                    if claim < *held {
                        *held = claim.clone();
                    }
                })
                .or_insert(claim);
        }
    }

    // Collisions are resolved inside a directory, because that is where two
    // names would actually meet. Decision 0018 leaves two ways for them to:
    // two paths can no longer produce one name, since the only way two paths
    // collide as directory trees is if they are the same path.
    let mut by_directory: BTreeMap<String, Vec<(RevisionId, String, bool)>> = BTreeMap::new();
    for (held, (revision, path, is_document)) in claims {
        let Some(stem) = stems.get(&revision) else {
            continue;
        };
        let name = match is_document {
            true => format!("{}.{OPERATION_EXT}", scrubbed(&path)),
            false => scrubbed(&path),
        };
        by_directory
            .entry(stem.clone())
            .or_default()
            .push((held, name, is_document));
    }

    let mut out = BTreeMap::new();
    for (stem, mut sharing) in by_directory {
        sharing.sort();

        // Every directory these names need. A name that *is* one of them is a
        // file where another file needs a directory: 0008 has no directories,
        // so nothing stops a history holding both `notes` and
        // `notes/photo.png`, and no filesystem can hold both either.
        let mut directories: BTreeSet<&str> = BTreeSet::new();
        for (_, name, _) in &sharing {
            let mut rest = name.as_str();
            while let Some(cut) = rest.rfind('/') {
                rest = &rest[..cut];
                directories.insert(rest);
            }
        }

        let mut counts: BTreeMap<&str, usize> = BTreeMap::new();
        for (_, name, _) in &sharing {
            *counts.entry(name.as_str()).or_default() += 1;
        }
        let taken: BTreeMap<String, bool> = counts
            .into_iter()
            .map(|(name, count)| (name.to_owned(), count > 1))
            .collect();

        for (held, name, is_document) in &sharing {
            // Whether this is a document is carried, never read back off the
            // name: a payload for a path that ends in `.ops` is a payload, and
            // a rename that made it look like a document would hand it to the
            // parser, which is the one thing a disambiguator may not do.
            let name = if directories.contains(name.as_str()) {
                // The file at the shorter path yields, and keeps its digest
                // name at the top of the revision's directory, where nothing
                // can be a directory over it.
                match is_document {
                    true => format!("{held}.{OPERATION_EXT}"),
                    false => held.to_string(),
                }
            } else if taken.get(name.as_str()).copied().unwrap_or(false) {
                // A payload and a document one path apart — `x.ops` and `x` —
                // are the only two names left that can meet. The suffix goes
                // on the last component, and inside the extension where there
                // is one, because a document that lost `.ops` would stop being
                // one and a payload that gained it would start.
                let (head, last) = match name.rfind('/') {
                    Some(cut) => name.split_at(cut + 1),
                    None => ("", name.as_str()),
                };
                let suffix = held.abbreviate(DIGEST_CHARS);
                match is_document {
                    true => {
                        let last = last
                            .strip_suffix(&format!(".{OPERATION_EXT}"))
                            .unwrap_or(last);
                        format!("{head}{last} {suffix}.{OPERATION_EXT}")
                    }
                    false => format!("{head}{last} {suffix}"),
                }
            } else {
                name.clone()
            };
            out.insert(*held, (stem.clone(), name));
        }
    }
    Ok(out)
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
fn scrubbed(path: &str) -> String {
    path.chars()
        .map(|character| match character {
            character if character.is_control() => ' ',
            character => character,
        })
        .collect()
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
fn shown(path: &Path, within: &Path) -> String {
    // Relative to the directory being arranged, not just the filename:
    // nesting means two documents can share a name and differ by the
    // directory, and a commentary that printed only the name would report
    // the same rename twice.
    path.strip_prefix(within)
        .unwrap_or(path)
        .to_string_lossy()
        .into_owned()
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
