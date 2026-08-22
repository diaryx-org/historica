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
use historica::format::digest;
use historica::fs::Disk;
use historica::naming::{self, Filing};
use historica::store::{
    OPERATIONS_DIR, REVISION_SUFFIX, REVISION_SUFFIXES, REVISIONS_DIR, Store, claims,
};

use super::Failure;

/// Rename every document to its arranged name.
pub fn arrange(root: &Path, dry_run: bool) -> Result<u8, Failure> {
    // Opening first means a store that does not parse is refused before
    // anything is renamed, and refused in the parser's own words.
    let store = Store::open(root)?;
    let wanted = naming::stems(store.iter());
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
    let mut paths = historica::store::walk(&Disk, root, REVISIONS_DIR)?.files;
    paths.retain(|path| claims(path, &REVISION_SUFFIXES));
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
            .join(format!("{stem}{REVISION_SUFFIX}"));
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
    let paths = historica::store::walk(&Disk, root, OPERATIONS_DIR)?.files;
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
/// name without the `.ops.txt`, because a payload's name is the file's
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
    // names would actually meet. The rule is the library's, so what `arrange`
    // produces on a store is what `record` would have written into it.
    let mut by_directory: BTreeMap<String, Vec<Filing>> = BTreeMap::new();
    for (held, (revision, path, document)) in claims {
        let Some(stem) = stems.get(&revision) else {
            continue;
        };
        by_directory.entry(stem.clone()).or_default().push(Filing {
            held,
            path,
            document,
        });
    }

    let mut out = BTreeMap::new();
    for (stem, filings) in by_directory {
        for (held, name) in naming::filed(&filings) {
            out.insert(held, (stem.clone(), name));
        }
    }
    Ok(out)
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
