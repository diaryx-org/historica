//! Where each file in `operations/` is, so that reading one costs one read.
//!
//! Decision 0036. 0003 puts identity in content and makes filenames
//! presentation, which is what lets a person file a history however they
//! please — and what left the store no way to find a digest except to read
//! every file in the directory and hash it. 0035 removed the cost of
//! *replaying* a long history and left that one standing: `cat` on a store of
//! five hundred revisions read fifteen thousand files to answer from a cache
//! entry it already held.
//!
//! A catalogue is the other half. It says, for every file under
//! `operations/`, the digest of its bytes and — for a forgetting document —
//! the digest it forgets. It is kept in `cache/`, it is disposable, and it is
//! believed under exactly one condition: **the set of paths it names is the
//! set of paths the directory now holds**. That condition is checked by a
//! directory walk, which lists names without opening anything, and the store
//! already performs one.
//!
//! Anything the catalogue does not account for is read. A path it does not
//! name is new and is read and hashed; a path it names that is gone is
//! dropped. So a `record` that wrote three documents costs three reads rather
//! than the whole directory, and a store this program has never seen costs
//! one full pass and no more.
//!
//! What is believed and what is checked are worth separating. The digest of a
//! *file* is never believed: a lookup goes to the path the catalogue names,
//! reads it, and hashes it before parsing, so an entry left by an older
//! version or edited by a person is refused exactly where 0035 refuses a
//! stale state. What is believed, once the path set matches, is that a path
//! this catalogue called an ordinary document has not since become a
//! forgetting one. That inference is the store's own rule — documents are
//! immutable, written with `create_new`, and never overwritten — and `check`,
//! which builds its catalogue by reading the directory and never from
//! `cache/`, is the command that holds a store to it.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use crate::core::RevisionId;
use crate::format::{self, OperationDocument, digest};
use crate::fs::Filesystem;

use super::{
    CACHE_DIR, OPERATION_SUFFIXES, OPERATIONS_DIR, StoreError, claims, platform_file, walk,
};

/// What `cache/` calls the catalogue.
///
/// A fixed name rather than a digest, which is the one way this differs from
/// every other entry 0035 describes: a catalogue is not content and there is
/// nothing to look it up *by*. It is still disposable, still ignored when it
/// fails to read, and still correct to delete.
const CATALOGUE_FILE: &str = "operations.txt";

/// The line a catalogue starts with.
///
/// Not a document preamble — a catalogue claims nothing and is named in no
/// grammar. It is here so that a catalogue written by a version that spelled
/// this differently is discarded whole rather than half-understood, which is
/// the only failure mode a fixed name introduces that a digest-named entry
/// does not have.
const CATALOGUE_HEADER: &str = "historica-catalogue-1";

/// One file under `operations/`, as the catalogue holds it.
///
/// Not `arrange`'s `Filed`, which is about the name a person reads. This is
/// about where the bytes are.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct Located {
    /// Where it is, relative to the store root.
    pub(super) path: PathBuf,
    /// The digest it forgets, for a forgetting document (decision 0014).
    pub(super) forgets: Option<RevisionId>,
    /// Whether its name claims it is a document rather than a payload.
    pub(super) document: bool,
}

/// Every file in `operations/`, by the digest of its bytes.
#[derive(Debug, Clone, Default)]
pub(super) struct Catalogue {
    /// Digest to the file holding those bytes.
    ///
    /// A duplicate resolves to the first path in walk order, which is sorted,
    /// so two replicas holding one store answer alike.
    at: BTreeMap<RevisionId, Located>,
    /// Which held documents forget which digest, by the digest forgotten.
    ///
    /// Decision 0014 makes a forgetting document the thing a reader consumes,
    /// so every materialised operation asks this question. Derived from `at`
    /// and maintained with it, so the two cannot disagree.
    forgetting: BTreeMap<RevisionId, Vec<RevisionId>>,
}

impl Catalogue {
    /// Where the bytes with this digest are, if this store holds them.
    pub(super) fn at(&self, id: &RevisionId) -> Option<&Located> {
        self.at.get(id)
    }

    /// Every digest catalogued, with where it is.
    pub(super) fn iter(&self) -> impl Iterator<Item = (&RevisionId, &Located)> {
        self.at.iter()
    }

    /// The documents standing in for a destroyed digest.
    pub(super) fn forgetting(&self, target: &RevisionId) -> &[RevisionId] {
        self.forgetting.get(target).map_or(&[], Vec::as_slice)
    }

    /// Hold one more file, as a writer that has just written it knows it.
    ///
    /// A writer knows the path, the digest and what the document forgets
    /// without reading anything, so recording does not fall back to a pass
    /// over the directory to learn what it just did.
    pub(super) fn insert(&mut self, id: RevisionId, filed: Located) {
        if let Some(target) = filed.forgets {
            let standing = self.forgetting.entry(target).or_default();
            if !standing.contains(&id) {
                standing.push(id);
            }
        }
        self.at.insert(id, filed);
    }

    /// Let go of one file, and of the index entry standing for it.
    pub(super) fn remove(&mut self, id: &RevisionId) -> Option<Located> {
        let filed = self.at.remove(id)?;
        if let Some(target) = filed.forgets
            && let Some(standing) = self.forgetting.get_mut(&target)
        {
            standing.retain(|held| held != id);
            if standing.is_empty() {
                self.forgetting.remove(&target);
            }
        }
        Some(filed)
    }

    /// Rebuild `forgetting` from `at`, after loading or reconciling.
    fn index(&mut self) {
        self.forgetting.clear();
        for (id, filed) in &self.at {
            if let Some(target) = filed.forgets {
                self.forgetting.entry(target).or_default().push(*id);
            }
        }
    }
}

/// Catalogue `operations/`, taking what `cache/` already knows where it can.
///
/// `cached` is false for the one caller that must not take it: `check` exists
/// to do the work rather than to have the answer, and a catalogue is an
/// answer.
pub(super) fn read<F: Filesystem + ?Sized>(
    files: &F,
    root: &Path,
    cached: bool,
) -> Result<(Catalogue, BTreeMap<RevisionId, OperationDocument>), StoreError> {
    // The directory as it stands, which is names and no contents. This is the
    // walk the store performed anyway, and it is what every belief below is
    // checked against.
    let mut here: Vec<PathBuf> = walk(files, root, OPERATIONS_DIR)?.files;
    // Decision 0022: a file the platform wrote into our folder is not content
    // and not a fault. Nothing reads it, so nothing catalogues it.
    here.retain(|path| !platform_file(path));

    let held = if cached {
        held_catalogue(files, root)
    } else {
        BTreeMap::new()
    };
    // Whether this pass learned anything the held catalogue did not already
    // say. A store nobody has written to since the last read is the common
    // case, and rewriting the file for it would be the whole catalogue's
    // bytes for no change at all — on every command.
    let mut accounted = 0usize;

    let mut catalogue = Catalogue::default();
    // What this pass had to parse in order to learn what a document forgets.
    // Handed back rather than dropped: the store is about to be asked for
    // some of it, and parsing one file twice in one command is the cost this
    // whole module exists to remove.
    let mut parsed: BTreeMap<RevisionId, OperationDocument> = BTreeMap::new();
    for path in here {
        let relative = match path.strip_prefix(root) {
            Ok(relative) => relative.to_path_buf(),
            Err(_) => path.clone(),
        };
        let document = claims(&path, &OPERATION_SUFFIXES);
        // A path the catalogue already accounted for is taken as it stands.
        // A path it did not is read: it is new to this store, or the
        // catalogue is one this version does not understand, and either way
        // the directory is the authority.
        let (id, forgets) = match held.get(&relative) {
            Some((id, forgets)) => {
                accounted += 1;
                (*id, *forgets)
            }
            None => {
                let bytes = files
                    .read(&path)
                    .map_err(|error| StoreError::io(&path, error))?;
                let id = digest(&bytes);
                // Only a document can forget, and only a parse can say what
                // it forgets. A payload is bytes with no grammar, and a
                // resolution has no items to destroy — 0032 defers binary at
                // a merge and 0014 destroys an operation document's payload.
                let forgets = if document && !format::is_resolution(&bytes) {
                    match OperationDocument::parse(&bytes) {
                        Ok(document) => {
                            let forgets = document.forgets;
                            parsed.insert(id, document);
                            forgets
                        }
                        // Unparsable here is `check`'s finding, not a reason
                        // to refuse to catalogue where the file is.
                        Err(_) => None,
                    }
                } else {
                    None
                };
                (id, forgets)
            }
        };
        // Sorted by `walk`, so a duplicate resolves to the same path on every
        // replica: the first one found keeps the entry.
        catalogue.at.entry(id).or_insert(Located {
            path: relative,
            forgets,
            document,
        });
    }
    catalogue.index();

    // Written when the directory and the held catalogue disagreed: a path
    // this pass had to read, or one the catalogue named and the directory has
    // since lost. Writers do not write it as they go — a `record` that
    // rewrote the whole catalogue once per document would be quadratic in the
    // size of the store — so this is the one place it is kept up to date, and
    // the cost of that is the next reader reading the files this one wrote.
    if cached && (accounted != held.len() || accounted != catalogue.at.len()) {
        write(files, root, &catalogue);
    }
    Ok((catalogue, parsed))
}

/// What `cache/` says, by path, or nothing at all.
///
/// Every failure is silence. A catalogue that will not read, will not parse,
/// or was written by a version that spelled it differently is a catalogue
/// this store does not have, and a store that does not have one reads its
/// directory.
fn held_catalogue<F: Filesystem + ?Sized>(
    files: &F,
    root: &Path,
) -> BTreeMap<PathBuf, (RevisionId, Option<RevisionId>)> {
    let Ok(bytes) = files.read(&root.join(CACHE_DIR).join(CATALOGUE_FILE)) else {
        return BTreeMap::new();
    };
    let Ok(text) = std::str::from_utf8(&bytes) else {
        return BTreeMap::new();
    };
    parse(text)
}

/// One catalogue's text, read back.
///
/// Separated from the reading so that what a catalogue *is* can be tested
/// without a filesystem to hold it: this is a total function from a string to
/// what the store will believe, and every way of failing returns nothing.
fn parse(text: &str) -> BTreeMap<PathBuf, (RevisionId, Option<RevisionId>)> {
    let mut lines = text.lines();
    if lines.next() != Some(CATALOGUE_HEADER) {
        return BTreeMap::new();
    }
    let mut held = BTreeMap::new();
    for line in lines {
        // `<digest> <forgets|-> <path>`, path last because a path is the one
        // field that may hold a space.
        let Some((id, rest)) = line.split_once(' ') else {
            return BTreeMap::new();
        };
        let Some((forgets, path)) = rest.split_once(' ') else {
            return BTreeMap::new();
        };
        let Ok(id) = id.parse::<RevisionId>() else {
            return BTreeMap::new();
        };
        let forgets = match forgets {
            "-" => None,
            stated => match stated.parse::<RevisionId>() {
                Ok(target) => Some(target),
                Err(_) => return BTreeMap::new(),
            },
        };
        if path.is_empty() {
            return BTreeMap::new();
        }
        held.insert(PathBuf::from(path), (id, forgets));
    }
    held
}

/// Write the catalogue back, and say nothing about whether it worked.
///
/// 0035's rule, unchanged: a store on a read-only filesystem, a full disk,
/// and a `cache/` somebody deleted mid-command are all conditions under which
/// reading a file must still succeed. Nothing is lost when this fails — the
/// next reader walks the directory, as this one just did.
pub(super) fn write<F: Filesystem + ?Sized>(files: &F, root: &Path, catalogue: &Catalogue) {
    // Replaced rather than created: a catalogue is the one mutable file in
    // `cache/`, and 0026 makes replacement atomic, so a reader never meets
    // half of one. A half-read catalogue would be discarded anyway; this
    // means it never has to be.
    let _ = files.create_directory(&root.join(CACHE_DIR));
    let _ = files.write(
        &root.join(CACHE_DIR).join(CATALOGUE_FILE),
        render(catalogue).as_bytes(),
    );
}

/// One catalogue as the bytes `cache/` holds.
fn render(catalogue: &Catalogue) -> String {
    let mut text = String::from(CATALOGUE_HEADER);
    text.push('\n');
    // By path, so that a catalogue is a stable file: two stores holding one
    // history write one set of bytes, and reading two catalogues against each
    // other is about what the directories hold rather than about map order.
    let mut lines: Vec<String> = catalogue
        .at
        .iter()
        .filter_map(|(id, filed)| {
            // A path that is not UTF-8 cannot be written to a readable file,
            // and it is one entry rather than the whole catalogue: leaving it
            // out costs the next reader one read of that file.
            let path = filed.path.to_str()?;
            let forgets = filed
                .forgets
                .map_or_else(|| "-".to_owned(), |target| target.to_string());
            Some(format!("{id} {forgets} {path}\n"))
        })
        .collect();
    lines.sort();
    text.extend(lines);
    text
}

#[cfg(test)]
mod tests {
    use super::*;

    fn filed(path: &str, forgets: Option<RevisionId>) -> Located {
        Located {
            path: PathBuf::from(path),
            forgets,
            document: true,
        }
    }

    /// A path with a space in it survives the round trip, because the path is
    /// the last field on the line and everything after the second space is
    /// read as the path. A merge writes such a name by construction, and
    /// `arrange` writes one for every revision whose summary has a space.
    #[test]
    fn a_path_with_a_space_round_trips() {
        let id = digest(b"one");
        let mut catalogue = Catalogue::default();
        let path = "operations/2026-01-01 a name/notes.md.ops.txt";
        catalogue.insert(id, filed(path, None));

        let held = parse(&render(&catalogue));
        assert_eq!(held.get(Path::new(path)), Some(&(id, None)));
    }

    /// What a forgetting document forgets survives it too: that field is the
    /// one thing the catalogue is believed about without being re-read, so a
    /// catalogue that lost it would be worse than no catalogue at all.
    #[test]
    fn what_a_document_forgets_round_trips() {
        let target = digest(b"destroyed");
        let mut catalogue = Catalogue::default();
        catalogue.insert(
            digest(b"stand-in"),
            filed("operations/a.ops.txt", Some(target)),
        );

        let held = parse(&render(&catalogue));
        assert_eq!(
            held.get(Path::new("operations/a.ops.txt")),
            Some(&(digest(b"stand-in"), Some(target)))
        );
    }

    /// A catalogue whose header is not this one is a catalogue this version
    /// does not have. Discarding it whole is what a fixed name costs, and it
    /// is what keeps it from being read as something it is not.
    #[test]
    fn a_catalogue_from_another_version_is_discarded() {
        assert!(parse("historica-catalogue-0\n").is_empty());
        assert!(parse("").is_empty());
    }

    /// One malformed line discards the whole catalogue rather than the line.
    /// A catalogue is believed only when it accounts for the whole directory,
    /// so a partial one is not a smaller catalogue — it is a claim about a
    /// path set that is now wrong, and the directory is right there.
    #[test]
    fn a_line_that_does_not_parse_discards_the_catalogue() {
        let id = digest(b"one");
        let good = format!("{CATALOGUE_HEADER}\n{id} - operations/a.ops.txt\n");
        assert_eq!(parse(&good).len(), 1);

        for bad in [
            format!("{CATALOGUE_HEADER}\nnot-a-digest - operations/a.ops.txt\n"),
            format!("{CATALOGUE_HEADER}\n{id} not-a-digest operations/a.ops.txt\n"),
            format!("{CATALOGUE_HEADER}\n{id} -\n"),
            format!("{CATALOGUE_HEADER}\n{id} - \n"),
            format!("{good}oh dear\n"),
        ] {
            assert!(parse(&bad).is_empty(), "should have been discarded: {bad}");
        }
    }

    /// Forgetting is indexed by what is forgotten, and two documents may
    /// forget one digest — 0014's union, which arrives in either order.
    #[test]
    fn two_documents_forgetting_one_digest_both_stand_in() {
        let target = digest(b"destroyed");
        let mut catalogue = Catalogue::default();
        catalogue.insert(
            digest(b"first"),
            filed("operations/a.ops.txt", Some(target)),
        );
        catalogue.insert(
            digest(b"second"),
            filed("operations/b.ops.txt", Some(target)),
        );
        assert_eq!(catalogue.forgetting(&target).len(), 2);

        catalogue.remove(&digest(b"first"));
        assert_eq!(catalogue.forgetting(&target), [digest(b"second")]);
        catalogue.remove(&digest(b"second"));
        assert!(catalogue.forgetting(&target).is_empty());
    }

    /// Rebuilding the index from the entries is what loading does, and it has
    /// to agree with what inserting one at a time builds.
    #[test]
    fn the_index_rebuilt_agrees_with_the_index_maintained() {
        let target = digest(b"destroyed");
        let mut maintained = Catalogue::default();
        maintained.insert(
            digest(b"first"),
            filed("operations/a.ops.txt", Some(target)),
        );
        maintained.insert(digest(b"second"), filed("operations/b.ops.txt", None));

        let mut rebuilt = maintained.clone();
        rebuilt.forgetting.clear();
        rebuilt.index();
        assert_eq!(rebuilt.forgetting, maintained.forgetting);
    }
}
