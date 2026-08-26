//! `arrange`: the advisory names decision 0006 made deterministic.
//!
//! Identity comes from content, so a revision's filename means nothing to the
//! reader and everything to the person browsing the folder. This gives each
//! revision document the name `YYYY-MM-DD summary.rev.txt` and files each
//! operation document and payload under the revision that named it, at the
//! path it had — and touches no file's bytes, so no identity moves and no
//! reference dangles.
//!
//! Where the revision document *sits* is [`Placement`]'s question, and the
//! default answer is: wherever it already does. Decision 0016 says a name that
//! differs is usually a person filing their own history, and a revision is one
//! file with nothing for a directory to group, so a folder around one is that
//! person's statement rather than an accident to be tidied away. Decision 0041
//! gave the writer a month to file under; [`Placement::Refiled`] is what
//! applies that to a store written before it, and is the whole of the
//! migration.
//!
//! It lives here rather than in the command-line front end because the thing
//! being offered is readability. A host syncing a store into somebody's iCloud
//! folder wants the arranged names for exactly the reason a person at a
//! terminal does, and 0025's open question — whether this belonged in the
//! library — is answered by noticing that the interesting half of it,
//! [`operation_names`], was already pure library work sitting in `src/cli/`.
//! What stays in the front end is the rendering: what to print, and in what
//! order.
//!
//! The one hard rule is determinism. Two replicas arranging the same history
//! must produce the same filenames, or sync sees two files per revision and a
//! scheme meant to make a folder readable fills it with conflicted copies.
//! That is why a collision appends a change ID rather than a counter: a
//! counter depends on what else is in the directory, and a content-derived
//! suffix does not.

use std::collections::BTreeMap;
use std::fmt;
use std::path::{Path, PathBuf};

use crate::core::RevisionId;
use crate::fs::Filesystem;
use crate::naming::{self, Filing};

use super::{
    MaterialiseError, OPERATIONS_DIR, REVISION_SUFFIX, REVISION_SUFFIXES, REVISIONS_DIR, Store,
    StoreError, claims, walk, within,
};

/// Whether `arrange` decides where a revision document sits, or only what it
/// is called there.
///
/// Only revision documents have the question. `operations/` is the scheme's
/// own territory — decisions 0016, 0017 and 0018 make its directories say
/// which revision and which path, which is a fact about the history rather
/// than a place a person chose — so it is filed the same way under both.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Placement {
    /// Rename a revision document where it sits.
    ///
    /// The default, and what `arrange` did before decision 0041: a directory
    /// a person put a revision in is a directory they meant, and the store
    /// loads from any depth, so keeping it costs the reader nothing. A store
    /// the writer produced is already in its month, so this leaves it there.
    #[default]
    Kept,
    /// File every revision document under decision 0041's month, wherever it
    /// sat.
    ///
    /// The migration for a store written flat — by an older version, by
    /// another tool, or by hand — and the one thing that overrules a person's
    /// own filing, which is why it has to be asked for.
    Refiled,
}

/// Which of the store's two arranged directories a file sits in.
///
/// Not what the file *is*: `operations/` holds documents and payloads alike,
/// and 0017's whole point is that arranging treats them the same way. This is
/// the directory, because that is what a report groups by.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Filed {
    /// A revision document, in `revisions/`.
    Revision,
    /// An operation document or a payload, in `operations/`.
    Operation,
}

impl Filed {
    /// The directory this kind lives in.
    pub fn directory(self) -> &'static str {
        match self {
            Filed::Revision => REVISIONS_DIR,
            Filed::Operation => OPERATIONS_DIR,
        }
    }
}

/// One file, and the name it should have.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct Rename {
    /// Where it is, relative to the store root.
    pub from: PathBuf,
    /// Where it belongs, relative to the store root.
    pub to: PathBuf,
    /// Which directory it is in.
    pub filed: Filed,
}

/// A file already at the name arranging would give it.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct Arranged {
    /// Where it is, relative to the store root.
    pub path: PathBuf,
    /// Which directory it is in.
    pub filed: Filed,
}

/// A file left where it is, because its arranged name is taken.
///
/// By the same bytes: a name is a digest's, and two files holding one document
/// is `check`'s `Duplicate` note rather than a fault. Arranging cannot merge
/// them, so it says so and moves on.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct Occupied {
    /// The file that stayed, relative to the store root.
    pub path: PathBuf,
    /// The file already at the name it wanted.
    pub holder: PathBuf,
    /// Which directory both are in.
    pub filed: Filed,
}

/// What arranging did, or would do.
///
/// [`Store::arrange`] acts on exactly what [`Store::arrangement`] describes,
/// so a dry run and the real thing can never name different files — the same
/// promise `prunable`/`prune` and `forget_plan`/`forget` make.
#[derive(Debug, Clone, Default)]
#[non_exhaustive]
pub struct Arrangement {
    /// Every file that moved, or would, in the order it was done.
    pub renames: Vec<Rename>,
    /// Files already at the name arranging would give them.
    pub already: Vec<Arranged>,
    /// Files left where they are, because the name is taken.
    pub occupied: Vec<Occupied>,
    /// Files in `operations/` that no revision this store holds names.
    ///
    /// Left rather than reported as a fault: 0013's `prune` is what removes
    /// one, and until it runs the file is simply unreferenced.
    pub unnamed: Vec<PathBuf>,
}

impl Arrangement {
    /// Whether arranging would move nothing, which arranging twice does.
    pub fn is_empty(&self) -> bool {
        self.renames.is_empty()
    }

    /// How many files in one directory moved, were already right, and were
    /// left because the name was taken.
    ///
    /// The three numbers a report says out loud, counted here so that two
    /// front ends counting them cannot disagree.
    pub fn tally(&self, filed: Filed) -> Tally {
        Tally {
            renamed: self.renames.iter().filter(|r| r.filed == filed).count(),
            already: self.already.iter().filter(|a| a.filed == filed).count(),
            occupied: self.occupied.iter().filter(|o| o.filed == filed).count(),
            unnamed: match filed {
                Filed::Operation => self.unnamed.len(),
                Filed::Revision => 0,
            },
        }
    }
}

/// What arranging one directory came to.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
#[non_exhaustive]
pub struct Tally {
    /// Files that moved, or would.
    pub renamed: usize,
    /// Files already at their arranged name.
    pub already: usize,
    /// Files left because the name was taken.
    pub occupied: usize,
    /// Files no revision names. Always zero for `revisions/`, where a file
    /// whose digest is unknown is an error rather than an observation.
    pub unnamed: usize,
}

impl<F: Filesystem> Store<F> {
    /// What `arrange` would rename, without renaming anything.
    pub fn arrangement(&self, placement: Placement) -> Result<Arrangement, ArrangeError> {
        let documents = self.documents()?;
        let stems = naming::stems(documents.iter().copied());
        let operations = self.operation_names(&stems, documents.iter().copied())?;
        let mut plan = Arrangement::default();

        // The store's own walk, so arranging handles exactly the files the
        // loader read — including any a person has already filed into
        // directories of their own, which decision 0016 lets them do.
        let revisions = self.root.join(REVISIONS_DIR);
        let mut paths = walk(&self.files, &self.root, REVISIONS_DIR)?.files;
        paths.retain(|path| claims(path, &REVISION_SUFFIXES));
        for path in paths {
            let id = self.digest_of(&path)?;
            let Some(stem) = stems.get(&id) else {
                // Only reachable if the directory changed under us: the loader
                // read these same files when the store was opened.
                return Err(ArrangeError::Changed { file: path });
            };
            // Renamed where it sits, unless refiling was asked for. A revision
            // is one file, so there is nothing for a directory to group, and a
            // person who filed one somewhere meant to — decision 0016's rule,
            // which decision 0041 keeps by making its month `--refile`'s to
            // apply rather than every run's. Both spellings of the name are
            // the same stem: the month is only the directory half of it, so a
            // rename in place uses the filename half and moves nothing.
            let target = match placement {
                Placement::Kept => path
                    .parent()
                    .unwrap_or(&revisions)
                    .join(format!("{}{REVISION_SUFFIX}", leaf(stem))),
                Placement::Refiled => within(&revisions, &format!("{stem}{REVISION_SUFFIX}")),
            };
            self.place(&mut plan, path, target, Filed::Revision)?;
        }

        // Every file, not only the documents: decision 0017 puts payloads here
        // too, and a payload's whole point is that it carries the file's own
        // name rather than an extension of the format's.
        let operations_dir = self.root.join(OPERATIONS_DIR);
        for path in walk(&self.files, &self.root, OPERATIONS_DIR)?.files {
            let id = self.digest_of(&path)?;
            let Some((stem, name)) = operations.get(&id) else {
                plan.unnamed.push(self.relative(&path));
                continue;
            };
            // Here a file *is* moved, under both placements, which is the
            // whole of the nesting: the directory carries the revision, so a
            // document in the wrong one is in the wrong place rather than
            // merely misnamed. Decision 0018: the rest of the name is the
            // path, as directories. The stem is the whole stem, month and
            // all, so a revision's folder is named by what the revision is
            // rather than by where its document happens to sit — which is the
            // relationship `operations/` has always had, and the only one that
            // could be derived from the documents alone.
            let target = within(&operations_dir, &format!("{stem}/{name}"));
            self.place(&mut plan, path, target, Filed::Operation)?;
        }

        Ok(plan)
    }

    /// Rename every document to its arranged name.
    ///
    /// Renames are applied in the order [`Store::arrangement`] gives them, and
    /// each target is looked at once more immediately before its file moves:
    /// planning and acting are two passes over a folder a person may be
    /// touching, and a name that filled in between them is a name arranging
    /// leaves alone rather than overwrites. The returned [`Arrangement`] is
    /// therefore what happened, not what was intended.
    pub fn arrange(&mut self, placement: Placement) -> Result<Arrangement, ArrangeError> {
        let planned = self.arrangement(placement)?;
        let mut done = Arrangement {
            already: planned.already,
            occupied: planned.occupied,
            unnamed: planned.unnamed,
            renames: Vec::new(),
        };

        for rename in planned.renames {
            let from = self.root.join(&rename.from);
            let to = self.root.join(&rename.to);

            if let Some(holder) = self.look(&to)? {
                done.occupied.push(Occupied {
                    path: rename.from,
                    holder,
                    filed: rename.filed,
                });
                continue;
            }
            if let Some(parent) = to.parent() {
                self.files
                    .create_directory(parent)
                    .map_err(|error| StoreError::io(parent, error))?;
            }
            self.files
                .rename(&from, &to)
                .map_err(|error| StoreError::io(&from, error))?;

            // Tidying the directories this file was the last thing in.
            // Upwards, because decision 0018 files a path as directories, so
            // emptying one can empty the one above it — and `remove_directory`
            // refuses a directory holding anything, which is the guard: a
            // directory a person put something else in survives, and so does
            // everything above it. Revisions are tidied on the same terms,
            // which matters only under [`Placement::Refiled`], the one mode
            // that empties a directory of them: a rename in place leaves the
            // file in the folder being offered, so the offer is refused. The
            // store's own directory is where it stops, so the month directory
            // this pass is filling is never a candidate.
            if let Some(parent) = from.parent() {
                self.tidy(parent, rename.filed.directory());
            }
            done.renames.push(rename);
        }

        // Names are presentation and identity is content, so no document has
        // changed and `self.documents` is still true. The payload index is
        // not: it maps digests to paths, and the paths have just moved.
        self.forget_catalogue();
        Ok(done)
    }

    /// Add one file's outcome to the plan.
    fn place(
        &self,
        plan: &mut Arrangement,
        path: PathBuf,
        target: PathBuf,
        filed: Filed,
    ) -> Result<(), ArrangeError> {
        if path == target {
            plan.already.push(Arranged {
                path: self.relative(&path),
                filed,
            });
            return Ok(());
        }
        if let Some(holder) = self.look(&target)? {
            plan.occupied.push(Occupied {
                path: self.relative(&path),
                holder,
                filed,
            });
            return Ok(());
        }
        plan.renames.push(Rename {
            from: self.relative(&path),
            to: self.relative(&target),
            filed,
        });
        Ok(())
    }

    /// Whether anything already holds this name, said relatively.
    fn look(&self, target: &Path) -> Result<Option<PathBuf>, ArrangeError> {
        let held = self
            .files
            .look(target)
            .map_err(|error| StoreError::io(target, error))?;
        Ok(held.map(|_| self.relative(target)))
    }

    /// Remove the directories a moved file emptied, upwards, until one refuses.
    ///
    /// Failure is the stop condition rather than an error: `remove_directory`
    /// refuses a directory that holds anything, and that refusal is the whole
    /// guard. `until` is the store directory the file belongs to, which is
    /// never removed however empty a pass leaves it.
    fn tidy(&self, from: &Path, until: &str) {
        let boundary = self.root.join(until);
        let mut empty = from;
        while empty != boundary && self.files.remove_directory(empty).is_ok() {
            match empty.parent() {
                Some(parent) => empty = parent,
                None => break,
            }
        }
    }

    /// What a file in the store hashes to, which is what it is.
    ///
    /// Decision 0043: taken in pieces, because arranging a folder full of
    /// photographs is a question about their names.
    fn digest_of(&self, path: &Path) -> Result<RevisionId, ArrangeError> {
        crate::fs::digest_of(&self.files, path).map_err(|error| StoreError::io(path, error).into())
    }

    /// Where everything in `operations/` belongs: a directory, and a path.
    ///
    /// Decision 0016. The directory is the revision's own arranged stem, so
    /// `revisions/2026-08/2026-08-20 Initial state.rev.txt` and
    /// `operations/2026-08/2026-08-20 Initial state/` are visibly the same
    /// thing — including decision 0041's month, which is part of the stem and
    /// so files both halves alike without either side being told about it.
    /// A revision document kept in a folder of somebody's own is the one case
    /// where the two part company, and the directory here still follows the
    /// stem: it has to be derivable from the documents alone, or two replicas
    /// that filed their revisions differently by hand would grow two
    /// `operations/` trees for one history.
    /// What is left to say is the path — which decision 0018 says as a path,
    /// in real directories, rather than spelling one into a filename. So a
    /// revision's folder is the subtree of the repository that revision
    /// touched, and `notes/photo.png` inside it opens as a picture from a
    /// folder called `notes`.
    ///
    /// Decision 0017 puts payloads in the same directory and gives them the
    /// same name without the `.ops.txt`, because a payload's name is the
    /// file's own. The extension is what tells a document from a payload, so
    /// it is part of the name a collision is decided on, and a document keeps
    /// it whatever else happens.
    ///
    /// The path is not in the revision document for an `edit`, so the tree at
    /// each revision has to be materialised to find it. That is real work, and
    /// it is affordable for one reason: `arrange` is a manual tidying command
    /// that nothing runs in a loop.
    ///
    /// `revisions` is which revisions may claim a document, which is the whole
    /// store for `arrange` and the ancestry that travels for
    /// [`Store::export_onto`]: a name decided by a revision the copy does not
    /// hold is a name the copy's own `arrange` would immediately disagree with.
    pub(super) fn operation_names<'a>(
        &'a self,
        stems: &BTreeMap<RevisionId, String>,
        revisions: impl IntoIterator<Item = (&'a RevisionId, &'a crate::format::RevisionDocument)>,
    ) -> Result<BTreeMap<RevisionId, (String, String)>, MaterialiseError> {
        // A document is one document however many files arrive at its content,
        // so the same digest can be claimed by several paths and several
        // revisions. It can only live in one directory, so one claim has to
        // win: the smallest revision digest, then the smallest path. Both
        // halves are content-derived, so two replicas choose alike, and
        // neither depends on what else is on disk. It is arbitrary from a
        // person's point of view — the winning revision need not be the one
        // where the content first appeared — and it is deterministic, which is
        // the property that matters.
        let mut claims: BTreeMap<RevisionId, (RevisionId, String, bool)> = BTreeMap::new();
        for (id, document) in revisions {
            if document.edited.is_empty() && document.text.is_empty() && document.bytes.is_empty() {
                continue;
            }
            let tree = self.merged_tree_of(&[*id])?.tree;
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
                // `added` covers the revision that brought the file into
                // being, where the tree has it too; between them a path is
                // always found.
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

        // Collisions are resolved inside a directory, because that is where
        // two names would actually meet. The rule is `naming`'s, so what
        // `arrange` produces on a store is what `record` would have written
        // into it.
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
}

/// The filename half of a stem, which is all a rename in place may use.
///
/// Decision 0041 made a stem two components — the month, then the name — and
/// [`Placement::Kept`] keeps the directory the file is in, so it takes the
/// second. The filename still carries the whole date, so a revision kept in a
/// folder of somebody's own says as much about itself as one in its month.
fn leaf(stem: &str) -> &str {
    match stem.rsplit_once('/') {
        Some((_, name)) => name,
        None => stem,
    }
}

/// Why nothing was arranged.
#[derive(Debug)]
#[non_exhaustive]
pub enum ArrangeError {
    /// A file changed between the store being opened and being arranged.
    Changed {
        /// The file whose bytes no revision in this store claims.
        file: PathBuf,
    },
    /// A revision's tree could not be materialised, so its paths are unknown.
    Materialise(Box<MaterialiseError>),
    /// The store could not be read or written.
    Store(StoreError),
}

impl From<MaterialiseError> for ArrangeError {
    fn from(error: MaterialiseError) -> Self {
        Self::Materialise(Box::new(error))
    }
}

impl From<StoreError> for ArrangeError {
    fn from(error: StoreError) -> Self {
        Self::Store(error)
    }
}

impl fmt::Display for ArrangeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ArrangeError::Changed { file } => {
                write!(f, "{} changed while it was being arranged", file.display())
            }
            ArrangeError::Materialise(error) => error.fmt(f),
            ArrangeError::Store(error) => error.fmt(f),
        }
    }
}

impl std::error::Error for ArrangeError {}
