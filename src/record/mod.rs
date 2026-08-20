//! Recording a revision: what a writer supplies, and what it is given.
//!
//! Decisions 0010 and 0011 between them: the three facts nothing can derive —
//! a change ID, an author, a time — and the folder they are recorded about.
//! Everything else in a revision falls out of comparing the working copy with
//! the tree at its parent.
//!
//! What this does not do is what 0011 says it does not: no amend, no merge,
//! and nothing where the parent's ancestry holds one, because restating
//! operations against a changed parent is 0007's merge under another name.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

use crate::core::{ChangeId, FileId, RevisionId};
use crate::diff::diff;
use crate::format::{OperationDocument, RevisionDocument, Timestamp};
use crate::replay::State;
use crate::store::{MaterialiseError, Name, Store, StoreError};
use crate::tree::Tree;
use crate::working::{Working, WorkingError};

pub mod identity;
pub mod source;

pub use identity::{Identities, IdentityError, author_for};
pub use source::{Clock, Entropy, Platform, SourceError};

/// What one file's state on disk means for the file set.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Fact {
    /// A file the tree does not hold yet.
    Added,
    /// A file whose path changed, which only a person can say.
    Moved,
    /// A file the tree holds and the folder does not.
    Dropped,
    /// A file whose content differs from the parent's.
    Edited,
}

impl fmt::Display for Fact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // `f.pad` rather than `write_str`, so a column of these lines up.
        f.pad(match self {
            Fact::Added => "added",
            Fact::Moved => "moved",
            Fact::Dropped => "dropped",
            Fact::Edited => "edited",
        })
    }
}

/// What recording would do, before anything is written.
///
/// `--dry-run` prints this. Recording produces it and then acts on it, so the
/// two can never describe different work.
#[derive(Debug, Clone, Default)]
pub struct Plan {
    /// Files entering the tree, with the path they enter at.
    pub added: BTreeMap<FileId, String>,
    /// Files whose path changed, with the path they moved to.
    pub moved: BTreeMap<FileId, String>,
    /// Files leaving the file set.
    pub dropped: BTreeSet<FileId>,
    /// What each edited file's revision did to it.
    pub edited: BTreeMap<FileId, OperationDocument>,
    /// Where each file sits after this revision, for rendering.
    pub paths: BTreeMap<FileId, String>,
    /// The revision this would be recorded against.
    pub parent: Option<RevisionId>,
}

impl Plan {
    /// Whether this would state nothing at all.
    pub fn is_empty(&self) -> bool {
        self.added.is_empty()
            && self.moved.is_empty()
            && self.dropped.is_empty()
            && self.edited.is_empty()
    }

    /// Every fact, by the path it concerns, for a person reading.
    pub fn facts(&self) -> Vec<(Fact, String)> {
        let named = |file: &FileId| {
            self.paths
                .get(file)
                .cloned()
                .unwrap_or_else(|| file.to_string())
        };
        let mut facts: Vec<(Fact, String)> = Vec::new();
        facts.extend(self.added.values().map(|path| (Fact::Added, path.clone())));
        facts.extend(self.moved.values().map(|path| (Fact::Moved, path.clone())));
        facts.extend(self.dropped.iter().map(|file| (Fact::Dropped, named(file))));
        facts.extend(
            self.edited
                .keys()
                .filter(|file| !self.added.contains_key(*file))
                .map(|file| (Fact::Edited, named(file))),
        );
        facts.sort();
        facts
    }
}

/// What a person supplies, beside the folder itself.
#[derive(Debug, Clone)]
pub struct Recording {
    /// The revision to record against, or `None` for a root.
    pub onto: Option<RevisionId>,
    /// Who is recording, per decision 0010.
    pub author: String,
    /// When, per decision 0010.
    pub when: Timestamp,
    /// The message, verbatim, which may be empty.
    pub message: String,
    /// Renames, as `(from, to)`. The one fact that cannot be observed.
    pub moves: Vec<(String, String)>,
}

/// What was recorded.
#[derive(Debug, Clone)]
pub struct Recorded {
    /// The revision written.
    pub revision: RevisionId,
    /// Its change, newly minted.
    pub change: ChangeId,
    /// What it did.
    pub plan: Plan,
    /// Bookmarks that followed the work forward.
    pub advanced: Vec<String>,
}

/// Work out what recording would state, without writing anything.
pub fn plan(
    store: &Store,
    working: &Working,
    onto: Option<RevisionId>,
    moves: &[(String, String)],
    entropy: &mut impl Entropy,
) -> Result<Plan, RecordError> {
    let tree = match onto {
        Some(parent) => store.tree(&parent)?,
        None => Tree::empty(),
    };

    // Where each file the tree holds sits after the renames a person stated.
    let mut placed: BTreeMap<FileId, String> = tree
        .files()
        .map(|(file, path)| (*file, path.to_owned()))
        .collect();
    let mut moved = BTreeMap::new();
    for (from, to) in moves {
        let file = one_file_at(&tree, from)?;
        crate::format::check_path(to).map_err(|because| RecordError::UnusablePath {
            path: to.clone(),
            because: because.to_string(),
        })?;
        placed.insert(file, to.clone());
        moved.insert(file, to.clone());
    }

    let held: BTreeMap<&str, FileId> = placed
        .iter()
        .map(|(file, path)| (path.as_str(), *file))
        .collect();

    let mut plan = Plan {
        moved,
        parent: onto,
        ..Plan::default()
    };

    // A path in the folder is either a file the tree already holds, or a file
    // nobody has recorded yet, which mints an identifier as 0010 mints one.
    for (path, _) in working.iter() {
        let file = match held.get(path.as_str()) {
            Some(file) => *file,
            None => {
                let file = entropy.file()?;
                plan.added.insert(file, path.clone());
                file
            }
        };
        plan.paths.insert(file, path.clone());

        let before = match (onto, plan.added.contains_key(&file)) {
            (Some(parent), false) => store.content(&parent, &file)?,
            _ => State::empty(),
        };
        let after = State::from_text(&working.text(path)?);
        if let Some(document) = diff(&before, &after) {
            plan.edited.insert(file, document);
        }
    }

    // A file the tree holds and the folder does not is gone, which is a fact
    // rather than a guess — decision 0011's reason for having no `--drop`.
    for (file, path) in &placed {
        if !working.holds(path) {
            plan.dropped.insert(*file);
            plan.paths.insert(*file, path.clone());
            plan.moved.remove(file);
        }
    }

    Ok(plan)
}

/// Record a revision, writing the documents it names before the revision.
///
/// An interrupted record therefore leaves operation documents nothing points
/// at, which `check` reports as a note, rather than a revision naming a
/// document that is not there, which it reports as an error.
pub fn record(
    store: &mut Store,
    working: &Working,
    recording: &Recording,
    entropy: &mut impl Entropy,
) -> Result<Recorded, RecordError> {
    let plan = plan(store, working, recording.onto, &recording.moves, entropy)?;
    if plan.is_empty() {
        return Err(RecordError::NothingToRecord);
    }

    let mut edited = BTreeMap::new();
    for (file, document) in &plan.edited {
        edited.insert(*file, store.insert_operation(document)?);
    }

    let change = entropy.change()?;
    let document = RevisionDocument {
        change,
        parents: recording.onto.into_iter().collect(),
        supersedes: BTreeSet::new(),
        author: recording.author.clone(),
        when: recording.when.clone(),
        revised_by: None,
        revised: None,
        added: plan.added.clone(),
        moved: plan.moved.clone(),
        dropped: plan.dropped.clone(),
        edited,
        extensions: BTreeMap::new(),
        message: recording.message.clone(),
    };
    let revision = store.insert(&document)?;

    // Decision 0011: a bookmark that named the parent's change follows the
    // work forward. A `revision` bookmark is the pin that must not move.
    let mut advanced = Vec::new();
    if let Some(parent) = recording.onto
        && let Some(before) = store.get(&parent).map(|document| document.change)
    {
        let following: Vec<String> = store
            .names()
            .iter()
            .filter(|(_, target)| **target == Name::Change(before))
            .map(|(name, _)| name.clone())
            .collect();
        for name in following {
            store.set_name(&name, Name::Change(change))?;
            advanced.push(name);
        }
    }

    Ok(Recorded {
        revision,
        change,
        plan,
        advanced,
    })
}

/// The one file at `path`, or a reason there is not exactly one.
fn one_file_at(tree: &Tree, path: &str) -> Result<FileId, RecordError> {
    match tree.at(path).as_slice() {
        [] => Err(RecordError::NotInTheTree {
            path: path.to_owned(),
        }),
        [only] => Ok(*only),
        several => Err(RecordError::Contested {
            path: path.to_owned(),
            files: several.to_vec(),
        }),
    }
}

/// Why nothing was recorded.
#[derive(Debug)]
#[non_exhaustive]
pub enum RecordError {
    /// Nothing about the folder differs from the parent.
    NothingToRecord,
    /// A `--move` naming a path the tree does not hold.
    NotInTheTree {
        /// The path as given.
        path: String,
    },
    /// A path two files claim, which only a person can settle.
    Contested {
        /// The path.
        path: String,
        /// The files claiming it.
        files: Vec<FileId>,
    },
    /// A path the format cannot hold.
    UnusablePath {
        /// The path.
        path: String,
        /// Why not.
        because: String,
    },
    /// The parent's tree or content could not be produced.
    ///
    /// Boxed because it is much the largest thing that can go wrong here, and
    /// every other caller pays for it in every `Ok` otherwise.
    Materialise(Box<MaterialiseError>),
    /// The working copy could not be read.
    Working(WorkingError),
    /// The store could not be written.
    Store(StoreError),
    /// The clock or the random source refused.
    Source(SourceError),
}

impl From<MaterialiseError> for RecordError {
    fn from(error: MaterialiseError) -> Self {
        Self::Materialise(Box::new(error))
    }
}

impl From<WorkingError> for RecordError {
    fn from(error: WorkingError) -> Self {
        Self::Working(error)
    }
}

impl From<StoreError> for RecordError {
    fn from(error: StoreError) -> Self {
        Self::Store(error)
    }
}

impl From<SourceError> for RecordError {
    fn from(error: SourceError) -> Self {
        Self::Source(error)
    }
}

impl fmt::Display for RecordError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RecordError::NothingToRecord => write!(
                f,
                "nothing here differs from what is already recorded, and a \
                 revision that states nothing would mean nothing"
            ),
            RecordError::NotInTheTree { path } => write!(
                f,
                "`{path}` is not a file this history holds, so nothing can be \
                 moved from it"
            ),
            RecordError::Contested { path, files } => write!(
                f,
                "{} files hold `{path}` here, so the path does not name one of \
                 them: {}",
                files.len(),
                files
                    .iter()
                    .map(FileId::to_string)
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            RecordError::UnusablePath { path, because } => {
                write!(f, "`{path}` cannot be a path here: {because}")
            }
            RecordError::Materialise(error) => error.fmt(f),
            RecordError::Working(error) => error.fmt(f),
            RecordError::Store(error) => error.fmt(f),
            RecordError::Source(error) => error.fmt(f),
        }
    }
}

impl std::error::Error for RecordError {}
