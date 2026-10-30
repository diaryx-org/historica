//! Undoing one revision's work on top of everything recorded since: decision
//! 0090.
//!
//! Every other way back rewrites. `amend` and `abandon` supersede the tip,
//! `abandon --only` withdraws a revision from the middle and restates what
//! stood on it, and `squash` folds a run into one — each of them a statement
//! that the history should have said something else. A mistake found a week
//! later, with a week of work standing on it, wants the opposite statement:
//! the history said exactly what happened, and what happens *next* is that
//! the mistake is taken back. That is a new revision on the head, and nothing
//! that came before it changes.
//!
//! [`plan`] works out what that revision would hold, and hands it back as an
//! [`Update`] — the folder, made to hold the head with the one revision's
//! work taken out of it — so that [`crate::update::apply`] writes it under
//! the guards it already keeps, and `record` writes the revision from the
//! folder exactly as it writes any other. Nothing here writes to the store,
//! and nothing here mints, stamps, or reads a clock: the person who records
//! the result is the author of the undoing.
//!
//! The undoing itself is decision 0007's merge, run the way 0059's carry runs
//! it. For a file of lines, the content the revision left is the base; the
//! delta back to what its parent held is one side, the delta forward to what
//! the head holds is the other, and the two replay concurrently. Where they
//! touch one region — later work edited a line the mistake wrote — the plan
//! refuses that file and says so, because which of the two a person meant to
//! keep is not the tool's to guess.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

use crate::core::{FileId, RevisionId};
use crate::diff::diff;
use crate::format::{LinkTarget, Mode, OperationDocument, digest};
use crate::fs::Filesystem;
use crate::merge::{self, Event, MergeError};
use crate::record::{Fact, Kinds};
use crate::replay::State;
use crate::store::{MaterialiseError, Store, StoreError};
use crate::tree::{Entry, Kind, Tree};
use crate::update::{
    Chmod, Linking, Remove, Stood, Update, Write, Written, materialise, spell_reference,
};
use crate::working::{Working, WorkingError};

/// What undoing one revision would do to the folder, computed before anything
/// is done.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct Reversal {
    /// The revision whose work is being taken back.
    pub target: RevisionId,
    /// The head the undoing stands on, which the folder holds.
    pub head: RevisionId,
    /// The folder's part: what to write, remove, re-point and re-mode, for
    /// [`crate::update::apply`] to perform.
    pub update: Update,
    /// Every rename the undoing puts back, as (where the head has it, where
    /// it was before). The folder cannot show a rename, so `record` has to be
    /// told each of these with `--move`, or the file comes back as a new one.
    pub moves: Vec<(String, String)>,
    /// What the recorded revision will state, path by path, in path order —
    /// the same facts `record` prints.
    pub facts: Vec<(Fact, String)>,
    /// Every path the record should survey, in path order: what the undoing
    /// touches and nothing else, so unrecorded work elsewhere in the folder
    /// stays unrecorded (decision 0039).
    pub paths: Vec<String>,
    /// The kind of every file the undoing brings back, for `record` to be
    /// told rather than to sniff again (0017): a file the history decided was
    /// bytes comes back as bytes, whatever its bytes look like now.
    pub kinds: Kinds,
    /// Parts of the revision later work already took back or carried on
    /// from, with why each is left as the head has it. Not a refusal: there
    /// is nothing left there to undo.
    pub left: Vec<(String, String)>,
}

impl Reversal {
    /// Whether there is nothing to undo: everything the revision did, later
    /// work has already taken back.
    pub fn is_settled(&self) -> bool {
        self.update.is_settled()
    }
}

/// Why a revision's work could not be taken back.
#[derive(Debug)]
#[non_exhaustive]
pub enum RevertError {
    /// The store holds no such revision.
    Unknown {
        /// The revision named.
        target: RevisionId,
    },
    /// The revision is not behind the head, so the head holds none of its
    /// work to undo.
    NotBehind {
        /// The revision named.
        target: RevisionId,
        /// The head it is not behind.
        head: RevisionId,
    },
    /// The revision is a merge and no parent was named: undoing one means
    /// saying which side it joined to keep, and [`plan_against`] takes it.
    Merge {
        /// The merge named.
        target: RevisionId,
    },
    /// The side named to keep is not one of the revision's parents.
    NotAParent {
        /// The revision named.
        target: RevisionId,
        /// The side named, which it was not recorded on.
        parent: RevisionId,
    },
    /// Some files cannot be put back, so nothing was planned. Each is named
    /// with what stands in the way, in path order: the plan is all or
    /// nothing, as an update is.
    Refused {
        /// Every path in the way, with the reason.
        paths: Vec<(String, String)>,
    },
    /// The concurrent replay refused, which means the store contradicts
    /// itself rather than that the work met.
    Merging(MergeError),
    /// A tree or a file's content could not be materialised.
    Materialise(Box<MaterialiseError>),
    /// The store could not be read.
    Store(StoreError),
    /// The folder could not be read.
    Working(WorkingError),
}

impl fmt::Display for RevertError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RevertError::Unknown { target } => {
                write!(f, "this store holds no revision {}", target.abbreviate(12))
            }
            RevertError::NotBehind { target, head } => write!(
                f,
                "{} is not behind {}, so the head holds none of its work to undo",
                target.abbreviate(12),
                head.abbreviate(12)
            ),
            RevertError::Merge { target } => write!(
                f,
                "{} is a merge, so undoing it means naming the side it joined \
                 to keep: the work that came in from the others is what is taken back",
                target.abbreviate(12)
            ),
            RevertError::NotAParent { target, parent } => write!(
                f,
                "{} is not a parent of {}, so there is no side of it to keep",
                parent.abbreviate(12),
                target.abbreviate(12)
            ),
            RevertError::Refused { paths } => {
                write!(f, "this cannot be undone whole, so nothing was written:")?;
                for (path, because) in paths {
                    write!(f, "\n  {path}: {because}")?;
                }
                Ok(())
            }
            RevertError::Merging(error) => error.fmt(f),
            RevertError::Materialise(error) => error.fmt(f),
            RevertError::Store(error) => error.fmt(f),
            RevertError::Working(error) => error.fmt(f),
        }
    }
}

impl std::error::Error for RevertError {}

impl From<MaterialiseError> for RevertError {
    fn from(error: MaterialiseError) -> Self {
        RevertError::Materialise(Box::new(error))
    }
}

impl From<StoreError> for RevertError {
    fn from(error: StoreError) -> Self {
        RevertError::Store(error)
    }
}

impl From<WorkingError> for RevertError {
    fn from(error: WorkingError) -> Self {
        RevertError::Working(error)
    }
}

/// What one file holds, whichever kind of file it is — the thing three
/// readings of a file are compared by.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Held {
    Lines(State),
    Whole(Option<RevisionId>),
    Link(Option<LinkTarget>),
}

impl Held {
    fn digest(&self) -> Option<RevisionId> {
        match self {
            Held::Lines(state) => Some(state.digest()),
            Held::Whole(payload) => *payload,
            Held::Link(_) => None,
        }
    }

    /// The kind `record` should be told a restored file is, so the sniff
    /// does not decide again what the file was decided to be when it was
    /// added (0017). A link is what the filesystem says it is, and is never
    /// stated.
    fn kind(&self) -> Option<Kind> {
        match self {
            Held::Lines(_) => Some(Kind::Lines),
            Held::Whole(_) => Some(Kind::Whole),
            Held::Link(_) => None,
        }
    }
}

/// Undo `target` on top of `head`, as the folder beside `store` would have to
/// hold it.
///
/// The folder has to hold what the head records at every path the undoing
/// touches — bytes and mode, or where a link points — and nothing at a path
/// it brings a file back to: what is there otherwise is somebody's
/// unrecorded work, and the plan refuses rather than writing over it. Paths
/// it does not touch are not looked at, except a link that names a file the
/// undoing moves, which is re-pointed so that it still names that file.
///
/// A merge is refused here; [`plan_against`] undoes one against a side.
pub fn plan<F: Filesystem, G: Filesystem>(
    store: &Store<F>,
    working: &Working<G>,
    target: &RevisionId,
    head: &RevisionId,
) -> Result<Reversal, RevertError> {
    plan_against(store, working, target, None, head)
}

/// Undo `target` on top of `head` against one of its parents, `mainline`:
/// what the folder holds afterwards is the head with everything `target`
/// changed relative to that parent changed back.
///
/// For a revision with one parent, naming it is the same as [`plan`]. For a
/// merge it is the only way to undo one: the side named is the one kept, and
/// the work the merge brought in from its other parents — an accepted
/// change set, a colleague's line of work — is what is taken back, in one
/// undoing, under the same rules as any other. A parent the revision does
/// not have is refused.
pub fn plan_against<F: Filesystem, G: Filesystem>(
    store: &Store<F>,
    working: &Working<G>,
    target: &RevisionId,
    mainline: Option<&RevisionId>,
    head: &RevisionId,
) -> Result<Reversal, RevertError> {
    let document = store
        .get(target)?
        .ok_or(RevertError::Unknown { target: *target })?
        .clone();
    if let Some(mainline) = mainline
        && !document.parents.contains(mainline)
    {
        return Err(RevertError::NotAParent {
            target: *target,
            parent: *mainline,
        });
    }
    let merge = document.parents.len() > 1;
    if merge && mainline.is_none() {
        return Err(RevertError::Merge { target: *target });
    }
    if !store
        .reachable_from(&[*head])?
        .iter()
        .any(|(id, _)| id == target)
    {
        return Err(RevertError::NotBehind {
            target: *target,
            head: *head,
        });
    }
    let parent = mainline
        .copied()
        .or_else(|| document.parents.iter().next().copied());

    let before = match &parent {
        Some(parent) => store.tree(parent)?,
        None => Tree::empty(),
    };
    let after = store.tree(target)?;
    let now = store.tree(head)?;

    // Everything the revision said it did, which is every file it touched.
    // A merge's document states only what joining needed — what came in from
    // the other sides was stated by the revisions on them — so for a merge
    // the files are the ones its tree holds differently from the side kept.
    let touched: BTreeSet<FileId> = if merge {
        let parent = parent.expect("a merge has parents");
        differing(store, &parent, &before, target, &after)?
    } else {
        document
            .added
            .keys()
            .chain(document.moved.keys())
            .chain(document.modes.keys())
            .chain(&document.dropped)
            .chain(document.edited.keys())
            .chain(document.text.keys())
            .chain(document.bytes.keys())
            .chain(document.links.keys())
            .copied()
            .collect()
    };

    let mut planned = Planned {
        reversal: Reversal {
            target: *target,
            head: *head,
            update: Update::default(),
            moves: Vec::new(),
            facts: Vec::new(),
            paths: Vec::new(),
            kinds: Kinds::default(),
            left: Vec::new(),
        },
        refused: Vec::new(),
        placed: BTreeMap::new(),
        links: Vec::new(),
    };
    let sides = Sides {
        store,
        working,
        target: *target,
        parent,
        head: *head,
        before: &before,
        after: &after,
        now: &now,
    };

    for file in &touched {
        match (before.entry(file), after.entry(file)) {
            (None, None) => {}
            (None, Some(added)) => sides.unadd(file, added, &mut planned)?,
            (Some(dropped), None) => sides.undrop(file, dropped, &mut planned)?,
            (Some(was), Some(became)) => sides.unedit(file, was, became, &mut planned)?,
        }
    }
    sides.point(&mut planned)?;

    let Planned {
        mut reversal,
        mut refused,
        ..
    } = planned;
    if !refused.is_empty() {
        refused.sort();
        refused.dedup();
        return Err(RevertError::Refused { paths: refused });
    }

    let update = &mut reversal.update;
    update.writes.sort_by(|a, b| a.path.cmp(&b.path));
    update.removes.sort_by(|a, b| a.path.cmp(&b.path));
    update.modes.sort_by(|a, b| a.path.cmp(&b.path));
    update.links.sort_by(|a, b| a.path.cmp(&b.path));
    reversal.moves.sort();
    reversal
        .facts
        .sort_by(|a, b| a.1.cmp(&b.1).then(a.0.cmp(&b.0)));
    reversal.left.sort();
    reversal.paths.sort();
    reversal.paths.dedup();
    Ok(reversal)
}

/// Every file two trees hold differently: added or dropped between them, or
/// held at another path, kind, payload, mode or target, or holding other
/// lines.
fn differing<F: Filesystem>(
    store: &Store<F>,
    from: &RevisionId,
    before: &Tree,
    to: &RevisionId,
    after: &Tree,
) -> Result<BTreeSet<FileId>, RevertError> {
    let mut files = BTreeSet::new();
    for (file, entry) in before.entries() {
        match after.entry(file) {
            None => {
                files.insert(*file);
            }
            Some(other) if other != entry => {
                files.insert(*file);
            }
            Some(_) if entry.kind == Kind::Lines => {
                if store.content(from, file)?.digest() != store.content(to, file)?.digest() {
                    files.insert(*file);
                }
            }
            Some(_) => {}
        }
    }
    for (file, _) in after.entries() {
        if before.entry(file).is_none() {
            files.insert(*file);
        }
    }
    Ok(files)
}

/// A reversal while it is being worked out.
struct Planned {
    reversal: Reversal,
    /// Every path in the way, with the reason.
    refused: Vec<(String, String)>,
    /// Where the undoing leaves each file it puts somewhere else than the
    /// head has it: a path, or nowhere for a file it removes.
    placed: BTreeMap<FileId, Option<String>>,
    /// The links the undoing lays down, held back until every file has a
    /// place, since a `file:` target is spelled against where its file ends
    /// up rather than where the head has it.
    links: Vec<Pointing>,
}

/// A link to lay down once every file has its final path.
struct Pointing {
    file: FileId,
    path: String,
    target: LinkTarget,
    replaces: Stood,
}

/// The three readings a reversal compares, and the folder it plans for.
struct Sides<'a, F: Filesystem, G: Filesystem> {
    store: &'a Store<F>,
    working: &'a Working<G>,
    target: RevisionId,
    parent: Option<RevisionId>,
    head: RevisionId,
    /// The tree the revision was recorded against.
    before: &'a Tree,
    /// The tree it left.
    after: &'a Tree,
    /// The tree at the head.
    now: &'a Tree,
}

impl<F: Filesystem, G: Filesystem> Sides<'_, F, G> {
    /// What one file holds at one revision, given that revision's tree.
    fn held(&self, tree: &Tree, at: &RevisionId, file: &FileId) -> Result<Held, RevertError> {
        let entry = tree
            .entry(file)
            .expect("asked only of a tree holding the file");
        Ok(match entry.kind {
            Kind::Lines => Held::Lines(self.store.content(at, file)?),
            Kind::Whole => Held::Whole(entry.payload),
            Kind::Link => Held::Link(entry.target.clone()),
        })
    }

    fn at_parent(&self, file: &FileId) -> Result<Held, RevertError> {
        let parent = self
            .parent
            .expect("a file the parent holds has a parent to hold it");
        self.held(self.before, &parent, file)
    }

    fn at_target(&self, file: &FileId) -> Result<Held, RevertError> {
        self.held(self.after, &self.target, file)
    }

    fn at_head(&self, file: &FileId) -> Result<Held, RevertError> {
        self.held(self.now, &self.head, file)
    }

    /// Whether the folder holds exactly what the head records at `path` —
    /// its bytes and its mode, or where it points — which is the only thing
    /// the undoing may write over or take away.
    ///
    /// The mode is asked where the folder can say one, as `status` asks it
    /// (0034): a `chmod` nobody recorded is unrecorded work too.
    fn folder_holds(&self, path: &str, held: &Held, mode: Mode) -> Result<bool, RevertError> {
        if let Held::Link(target) = held {
            let wanted = target
                .as_ref()
                .and_then(|target| materialise(self.now, path, target));
            return Ok(self.working.is_link(path)
                && wanted.is_some()
                && self.working.link_target(path) == wanted.as_deref());
        }
        if !self.working.holds(path) || self.working.is_link(path) {
            return Ok(false);
        }
        if Some(self.working.digest(path)?) != held.digest() {
            return Ok(false);
        }
        Ok(match self.working.executable(path)? {
            Some(executable) => Mode::of(executable) == mode,
            None => true,
        })
    }

    /// Whether the folder holds anything at all at `path`, where the undoing
    /// would bring a file back.
    fn folder_occupied(&self, path: &str) -> bool {
        self.working.holds(path) || self.working.is_link(path)
    }

    /// The reason a path the undoing would write over or remove cannot be.
    fn not_the_head(path: &str) -> (String, String) {
        (
            path.to_owned(),
            "the folder does not hold what the head records here; record it or set \
             it aside first"
                .to_owned(),
        )
    }

    /// A file the revision added: it goes, if nothing since has changed it.
    fn unadd(
        &self,
        file: &FileId,
        added: &Entry,
        planned: &mut Planned,
    ) -> Result<(), RevertError> {
        let Some(now) = self.now.entry(file) else {
            planned
                .reversal
                .left
                .push((added.path.clone(), "dropped since".to_owned()));
            return Ok(());
        };
        let then = self.at_target(file)?;
        let held = self.at_head(file)?;
        if then != held || now.mode != added.mode {
            planned.refused.push((
                now.path.clone(),
                "changed since it was added, and taking it away would take that work \
                 too; drop it with `record` if that is what you mean"
                    .to_owned(),
            ));
            return Ok(());
        }
        if !self.folder_holds(&now.path, &held, now.mode)? {
            planned.refused.push(Self::not_the_head(&now.path));
            return Ok(());
        }
        planned
            .reversal
            .update
            .removes
            .push(self.removing(&now.path, &held)?);
        planned.placed.insert(*file, None);
        planned
            .reversal
            .facts
            .push((Fact::Dropped, now.path.clone()));
        planned.reversal.paths.push(now.path.clone());
        Ok(())
    }

    /// A file the revision dropped: it comes back where it was, as its parent
    /// held it, and as the kind it was.
    fn undrop(
        &self,
        file: &FileId,
        dropped: &Entry,
        planned: &mut Planned,
    ) -> Result<(), RevertError> {
        if let Some(now) = self.now.entry(file) {
            planned
                .reversal
                .left
                .push((now.path.clone(), "back since".to_owned()));
            return Ok(());
        }
        let path = &dropped.path;
        if !self.now.at(path).is_empty() {
            planned.refused.push((
                path.clone(),
                "another file holds this path now; move it, then undo".to_owned(),
            ));
            return Ok(());
        }
        if self.folder_occupied(path) {
            planned.refused.push((
                path.clone(),
                "the folder holds a file here that nothing has recorded".to_owned(),
            ));
            return Ok(());
        }
        let held = self.at_parent(file)?;
        if !self.lay(*file, path, &held, None, dropped.mode, planned)? {
            return Ok(());
        }
        if let Some(kind) = held.kind() {
            planned.reversal.kinds.state(path, kind);
        }
        planned.placed.insert(*file, Some(path.clone()));
        planned.reversal.facts.push((Fact::Added, path.clone()));
        planned.reversal.paths.push(path.clone());
        Ok(())
    }

    /// A file the revision edited, moved, re-moded or re-pointed: each of
    /// those it did is undone where the head still holds what it left.
    fn unedit(
        &self,
        file: &FileId,
        was: &Entry,
        became: &Entry,
        planned: &mut Planned,
    ) -> Result<(), RevertError> {
        let Some(now) = self.now.entry(file) else {
            planned
                .reversal
                .left
                .push((became.path.clone(), "dropped since".to_owned()));
            return Ok(());
        };
        let refused_before = planned.refused.len();

        // Where it goes back to.
        let mut destination = now.path.clone();
        if was.path != became.path {
            if now.path != became.path {
                planned.reversal.left.push((
                    now.path.clone(),
                    format!("moved again since {}", became.path),
                ));
            } else if !self.now.at(&was.path).is_empty() {
                planned.refused.push((
                    was.path.clone(),
                    format!(
                        "another file holds this path now, so {} cannot move back to it",
                        now.path
                    ),
                ));
            } else if self.folder_occupied(&was.path) {
                planned.refused.push((
                    was.path.clone(),
                    "the folder holds a file here that nothing has recorded".to_owned(),
                ));
            } else {
                destination = was.path.clone();
            }
        }

        // What it holds there.
        let then = self.at_parent(file)?;
        let left = self.at_target(file)?;
        let held = self.at_head(file)?;
        let content = if then == left || then == held {
            // The revision did not touch the content, or later work already
            // put it back.
            None
        } else if held == left {
            Some(then)
        } else {
            match (&then, &left, &held) {
                (Held::Lines(then), Held::Lines(left), Held::Lines(held)) => {
                    match self.three_way(then, left, held) {
                        // Later work already took the change back by other
                        // means, so there is nothing of it left here.
                        Ok(state) if state == *held => None,
                        Ok(state) => Some(Held::Lines(state)),
                        Err(because) => {
                            planned.refused.push((now.path.clone(), because));
                            None
                        }
                    }
                }
                (Held::Whole(_), _, _) => {
                    planned.refused.push((
                        now.path.clone(),
                        "its bytes were replaced again since, and there is no line in a \
                         file of bytes to undo one change by; put back the version you \
                         want by hand"
                            .to_owned(),
                    ));
                    None
                }
                _ => {
                    planned.refused.push((
                        now.path.clone(),
                        "this link was pointed somewhere else again since; point it by hand"
                            .to_owned(),
                    ));
                    None
                }
            }
        };

        // How it may be run.
        let mut mode = now.mode;
        if was.mode != became.mode {
            if now.mode == became.mode {
                mode = was.mode;
            } else {
                planned
                    .reversal
                    .left
                    .push((now.path.clone(), format!("made {} again since", now.mode)));
            }
        }

        if planned.refused.len() > refused_before {
            return Ok(());
        }
        let moving = destination != now.path;
        if !moving && content.is_none() && mode == now.mode {
            return Ok(());
        }
        if !self.folder_holds(&now.path, &held, now.mode)? {
            planned.refused.push(Self::not_the_head(&now.path));
            return Ok(());
        }

        if moving {
            planned
                .reversal
                .update
                .removes
                .push(self.removing(&now.path, &held)?);
            let laid = content.as_ref().unwrap_or(&held);
            if !self.lay(*file, &destination, laid, None, mode, planned)? {
                return Ok(());
            }
            planned.placed.insert(*file, Some(destination.clone()));
            planned
                .reversal
                .moves
                .push((now.path.clone(), destination.clone()));
            planned
                .reversal
                .facts
                .push((Fact::Moved, destination.clone()));
            planned.reversal.paths.push(now.path.clone());
        } else if let Some(content) = &content {
            if !self.lay(*file, &now.path, content, Some(&held), mode, planned)? {
                return Ok(());
            }
        } else {
            planned.reversal.update.modes.push(Chmod {
                path: now.path.clone(),
                mode,
            });
        }
        if let Some(content) = &content {
            let fact = match content {
                Held::Link(_) => Fact::Link,
                _ => Fact::Edited,
            };
            planned.reversal.facts.push((fact, destination.clone()));
        }
        if mode != now.mode {
            planned
                .reversal
                .facts
                .push((Fact::Mode, destination.clone()));
        }
        planned.reversal.paths.push(destination);
        Ok(())
    }

    /// Every link the undoing lays down, and every link at the head naming a
    /// file the undoing moves, pointed at where its file ends up.
    ///
    /// Decision 0040 spells a `file:` target relative to the link, from the
    /// file's current path, so moving a file back changes how every link to
    /// it is spelled — and a folder left with the old spelling would hold a
    /// link naming nowhere, which the next `record` would state.
    fn point(&self, planned: &mut Planned) -> Result<(), RevertError> {
        let ends = |file: &FileId, placed: &BTreeMap<FileId, Option<String>>| match placed.get(file)
        {
            Some(path) => path.clone(),
            None => self.now.path(file).map(str::to_owned),
        };
        let spell =
            |at: &str, target: &LinkTarget, placed: &BTreeMap<FileId, Option<String>>| match target
            {
                LinkTarget::Verbatim(spelling) => Some(spelling.clone()),
                LinkTarget::Reference(named) => {
                    ends(named, placed).map(|to| spell_reference(at, &to))
                }
            };

        let laying = std::mem::take(&mut planned.links);
        let laid: BTreeSet<FileId> = laying.iter().map(|link| link.file).collect();
        for link in laying {
            let Some(target) = spell(&link.path, &link.target, &planned.placed) else {
                planned.refused.push((
                    link.path.clone(),
                    "the file this link pointed at would be gone, so it would name nowhere"
                        .to_owned(),
                ));
                continue;
            };
            planned.reversal.update.links.push(Linking {
                path: link.path,
                target,
                replaces: link.replaces,
            });
        }

        // A link the undoing did not otherwise touch, naming a file it moves
        // or removes.
        for (file, entry) in self.now.entries() {
            if entry.kind != Kind::Link || laid.contains(file) || planned.placed.contains_key(file)
            {
                continue;
            }
            let Some(target @ LinkTarget::Reference(named)) = &entry.target else {
                continue;
            };
            if !planned.placed.contains_key(named) {
                continue;
            }
            let Some(spelled) = spell(&entry.path, target, &planned.placed) else {
                planned.refused.push((
                    entry.path.clone(),
                    "this link points at a file the undoing removes; point it elsewhere \
                     or drop it first"
                        .to_owned(),
                ));
                continue;
            };
            let held = Held::Link(entry.target.clone());
            let standing = materialise(self.now, &entry.path, target);
            if standing.as_deref() == Some(spelled.as_str()) {
                continue;
            }
            if !self.folder_holds(&entry.path, &held, entry.mode)? {
                planned.refused.push(Self::not_the_head(&entry.path));
                continue;
            }
            planned.reversal.update.links.push(Linking {
                path: entry.path.clone(),
                target: spelled,
                replaces: Stood::Link(standing.unwrap_or_default()),
            });
            planned.reversal.paths.push(entry.path.clone());
        }
        Ok(())
    }

    /// The revision's change to one file of lines, taken back out of what the
    /// head holds: decision 0007's merge, with what the revision left as the
    /// base, the way back to its parent as one side and the way on to the
    /// head as the other.
    fn three_way(&self, then: &State, left: &State, held: &State) -> Result<State, String> {
        let forgotten = [then, left, held]
            .iter()
            .any(|state| state.items().iter().any(|item| item.forgotten));
        if forgotten {
            // Decision 0014: recording the marker's text as content would
            // launder a redaction into authority, as it would in a carry.
            return Err("it holds lines `forget` destroyed, which cannot be restated".to_owned());
        }
        let parent = self
            .parent
            .expect("a file the parent holds has a parent to hold it");
        let creation = crate::replay::creation(&left.text());
        let back = diff(left, then).expect("the two differ, or nothing would be undone");
        let on = diff(left, held).expect("the two differ, or the head would hold the base");
        // What the head has already taken back is not taken back again. Both
        // documents count positions in the target's content, so an operation
        // the two share is the same edit, and replaying it on both sides would
        // read as two concurrent inserts rather than one agreed one.
        let back = OperationDocument {
            forgets: None,
            result: None,
            operations: back
                .operations
                .into_iter()
                .filter(|operation| !on.operations.contains(operation))
                .collect(),
        };
        if back.operations.is_empty() {
            return Ok(held.clone());
        }
        let mut events: Vec<Event<'_>> = Vec::new();
        match &creation {
            Some(document) => events.push(Event::operations(
                self.target,
                Vec::new(),
                digest(&document.write()),
                document,
            )),
            None => events.push(Event::nothing(self.target, Vec::new())),
        }
        events.push(Event::operations(
            parent,
            vec![self.target],
            digest(&back.write()),
            &back,
        ));
        events.push(Event::operations(
            self.head,
            vec![self.target],
            digest(&on.write()),
            &on,
        ));
        let merged = merge::merge(events).map_err(|error| error.to_string())?;
        if !merged.contested.is_empty() {
            return Err(
                "later work changed lines this revision wrote, and which of the two \
                 to keep is a person's to say; undo it here by hand"
                    .to_owned(),
            );
        }
        Ok(merged.state)
    }

    /// Taking the head's file away from `path`, guarded by what it holds.
    fn removing(&self, path: &str, held: &Held) -> Result<Remove, RevertError> {
        Ok(match held {
            Held::Link(_) => Remove {
                path: path.to_owned(),
                held: None,
                link: self.working.link_target(path).map(str::to_owned),
            },
            _ => Remove {
                path: path.to_owned(),
                held: Some(self.working.digest(path)?),
                link: None,
            },
        })
    }

    /// Putting `content` at `path`, over what the head holds there where
    /// `replacing` says so and onto nothing otherwise. A link is held back
    /// for [`Sides::point`]. Whether anything was planned: where not, the
    /// path is refused with the reason.
    fn lay(
        &self,
        file: FileId,
        path: &str,
        content: &Held,
        replacing: Option<&Held>,
        mode: Mode,
        planned: &mut Planned,
    ) -> Result<bool, RevertError> {
        match content {
            Held::Lines(state) => planned.reversal.update.writes.push(Write {
                path: path.to_owned(),
                content: Written::Lines {
                    bytes: state.text().into_bytes(),
                    replaces: match replacing {
                        Some(_) => Some(self.working.bytes(path)?),
                        None => None,
                    },
                },
                mode,
            }),
            Held::Whole(None) => {
                planned.refused.push((
                    path.to_owned(),
                    "concurrent work left two versions of its bytes; merge first".to_owned(),
                ));
                return Ok(false);
            }
            Held::Whole(Some(payload)) => {
                if !self.store.holds_payload(payload)? {
                    planned.refused.push((
                        path.to_owned(),
                        format!(
                            "this store does not hold the bytes it goes back to ({}); \
                             `fetch` brings them",
                            payload.abbreviate(12)
                        ),
                    ));
                    return Ok(false);
                }
                planned.reversal.update.writes.push(Write {
                    path: path.to_owned(),
                    content: Written::Whole {
                        payload: *payload,
                        replaces: match replacing {
                            Some(_) => Some(self.working.digest(path)?),
                            None => None,
                        },
                    },
                    mode,
                });
            }
            Held::Link(None) => {
                planned.refused.push((
                    path.to_owned(),
                    "concurrent work left this link two targets; merge first".to_owned(),
                ));
                return Ok(false);
            }
            Held::Link(Some(target)) => planned.links.push(Pointing {
                file,
                path: path.to_owned(),
                target: target.clone(),
                replaces: match replacing {
                    Some(_) => Stood::Link(
                        self.working
                            .link_target(path)
                            .unwrap_or_default()
                            .to_owned(),
                    ),
                    None => Stood::Nothing,
                },
            }),
        }
        Ok(true)
    }
}
