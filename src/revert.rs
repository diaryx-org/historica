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

use std::collections::BTreeSet;
use std::fmt;

use crate::core::{FileId, RevisionId};
use crate::diff::diff;
use crate::format::{LinkTarget, Mode, digest};
use crate::fs::Filesystem;
use crate::merge::{self, Event, MergeError};
use crate::record::Fact;
use crate::replay::State;
use crate::store::{MaterialiseError, Store, StoreError};
use crate::tree::{Entry, Kind, Tree};
use crate::update::{Chmod, Linking, Remove, Stood, Update, Write, Written, materialise};
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
    /// The revision is a merge, and undoing one means choosing which side it
    /// joined to keep — which is a different question from undoing work.
    Merge {
        /// The merge named.
        target: RevisionId,
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
                "{} is a merge, and undoing one is choosing a side rather than \
                 taking work back; undo the revision on the side you meant to lose",
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
}

/// Undo `target` on top of `head`, as the folder beside `store` would have to
/// hold it.
///
/// The folder has to hold what the head records at every path the undoing
/// touches, and nothing at a path it brings a file back to: what is there
/// otherwise is somebody's unrecorded work, and the plan refuses rather than
/// writing over it. Paths it does not touch are not looked at.
pub fn plan<F: Filesystem, G: Filesystem>(
    store: &Store<F>,
    working: &Working<G>,
    target: &RevisionId,
    head: &RevisionId,
) -> Result<Reversal, RevertError> {
    let document = store
        .get(target)?
        .ok_or(RevertError::Unknown { target: *target })?
        .clone();
    if document.parents.len() > 1 {
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
    let parent = document.parents.iter().next().copied();

    let before = match &parent {
        Some(parent) => store.tree(parent)?,
        None => Tree::empty(),
    };
    let after = store.tree(target)?;
    let now = store.tree(head)?;

    // Everything the revision said it did, which is every file it touched.
    let touched: BTreeSet<FileId> = document
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
        .collect();

    let mut reversal = Reversal {
        target: *target,
        head: *head,
        update: Update::default(),
        moves: Vec::new(),
        facts: Vec::new(),
        paths: Vec::new(),
        left: Vec::new(),
    };
    let mut refused: Vec<(String, String)> = Vec::new();
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
            (None, Some(added)) => sides.unadd(file, added, &mut reversal, &mut refused)?,
            (Some(dropped), None) => sides.undrop(file, dropped, &mut reversal, &mut refused)?,
            (Some(was), Some(became)) => {
                sides.unedit(file, was, became, &mut reversal, &mut refused)?;
            }
        }
    }

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

    /// Whether the folder holds exactly what the head records at `path`, which
    /// is the only thing the undoing may write over or take away.
    fn folder_holds(&self, path: &str, held: &Held) -> Result<bool, RevertError> {
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
        Ok(Some(self.working.digest(path)?) == held.digest())
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
        reversal: &mut Reversal,
        refused: &mut Vec<(String, String)>,
    ) -> Result<(), RevertError> {
        let Some(now) = self.now.entry(file) else {
            reversal
                .left
                .push((added.path.clone(), "dropped since".to_owned()));
            return Ok(());
        };
        let then = self.at_target(file)?;
        let held = self.at_head(file)?;
        if then != held {
            refused.push((
                now.path.clone(),
                "edited since it was added, and taking it away would take that work too; \
                 drop it with `record` if that is what you mean"
                    .to_owned(),
            ));
            return Ok(());
        }
        if !self.folder_holds(&now.path, &held)? {
            refused.push(Self::not_the_head(&now.path));
            return Ok(());
        }
        reversal
            .update
            .removes
            .push(self.removing(&now.path, &held)?);
        reversal.facts.push((Fact::Dropped, now.path.clone()));
        reversal.paths.push(now.path.clone());
        Ok(())
    }

    /// A file the revision dropped: it comes back where it was, as its parent
    /// held it.
    fn undrop(
        &self,
        file: &FileId,
        dropped: &Entry,
        reversal: &mut Reversal,
        refused: &mut Vec<(String, String)>,
    ) -> Result<(), RevertError> {
        if let Some(now) = self.now.entry(file) {
            reversal
                .left
                .push((now.path.clone(), "back since".to_owned()));
            return Ok(());
        }
        let path = &dropped.path;
        if !self.now.at(path).is_empty() {
            refused.push((
                path.clone(),
                "another file holds this path now; move it, then undo".to_owned(),
            ));
            return Ok(());
        }
        if self.working.holds(path) || self.working.is_link(path) {
            refused.push((
                path.clone(),
                "the folder holds a file here that nothing has recorded".to_owned(),
            ));
            return Ok(());
        }
        let held = self.at_parent(file)?;
        match self.laying(path, &held, None, dropped.mode)? {
            Laying::Write(write) => reversal.update.writes.push(write),
            Laying::Link(link) => reversal.update.links.push(link),
            Laying::Cannot(because) => {
                refused.push((path.clone(), because));
                return Ok(());
            }
        }
        reversal.facts.push((Fact::Added, path.clone()));
        reversal.paths.push(path.clone());
        Ok(())
    }

    /// A file the revision edited, moved, re-moded or re-pointed: each of
    /// those it did is undone where the head still holds what it left.
    fn unedit(
        &self,
        file: &FileId,
        was: &Entry,
        became: &Entry,
        reversal: &mut Reversal,
        refused: &mut Vec<(String, String)>,
    ) -> Result<(), RevertError> {
        let Some(now) = self.now.entry(file) else {
            reversal
                .left
                .push((became.path.clone(), "dropped since".to_owned()));
            return Ok(());
        };
        let refused_before = refused.len();

        // Where it goes back to.
        let mut destination = now.path.clone();
        if was.path != became.path {
            if now.path != became.path {
                reversal.left.push((
                    now.path.clone(),
                    format!("moved again since {}", became.path),
                ));
            } else if !self.now.at(&was.path).is_empty() {
                refused.push((
                    was.path.clone(),
                    format!(
                        "another file holds this path now, so {} cannot move back to it",
                        now.path
                    ),
                ));
            } else if self.working.holds(&was.path) || self.working.is_link(&was.path) {
                refused.push((
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
                            refused.push((now.path.clone(), because));
                            None
                        }
                    }
                }
                (Held::Whole(_), _, _) => {
                    refused.push((
                        now.path.clone(),
                        "its bytes were replaced again since, and there is no line in a \
                         file of bytes to undo one change by; put back the version you \
                         want by hand"
                            .to_owned(),
                    ));
                    None
                }
                _ => {
                    refused.push((
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
                reversal
                    .left
                    .push((now.path.clone(), format!("made {} again since", now.mode)));
            }
        }

        if refused.len() > refused_before {
            return Ok(());
        }
        let moving = destination != now.path;
        if !moving && content.is_none() && mode == now.mode {
            return Ok(());
        }
        if !self.folder_holds(&now.path, &held)? {
            refused.push(Self::not_the_head(&now.path));
            return Ok(());
        }

        if moving {
            reversal
                .update
                .removes
                .push(self.removing(&now.path, &held)?);
            let laid = content.as_ref().unwrap_or(&held);
            match self.laying(&destination, laid, None, mode)? {
                Laying::Write(write) => reversal.update.writes.push(write),
                Laying::Link(link) => reversal.update.links.push(link),
                Laying::Cannot(because) => {
                    refused.push((destination.clone(), because));
                    return Ok(());
                }
            }
            reversal.moves.push((now.path.clone(), destination.clone()));
            reversal.facts.push((Fact::Moved, destination.clone()));
            reversal.paths.push(now.path.clone());
        } else if let Some(content) = &content {
            let replacing = Some(&held);
            match self.laying(&now.path, content, replacing, mode)? {
                Laying::Write(write) => reversal.update.writes.push(write),
                Laying::Link(link) => reversal.update.links.push(link),
                Laying::Cannot(because) => {
                    refused.push((now.path.clone(), because));
                    return Ok(());
                }
            }
        } else {
            reversal.update.modes.push(Chmod {
                path: now.path.clone(),
                mode,
            });
        }
        if content.is_some() {
            let fact = match content {
                Some(Held::Link(_)) => Fact::Link,
                _ => Fact::Edited,
            };
            reversal.facts.push((fact, destination.clone()));
        }
        if mode != now.mode {
            reversal.facts.push((Fact::Mode, destination.clone()));
        }
        reversal.paths.push(destination);
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
    /// `replacing` says so and onto nothing otherwise.
    fn laying(
        &self,
        path: &str,
        content: &Held,
        replacing: Option<&Held>,
        mode: Mode,
    ) -> Result<Laying, RevertError> {
        Ok(match content {
            Held::Lines(state) => Laying::Write(Write {
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
            Held::Whole(None) => Laying::Cannot(
                "concurrent work left two versions of its bytes; merge first".to_owned(),
            ),
            Held::Whole(Some(payload)) => {
                if !self.store.holds_payload(payload)? {
                    return Ok(Laying::Cannot(format!(
                        "this store does not hold the bytes it goes back to ({}); `fetch` \
                         brings them",
                        payload.abbreviate(12)
                    )));
                }
                Laying::Write(Write {
                    path: path.to_owned(),
                    content: Written::Whole {
                        payload: *payload,
                        replaces: match replacing {
                            Some(_) => Some(self.working.digest(path)?),
                            None => None,
                        },
                    },
                    mode,
                })
            }
            Held::Link(target) => {
                // A `file:` target is spelled against where its file sits at
                // the head, so the link follows it through every rename since.
                let Some(spelled) = target.as_ref().and_then(|target| {
                    materialise(self.now, path, target)
                        .or_else(|| materialise(self.before, path, target))
                }) else {
                    return Ok(Laying::Cannot(
                        "the file this link pointed at is gone, so it would name nowhere"
                            .to_owned(),
                    ));
                };
                Laying::Link(Linking {
                    path: path.to_owned(),
                    target: spelled,
                    replaces: match replacing {
                        Some(_) => Stood::Link(
                            self.working
                                .link_target(path)
                                .unwrap_or_default()
                                .to_owned(),
                        ),
                        None => Stood::Nothing,
                    },
                })
            }
        })
    }
}

/// What putting one file down amounts to.
enum Laying {
    Write(Write),
    Link(Linking),
    Cannot(String),
}
