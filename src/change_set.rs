//! A change set: a line of work proposed beside a history, and the decision on
//! it.
//!
//! Decision 0090. A change set is three things this format already had, put
//! together under one name:
//!
//! - **An opening revision.** It stands on the revisions the change set is
//!   proposed against, records nothing, and carries the proposal in its
//!   message: a title on the first line, and whatever the proposer says after
//!   it. Its author is the proposer and its moment is when the change set
//!   began. Its change is the change set's identity.
//! - **A line.** Ordinary revisions, each standing on the one before, the
//!   first on the opening.
//! - **Shared bookmarks under `change-sets/<id>`.** `change-sets/<id>` pins
//!   the line's tip. `change-sets/<id>/submitted` pins the tip the proposer
//!   said was finished, `change-sets/<id>/accepted` the merge that took the
//!   line in, and `change-sets/<id>/declined` the tombstone that abandoned it.
//!
//! So everything that travels already travels: the revisions by any
//! transport, the bookmarks by `receive`, `export` and `fetch`. Each bookmark
//! is a pin to a revision, so `record` and `abandon` never drag one along —
//! except that recording onto a change set's tip, with that tip as the only
//! parent, is the change set's next step, and moves the tip pin onto it.
//!
//! The decision names are written once and never moved, and the tip and
//! `submitted` move only forward along the line. That is what makes two
//! replicas converge: [`reconcile`] takes the reading further along, and only
//! two readings neither of which is behind the other are a conflict.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

use crate::core::{ChangeId, History, RevisionId};
use crate::format::{self, RevisionDocument, Timestamp};
use crate::fs::Filesystem;
use crate::naming;
use crate::record::{Entropy, RecordError, SourceError};
use crate::store::{Bookmark, Name, REVISION_SUFFIX, Store, StoreError};

/// The directory of bookmarks every change set lives under.
pub const CHANGE_SETS: &str = "change-sets";

/// The bookmark below a change set's own that pins what was submitted.
pub const SUBMITTED: &str = "submitted";
/// The bookmark below a change set's own that pins its acceptance.
pub const ACCEPTED: &str = "accepted";
/// The bookmark below a change set's own that pins its tombstone.
pub const DECLINED: &str = "declined";

/// The bookmark pinning a change set's tip.
pub fn tip_name(id: &ChangeId) -> String {
    format!("{CHANGE_SETS}/{id}")
}

/// The bookmark pinning one of a change set's facts: [`SUBMITTED`],
/// [`ACCEPTED`] or [`DECLINED`].
pub fn fact_name(id: &ChangeId, fact: &str) -> String {
    format!("{CHANGE_SETS}/{id}/{fact}")
}

/// Which of a change set's bookmarks a name is, if it is one.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Part {
    /// `change-sets/<id>`: the tip, which moves forward as the line grows.
    Tip(ChangeId),
    /// `change-sets/<id>/submitted`: the tip the proposer finished at, which
    /// moves forward if they add to the line and submit again.
    Submitted(ChangeId),
    /// `change-sets/<id>/accepted`, written once.
    Accepted(ChangeId),
    /// `change-sets/<id>/declined`, written once.
    Declined(ChangeId),
}

impl Part {
    /// Read a bookmark's name as a part of a change set.
    pub fn of(name: &str) -> Option<Self> {
        let rest = name.strip_prefix(CHANGE_SETS)?.strip_prefix('/')?;
        let (id, fact) = match rest.split_once('/') {
            Some((id, fact)) => (id, Some(fact)),
            None => (rest, None),
        };
        let id: ChangeId = id.parse().ok()?;
        Some(match fact {
            None => Self::Tip(id),
            Some(SUBMITTED) => Self::Submitted(id),
            Some(ACCEPTED) => Self::Accepted(id),
            Some(DECLINED) => Self::Declined(id),
            Some(_) => return None,
        })
    }

    /// Whether this part moves forward along the line rather than being
    /// written once.
    pub fn moves(&self) -> bool {
        matches!(self, Self::Tip(_) | Self::Submitted(_))
    }
}

/// Where a change set stands.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum State {
    /// The proposer is still adding to it.
    Open,
    /// The proposer says it is finished.
    Submitted,
    /// A merge took its tip in.
    Accepted,
    /// A tombstone abandoned it. Its revisions are still in the history.
    Declined,
}

impl State {
    /// The word for it.
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Open => "open",
            Self::Submitted => "submitted",
            Self::Accepted => "accepted",
            Self::Declined => "declined",
        }
    }

    /// Whether nobody has decided it yet.
    pub fn is_undecided(self) -> bool {
        matches!(self, Self::Open | Self::Submitted)
    }
}

impl fmt::Display for State {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

/// A change set, read from the store.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct ChangeSet {
    /// Its identity: the change of its opening revision.
    pub id: ChangeId,
    /// The opening revision the line stands on.
    pub opening: RevisionId,
    /// The first line of the opening's message.
    pub title: String,
    /// The rest of the opening's message, trimmed.
    pub description: String,
    /// Who proposed it: the opening's author.
    pub author: String,
    /// When it began: the opening's moment.
    pub created: Timestamp,
    /// What it is proposed against: the opening's parents.
    pub base: BTreeSet<RevisionId>,
    /// The end of the line: the revision its tip bookmark pins while it is
    /// undecided, and the last step its decision covers once it is decided.
    pub tip: RevisionId,
    /// The line from the opening to the tip, the opening excluded, parents
    /// before children.
    pub steps: Vec<RevisionId>,
    /// Steps on the line beyond what its decision covers: recorded on
    /// another replica before that replica heard of the decision. They are
    /// not part of what was accepted or declined. Always empty while the
    /// change set is undecided.
    pub after: Vec<RevisionId>,
    /// The tip the proposer submitted, if they have.
    pub submitted: Option<RevisionId>,
    /// The merge that accepted it, if one did.
    pub accepted: Option<RevisionId>,
    /// The tombstone that declined it, if one did.
    pub declined: Option<RevisionId>,
}

impl ChangeSet {
    /// Where it stands.
    ///
    /// An acceptance outranks a tombstone. Two replicas can decide one change
    /// set two ways before either hears of the other, and then both names
    /// arrive. The tombstone supersedes the line, but the line is still in the
    /// ancestry of the merge, so the accepted history holds the change set's
    /// content however it was declined. *Accepted* is the true description.
    /// Both facts stay readable here, so a tool can say it was declined too.
    pub fn state(&self) -> State {
        if self.accepted.is_some() {
            State::Accepted
        } else if self.declined.is_some() {
            State::Declined
        } else if self.submitted.is_some() {
            State::Submitted
        } else {
            State::Open
        }
    }

    /// Its tip bookmark's name.
    pub fn name(&self) -> String {
        tip_name(&self.id)
    }

    /// Every revision of the change set, the opening first.
    pub fn revisions(&self) -> impl Iterator<Item = RevisionId> + '_ {
        std::iter::once(self.opening).chain(self.steps.iter().copied())
    }
}

/// What a person supplies to propose a change set.
#[derive(Debug, Clone)]
pub struct Proposing {
    /// What it is proposed against: the opening's parents. Usually one head.
    pub on: Vec<RevisionId>,
    /// Who proposes it.
    pub author: String,
    /// When.
    pub when: Timestamp,
    /// The proposal: a title on the first line, and anything after it.
    /// Required, because it is the only thing the opening carries.
    pub message: String,
    /// Headers another tool states on the opening, decision 0070's.
    pub extensions: BTreeMap<String, String>,
}

/// What a person supplies to decline a change set.
#[derive(Debug, Clone)]
pub struct Declining {
    /// Who declines it.
    pub author: String,
    /// When.
    pub when: Timestamp,
    /// Why. Required, as every tombstone's is (decision 0013).
    pub message: String,
}

/// Why a change set could not be read or changed.
#[derive(Debug)]
#[non_exhaustive]
pub enum ChangeSetError {
    /// No bookmark `change-sets/<id>` here.
    Unknown {
        /// The change set asked for.
        id: ChangeId,
    },
    /// Its bookmark is here and its opening revision is not, or the tip it
    /// pins does not stand on the opening.
    Unreadable {
        /// The change set.
        id: ChangeId,
        /// What is wrong, in a sentence.
        because: String,
    },
    /// It has been decided already.
    Decided {
        /// The change set.
        id: ChangeId,
        /// How.
        state: State,
    },
    /// Submitting a change set with nothing in it.
    Empty {
        /// The change set.
        id: ChangeId,
    },
    /// A proposal with no title.
    NoTitle,
    /// A revision the change set was asked to stand on, or to be accepted by,
    /// that this store does not hold.
    NotHeld {
        /// The revision.
        revision: RevisionId,
    },
    /// A tip moved somewhere that is not further along the line.
    NotForward {
        /// The change set.
        id: ChangeId,
        /// Its tip.
        tip: RevisionId,
        /// Where it was asked to go.
        to: RevisionId,
    },
    /// An acceptance that is not a merge naming the tip.
    NotAMerge {
        /// The change set.
        id: ChangeId,
        /// Its tip.
        tip: RevisionId,
        /// The revision offered as its acceptance.
        revision: RevisionId,
    },
    /// Declining would leave work that is not the change set's standing on
    /// what it supersedes: another change set proposed on its tip, say.
    StoodOn {
        /// The change set.
        id: ChangeId,
        /// The current revisions standing on its line from outside it.
        revisions: Vec<RevisionId>,
    },
    /// A header this format cannot hold, as decision 0070 refuses it.
    UnusableHeader {
        /// The key.
        key: String,
        /// Why.
        because: String,
    },
    /// The store refused.
    Store(StoreError),
    /// Writing the opening or the tombstone failed.
    Record(RecordError),
    /// No random source for the opening's change.
    Source(SourceError),
}

impl fmt::Display for ChangeSetError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Unknown { id } => write!(f, "there is no change set {} here", tip_name(id)),
            Self::Unreadable { id, because } => {
                write!(f, "change set {} cannot be read: {because}", tip_name(id))
            }
            Self::Decided { id, state } => {
                write!(f, "change set {} is already {state}", tip_name(id))
            }
            Self::Empty { id } => write!(
                f,
                "change set {} has nothing in it yet, so there is nothing to review",
                tip_name(id)
            ),
            Self::NoTitle => write!(
                f,
                "a change set wants a title: its opening revision records nothing, \
                 so the message is the whole of what it says"
            ),
            Self::NotHeld { revision } => {
                write!(
                    f,
                    "this store holds no revision {}",
                    revision.abbreviate(12)
                )
            }
            Self::NotForward { id, tip, to } => write!(
                f,
                "{} does not stand on {}, the tip of change set {}, so the tip \
                 cannot move to it",
                to.abbreviate(12),
                tip.abbreviate(12),
                tip_name(id)
            ),
            Self::NotAMerge { id, tip, revision } => write!(
                f,
                "{} does not accept change set {}: an acceptance is a merge, and \
                 its parents must include the tip, {}",
                revision.abbreviate(12),
                tip_name(id),
                tip.abbreviate(12)
            ),
            Self::StoodOn { id, revisions } => write!(
                f,
                "change set {} cannot be declined while other work stands on it: {}. \
                 decline or move that first, or, if it is a step of this change \
                 set, advance the tip onto it",
                tip_name(id),
                revisions
                    .iter()
                    .map(|revision| revision.abbreviate(12))
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            Self::UnusableHeader { key, because } => {
                write!(f, "`{key}` cannot be a header: {because}")
            }
            Self::Store(error) => write!(f, "{error}"),
            Self::Record(error) => write!(f, "{error}"),
            Self::Source(error) => write!(f, "{error}"),
        }
    }
}

impl std::error::Error for ChangeSetError {}

impl From<StoreError> for ChangeSetError {
    fn from(error: StoreError) -> Self {
        Self::Store(error)
    }
}

impl From<RecordError> for ChangeSetError {
    fn from(error: RecordError) -> Self {
        Self::Record(error)
    }
}

impl From<SourceError> for ChangeSetError {
    fn from(error: SourceError) -> Self {
        Self::Source(error)
    }
}

/// What two replicas' readings of one bookmark come to.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Reconciled {
    /// Keep this store's bookmark as it is.
    Keep,
    /// Write this bookmark here.
    Take(Bookmark),
    /// The two point at different things and neither is behind the other.
    Conflict,
}

/// What a bookmark this store holds becomes, given another replica's reading.
///
/// The rule `receive` applies to every name, and the rule a host's own sync
/// (one that inserts documents rather than calling `receive`) should apply:
///
/// - Readings at one target agree, and their travel axes join (decision
///   0062).
/// - A change set's tip, or its `submitted`, moves forward. When one
///   reading's revision is in the ancestry of the other's, the one further
///   along wins on both sides. `history` must hold both revisions for this to
///   be seen: on a receive, the union of the two stores.
/// - Anything else that disagrees is a conflict, as it always was.
pub fn reconcile(history: &History, name: &str, here: Bookmark, there: Bookmark) -> Reconciled {
    if here.target == there.target {
        let joined = here.joined(there);
        return match joined == here {
            true => Reconciled::Keep,
            false => Reconciled::Take(joined),
        };
    }
    let moves = Part::of(name).is_some_and(|part| part.moves());
    if let (true, Name::Revision(ours), Name::Revision(theirs)) = (moves, here.target, there.target)
    {
        if descends(history, &theirs, &ours) {
            return Reconciled::Take(Bookmark {
                target: there.target,
                private: here.private || there.private,
            });
        }
        if descends(history, &ours, &theirs) {
            let joined = Bookmark {
                target: here.target,
                private: here.private || there.private,
            };
            return match joined == here {
                true => Reconciled::Keep,
                false => Reconciled::Take(joined),
            };
        }
    }
    Reconciled::Conflict
}

/// Whether `later` stands on `earlier`, strictly.
fn descends(history: &History, later: &RevisionId, earlier: &RevisionId) -> bool {
    if later == earlier {
        return false;
    }
    let mut seen = BTreeSet::new();
    let mut walking = vec![*later];
    while let Some(id) = walking.pop() {
        let Some(revision) = history.get(&id) else {
            continue;
        };
        for parent in &revision.parents {
            if parent == earlier {
                return true;
            }
            if seen.insert(*parent) {
                walking.push(*parent);
            }
        }
    }
    false
}

/// Whether a revision is a tombstone: it supersedes work of other changes and
/// records nothing (decision 0013). A retitled opening records nothing and
/// supersedes too, but what it supersedes is its own change.
fn is_tombstone<F: Filesystem>(store: &Store<F>, document: &RevisionDocument) -> bool {
    !document.supersedes.is_empty()
        && document.supersedes.iter().all(|revision| {
            store
                .revision(revision)
                .is_none_or(|held| held.change != document.change)
        })
        && document.added.is_empty()
        && document.moved.is_empty()
        && document.modes.is_empty()
        && document.links.is_empty()
        && document.dropped.is_empty()
        && document.edited.is_empty()
        && document.text.is_empty()
        && document.bytes.is_empty()
}

/// The revision of `change` no other revision of it supersedes: the current
/// one, or, once the change is abandoned, the last one before that.
fn latest_of(history: &History, change: &ChangeId) -> Option<RevisionId> {
    let of: Vec<&crate::core::Revision> = history.revisions_of(change).collect();
    let replaced: BTreeSet<RevisionId> = of
        .iter()
        .flat_map(|revision| revision.supersedes.iter().copied())
        .collect();
    let mut left = of.iter().map(|r| r.id).filter(|id| !replaced.contains(id));
    match (left.next(), left.next()) {
        (Some(one), None) => Some(one),
        _ => None,
    }
}

/// Every revision `tip` stands on, itself included, parents before children,
/// walking no further down than a revision of `opening`: what is beneath the
/// opening is the base's history, not the change set's.
fn ancestry(history: &History, tip: &RevisionId, opening: &ChangeId) -> Vec<RevisionId> {
    // A post-order walk, iterative because a line can be as long as a
    // history is.
    let mut order = Vec::new();
    let mut done = BTreeSet::new();
    let mut stack = vec![(*tip, false)];
    while let Some((id, expanded)) = stack.pop() {
        if expanded {
            order.push(id);
            continue;
        }
        if !done.insert(id) {
            continue;
        }
        stack.push((id, true));
        if let Some(revision) = history.get(&id).filter(|r| r.change != *opening) {
            for parent in &revision.parents {
                if !done.contains(parent) {
                    stack.push((*parent, false));
                }
            }
        }
    }
    order
}

impl<F: Filesystem> Store<F> {
    /// Every change set this store can read, newest first.
    ///
    /// A `change-sets/<id>` bookmark whose opening has not arrived yet is
    /// left out, because nothing here can say what it proposes. It is listed
    /// once the revisions arrive.
    pub fn change_sets(&self) -> Result<Vec<ChangeSet>, StoreError> {
        let history = self.history();
        let mut out = Vec::new();
        for name in self.names().keys() {
            if let Some(Part::Tip(id)) = Part::of(name) {
                match self.read_change_set(&history, &id) {
                    Ok(change_set) => out.push(change_set),
                    Err(ChangeSetError::Store(error)) => return Err(error),
                    Err(_) => continue,
                }
            }
        }
        out.sort_by(|a, b| b.created.cmp(&a.created).then(a.id.cmp(&b.id)));
        Ok(out)
    }

    /// The change set `id` names.
    pub fn change_set(&self, id: &ChangeId) -> Result<ChangeSet, ChangeSetError> {
        self.read_change_set(&self.history(), id)
    }

    fn read_change_set(
        &self,
        history: &History,
        id: &ChangeId,
    ) -> Result<ChangeSet, ChangeSetError> {
        let pinned = |fact: Option<&str>| {
            let name = match fact {
                Some(fact) => fact_name(id, fact),
                None => tip_name(id),
            };
            match self.name(&name) {
                Some(Name::Revision(revision)) => Ok(Some(revision)),
                Some(other) => Err(ChangeSetError::Unreadable {
                    id: *id,
                    because: format!("{name} names {other}, and it should pin a revision"),
                }),
                None => Ok(None),
            }
        };
        let tip = pinned(None)?.ok_or(ChangeSetError::Unknown { id: *id })?;
        let unreadable = |because: String| ChangeSetError::Unreadable { id: *id, because };
        if !self.holds(&tip) {
            return Err(unreadable(format!(
                "its tip, {}, has not arrived",
                tip.abbreviate(12)
            )));
        }

        // The opening the line stands on is the one in the tip's ancestry.
        // Another revision of the same change is a retitling, and its message
        // is the one to show.
        let line = ancestry(history, &tip, id);
        let opening = line
            .iter()
            .copied()
            .find(|revision| history.get(revision).is_some_and(|r| r.change == *id))
            .ok_or_else(|| unreadable("its tip does not stand on its opening".to_owned()))?;
        let described = latest_of(history, id).unwrap_or(opening);
        let document = self
            .get(&described)?
            .ok_or_else(|| unreadable("its opening has not arrived".to_owned()))?;
        let message = document.message.trim();
        let (title, description) = match message.split_once('\n') {
            Some((title, rest)) => (title.trim().to_owned(), rest.trim().to_owned()),
            None => (message.to_owned(), String::new()),
        };

        let mut on_line: BTreeSet<RevisionId> = BTreeSet::from([opening]);
        let mut steps = Vec::new();
        for revision in &line {
            if *revision == opening {
                continue;
            }
            let stands = history
                .get(revision)
                .is_some_and(|r| r.parents.iter().any(|p| on_line.contains(p)));
            if stands {
                on_line.insert(*revision);
                steps.push(*revision);
            }
        }

        // A decision covers the line as its decider saw it. A step another
        // replica recorded before hearing of the decision moves the pin on
        // when the two meet, and it is not part of what was decided: the
        // merge does not hold it, and the tombstone does not supersede it.
        let accepted = pinned(Some(ACCEPTED))?;
        let declined = pinned(Some(DECLINED))?;
        let covered: Option<BTreeSet<RevisionId>> = match (
            accepted.and_then(|m| history.get(&m)),
            declined.and_then(|d| history.get(&d)),
        ) {
            (Some(merge), _) => {
                let mut covered = BTreeSet::new();
                for parent in merge.parents.iter().filter(|p| on_line.contains(p)) {
                    covered.extend(ancestry(history, parent, id));
                }
                (!covered.is_empty()).then_some(covered)
            }
            (None, Some(tombstone)) => Some(tombstone.supersedes.clone()),
            (None, None) => None,
        };
        let (steps, after): (Vec<RevisionId>, Vec<RevisionId>) = match &covered {
            Some(covered) => steps.into_iter().partition(|step| covered.contains(step)),
            None => (steps, Vec::new()),
        };
        let tip = match covered {
            Some(_) => steps.last().copied().unwrap_or(opening),
            None => tip,
        };

        Ok(ChangeSet {
            id: *id,
            opening,
            title,
            description,
            author: document.author.clone(),
            created: document.when.clone(),
            base: document.parents.clone(),
            tip,
            steps,
            after,
            submitted: pinned(Some(SUBMITTED))?,
            accepted,
            declined,
        })
    }

    /// The merges that name a change set's tip as a parent: what could be
    /// recorded as its acceptance.
    pub fn acceptances(&self, id: &ChangeId) -> Result<Vec<RevisionId>, ChangeSetError> {
        let change_set = self.change_set(id)?;
        Ok(self
            .revisions()
            .filter(|(_, revision)| {
                revision.parents.len() > 1 && revision.parents.contains(&change_set.tip)
            })
            .map(|(id, _)| *id)
            .collect())
    }
}

/// Undecided, or the error saying how it was decided.
fn undecided(change_set: &ChangeSet) -> Result<(), ChangeSetError> {
    match change_set.state() {
        state if state.is_undecided() => Ok(()),
        state => Err(ChangeSetError::Decided {
            id: change_set.id,
            state,
        }),
    }
}

/// Propose a change set: write its opening revision on `proposing.on`, and
/// pin its tip there.
///
/// The opening records nothing. Like a tombstone (decision 0013), its message
/// is what it says, so a message is required. Its change is minted, and that
/// change is the change set's identity from then on.
pub fn propose<F: Filesystem>(
    store: &mut Store<F>,
    proposing: &Proposing,
    entropy: &mut impl Entropy,
) -> Result<ChangeSet, ChangeSetError> {
    if proposing.message.trim().is_empty() {
        return Err(ChangeSetError::NoTitle);
    }
    for revision in &proposing.on {
        if !store.holds(revision) {
            return Err(ChangeSetError::NotHeld {
                revision: *revision,
            });
        }
    }
    for (key, value) in &proposing.extensions {
        format::check_extension(key, value).map_err(|because| ChangeSetError::UnusableHeader {
            key: key.clone(),
            because: because.to_string(),
        })?;
    }

    let change = entropy.change()?;
    let document = RevisionDocument {
        change,
        parents: proposing.on.iter().copied().collect(),
        supersedes: BTreeSet::new(),
        author: proposing.author.clone(),
        when: proposing.when.clone(),
        revised_by: None,
        revised: None,
        added: BTreeMap::new(),
        moved: BTreeMap::new(),
        modes: BTreeMap::new(),
        links: BTreeMap::new(),
        dropped: BTreeSet::new(),
        edited: BTreeMap::new(),
        text: BTreeMap::new(),
        bytes: BTreeMap::new(),
        sizes: BTreeMap::new(),
        extensions: proposing.extensions.clone(),
        message: proposing.message.clone(),
    };
    let stem = naming::stem_for(
        &proposing.when,
        &proposing.message,
        &change,
        &document.id(),
        store.documents()?.into_iter().map(|(_, held)| held),
    );
    let opening = store.insert_at(&document, &format!("{stem}{REVISION_SUFFIX}"))?;
    store.set_bookmark(
        &tip_name(&change),
        Bookmark::shared(Name::Revision(opening)),
    )?;
    store.change_set(&change)
}

/// Move a change set's tip to `to`, which must stand on the tip it has.
///
/// `record` does this itself for a revision whose one parent is the tip.
/// This is for a step that has other parents, such as the proposer merging in
/// what the base has gained since.
pub fn advance<F: Filesystem>(
    store: &mut Store<F>,
    id: &ChangeId,
    to: RevisionId,
) -> Result<ChangeSet, ChangeSetError> {
    let change_set = store.change_set(id)?;
    undecided(&change_set)?;
    if !store.holds(&to) {
        return Err(ChangeSetError::NotHeld { revision: to });
    }
    if to == change_set.tip {
        return Ok(change_set);
    }
    if !descends(&store.history(), &to, &change_set.tip) {
        return Err(ChangeSetError::NotForward {
            id: *id,
            tip: change_set.tip,
            to,
        });
    }
    store.set_name(&tip_name(id), Name::Revision(to))?;
    store.change_set(id)
}

/// Say a change set is finished, at the tip it has now.
///
/// Submitting again after adding to it moves `submitted` forward to the new
/// tip.
pub fn submit<F: Filesystem>(
    store: &mut Store<F>,
    id: &ChangeId,
) -> Result<ChangeSet, ChangeSetError> {
    let change_set = store.change_set(id)?;
    undecided(&change_set)?;
    if change_set.steps.is_empty() {
        return Err(ChangeSetError::Empty { id: *id });
    }
    if change_set.submitted != Some(change_set.tip) {
        store.set_name(&fact_name(id, SUBMITTED), Name::Revision(change_set.tip))?;
    }
    store.change_set(id)
}

/// Record that `acceptance`, a merge naming the change set's tip among its
/// parents, accepted it.
///
/// The merge is the acceptance. It is recorded the way any merge is, by
/// whoever accepts, and this writes the name that says which merge it was.
/// A tool that signs its revisions signs the merge, which vouches for the
/// line beneath it (decision 0046).
pub fn accept<F: Filesystem>(
    store: &mut Store<F>,
    id: &ChangeId,
    acceptance: RevisionId,
) -> Result<ChangeSet, ChangeSetError> {
    let change_set = store.change_set(id)?;
    undecided(&change_set)?;
    let revision = store.revision(&acceptance).ok_or(ChangeSetError::NotHeld {
        revision: acceptance,
    })?;
    if revision.parents.len() < 2 || !revision.parents.contains(&change_set.tip) {
        return Err(ChangeSetError::NotAMerge {
            id: *id,
            tip: change_set.tip,
            revision: acceptance,
        });
    }
    store.set_name(&fact_name(id, ACCEPTED), Name::Revision(acceptance))?;
    store.change_set(id)
}

/// Decline a change set: supersede its opening and every step with one
/// tombstone (decision 0013), and pin the tombstone.
///
/// The tombstone stands where the opening stands, on the base, so the
/// content falls out of the ancestry and nothing has to be undone. Its
/// revisions stay in the store, superseded, until a `prune` takes them.
///
/// It supersedes the change set's own revisions and nothing else. 0013's
/// `abandon` takes everything standing on what it abandons, which here could
/// be another change set proposed on this one's tip. So this writes the
/// tombstone itself, over exactly the line, and refuses while any other work
/// stands on it. And where the opening was retitled, the tombstone
/// supersedes the current revision of the opening's change, not the one the
/// line stands on, which its retitling already superseded.
pub fn decline<F: Filesystem>(
    store: &mut Store<F>,
    id: &ChangeId,
    declining: &Declining,
    entropy: &mut impl Entropy,
) -> Result<ChangeSet, ChangeSetError> {
    if declining.message.trim().is_empty() {
        return Err(ChangeSetError::Record(RecordError::NoReasonGiven));
    }
    let change_set = store.change_set(id)?;
    undecided(&change_set)?;
    let history = store.history();
    let superseded = history.superseded();

    // A tombstone standing on the line holds no work, so it is no reason to
    // refuse: declining a change set proposed on this one's tip leaves one.
    let line: BTreeSet<RevisionId> = change_set.revisions().collect();
    let mut standing = Vec::new();
    for (revision, held) in store.documents()? {
        if !line.contains(revision)
            && !superseded.contains(revision)
            && held.parents.iter().any(|parent| line.contains(parent))
            && !is_tombstone(store, held)
        {
            standing.push(*revision);
        }
    }
    if !standing.is_empty() {
        return Err(ChangeSetError::StoodOn {
            id: *id,
            revisions: standing,
        });
    }

    let opening = latest_of(&history, id).unwrap_or(change_set.opening);
    let parents = store
        .revision(&opening)
        .map(|revision| revision.parents.clone())
        .unwrap_or_else(|| change_set.base.clone());
    let supersedes: BTreeSet<RevisionId> = std::iter::once(opening)
        .chain(change_set.steps.iter().copied())
        .filter(|revision| !superseded.contains(revision))
        .collect();

    let change = entropy.change()?;
    let document = RevisionDocument {
        change,
        parents,
        supersedes,
        author: declining.author.clone(),
        when: declining.when.clone(),
        revised_by: None,
        // Decision 0005: `revised` is the moment of every supersession, and
        // here the work and the rewrite are one act, as in any tombstone.
        revised: Some(declining.when.clone()),
        added: BTreeMap::new(),
        moved: BTreeMap::new(),
        modes: BTreeMap::new(),
        links: BTreeMap::new(),
        dropped: BTreeSet::new(),
        edited: BTreeMap::new(),
        text: BTreeMap::new(),
        bytes: BTreeMap::new(),
        sizes: BTreeMap::new(),
        extensions: BTreeMap::new(),
        message: declining.message.clone(),
    };
    let stem = naming::stem_for(
        &declining.when,
        &declining.message,
        &change,
        &document.id(),
        store.documents()?.into_iter().map(|(_, held)| held),
    );
    let tombstone = store.insert_at(&document, &format!("{stem}{REVISION_SUFFIX}"))?;

    // What `abandon` does for a bookmark that followed the abandoned work: it
    // follows the tombstone. A pin, every change set's own included, stays.
    let followed: BTreeSet<ChangeId> = document
        .supersedes
        .iter()
        .filter_map(|revision| store.revision(revision).map(|held| held.change))
        .collect();
    let following: Vec<String> = store
        .names()
        .iter()
        .filter(|(_, bookmark)| matches!(bookmark.target, Name::Change(named) if followed.contains(&named)))
        .map(|(name, _)| name.clone())
        .collect();
    for name in following {
        store.set_name(&name, Name::Change(change))?;
    }

    store.set_name(&fact_name(id, DECLINED), Name::Revision(tombstone))?;
    store.change_set(id)
}

/// The change sets whose tip a revision recorded on `parents` is the next
/// step of: exactly one parent, and it is an undecided change set's tip.
///
/// What `record` asks after writing, so that recording onto a change set adds
/// to it the way recording onto a bookmarked change moves the bookmark.
pub(crate) fn stepped_on<F: Filesystem>(store: &Store<F>, parents: &[RevisionId]) -> Vec<String> {
    let [parent] = parents else {
        return Vec::new();
    };
    store
        .names()
        .iter()
        .filter(|(name, bookmark)| {
            matches!(Part::of(name), Some(Part::Tip(_)))
                && bookmark.target == Name::Revision(*parent)
        })
        .filter(|(name, _)| {
            let Some(Part::Tip(id)) = Part::of(name) else {
                return false;
            };
            store.name(&fact_name(&id, ACCEPTED)).is_none()
                && store.name(&fact_name(&id, DECLINED)).is_none()
        })
        .map(|(name, _)| name.clone())
        .collect()
}
