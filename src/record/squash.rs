//! Squashing: one revision standing for a run of them.
//!
//! Decision 0082. Decision 0001 already named the state this reaches — "a
//! revision may supersede revisions of *other* changes, which is what
//! squashing is" — and 0013 recorded the first act that reaches it on
//! purpose. A squash is the other: where a tombstone says the work is gone, a
//! squash says the work is here, stated once.
//!
//! What it states needs no folder. The tip's file set and the base's are both
//! in the store, every file keeps the identifier it already has, so the
//! revision is the difference between two trees — worked out the way `record`
//! works out the difference between a tree and a folder, from states rather
//! than from files on disk. That is what lets it squash a run with work
//! already standing on top of it.

use std::collections::{BTreeMap, BTreeSet};

use crate::core::{ChangeId, RevisionId};
use crate::diff::diff;
use crate::format::{OperationKind, RevisionDocument, Timestamp};
use crate::fs::Filesystem;
use crate::naming;
use crate::replay::State;
use crate::store::{Name, REVISION_SUFFIX, Store};
use crate::tree::{Kind, Tree};

use super::{Change, Entropy, Plan, RecordError, carry, carrying_for, content_of};

/// What a person supplies to squash a run of work.
#[derive(Debug, Clone)]
pub struct Squashing {
    /// Where the run starts from: the squash stands on this, and it is not
    /// part of what is squashed.
    pub base: RevisionId,
    /// The last of the run: what the squash states, and where work standing
    /// on the run is carried from.
    pub tip: RevisionId,
    /// The message, or `None` for the run's own messages, in order.
    pub message: Option<String>,
    /// Who is squashing, which 0005 spells `revised-by` where it is not the
    /// run's author.
    pub reviser: String,
    /// When, per 0010: a fresh reading, because a person asked for this.
    pub revised: Timestamp,
}

/// What was squashed.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct Squashed {
    /// The revision written.
    pub revision: RevisionId,
    /// Its change, newly minted.
    pub change: ChangeId,
    /// The run it supersedes, earliest first.
    pub superseded: Vec<RevisionId>,
    /// What it states against the base.
    pub plan: Plan,
    /// The work standing on the tip, carried onto it. Decision 0059.
    pub carried: carry::CarryPlan,
    /// Bookmarks that moved from the squashed work to the squash.
    pub advanced: Vec<String>,
}

/// The run one squash would supersede, earliest first, without writing
/// anything.
///
/// Decision 0063's range: everything the tip has behind it that the base does
/// not. Every refusal is here, so `--dry-run` meets each of them at the moment
/// the real thing would.
pub fn squash_plan<F: Filesystem>(
    store: &Store<F>,
    base: &RevisionId,
    tip: &RevisionId,
) -> Result<Vec<RevisionId>, RecordError> {
    for revision in [base, tip] {
        if store.revision(revision).is_none() {
            return Err(RecordError::NotHeld {
                revision: *revision,
            });
        }
    }
    let behind_tip: BTreeSet<RevisionId> = store
        .reachable_from(&[*tip])?
        .into_iter()
        .map(|(id, _)| id)
        .collect();
    // A base the tip does not stand on would put a line of work into the
    // squash's ancestry that none of the run had, and the tip's files stated
    // against it would undo whatever that line did.
    if !behind_tip.contains(base) || base == tip {
        return Err(RecordError::NotBehind {
            base: *base,
            tip: *tip,
        });
    }
    let behind_base: BTreeSet<RevisionId> = store
        .reachable_from(&[*base])?
        .into_iter()
        .map(|(id, _)| id)
        .collect();
    let run: BTreeSet<RevisionId> = behind_tip.difference(&behind_base).copied().collect();
    if run.len() < 2 {
        return Err(RecordError::NothingToSquash { tip: *tip });
    }

    let history = store.history();
    let superseded = history.superseded();
    for revision in &run {
        super::already_rewritten(store, revision)?;
    }

    // Work standing on the tip is carried onto the squash. Work standing on
    // any other revision of the run stands on something that no longer means
    // what it meant — its base is half of the run — and carrying it would be
    // squashing it in too, which is not what was named. A revision already
    // rewritten is somebody's undo, not work, and stands nowhere.
    let inside: BTreeMap<RevisionId, Vec<RevisionId>> = run
        .iter()
        .filter(|revision| *revision != tip)
        .filter_map(|revision| {
            let standing: Vec<RevisionId> = super::standing_on(store, revision)
                .into_iter()
                .filter(|id| !run.contains(id) && !superseded.contains(id))
                .collect();
            (!standing.is_empty()).then_some((*revision, standing))
        })
        .collect();
    if let Some((revision, standing)) = inside.into_iter().next() {
        return Err(RecordError::StandsInside { revision, standing });
    }

    // Who and when live in the part of a document opening the store does not
    // read (0061), so the run's are parsed here.
    let mut documents = Vec::with_capacity(run.len());
    for id in &run {
        let document = store
            .get(id)?
            .ok_or(RecordError::NotHeld { revision: *id })?;
        documents.push((*id, document));
    }
    // A merge's author joined the work, and the work's authors are on the
    // revisions it joined — a sync that merges on every device alike names
    // itself, so that each writes the same merge. Only the revisions that did
    // work say whose it is; a run of nothing but merges keeps theirs.
    let working: BTreeSet<&str> = documents
        .iter()
        .filter(|(_, held)| held.parents.len() < 2)
        .map(|(_, held)| held.author.as_str())
        .collect();
    let authors = match working.is_empty() {
        false => working,
        true => documents
            .iter()
            .map(|(_, held)| held.author.as_str())
            .collect(),
    };
    if authors.len() > 1 {
        return Err(RecordError::SeveralAuthors {
            authors: authors.into_iter().map(str::to_owned).collect(),
        });
    }

    // Parents before children, and among revisions free to go next the
    // earlier first: two recorded in the same second are still in order when
    // one stands on the other.
    let when: BTreeMap<RevisionId, Option<jiff::Timestamp>> = documents
        .iter()
        .map(|(id, held)| (*id, instant(held)))
        .collect();
    let mut waiting: BTreeMap<RevisionId, usize> = documents
        .iter()
        .map(|(id, held)| (*id, held.parents.iter().filter(|p| run.contains(p)).count()))
        .collect();
    let mut ordered = Vec::with_capacity(run.len());
    while !waiting.is_empty() {
        let next = waiting
            .iter()
            .filter(|(_, count)| **count == 0)
            .map(|(id, _)| (when[id], *id))
            .min()
            .map(|(_, id)| id)
            .expect("a history has no cycle");
        waiting.remove(&next);
        for (id, held) in &documents {
            if held.parents.contains(&next)
                && let Some(count) = waiting.get_mut(id)
            {
                *count -= 1;
            }
        }
        ordered.push(next);
    }
    Ok(ordered)
}

/// When a revision says its work was done, as an instant, so that two
/// offsets compare as times rather than as spellings.
fn instant(document: &RevisionDocument) -> Option<jiff::Timestamp> {
    document.when.as_str().parse().ok()
}

/// Squash a run of work into one revision standing on its base.
///
/// Decision 0082. The squash states the tip's files against the base, keeps
/// the run's author and the moment its work began, mints a change — every
/// change in the run is then squashed, 0001's word for it — and supersedes
/// every revision in the run. What stood on the tip is carried onto it in
/// the same act (0059), verbatim, since the two hold the same files.
pub fn squash<F: Filesystem>(
    store: &mut Store<F>,
    squashing: &Squashing,
    entropy: &mut impl Entropy,
) -> Result<Squashed, RecordError> {
    let run = squash_plan(store, &squashing.base, &squashing.tip)?;
    let mut documents = Vec::with_capacity(run.len());
    for id in &run {
        documents.push(store.get(id)?.expect("the plan held it").clone());
    }
    // Whose: the plan already refused a run with two, so the first revision
    // that did work names the one there is. When: the earliest instant.
    let author = documents
        .iter()
        .find(|held| held.parents.len() < 2)
        .unwrap_or(&documents[0])
        .author
        .clone();
    let when = documents
        .iter()
        .min_by_key(|held| (instant(held), held.when.clone()))
        .expect("a run of two or more")
        .when
        .clone();

    let plan = stating(store, &squashing.base, &squashing.tip)?;
    let content = content_of(&plan);

    let message = match &squashing.message {
        Some(message) => message.clone(),
        None => messages(store, &run),
    };
    let change = entropy.change()?;
    let document = RevisionDocument {
        change,
        parents: BTreeSet::from([squashing.base]),
        supersedes: run.iter().copied().collect(),
        // Decision 0005: written only where it differs from the author.
        revised_by: (squashing.reviser != author).then(|| squashing.reviser.clone()),
        author,
        when,
        revised: Some(squashing.revised.clone()),
        added: plan.added.clone(),
        moved: plan.moved.clone(),
        modes: plan.modes.clone(),
        links: plan.links.clone(),
        dropped: plan.dropped.clone(),
        edited: content.edited.clone(),
        text: content.text.clone(),
        bytes: content.bytes.clone(),
        sizes: content.sizes.clone(),
        // A header another tool wrote describes the revision it was written
        // on, and a squash of several is none of them. 0065 forbids dropping
        // what this writer cannot read from a revision it *restates*; a
        // squash restates no one revision, so it states none.
        extensions: BTreeMap::new(),
        message,
    };

    let stem = naming::stem_for(
        &document.when,
        &document.message,
        &change,
        &document.id(),
        store.documents()?.into_iter().map(|(_, held)| held),
    );
    let filed = naming::filed(&content.filings);
    let name = |held: &RevisionId| match filed.get(held) {
        Some(name) => format!("{stem}/{name}"),
        None => held.to_string(),
    };
    for held in plan.edited.values() {
        match held {
            Change::Operations(document) => {
                store.insert_operation_at(
                    document,
                    &name(&crate::format::digest(&document.write())),
                )?;
            }
            Change::Created(payload) => {
                store.insert_payload_at(payload, &name(&crate::format::digest(payload)))?;
            }
            // Bytes the tip already names, by digest: the store holds them
            // under the revision that brought them, or they are held
            // elsewhere, and either way there is nothing to write.
            Change::Whole { .. } | Change::Resolution(_) => {}
        }
    }
    // Decision 0059 plans a rewrite's carries before anything is written, and
    // a tombstone or a reword can be held provisionally for it because they
    // name no content of their own. A squash names operation documents, and
    // the carry reads the squash's files to compare them with the tip's, so
    // its content is filed first — the order `record` keeps (0011): a refusal
    // here leaves content nothing names, which `check` calls a note, and
    // never a revision naming what is not there. Nothing is refused in
    // practice: the squash holds the tip's files exactly, so what stood on
    // the tip is carried verbatim.
    let planned = carrying_for(store, &document)?;
    let revision = store.insert_at(&document, &format!("{stem}{REVISION_SUFFIX}"))?;
    let carried = carry::write(store, planned)?;

    // A bookmark that followed any of the squashed work follows it here, as
    // one that followed abandoned work follows the tombstone. A pin stays put.
    let followed: BTreeSet<ChangeId> = run
        .iter()
        .filter_map(|squashed| store.revision(squashed).map(|held| held.change))
        .collect();
    let following: Vec<String> = store
        .names()
        .iter()
        .filter(|(_, bookmark)| match bookmark.target {
            Name::Change(named) => followed.contains(&named),
            Name::Revision(_) | Name::File(_) => false,
        })
        .map(|(name, _)| name.clone())
        .collect();
    let mut advanced = Vec::new();
    for name in following {
        store.set_name(&name, Name::Change(change))?;
        advanced.push(name);
    }

    Ok(Squashed {
        revision,
        change,
        superseded: run,
        plan,
        carried,
        advanced,
    })
}

/// The run's messages, in order, each once: what a squash says when nobody
/// said anything else. Empty where the run said nothing, which 0002 allows.
fn messages<F: Filesystem>(store: &Store<F>, run: &[RevisionId]) -> String {
    let mut said: Vec<&str> = Vec::new();
    for id in run {
        let Ok(Some(held)) = store.get(id) else {
            continue;
        };
        let message = held.message.trim();
        if !message.is_empty() && !said.contains(&message) {
            said.push(message);
        }
    }
    said.join("\n\n")
}

/// What the tip's files are, stated against the base's: the facts of one
/// revision taking the base to the tip.
///
/// Every file keeps its identifier, so nothing is minted and no rename has to
/// be noticed — a file whose path differs was moved, because it is the same
/// file. A file of lines states the operations taking its content at the base
/// to its content at the tip, which is 0007's diff; one being added states
/// its lines outright, as 0017 has `record` do; bytes and links state what the
/// tip states.
fn stating<F: Filesystem>(
    store: &Store<F>,
    base: &RevisionId,
    tip: &RevisionId,
) -> Result<Plan, RecordError> {
    let before: Tree = store.tree(base)?;
    let after: Tree = store.tree(tip)?;
    let mut plan = Plan {
        parents: vec![*base],
        ..Plan::default()
    };

    for (file, was) in before.entries() {
        if after.entry(file).is_none() {
            plan.dropped.insert(*file);
            plan.paths.insert(*file, was.path.clone());
        }
    }

    for (file, is) in after.entries() {
        plan.paths.insert(*file, is.path.clone());
        let was = before.entry(file);
        match was {
            None => {
                plan.added.insert(*file, is.path.clone());
            }
            Some(was) if was.path != is.path => {
                plan.moved.insert(*file, is.path.clone());
            }
            Some(_) => {}
        }
        if was.map_or(crate::format::Mode::Plain, |was| was.mode) != is.mode {
            plan.modes.insert(*file, is.mode);
        }
        match is.kind {
            Kind::Link => {
                let target = is.target.clone().expect("a link has a target");
                if was.and_then(|was| was.target.as_ref()) != Some(&target) {
                    plan.links.insert(*file, target);
                }
            }
            Kind::Whole => {
                // 0008 leaves a payload two concurrent revisions each stated
                // undecided rather than pick one, and a squash stating either
                // would be the choice nobody made.
                let payload = is.payload.ok_or_else(|| RecordError::UndecidedBytes {
                    path: is.path.clone(),
                })?;
                if was.and_then(|was| was.payload) != Some(payload) {
                    // Decision 0083: the size the tip's tree states, which
                    // is none where the line that brought the payload
                    // predates sizes — restated as found, never guessed.
                    plan.edited.insert(
                        *file,
                        Change::Whole {
                            payload,
                            size: is.size,
                        },
                    );
                }
            }
            Kind::Lines => {
                let now = store.content(tip, file)?;
                let then = match was {
                    Some(_) => store.content(base, file)?,
                    None => State::empty(),
                };
                if let Some(change) = lines(&then, &now, was.is_none(), &is.path)? {
                    plan.edited.insert(*file, change);
                }
            }
        }
    }
    Ok(plan)
}

/// What one file of lines contributes, from its content at the base to its
/// content at the tip. `None` where the two are the same file.
///
/// A forgotten run (0014) in the tip's content that the base does not also
/// hold is refused: the squash would have to state lines whose bytes were
/// destroyed, and writing the marker in their place would state a line
/// nobody typed.
fn lines(
    then: &State,
    now: &State,
    adding: bool,
    path: &str,
) -> Result<Option<Change>, RecordError> {
    let forgotten = || RecordError::SquashesForgotten {
        path: path.to_owned(),
    };
    if adding {
        if now.items().iter().any(|item| item.forgotten) {
            return Err(forgotten());
        }
        let bytes = now.text().into_bytes();
        return Ok((!bytes.is_empty()).then_some(Change::Created(bytes)));
    }
    let Some(document) = diff(then, now) else {
        return Ok(None);
    };
    let inserts_forgotten = document.operations.iter().any(|operation| {
        operation.kind == OperationKind::Insert && operation.items.iter().any(|item| item.forgotten)
    });
    if inserts_forgotten {
        return Err(forgotten());
    }
    Ok(Some(Change::Operations(document)))
}

/// A squash's plan is the same answer whether asked for its own sake or
/// before writing, and `--dry-run` wants it without a change minted.
pub fn squash_statement<F: Filesystem>(
    store: &Store<F>,
    base: &RevisionId,
    tip: &RevisionId,
) -> Result<Plan, RecordError> {
    squash_plan(store, base, tip)?;
    stating(store, base, tip)
}
