//! Recording a revision: what a writer supplies, and what it is given.
//!
//! Decisions 0010 and 0011 between them: the three facts nothing can derive —
//! a change ID, an author, a time — and the folder they are recorded about.
//! Everything else in a revision falls out of comparing the working copy with
//! the tree at its parent.
//!
//! It also rewrites one, which decision 0023 decides the terms of: an
//! amendment supersedes the revision it names, keeps everything that describes
//! the work — the change, the author, the moment it was first recorded — and
//! works the rest out again from the folder. What it will not do is what 0011
//! says it will not: rewrite a revision something stands on, because restating
//! a descendant's operations against a changed parent is 0007's merge under
//! another name.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

use crate::core::{ChangeId, FileId, RevisionId};
use crate::diff::diff;
use crate::format::{OperationDocument, RevisionDocument, Timestamp, Version, digest};
use crate::naming;
use crate::replay::State;
use crate::store::{MaterialiseError, Name, REVISION_SUFFIX, Store, StoreError};
use crate::tree::{Kind, Tree, TreeContest};
use crate::working::{self, Working, WorkingError};

pub mod identity;
pub mod source;

pub use identity::{Identities, IdentityError, author_for};
pub use source::{Clock, Entropy, Platform, SourceError};

/// What one path's content contributes to a revision.
///
/// Decision 0017: three spellings, decided by what the file is rather than by
/// what the recorder feels like writing. A file of lines that already exists
/// contributes an operation document; a file of lines being created
/// contributes the lines themselves; a file of bytes contributes its bytes.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Change {
    /// An operation document, against the file as its parents leave it.
    Operations(OperationDocument),
    /// The lines a file is created with, which `text` names.
    Created(Vec<u8>),
    /// A file's whole content, which `bytes` names.
    Whole(Vec<u8>),
}

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

/// What the folder says, before any identifier is minted.
///
/// Decision 0015 makes this the primitive and [`Plan`] the thing derived from
/// it. One traversal produces every fact, keyed by path where a path is all
/// there is and by [`FileId`] where the tree has already given one, so that
/// `status` can say what recording would do without minting the identifiers
/// only recording is entitled to mint.
///
/// Everything expensive happens here once — the merged tree, the replay of
/// each file, the diff — which is what keeps `status` and `record --dry-run`
/// from ever describing different work.
#[derive(Debug, Clone, Default)]
pub struct Survey {
    /// Paths the tree does not hold yet.
    pub added: BTreeSet<String>,
    /// Files whose path changed, with the path they moved to.
    ///
    /// Only ever what a person stated. Decision 0011 observes everything
    /// except a rename, so a folder somebody typed `mv` in and said nothing
    /// about states an `added` and a `dropped`, and `renames` is where this
    /// says it noticed.
    pub moved: BTreeMap<FileId, String>,
    /// Files the tree holds and the folder does not, with where they sat.
    pub dropped: BTreeMap<FileId, String>,
    /// What each path's content contributes, added paths included.
    pub edited: BTreeMap<String, Change>,
    /// Where each surveyed path's file is, for the paths the tree holds.
    pub held: BTreeMap<String, FileId>,
    /// Paths the folder holds that nothing here can take, and why.
    pub refused: Vec<(String, String)>,
    /// A dropped path and an added path holding the same bytes, one to one.
    pub renames: Vec<(String, String)>,
    /// What the tree decided by rule rather than by agreement.
    pub contested: Vec<TreeContest>,
    /// Paths several files claim that `--at` has not settled.
    pub unsettled: BTreeMap<String, Vec<FileId>>,
    /// Marker lines still standing, by path, when joining.
    pub standing: Vec<(String, usize)>,
    /// The revisions this was surveyed against.
    pub parents: Vec<RevisionId>,
}

impl Survey {
    /// Whether the folder states nothing the parents do not already say.
    pub fn is_empty(&self) -> bool {
        self.added.is_empty()
            && self.moved.is_empty()
            && self.dropped.is_empty()
            && self.edited.is_empty()
    }

    /// Every fact, by the path it concerns, for a person reading.
    pub fn facts(&self) -> Vec<(Fact, String)> {
        let mut facts: Vec<(Fact, String)> = Vec::new();
        facts.extend(self.added.iter().map(|path| (Fact::Added, path.clone())));
        facts.extend(self.moved.values().map(|path| (Fact::Moved, path.clone())));
        facts.extend(
            self.dropped
                .values()
                .map(|path| (Fact::Dropped, path.clone())),
        );
        facts.extend(
            self.edited
                .keys()
                .filter(|path| !self.added.contains(*path))
                .map(|path| (Fact::Edited, path.clone())),
        );
        facts.sort();
        facts
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
    pub edited: BTreeMap<FileId, Change>,
    /// Where each file sits after this revision, for rendering.
    pub paths: BTreeMap<FileId, String>,
    /// The revisions this would be recorded against.
    pub parents: Vec<RevisionId>,
    /// What the folder said, before the identifiers below were minted.
    pub survey: Survey,
}

impl Plan {
    /// Whether this would state nothing at all.
    pub fn is_empty(&self) -> bool {
        self.survey.is_empty()
    }

    /// Every fact, by the path it concerns, for a person reading.
    ///
    /// The survey's, so that what `record` prints after writing is the list
    /// `status` printed before it.
    pub fn facts(&self) -> Vec<(Fact, String)> {
        self.survey.facts()
    }
}

/// What a person supplies, beside the folder itself.
#[derive(Debug, Clone)]
pub struct Recording {
    /// The revisions to record against. Empty for a root, two for a merge.
    pub parents: Vec<RevisionId>,
    /// Who is recording, per decision 0010.
    pub author: String,
    /// When, per decision 0010.
    pub when: Timestamp,
    /// The message, verbatim, which may be empty.
    pub message: String,
    /// Renames, as `(from, to)`. The one fact that cannot be observed.
    pub moves: Vec<(String, String)>,
    /// Where a contested file goes, by identifier: decision 0012's `--at`.
    ///
    /// A path is a value rather than prose, so a person states it rather than
    /// editing it, and by identifier because after a merge a path may name two
    /// files.
    pub at: Vec<(FileId, String)>,
}

/// What a person supplies to rewrite a revision.
///
/// Decision 0023: everything that describes the *work* comes from the revision
/// being rewritten rather than from here, which is why this carries so much
/// less than a [`Recording`] does. What is left is the rewrite itself.
#[derive(Debug, Clone)]
pub struct Amendment {
    /// The revision being rewritten.
    pub revision: RevisionId,
    /// A new message, or `None` to keep the one that revision carries.
    pub message: Option<String>,
    /// Who is doing the rewriting, which 0005 spells `revised-by`.
    pub reviser: String,
    /// When, per 0010: a fresh reading, because a person asked for this.
    pub revised: Timestamp,
    /// Renames, stated against the tree at the amended revision's parents.
    pub moves: Vec<(String, String)>,
}

/// What was amended.
#[derive(Debug, Clone)]
pub struct Amended {
    /// The revision written.
    pub revision: RevisionId,
    /// Its change, which is the amended revision's.
    pub change: ChangeId,
    /// The revision it supersedes, which is still in the store.
    pub superseded: RevisionId,
    /// What it says the folder holds.
    pub plan: Plan,
}

/// What a person supplies to abandon work.
///
/// Decision 0013: the tombstone records nothing, so the reason is the only
/// thing it carries — which is why the message is required here and nowhere
/// else.
#[derive(Debug, Clone)]
pub struct Abandoning {
    /// The earliest revision to go: it and everything standing on it.
    pub revision: RevisionId,
    /// Who is abandoning, per decision 0010.
    pub author: String,
    /// When, per decision 0010.
    pub when: Timestamp,
    /// Why. A tombstone with no message is a hole in the log.
    pub message: String,
}

/// What was abandoned.
#[derive(Debug, Clone)]
pub struct Abandoned {
    /// The tombstone written.
    pub revision: RevisionId,
    /// Its change, newly minted — minting is what leaves the old change
    /// `Abandoned` rather than merely empty.
    pub change: ChangeId,
    /// The run the tombstone supersedes, the named revision first.
    pub superseded: Vec<RevisionId>,
    /// Bookmarks that moved from the abandoned work to the tombstone.
    pub advanced: Vec<String>,
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

/// Work out what the folder says, without minting or writing anything.
///
/// The primitive decision 0015 makes this: everything expensive happens here,
/// and both `status` and `record` read the result rather than computing their
/// own. What a person stated — the parents, the renames, and where a contested
/// file goes — is passed in, because those are the three things that cannot be
/// observed.
pub fn survey(
    store: &Store,
    working: &Working,
    parents: &[RevisionId],
    moves: &[(String, String)],
    at: &[(FileId, String)],
) -> Result<Survey, RecordError> {
    let joining = parents.len() > 1;
    let (tree, contested) = if parents.is_empty() {
        (Tree::empty(), Vec::new())
    } else {
        let merged = store.merged_tree_of(parents)?;
        (merged.tree, merged.contested)
    };

    // Where each file the tree holds sits after the renames a person stated.
    let mut placed: BTreeMap<FileId, String> = tree
        .files()
        .map(|(file, path)| (*file, path.to_owned()))
        .collect();
    let mut moved = BTreeMap::new();
    for (file, to) in at {
        if placed.insert(*file, to.clone()).is_none() {
            return Err(RecordError::NotInTheTree {
                path: file.to_string(),
            });
        }
        moved.insert(*file, to.clone());
    }
    for (from, to) in moves {
        let file = one_file_at(&placed, from)?;
        crate::format::check_path(to).map_err(|because| RecordError::UnusablePath {
            path: to.clone(),
            because: because.to_string(),
        })?;
        placed.insert(file, to.clone());
        moved.insert(file, to.clone());
    }

    // A rule that covers a file the tree already holds, refused before any of
    // it is described. Decision 0011: the walk never offered these paths, so
    // every one of them would survey as `dropped`, and a person who wrote the
    // rule for privacy would get history's copy kept and the folder's deleted
    // — the opposite of the request, in an append-only history. Checked
    // against `placed` rather than the tree, so a `--move` onto a skipped path
    // is caught by the same line.
    let skipped = store.skipped();
    let covered: Vec<String> = placed
        .values()
        .filter(|path| skipped.skips(path))
        .cloned()
        .collect();
    if !covered.is_empty() {
        return Err(RecordError::SkipsTracked { paths: covered });
    }

    // A path two files claim is not a name for either of them. 0008 lets a
    // merge produce this and 0012's `--at` is how a person settles it; until
    // they have, it is reported rather than resolved to whichever a map kept.
    let mut claimants: BTreeMap<&str, Vec<FileId>> = BTreeMap::new();
    for (file, path) in &placed {
        claimants.entry(path.as_str()).or_default().push(*file);
    }
    let mut held: BTreeMap<String, FileId> = BTreeMap::new();
    let mut unsettled: BTreeMap<String, Vec<FileId>> = BTreeMap::new();
    for (path, files) in claimants {
        match files.as_slice() {
            [only] => {
                held.insert(path.to_owned(), *only);
            }
            several => {
                unsettled.insert(path.to_owned(), several.to_vec());
            }
        }
    }

    let mut survey = Survey {
        moved,
        contested,
        unsettled,
        parents: parents.to_vec(),
        refused: working.refused().to_vec(),
        ..Survey::default()
    };

    // Kept only for the paths that turn out to be added, since that is the
    // only place the bytes are wanted twice.
    let mut arrived: BTreeMap<String, Vec<u8>> = BTreeMap::new();

    // A path in the folder is either a file the tree already holds, or a file
    // nobody has recorded yet, which recording mints an identifier for.
    for (path, _) in working.iter() {
        if survey.unsettled.contains_key(path.as_str()) {
            continue;
        }
        let file = held.get(path.as_str()).copied();
        if file.is_none() {
            survey.added.insert(path.clone());
        }

        let bytes = working.bytes(path)?;

        // Decision 0017: a file the tree holds is addressed as the kind it was
        // added as, and a file nobody has recorded yet is sniffed once, here.
        let kind = match file.and_then(|file| tree.kind(&file)) {
            Some(kind) => kind,
            None if working::is_text(&bytes) => Kind::Lines,
            None => Kind::Whole,
        };

        if file.is_none() {
            arrived.insert(path.clone(), bytes.clone());
        }

        if kind == Kind::Whole {
            // Nothing to compare line by line, so the comparison is the whole
            // of it: the payload it holds now against the payload it held.
            let before = match file {
                Some(file) if !parents.is_empty() => held_bytes(store, parents, &file)?,
                _ => None,
            };
            if before.as_deref() != Some(bytes.as_slice()) {
                survey.edited.insert(path.clone(), Change::Whole(bytes));
            }
            continue;
        }

        let text = match String::from_utf8(bytes) {
            Ok(text) => text,
            Err(_) => {
                // 0015: a refusal is a line of the report rather than the end
                // of it. 0017 narrows what is refused to this one case — a
                // file recorded as lines that no longer holds any.
                let refusal = WorkingError::NotText { path: path.clone() };
                survey.refused.push((path.clone(), refusal.because()));
                survey.added.remove(path);
                arrived.remove(path);
                continue;
            }
        };

        let before = match file {
            Some(file) if !parents.is_empty() => {
                let merged = store.merged_content_of(parents, &file)?;
                // Decision 0012: while recording a merge, a contested file
                // holding any line the renderer wrote is refused — per line,
                // because a person can edit inside a fence and leave it
                // standing. Here it is counted; `plan` is what refuses.
                if joining && !merged.contested.is_empty() {
                    let standing = crate::conflict::unresolved(&merged, &text);
                    if !standing.is_empty() {
                        survey.standing.push((path.clone(), standing.len()));
                    }
                }
                merged.state
            }
            _ => State::empty(),
        };

        // A file being created states its lines outright rather than as an
        // insert of every one of them, which is decision 0017's whole point.
        if file.is_none() {
            if !text.is_empty() {
                survey
                    .edited
                    .insert(path.clone(), Change::Created(text.into_bytes()));
            }
            continue;
        }

        let after = State::from_text(&text);
        if let Some(document) = diff(&before, &after) {
            survey
                .edited
                .insert(path.clone(), Change::Operations(document));
        }
    }

    // A file the tree holds and the folder does not is gone, which is a fact
    // rather than a guess — decision 0011's reason for having no `--drop`.
    for (file, path) in &placed {
        if !working.holds(path) {
            survey.dropped.insert(*file, path.clone());
            survey.moved.remove(file);
        }
    }

    survey.renames = renames(store, parents, &survey.dropped, &arrived)?;
    survey.held = held;
    Ok(survey)
}

/// A dropped path and an added path holding exactly the same bytes.
///
/// Decision 0015: byte equality, never a similarity score. The `similar`
/// matcher is already here and would catch a rename that was also edited, and
/// reaching for it would be a heuristic recovering the connection 0008 built
/// the tree so that nothing would have to recover. So this misses `mv`
/// followed by an edit, and says nothing rather than guessing.
///
/// Only a one-to-one match is offered: two added paths holding one dropped
/// file's bytes is a choice nobody here is entitled to make. Empty content
/// matches nothing, since every empty file has the bytes of every other.
fn renames(
    store: &Store,
    parents: &[RevisionId],
    dropped: &BTreeMap<FileId, String>,
    arrived: &BTreeMap<String, Vec<u8>>,
) -> Result<Vec<(String, String)>, RecordError> {
    if dropped.is_empty() || arrived.is_empty() {
        return Ok(Vec::new());
    }

    let mut by_content: BTreeMap<&[u8], Vec<&str>> = BTreeMap::new();
    for (path, bytes) in arrived {
        if !bytes.is_empty() {
            by_content.entry(bytes.as_slice()).or_default().push(path);
        }
    }

    let mut gone: BTreeMap<Vec<u8>, Vec<&str>> = BTreeMap::new();
    for (file, path) in dropped {
        // Whichever kind the file is: an image moved with `mv` is the same
        // question a paragraph moved with `mv` is.
        let bytes = match store.content_at_heads(parents, file) {
            Ok(content) => content.bytes(),
            // A file whose content two branches disagree about is not a file
            // this can offer a rename for.
            Err(MaterialiseError::ContestedContent { .. }) => continue,
            Err(error) => return Err(error.into()),
        };
        if !bytes.is_empty() {
            gone.entry(bytes).or_default().push(path);
        }
    }

    let mut renames = Vec::new();
    for (bytes, from) in &gone {
        let Some(to) = by_content.get(bytes.as_slice()) else {
            continue;
        };
        if let ([from], [to]) = (from.as_slice(), to.as_slice()) {
            renames.push(((*from).to_owned(), (*to).to_owned()));
        }
    }
    Ok(renames)
}

/// The payload a file of bytes holds at these parents, if it holds one.
///
/// `None` where concurrent revisions each stated one: 0008 refuses to pick,
/// so what the folder holds now is the change, whatever it is.
fn held_bytes(
    store: &Store,
    parents: &[RevisionId],
    file: &FileId,
) -> Result<Option<Vec<u8>>, RecordError> {
    match store.content_at_heads(parents, file) {
        Ok(content) => Ok(Some(content.bytes())),
        Err(MaterialiseError::ContestedContent { .. }) => Ok(None),
        Err(error) => Err(error.into()),
    }
}

/// Work out what recording would state, without writing anything.
///
/// The survey with an identifier minted per added path, which is the whole of
/// the difference between describing a folder and recording one.
pub fn plan(
    store: &Store,
    working: &Working,
    recording: &Recording,
    entropy: &mut impl Entropy,
) -> Result<Plan, RecordError> {
    plan_with(store, working, recording, entropy, &BTreeMap::new())
}

/// The same, keeping identifiers a rewritten revision already minted.
///
/// Decision 0023: an amendment surveys the folder against its predecessor's
/// parents, where the files that predecessor *added* do not exist — so every
/// one of them surveys as added again, and minting afresh would make the same
/// file, in the same place, in the same piece of work, a different file after
/// every amendment. `kept` is that predecessor's `add` lines, by path, and
/// minting happens only for a path it does not name.
fn plan_with(
    store: &Store,
    working: &Working,
    recording: &Recording,
    entropy: &mut impl Entropy,
    kept: &BTreeMap<String, FileId>,
) -> Result<Plan, RecordError> {
    let surveyed = survey(
        store,
        working,
        &recording.parents,
        &recording.moves,
        &recording.at,
    )?;

    // Three things the survey reports and recording refuses. Decision 0015
    // puts the refusals here rather than in the walk, so that one command can
    // describe a folder another command will not take.
    if let Some((path, files)) = surveyed.unsettled.iter().next() {
        return Err(RecordError::Contested {
            path: path.clone(),
            files: files.clone(),
        });
    }
    if !surveyed.refused.is_empty() {
        return Err(RecordError::Refused {
            files: surveyed.refused.clone(),
        });
    }
    if !surveyed.standing.is_empty() {
        return Err(RecordError::Unresolved {
            files: surveyed.standing.clone(),
        });
    }

    let mut minted: BTreeMap<String, FileId> = BTreeMap::new();
    let mut added = BTreeMap::new();
    for path in &surveyed.added {
        let file = match kept.get(path) {
            Some(file) => *file,
            None => entropy.file()?,
        };
        minted.insert(path.clone(), file);
        added.insert(file, path.clone());
    }

    let mut edited = BTreeMap::new();
    for (path, document) in &surveyed.edited {
        let file = minted
            .get(path)
            .or_else(|| surveyed.held.get(path))
            .copied();
        if let Some(file) = file {
            edited.insert(file, document.clone());
        }
    }

    let mut paths: BTreeMap<FileId, String> = BTreeMap::new();
    for (path, file) in &surveyed.held {
        paths.insert(*file, path.clone());
    }
    for (file, path) in &added {
        paths.insert(*file, path.clone());
    }
    for (file, path) in &surveyed.dropped {
        paths.insert(*file, path.clone());
    }

    Ok(Plan {
        added,
        moved: surveyed.moved.clone(),
        dropped: surveyed.dropped.keys().copied().collect(),
        edited,
        paths,
        parents: surveyed.parents.clone(),
        survey: surveyed,
    })
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
    let plan = plan(store, working, recording, entropy)?;
    // A merge that states nothing still says something: these two lines of
    // work are one now, which is what `04-merge.rev` is and why it names no
    // operation document at all.
    if plan.is_empty() && recording.parents.len() < 2 {
        return Err(RecordError::NothingToRecord);
    }

    let change = entropy.change()?;

    let content = content_of(&plan);
    let document = RevisionDocument {
        version: Version::CURRENT,
        change,
        parents: recording.parents.iter().copied().collect(),
        supersedes: BTreeSet::new(),
        author: recording.author.clone(),
        when: recording.when.clone(),
        revised_by: None,
        revised: None,
        added: plan.added.clone(),
        moved: plan.moved.clone(),
        dropped: plan.dropped.clone(),
        edited: content.edited.clone(),
        text: content.text.clone(),
        bytes: content.bytes.clone(),
        extensions: BTreeMap::new(),
        message: recording.message.clone(),
    };

    // Decision 0019: the name a file is written under is the name it keeps, so
    // it is worked out before anything is written.
    let stem = naming::stem_for(
        &recording.when,
        &recording.message,
        &change,
        &document.id(),
        store.iter().map(|(_, held)| held),
    );
    file_content(store, &plan, &content, &stem)?;
    let revision = store.insert_at(&document, &format!("{stem}{REVISION_SUFFIX}"))?;

    // Decision 0011: a bookmark that named the parent's change follows the
    // work forward. A `revision` bookmark is the pin that must not move.
    let mut advanced = Vec::new();
    let followed: BTreeSet<ChangeId> = recording
        .parents
        .iter()
        .filter_map(|parent| store.get(parent).map(|document| document.change))
        .collect();
    let following: Vec<String> = store
        .names()
        .iter()
        .filter(|(_, target)| match target {
            Name::Change(change) => followed.contains(change),
            // A pin does not move, and decision 0024's file bookmark has
            // nothing to follow: an identifier outlives the revisions that
            // mention it.
            Name::Revision(_) | Name::File(_) => false,
        })
        .map(|(name, _)| name.clone())
        .collect();
    for name in following {
        store.set_name(&name, Name::Change(change))?;
        advanced.push(name);
    }

    Ok(Recorded {
        revision,
        change,
        plan,
        advanced,
    })
}

/// Work out what amending would state, without writing anything.
///
/// The refusals decision 0023 names happen here, so `--dry-run` meets them at
/// the same moment the real thing would.
pub fn amendment_plan(
    store: &Store,
    working: &Working,
    amendment: &Amendment,
    entropy: &mut impl Entropy,
) -> Result<Plan, RecordError> {
    Ok(rewrite(store, working, amendment, entropy)?.plan)
}

/// Rewrite one revision as the folder now stands, superseding it.
///
/// Decision 0023. The change, the author, the moment the work was first
/// recorded, and the parents are the amended revision's; `revised` is now;
/// everything else is worked out again from the folder against those parents,
/// by the survey `record` performs for the same reason.
pub fn amend(
    store: &mut Store,
    working: &Working,
    amendment: &Amendment,
    entropy: &mut impl Entropy,
) -> Result<Amended, RecordError> {
    let rewritten = rewrite(store, working, amendment, entropy)?;
    let Rewrite {
        plan,
        content,
        document,
        previous,
    } = rewritten;

    // Decision 0019's third tier is this command's: an amendment that reworded
    // nothing wants the name its predecessor already has, and only the digest
    // tells two revisions of one change apart.
    let stem = naming::stem_for(
        &document.when,
        &document.message,
        &document.change,
        &document.id(),
        store.iter().map(|(_, held)| held),
    );
    file_content(store, &plan, &content, &stem)?;
    let revision = store.insert_at(&document, &format!("{stem}{REVISION_SUFFIX}"))?;

    // Nothing follows the work forward here. A `change` bookmark already
    // resolves through supersession, and a `revision` bookmark is decision
    // 0011's exact pin, which an amendment is no more entitled to move than a
    // record is.
    Ok(Amended {
        revision,
        change: previous.change,
        superseded: amendment.revision,
        plan,
    })
}

/// One amendment worked out to the last byte, with nothing written.
///
/// Every refusal happens here, so `--dry-run` meets each of them at the moment
/// the real thing would — including the one that needs the finished document,
/// which is an amendment saying exactly what it is rewriting already says.
struct Rewrite {
    plan: Plan,
    content: Content,
    document: RevisionDocument,
    previous: RevisionDocument,
}

fn rewrite(
    store: &Store,
    working: &Working,
    amendment: &Amendment,
    entropy: &mut impl Entropy,
) -> Result<Rewrite, RecordError> {
    let (previous, recording, kept) = rewriting(store, amendment)?;
    let plan = plan_with(store, working, &recording, entropy, &kept)?;

    let content = content_of(&plan);
    let document = RevisionDocument {
        version: Version::CURRENT,
        change: previous.change,
        parents: previous.parents.clone(),
        supersedes: BTreeSet::from([amendment.revision]),
        author: previous.author.clone(),
        when: previous.when.clone(),
        // Decision 0005: written only when it differs from the author, since a
        // fact equal to another fact is a second spelling of it.
        revised_by: (amendment.reviser != previous.author).then(|| amendment.reviser.clone()),
        revised: Some(amendment.revised.clone()),
        added: plan.added.clone(),
        moved: plan.moved.clone(),
        dropped: plan.dropped.clone(),
        edited: content.edited.clone(),
        text: content.text.clone(),
        bytes: content.bytes.clone(),
        // 0023 carries the advisory headers forward: this writer cannot read
        // them, and dropping what it cannot read is the failure 0020 calls the
        // worst available.
        extensions: previous.extensions.clone(),
        message: recording.message.clone(),
    };
    if says_the_same(&document, &previous) {
        return Err(RecordError::NothingToAmend {
            revision: amendment.revision,
        });
    }

    Ok(Rewrite {
        plan,
        content,
        document,
        previous,
    })
}

/// The revision being rewritten, and what recording it again would be given.
///
/// Every refusal decision 0023 names is here, before anything reads the
/// folder: a revision this store does not hold, a revision something stands
/// on, and a revision something has already rewritten.
fn rewriting(
    store: &Store,
    amendment: &Amendment,
) -> Result<(RevisionDocument, Recording, BTreeMap<String, FileId>), RecordError> {
    let previous = store
        .get(&amendment.revision)
        .cloned()
        .ok_or(RecordError::NotHeld {
            revision: amendment.revision,
        })?;

    let standing: Vec<RevisionId> = store
        .iter()
        .filter(|(_, document)| document.parents.contains(&amendment.revision))
        .map(|(id, _)| *id)
        .collect();
    if !standing.is_empty() {
        return Err(RecordError::Followed {
            revision: amendment.revision,
            standing,
        });
    }

    let successors: Vec<RevisionId> = store
        .iter()
        .filter(|(_, document)| document.supersedes.contains(&amendment.revision))
        .map(|(id, _)| *id)
        .collect();
    if !successors.is_empty() {
        return Err(RecordError::AlreadyRewritten {
            revision: amendment.revision,
            successors,
        });
    }

    // Decision 0023: a rename is the fact 0011 says only a person can state,
    // so a recomputation cannot observe the one the amended revision already
    // states. Inherited as 0012's `--at` is — by identifier, against the tree
    // its parents hold — and overridden by any `--move` a person adds.
    let at: Vec<(FileId, String)> = previous
        .moved
        .iter()
        .map(|(file, path)| (*file, path.clone()))
        .collect();
    let mut kept: BTreeMap<String, FileId> = BTreeMap::new();
    for (file, path) in &previous.added {
        kept.entry(path.clone()).or_insert(*file);
    }

    let recording = Recording {
        parents: previous.parents.iter().copied().collect(),
        author: previous.author.clone(),
        when: previous.when.clone(),
        message: amendment
            .message
            .clone()
            .unwrap_or_else(|| previous.message.clone()),
        moves: amendment.moves.clone(),
        at,
    };
    Ok((previous, recording, kept))
}

/// The run one abandonment would supersede, without writing anything.
///
/// Decision 0013: the first version abandons a head, or a run ending at one,
/// and refuses anything else. The run is the named revision and everything
/// standing on it, and it must be a line — a fork means two branches where a
/// person named one, and a merge in it holds work that arrived from elsewhere,
/// which abandoning this run would silently take with it.
pub fn abandonment_plan(
    store: &Store,
    revision: &RevisionId,
) -> Result<Vec<RevisionId>, RecordError> {
    let mut run: Vec<RevisionId> = Vec::new();
    let mut current = *revision;
    loop {
        let document = store
            .get(&current)
            .ok_or(RecordError::NotHeld { revision: current })?;

        // A run member something already rewrote has a successor of its own,
        // and a tombstone would leave one piece of work superseded twice.
        let successors: Vec<RevisionId> = store
            .iter()
            .filter(|(_, held)| held.supersedes.contains(&current))
            .map(|(id, _)| *id)
            .collect();
        if !successors.is_empty() {
            return Err(RecordError::AlreadyRewritten {
                revision: current,
                successors,
            });
        }

        // Everything after the first must stand on the run and nothing else:
        // a second parent is work merged in from elsewhere, and it is not what
        // the person named.
        if let Some(previous) = run.last()
            && (document.parents.len() != 1 || !document.parents.contains(previous))
        {
            return Err(RecordError::JoinsOthers { revision: current });
        }
        run.push(current);

        let standing: Vec<RevisionId> = store
            .iter()
            .filter(|(_, held)| held.parents.contains(&current))
            .map(|(id, _)| *id)
            .collect();
        match standing.as_slice() {
            [] => break,
            [next] => current = *next,
            several => {
                return Err(RecordError::Forked {
                    revision: current,
                    standing: several.to_vec(),
                });
            }
        }
    }
    Ok(run)
}

/// Abandon a run of work, superseding it with a tombstone.
///
/// Decision 0013. The tombstone is an ordinary revision that states no facts:
/// its parents are the run's parents, so the abandoned content falls out of
/// the ancestry with nothing to undo. Its change is minted rather than
/// reused, which is what makes the old change `Abandoned` rather than merely
/// empty.
pub fn abandon(
    store: &mut Store,
    abandoning: &Abandoning,
    entropy: &mut impl Entropy,
) -> Result<Abandoned, RecordError> {
    // The message is required, inverting 0002's rule for exactly this command:
    // the question a tombstone raises — why is this gone — is asked by a
    // person who no longer has the work in front of them.
    if abandoning.message.trim().is_empty() {
        return Err(RecordError::NoReasonGiven);
    }

    let run = abandonment_plan(store, &abandoning.revision)?;
    let first = store
        .get(&abandoning.revision)
        .expect("the plan held it")
        .clone();

    let change = entropy.change()?;
    let document = RevisionDocument {
        version: Version::CURRENT,
        change,
        parents: first.parents.clone(),
        supersedes: run.iter().copied().collect(),
        author: abandoning.author.clone(),
        when: abandoning.when.clone(),
        revised_by: None,
        // A tombstone supersedes, and decision 0005 makes `revised` the moment
        // of every supersession. Here the work and the rewrite are one act, so
        // the two timestamps agree.
        revised: Some(abandoning.when.clone()),
        added: BTreeMap::new(),
        moved: BTreeMap::new(),
        dropped: BTreeSet::new(),
        edited: BTreeMap::new(),
        text: BTreeMap::new(),
        bytes: BTreeMap::new(),
        extensions: BTreeMap::new(),
        message: abandoning.message.clone(),
    };

    let stem = naming::stem_for(
        &abandoning.when,
        &abandoning.message,
        &change,
        &document.id(),
        store.iter().map(|(_, held)| held),
    );
    let revision = store.insert_at(&document, &format!("{stem}{REVISION_SUFFIX}"))?;

    // The tombstone stands where the abandoned revision stood, so a bookmark
    // that named the abandoned work follows it there — the rule `record`
    // applies to parents, applied to what was superseded. A pin stays put.
    let mut advanced = Vec::new();
    let followed: BTreeSet<ChangeId> = run
        .iter()
        .filter_map(|abandoned| store.get(abandoned).map(|held| held.change))
        .collect();
    let following: Vec<String> = store
        .names()
        .iter()
        .filter(|(_, target)| match target {
            Name::Change(named) => followed.contains(named),
            Name::Revision(_) | Name::File(_) => false,
        })
        .map(|(name, _)| name.clone())
        .collect();
    for name in following {
        store.set_name(&name, Name::Change(change))?;
        advanced.push(name);
    }

    Ok(Abandoned {
        revision,
        change,
        superseded: run,
        advanced,
    })
}

/// Whether two documents say the same thing about the same work.
///
/// `supersedes`, `revised`, and `revised-by` are set aside on both sides:
/// those three describe the rewrite rather than the work, so a revision that
/// differs by nothing else is one that reworded nothing and changed nothing.
fn says_the_same(left: &RevisionDocument, right: &RevisionDocument) -> bool {
    let bare = |document: &RevisionDocument| {
        let mut bare = document.clone();
        bare.supersedes = BTreeSet::new();
        bare.revised_by = None;
        bare.revised = None;
        bare
    };
    bare(left) == bare(right)
}

/// Everything a revision names, which is what its own digest covers.
///
/// Worked out before the revision is composed and before anything is written,
/// and deliberately without a name in it: a revision document says nothing
/// about what it is called, so what a revision *names* can be settled before
/// what any of it is *called* is — which is what lets a writer compare the
/// revision it would produce against one the store already holds, and what
/// lets 0019's third tier ask for a digest that does not exist yet.
struct Content {
    /// The operation document each edited file names.
    edited: BTreeMap<FileId, RevisionId>,
    /// The payload each created file names, which `text` spells.
    text: BTreeMap<FileId, RevisionId>,
    /// The payload each whole file names, which `bytes` spells.
    bytes: BTreeMap<FileId, RevisionId>,
    /// What is to be filed under the revision's directory, with its path.
    filings: Vec<naming::Filing>,
}

fn content_of(plan: &Plan) -> Content {
    let mut content = Content {
        edited: BTreeMap::new(),
        text: BTreeMap::new(),
        bytes: BTreeMap::new(),
        filings: Vec::new(),
    };
    for (file, held) in &plan.edited {
        let held_id = match held {
            Change::Operations(document) => digest(&document.write()),
            Change::Created(payload) | Change::Whole(payload) => digest(payload),
        };
        match held {
            Change::Operations(_) => content.edited.insert(*file, held_id),
            Change::Created(_) => content.text.insert(*file, held_id),
            Change::Whole(_) => content.bytes.insert(*file, held_id),
        };
        if let Some(path) = plan.paths.get(file) {
            content.filings.push(naming::Filing {
                held: held_id,
                path: path.clone(),
                document: matches!(held, Change::Operations(_)),
            });
        }
    }
    content
}

/// Write the documents and the payloads a revision names, before the revision.
///
/// Decision 0017's reasoning, which is 0011's: an interrupted record leaves
/// content nothing points at, which `check` calls a note, rather than a
/// revision naming content that is not there, which it reports as an error.
/// Decision 0019 is where each one goes — under the revision's own stem, at
/// the path it had.
fn file_content(
    store: &mut Store,
    plan: &Plan,
    content: &Content,
    stem: &str,
) -> Result<(), RecordError> {
    let filed = naming::filed(&content.filings);
    // A file the plan has no path for cannot be filed under one, so it keeps
    // the digest name decision 0003 makes the default.
    let name = |held: &RevisionId| match filed.get(held) {
        Some(name) => format!("{stem}/{name}"),
        None => held.to_string(),
    };
    for held in plan.edited.values() {
        match held {
            Change::Operations(document) => {
                store.insert_operation_at(document, &name(&digest(&document.write())))?;
            }
            Change::Created(payload) | Change::Whole(payload) => {
                store.insert_payload_at(payload, &name(&digest(payload)))?;
            }
        }
    }
    Ok(())
}

/// The one file at `path`, or a reason there is not exactly one.
///
/// Against where each file has been put rather than against the tree, so that
/// `--move` names a path as the revision being written currently has it. For a
/// record those are the same thing; for an amendment (0023) the second is the
/// path its predecessor's own `move` line already put the file at, which is
/// where the folder holds it and therefore what a person would type.
fn one_file_at(placed: &BTreeMap<FileId, String>, path: &str) -> Result<FileId, RecordError> {
    let claiming: Vec<FileId> = placed
        .iter()
        .filter(|(_, at)| at.as_str() == path)
        .map(|(file, _)| *file)
        .collect();
    match claiming.as_slice() {
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
    /// An amendment that would say exactly what it is rewriting says.
    NothingToAmend {
        /// The revision that already says it.
        revision: RevisionId,
    },
    /// A revision to be rewritten that this store does not hold.
    NotHeld {
        /// The revision as it was named.
        revision: RevisionId,
    },
    /// A revision to be rewritten that work already stands on.
    ///
    /// Decision 0023: restating a descendant's operations against a parent
    /// whose content moved is 0007's merge under another name, which is the
    /// wall 0011 and 0013 stopped at too.
    Followed {
        /// The revision that was asked for.
        revision: RevisionId,
        /// The revisions naming it as a parent.
        standing: Vec<RevisionId>,
    },
    /// A revision something has already superseded.
    AlreadyRewritten {
        /// The revision that was asked for.
        revision: RevisionId,
        /// What already rewrote it.
        successors: Vec<RevisionId>,
    },
    /// An abandonment with no reason on it.
    ///
    /// Decision 0013: the reason is the only thing a tombstone carries, so
    /// this is the one revision the format will not record without a message.
    NoReasonGiven,
    /// A run to abandon that forks, where a person named one line of work.
    Forked {
        /// The revision two lines of work stand on.
        revision: RevisionId,
        /// The revisions standing on it.
        standing: Vec<RevisionId>,
    },
    /// A run to abandon holding a merge, whose other side arrived from
    /// elsewhere and would silently fall out of the ancestry with it.
    JoinsOthers {
        /// The merge revision in the run.
        revision: RevisionId,
    },
    /// A merge whose contested files still hold what the renderer wrote.
    Unresolved {
        /// Each file, and how many marker lines still stand in it.
        files: Vec<(String, usize)>,
    },
    /// Paths the folder holds that the format cannot take.
    ///
    /// Every one of them at once, per decision 0015: the fix is a set of
    /// `skip` rules, and writing them one command at a time is the thing
    /// listing them avoids.
    Refused {
        /// Each path, and the short reason.
        files: Vec<(String, String)>,
    },
    /// A `skip` rule covering a path the tree already holds.
    ///
    /// Decision 0011: the walk excludes what `skipped.txt` names, so a rule over
    /// a tracked path makes the file look deleted, and the next record spells
    /// that as `drop` — a line asking for privacy quietly deleting history's
    /// copy of what it names. Refusing is the recoverable half.
    SkipsTracked {
        /// Each tracked path a rule covers.
        paths: Vec<String>,
    },
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
            RecordError::NothingToAmend { revision } => write!(
                f,
                "{} already says exactly this, and a revision superseding one \
                 identical to itself would mean nothing",
                revision.abbreviate(12)
            ),
            RecordError::NotHeld { revision } => write!(
                f,
                "this store does not hold the revision {revision}, so there is \
                 nothing here to rewrite"
            ),
            RecordError::Followed { revision, standing } => write!(
                f,
                "{} work stands on {}, and restating what {} did against a \
                 parent whose content moved is not built yet; only a revision \
                 nothing follows can be amended:{}",
                if standing.len() == 1 {
                    "some".to_owned()
                } else {
                    format!("{} lines of", standing.len())
                },
                revision.abbreviate(12),
                if standing.len() == 1 { "it" } else { "they" },
                standing
                    .iter()
                    .map(|id| format!("\n  {}", id.abbreviate(12)))
                    .collect::<String>()
            ),
            RecordError::AlreadyRewritten {
                revision,
                successors,
            } => write!(
                f,
                "{} has already been rewritten, and superseding it again would \
                 leave one change with two current revisions; amend what \
                 replaced it:{}",
                revision.abbreviate(12),
                successors
                    .iter()
                    .map(|id| format!("\n  {}", id.abbreviate(12)))
                    .collect::<String>()
            ),
            RecordError::NoReasonGiven => write!(
                f,
                "abandoning removes this work from what the history means, and \
                 the reason is the only thing the tombstone carries; say why \
                 with -m"
            ),
            RecordError::Forked { revision, standing } => write!(
                f,
                "{} lines of work stand on {}, and abandoning it would abandon \
                 all of them; name the one you mean, or abandon each in \
                 turn:{}",
                standing.len(),
                revision.abbreviate(12),
                standing
                    .iter()
                    .map(|id| format!("\n  {}", id.abbreviate(12)))
                    .collect::<String>()
            ),
            RecordError::JoinsOthers { revision } => write!(
                f,
                "{} joins work from another line, and abandoning it would take \
                 that work out of the ancestry too; abandon up to the merge, \
                 or the other line first",
                revision.abbreviate(12)
            ),
            RecordError::Unresolved { files } => write!(
                f,
                "concurrent work is still marked in {}; resolve {} and delete \
                 the lines historica wrote:{}",
                if files.len() == 1 {
                    "one file"
                } else {
                    "these files"
                },
                if files.len() == 1 { "it" } else { "them" },
                files
                    .iter()
                    .map(|(path, lines)| format!("\n  {path} ({lines} left)"))
                    .collect::<String>()
            ),
            RecordError::Refused { files } => write!(
                f,
                "{} the folder holds {} not something this format can record; \
                 rename or `skip` {} in `{}/{}`:{}",
                if files.len() == 1 {
                    "one file".to_owned()
                } else {
                    format!("{} files", files.len())
                },
                if files.len() == 1 { "is" } else { "are" },
                if files.len() == 1 { "it" } else { "them" },
                crate::store::STORE_DIR,
                crate::working::SKIPPED_FILE,
                files
                    .iter()
                    .map(|(path, because)| format!("\n  {path} ({because})"))
                    .collect::<String>()
            ),
            RecordError::SkipsTracked { paths } => write!(
                f,
                "`{}/{}` skips {} history already holds, so recording would \
                 spell {} as a deletion; delete the {} first and record that, \
                 or drop the rule — history holds what it holds:{}",
                crate::store::STORE_DIR,
                crate::working::SKIPPED_FILE,
                if paths.len() == 1 {
                    "a file".to_owned()
                } else {
                    format!("{} files", paths.len())
                },
                if paths.len() == 1 { "it" } else { "them" },
                if paths.len() == 1 { "file" } else { "files" },
                paths
                    .iter()
                    .map(|path| format!("\n  {path}"))
                    .collect::<String>()
            ),
            RecordError::NotInTheTree { path } => write!(
                f,
                "`{path}` is not a file this history holds, so nothing can be \
                 moved from it"
            ),
            RecordError::Contested { path, files } => write!(
                f,
                "{} files hold `{path}` here, so the path does not name one of \
                 them; say where each goes with --at:{}",
                files.len(),
                files
                    .iter()
                    .map(|file| format!("\n  --at {file}=<path>"))
                    .collect::<String>()
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
