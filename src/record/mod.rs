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
use crate::diff::{diff, resolve};
use crate::format::{
    LinkTarget, Mode, OperationDocument, ResolutionDocument, RevisionDocument, Timestamp,
    check_link_target, digest, nfc,
};
use crate::fs::Filesystem;
use crate::merge::Merged;
use crate::naming;
use crate::replay::State;
use crate::store::{MaterialiseError, Name, REVISION_SUFFIX, Store, StoreError};
use crate::tree::{Kind, Tree, TreeContest};
use crate::working::{Working, WorkingError};

pub mod carry;
pub mod identity;
pub mod source;

#[cfg(feature = "disk")]
pub use identity::author_for;
pub use identity::{Identities, IdentityError, author_for_on};
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
    /// Decision 0032's resolution: a merge's file, stated whole by reference,
    /// for a file its parents disagree about.
    Resolution(ResolutionDocument),
    /// The lines a file is created with, which `text` names.
    Created(Vec<u8>),
    /// A file's whole content, which `bytes` names — by digest.
    ///
    /// Decision 0067: the payload is named rather than carried, because a
    /// survey of a folder of photographs would otherwise hold every one of
    /// them at once, and because the bytes are already in a file that is not
    /// going anywhere. The recorder streams them out of the working copy at
    /// the moment it files them. A `text` payload beside it keeps its bytes,
    /// since decision 0007's items are its lines and every one of them is
    /// about to be named.
    Whole(RevisionId),
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
    /// A file the folder can run and the tree cannot, or the reverse.
    Mode,
    /// A link the folder points somewhere the tree does not.
    Link,
}

impl fmt::Display for Fact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // `f.pad` rather than `write_str`, so a column of these lines up.
        f.pad(match self {
            Fact::Added => "added",
            Fact::Moved => "moved",
            Fact::Dropped => "dropped",
            Fact::Edited => "edited",
            Fact::Mode => "mode",
            Fact::Link => "link",
        })
    }
}

/// Where a link points, as a survey can say it.
///
/// The same two spellings decision 0040 records, one step earlier: a reference
/// is a path here, because a survey mints nothing and the file at that path
/// may be one this record is adding.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Targeted {
    /// A path in the tree this revision states.
    Reference(String),
    /// A string, exactly as the folder holds it.
    Verbatim(String),
}

impl Targeted {
    /// What a person reading `status` or `diff` is shown.
    pub fn shown(&self) -> &str {
        match self {
            Targeted::Reference(path) | Targeted::Verbatim(path) => path.as_str(),
        }
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
    /// Files the folder gives a mode the tree does not, with that mode.
    ///
    /// Decision 0034: keyed by path, like everything a survey observes,
    /// because the identifier for an added file is not minted yet. A
    /// filesystem with no executable bit contributes nothing here, so a
    /// recorded mode survives a machine that cannot see it.
    pub modes: BTreeMap<String, Mode>,
    /// Links whose target this revision states, and what it states.
    ///
    /// Decision 0040: keyed by path like everything else a survey observes,
    /// and a reference is held as the *path* it resolved to, because the
    /// identifier of a file the same record is adding is not minted yet.
    /// [`plan`] is where a path becomes a file.
    pub links: BTreeMap<String, Targeted>,
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
    /// Paths a merge would have to empty, which no resolution can spell.
    ///
    /// Decision 0032's grammar has no resolution with no pieces, exactly as
    /// 0007's has no operation document with no operations. A merge that
    /// leaves a contested file with nothing in it is a merge and a deletion
    /// at once, and the second half belongs in the revision after.
    pub emptied: Vec<String>,
    /// Byte payloads whose selected parents state different content.
    ///
    /// There is no marker to find in a file of bytes. Decision 0028 requires a
    /// person to accept each path explicitly before a merge records what the
    /// folder happens to hold.
    pub contested_bytes: BTreeSet<String>,
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
            && self.modes.is_empty()
            && self.links.is_empty()
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
        // Decision 0034: a revision that states only a mode still states
        // something, and a fact `record` writes that `status` never mentioned
        // is what decision 0015 exists to prevent. A file being added carries
        // its mode in with it and needs no second line.
        facts.extend(
            self.modes
                .keys()
                .filter(|path| !self.added.contains(*path))
                .map(|path| (Fact::Mode, path.clone())),
        );
        // Decision 0040, on the same terms: a retarget is the whole of what
        // some revisions say, and a link arriving carries its target in with
        // its `add`.
        facts.extend(
            self.links
                .keys()
                .filter(|path| !self.added.contains(*path))
                .map(|path| (Fact::Link, path.clone())),
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
    /// Files whose mode this revision states, and what it states.
    pub modes: BTreeMap<FileId, Mode>,
    /// Links whose target this revision states, and what it states.
    pub links: BTreeMap<FileId, LinkTarget>,
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

/// Which paths a survey looks at.
///
/// Decision 0011 compares the whole folder with the tree, and that stays what
/// naming nothing means. Naming paths narrows what is *observed*: the paths
/// left out are not compared with anything, so nothing is recorded about them
/// and the next survey that does look sees whatever they hold. This is not an
/// index — there is nothing to remember between commands, because a
/// restriction is one argument list and lives exactly as long as it.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub enum Restriction {
    /// Every tracked path, which is `record` with no paths named.
    #[default]
    Everything,
    /// Only these paths, and everything beneath any that is a directory.
    Paths(BTreeSet<String>),
}

impl Restriction {
    /// Whether this looks at the whole folder.
    pub fn is_everything(&self) -> bool {
        matches!(self, Restriction::Everything)
    }

    /// Whether a path is one of the ones being looked at.
    ///
    /// A named directory covers everything beneath it, which is the rule
    /// `skipped.txt` spells with a trailing slash. There are no directories in
    /// this format — 0008 — so naming one can only mean the files under it.
    pub fn covers(&self, path: &str) -> bool {
        match self {
            Restriction::Everything => true,
            Restriction::Paths(paths) => paths.iter().any(|named| beneath(named, path)),
        }
    }

    /// Every path named, and nothing at all where the whole folder is meant.
    pub fn paths(&self) -> impl Iterator<Item = &String> {
        match self {
            Restriction::Everything => None,
            Restriction::Paths(paths) => Some(paths),
        }
        .into_iter()
        .flatten()
    }
}

/// Whether `path` is `named` or sits under it.
fn beneath(named: &str, path: &str) -> bool {
    path == named
        || path
            .strip_prefix(named)
            .is_some_and(|rest| rest.starts_with('/'))
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
    /// Contested byte payloads a person explicitly accepts from the folder.
    pub accepted: BTreeSet<String>,
    /// Which paths to look at, where a person named some.
    pub only: Restriction,
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

/// What a restriction refuses, before the folder is read.
///
/// Both refusals are here rather than only inside the survey, because a front
/// end performs a stated rename before it walks the folder, and a refusal that
/// waited for the survey would arrive after the folder had been rearranged.
pub fn check_restriction(recording: &Recording) -> Result<(), RecordError> {
    restricted(&recording.parents, &recording.moves, &recording.only)
}

fn restricted(
    parents: &[RevisionId],
    moves: &[(String, String)],
    only: &Restriction,
) -> Result<(), RecordError> {
    if only.is_everything() {
        return Ok(());
    }
    // Decision 0032: a merge states what each contested file is, all of them,
    // in the one revision that joins the work. Half of that is not a smaller
    // merge, it is a merge that lies about the files it left out.
    if parents.len() > 1 {
        return Err(RecordError::PartialMerge {
            paths: only.paths().cloned().collect(),
        });
    }
    // A restriction that spelled one end of a rename would record the other
    // end as a deletion, or as a file arriving from nowhere.
    for (from, to) in moves {
        if !only.covers(from) || !only.covers(to) {
            return Err(RecordError::HalfARename {
                from: from.clone(),
                to: to.clone(),
            });
        }
    }
    Ok(())
}

/// Work out what the folder says, without minting or writing anything.
///
/// The primitive decision 0015 makes this: everything expensive happens here,
/// and both `status` and `record` read the result rather than computing their
/// own. What a person stated — the parents, the renames, where a contested
/// file goes, and which paths to look at — is passed in, because those are the
/// things that cannot be observed.
pub fn survey<F: Filesystem>(
    store: &Store<F>,
    working: &Working<F>,
    parents: &[RevisionId],
    moves: &[(String, String)],
    at: &[(FileId, String)],
    only: &Restriction,
) -> Result<Survey, RecordError> {
    restricted(parents, moves, only)?;
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

    // A named path nothing answers to. Asked of the folder, of the tree, and
    // of where the stated renames put things, so that `--move a=b` with both
    // named finds `a` in the tree and `b` in the folder — and a path a rule
    // keeps out is told apart from a path nobody has, because the two have
    // different fixes.
    let mut absent: Vec<String> = Vec::new();
    let mut kept_out: Vec<String> = Vec::new();
    for named in only.paths() {
        let known = working.iter().any(|(path, _)| beneath(named, path))
            || tree.files().any(|(_, path)| beneath(named, path))
            || placed.values().any(|path| beneath(named, path));
        if known {
            continue;
        }
        if skipped.skips(named) || skipped.skips_directory(named) {
            kept_out.push(named.clone());
        } else {
            absent.push(named.clone());
        }
    }
    if !kept_out.is_empty() {
        return Err(RecordError::NamedButSkipped { paths: kept_out });
    }
    if !absent.is_empty() {
        return Err(RecordError::NothingAtPath { paths: absent });
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
            [one] => {
                held.insert(path.to_owned(), *one);
            }
            // A path nobody is looking at is a contest nobody has to settle
            // yet: `plan` refuses on this list, and refusing over a file this
            // record was never going to state would be the restriction
            // failing to restrict.
            several if only.covers(path) => {
                unsettled.insert(path.to_owned(), several.to_vec());
            }
            _ => {}
        }
    }

    let mut survey = Survey {
        moved,
        contested,
        unsettled,
        parents: parents.to_vec(),
        // A file the format cannot take stops a record, so a restriction that
        // did not narrow this would let a symlink in a corner of the folder
        // refuse a record about one file elsewhere.
        refused: working
            .refused()
            .iter()
            .filter(|(path, _)| only.covers(path))
            .cloned()
            .collect(),
        ..Survey::default()
    };

    // Kept only for the paths that turn out to be added, since that is the
    // only place the bytes are wanted twice.
    let mut arrived: BTreeMap<String, RevisionId> = BTreeMap::new();
    // The target each link on disk spells, before resolution — which cannot
    // happen until the whole folder has been walked, because decision 0040
    // resolves against the tree *this revision states* and a target added by
    // the same record has to resolve.
    let mut pointing: BTreeMap<String, String> = BTreeMap::new();

    // A path in the folder is either a file the tree already holds, or a file
    // nobody has recorded yet, which recording mints an identifier for.
    for (path, _) in working.iter() {
        // A path outside the restriction is not compared with anything, which
        // is what leaves it exactly as unrecorded as it was.
        if !only.covers(path) {
            continue;
        }
        if survey.unsettled.contains_key(path.as_str()) {
            continue;
        }
        let mut file = held.get(path.as_str()).copied();

        // Decision 0040: a link is a third kind of file, fixed at `add`, so a
        // path that changed between a link and a file is a `drop` and an
        // `add` — the same answer 0017 gives a file whose content model
        // changed, and for the same reason.
        let was = file.and_then(|file| tree.kind(&file));
        if let Some(previous) = file
            && working.is_link(path) != (was == Some(Kind::Link))
        {
            survey.dropped.insert(previous, path.clone());
            survey.moved.remove(&previous);
            file = None;
        }
        if file.is_none() {
            survey.added.insert(path.clone());
        }

        if working.is_link(path) {
            match working.link_target(path) {
                Some(target) => {
                    if let Err(unusable) = check_link_target(target) {
                        survey.refused.push((
                            path.clone(),
                            format!("it points at a target this format cannot hold: {unusable}"),
                        ));
                        survey.added.remove(path);
                        continue;
                    }
                    pointing.insert(path.clone(), target.to_owned());
                }
                // Decision 0034's rule, doing decision 0040's work: a
                // filesystem blind to the fact states nothing about it and
                // leaves the recorded target standing. A link nobody has
                // recorded yet cannot be added that way, because there is
                // nothing to leave standing.
                None if file.is_none() => {
                    survey.refused.push((
                        path.clone(),
                        "a link this folder reports and cannot read".to_owned(),
                    ));
                    survey.added.remove(path);
                }
                None => {}
            }
            continue;
        }

        // Decision 0034, before the kinds part company: a mode is a fact about
        // a file rather than about its content, so a photograph has one for
        // the same reasons a script does. `None` from the filesystem means it
        // has no such bit, and the recorded value stands.
        if let Some(executable) = working.executable(path)? {
            let observed = Mode::of(executable);
            let recorded = file.and_then(|file| tree.mode(&file)).unwrap_or_default();
            if observed != recorded {
                survey.modes.insert(path.clone(), observed);
            }
        }

        // A file nobody has recorded yet is read, and has to be: its own bytes
        // decide which kind of file it is (0017), and nothing is being
        // compared, so there is no digest that would answer instead. Decision
        // 0067 makes the read a pass rather than a buffer — the sniff and the
        // digest are taken together, and only a file that turns out to be
        // lines is still in memory when it finishes.
        let Some(file) = file else {
            let (found, text) = working.sniff(path)?;
            arrived.insert(path.clone(), found);
            // Decision 0017: valid UTF-8 with no NUL is lines and everything
            // else is bytes, sniffed once, here, and never again.
            let Some(bytes) = text else {
                survey.edited.insert(path.clone(), Change::Whole(found));
                continue;
            };
            // A file being created states its lines outright rather than as an
            // insert of every one of them, which is decision 0017's whole
            // point. Nothing before it exists to compare against.
            if !bytes.is_empty() {
                survey.edited.insert(path.clone(), Change::Created(bytes));
            }
            continue;
        };

        // Decision 0017: a file the tree holds is addressed as the kind it was
        // added as. `placed` is built from the tree, so the entry is there.
        let Some(kind) = tree.kind(&file) else {
            debug_assert!(false, "a placed file the tree does not hold");
            continue;
        };
        debug_assert_ne!(kind, Kind::Link, "a link left the walk above");

        if kind == Kind::Whole {
            // Nothing to compare line by line, so the comparison is the whole
            // of it — and decision 0043 makes it a comparison of digests
            // rather than of bytes. The tree already *states* the payload this
            // file holds (0017's `bytes <file> <digest>`), so an unchanged
            // photograph is settled without either copy of it being read.
            let recorded = if parents.is_empty() {
                None
            } else {
                match tree.entry(&file).and_then(|entry| entry.payload) {
                    Some(payload) => Some(payload),
                    // 0008 calls two concurrent `bytes` a divergence to report
                    // rather than a winner to pick, which is what an absent
                    // payload on a file the tree holds means.
                    None => {
                        survey.contested_bytes.insert(path.clone());
                        None
                    }
                }
            };
            if recorded == Some(working.digest(path)?) {
                continue;
            }
            // Read, and then asked again: what the folder holds is what the
            // read found, whatever `cache/working.txt` said about it. So a
            // catalogue that was wrong about this file costs this one read and
            // states nothing. Decision 0067: the read is a hash of the pieces,
            // so a changed photograph is settled without a copy of it existing
            // anywhere but on disk.
            let found = working.reread_digest(path)?;
            if recorded == Some(found) {
                continue;
            }
            survey.edited.insert(path.clone(), Change::Whole(found));
            continue;
        }

        // Decision 0032 splits what a merge says about a file in two. Where
        // the parents leave it identically there is nothing to resolve, and
        // the merge states a delta against that agreed state or nothing at
        // all. Where they differ the merge owes a resolution, and the walk is
        // demoted to what proposes one.
        let joined = if parents.is_empty() {
            Joined::Agreed(State::empty())
        } else if joining {
            joined_content(store, parents, &file)?
        } else {
            Joined::Agreed(store.content(&parents[0], &file)?)
        };

        // Decision 0043 again, on the other kind of file: where the parents
        // agree, what this revision has to say about the file is nothing at
        // all if the folder holds what they left — and that is a comparison of
        // digests, so the file is not opened. A merge is excluded, because a
        // proposed resolution has to be stated whether or not the folder
        // matches it.
        if let Joined::Agreed(before) = &joined
            && before.digest() == working.digest(path)?
        {
            continue;
        }

        // Read, and hashed as it is read, for the reason the whole branch
        // above is: a catalogue that spoke wrongly for this path is corrected
        // by the read it caused, and `diff` below says nothing about a file
        // that turns out not to have changed.
        let text = match working.text_and_digest(path) {
            Ok((text, _)) => text,
            // 0015: a refusal is a line of the report rather than the end of
            // it. 0017 narrows what is refused to this one case — a file
            // recorded as lines that no longer holds any.
            Err(WorkingError::NotText { .. }) => {
                let refusal = WorkingError::NotText { path: path.clone() };
                survey.refused.push((path.clone(), refusal.because()));
                survey.modes.remove(path);
                continue;
            }
            Err(error) => return Err(error.into()),
        };

        let after = State::from_text(&text);
        match joined {
            Joined::Agreed(before) => {
                if let Some(document) = diff(&before, &after) {
                    survey
                        .edited
                        .insert(path.clone(), Change::Operations(document));
                }
            }
            Joined::Proposed(merged) => {
                // Decision 0012: while recording a merge, a contested file
                // holding any line the renderer wrote is refused — per line,
                // because a person can edit inside a fence and leave it
                // standing. Here it is counted; `plan` is what refuses.
                if !merged.contested.is_empty() {
                    let standing = crate::conflict::unresolved(&merged, &text);
                    if !standing.is_empty() {
                        survey.standing.push((path.clone(), standing.len()));
                        continue;
                    }
                }
                match resolve(&merged.state, &merged.references, &after) {
                    Some(resolution) => {
                        survey
                            .edited
                            .insert(path.clone(), Change::Resolution(resolution));
                    }
                    // The grammar has no spelling for a file with no pieces,
                    // so a merge cannot be the revision that empties one.
                    None => survey.emptied.push(path.clone()),
                }
            }
        }
    }

    // A file the tree holds and the folder does not is gone, which is a fact
    // rather than a guess — decision 0011's reason for having no `--drop`.
    for (file, path) in &placed {
        if !only.covers(path) {
            continue;
        }
        if !working.holds(path) {
            survey.dropped.insert(*file, path.clone());
            survey.moved.remove(file);
        }
    }

    // Decision 0040's resolution, once the whole folder is known. The tree
    // this revision states is `placed` less what it drops, plus what it adds —
    // so a link pointing at a file arriving in the same record resolves to it,
    // and a link pointing at a file leaving in the same record does not.
    let mut stated: BTreeMap<&str, Option<FileId>> = BTreeMap::new();
    for (file, path) in &placed {
        if survey.dropped.contains_key(file) {
            continue;
        }
        stated.insert(path.as_str(), Some(*file));
    }
    for path in &survey.added {
        stated.insert(path.as_str(), None);
    }

    for (path, spelling) in &pointing {
        // What the recorded fact spells at the parent: the arithmetic `update`
        // does, done where the last `update` did it. A string equal to that is
        // not an observation of anything — 0034's reasoning about a machine
        // blind to a fact, here about a person who touched nothing — so the
        // recorded target stands and this revision says nothing about it.
        //
        // This is what keeps a reference through a move of its *target*: `mv`
        // never rewrites the links pointing at what it moved, so the folder
        // goes on spelling the old path, which resolves to nothing in the tree
        // this revision states. Resolving it would demote the reference to
        // that dead string — a retarget nobody made, undoing the one property
        // the reference exists for, at the moment it earns its keep.
        if standing(&tree, &held, &survey.dropped, path).as_deref() == Some(spelling.as_str()) {
            continue;
        }
        let observed = match resolution(path, spelling) {
            Some(at) if stated.contains_key(at.as_str()) => Targeted::Reference(at),
            // Escaping the folder, absolute, or naming nothing this history
            // holds: the honest record is the string a person chose.
            _ => Targeted::Verbatim(spelling.clone()),
        };
        // What the tree says now, spelled the same way, so that "did this
        // change" is one comparison rather than two shapes of one.
        let recorded = held
            .get(path.as_str())
            .filter(|file| !survey.dropped.contains_key(file))
            .and_then(|file| tree.target(file))
            .and_then(|target| match target {
                LinkTarget::Verbatim(spelling) => Some(Targeted::Verbatim(spelling.clone())),
                // A reference whose file this record drops is a reference
                // about to be false, and there is nothing to agree with: the
                // restatement below is the whole point of asking.
                LinkTarget::Reference(named) if survey.dropped.contains_key(named) => None,
                LinkTarget::Reference(named) => placed.get(named).cloned().map(Targeted::Reference),
            });
        if recorded.as_ref() != Some(&observed) {
            survey.links.insert(path.clone(), observed);
        }
    }

    // The dangling-reference rule, from the other end. The survey satisfies
    // `tree::apply` without anyone's help wherever it can see the link — the
    // link resolves to nothing tracked and is restated verbatim above — so
    // what is left here is a link this record was not looking at, which no
    // restatement can reach.
    for (file, path) in &placed {
        if survey.dropped.contains_key(file) || pointing.contains_key(path) {
            continue;
        }
        let Some(named) = tree.target(file).and_then(LinkTarget::reference) else {
            continue;
        };
        if let Some(gone) = survey.dropped.get(&named) {
            return Err(RecordError::WouldDangle {
                link: path.clone(),
                target: gone.clone(),
            });
        }
    }

    survey.renames = renames(store, parents, &survey.dropped, &arrived)?;
    survey.held = held;
    // Decision 0043: one write, here, where the folder has finished being
    // asked. A survey that wrote after every question would rewrite the whole
    // catalogue once per file, which is quadratic in the size of the folder —
    // and a survey that never wrote one would leave the next command doing
    // exactly this work again.
    working.remember();
    Ok(survey)
}

/// What the recorded link at a path spells, materialised at the parent.
///
/// Decision 0040's materialisation, run backwards: the string the last
/// `update` wrote into the folder for the fact the parent states. The
/// recorder resolves only what differs from this, because a folder holding
/// exactly what it was given is a folder nobody changed, and a fact stated
/// about it is a fact nobody made.
///
/// `None` where no link is recorded here, where this record drops it, or —
/// the one case that matters — where this record drops the file a reference
/// names. That drop owes the mandatory verbatim restatement of 0040's "When
/// the target is dropped", which takes precedence over any silence: an
/// unchanged string is only an unchanged fact while the fact is still one the
/// resulting tree can hold.
fn standing(
    tree: &Tree,
    held: &BTreeMap<String, FileId>,
    dropped: &BTreeMap<FileId, String>,
    path: &str,
) -> Option<String> {
    let file = held.get(path).filter(|file| !dropped.contains_key(file))?;
    let target = tree.target(file)?;
    if let LinkTarget::Reference(named) = target
        && dropped.contains_key(named)
    {
        return None;
    }
    // Spelled from where the link sat at the parent, since that is where the
    // arithmetic was done: a `mv` of the link itself no more rewrites its own
    // string than a `mv` of the target rewrites the links pointing at it.
    crate::update::materialise(tree, tree.path(file)?, target)
}

/// Where a link's target lands, as a store path, or `None` where it lands
/// outside this history's reach.
///
/// Decision 0040: lexical, against the tree, never against the filesystem.
/// The target is joined to the link's own directory, `.` and `..` are folded as
/// text, and the result takes 0033's normal form C — it is claiming to be a
/// store path now, so it is spelled as one. What lexical folding gets wrong —
/// a `..` walked through a directory that is itself a link on some machine —
/// is exactly the machine-dependence that makes such a target *outside* this
/// history, and it comes back `None`, correctly.
fn resolution(link: &str, target: &str) -> Option<String> {
    // A person who spelled an absolute path said something about a machine,
    // and rewriting it into a reference would change what the folder said.
    if target.starts_with('/') {
        return None;
    }
    // A target naming a directory names no file, and there are no directories
    // in this format for it to name.
    if target.ends_with('/') {
        return None;
    }
    let mut at: Vec<&str> = match link.rsplit_once('/') {
        Some((directory, _)) => directory.split('/').collect(),
        None => Vec::new(),
    };
    for component in target.split('/') {
        match component {
            "" | "." => {}
            ".." => {
                // Above the folder, which is outside this history by
                // construction.
                at.pop()?;
            }
            component => at.push(component),
        }
    }
    if at.is_empty() {
        return None;
    }
    Some(nfc(&at.join("/")).into_owned())
}

/// What a merge's parents leave one file as.
///
/// Decision 0032's two cases, and which one it is decides what the merge may
/// state: an agreed file takes a delta or nothing, and a disagreed one takes
/// a resolution and nothing else.
enum Joined {
    /// Every parent leaves the file exactly here.
    Agreed(State),
    /// They differ, so the merge owes a resolution. This is what the walk
    /// proposes, which is the draft a person edits.
    Proposed(Box<Merged>),
}

/// What the parents leave one file as, for a merge being recorded.
///
/// The parents' states come from decision 0032's reader — arithmetic and
/// reference-following — rather than from the walk, because "where the
/// parents' states for a file are identical" is a claim about what each side
/// *is*, which is exactly what the reader answers.
fn joined_content<F: Filesystem>(
    store: &Store<F>,
    parents: &[RevisionId],
    file: &FileId,
) -> Result<Joined, RecordError> {
    let mut agreed: Option<State> = None;
    for parent in parents {
        // A side whose history never mentions the file disagrees with nobody
        // about it: the tree decides whether the file exists, and 0008
        // already has that rule.
        let Some(state) = store.content_of(parent, file)? else {
            continue;
        };
        match &agreed {
            Some(held) if held == &state => {}
            None => agreed = Some(state),
            Some(_) => {
                return Ok(Joined::Proposed(Box::new(
                    store.merged_content_of(parents, file)?,
                )));
            }
        }
    }
    Ok(Joined::Agreed(agreed.unwrap_or_else(State::empty)))
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
///
/// Byte equality is asked as digest equality, decision 0067: a file's digest is
/// the one thing about it this whole format takes for its identity, both sides
/// of the comparison already have one, and a match that put two photographs in
/// memory to confirm what two numbers said would be the arithmetic done twice.
fn renames<F: Filesystem>(
    store: &Store<F>,
    parents: &[RevisionId],
    dropped: &BTreeMap<FileId, String>,
    arrived: &BTreeMap<String, RevisionId>,
) -> Result<Vec<(String, String)>, RecordError> {
    if dropped.is_empty() || arrived.is_empty() {
        return Ok(Vec::new());
    }

    let empty = digest(b"");
    let mut by_content: BTreeMap<RevisionId, Vec<&str>> = BTreeMap::new();
    for (path, found) in arrived {
        if *found != empty {
            by_content.entry(*found).or_default().push(path);
        }
    }

    let mut gone: BTreeMap<RevisionId, Vec<&str>> = BTreeMap::new();
    for (file, path) in dropped {
        // Whichever kind the file is: an image moved with `mv` is the same
        // question a paragraph moved with `mv` is.
        let found = match store.content_at_heads(parents, file) {
            Ok(content) => content.digest(),
            // A file whose content two branches disagree about is not a file
            // this can offer a rename for, and neither is a link: decision
            // 0040 gives it a target where the bytes would be, and two links
            // pointing the same way are not one link that moved.
            Err(MaterialiseError::ContestedContent { .. } | MaterialiseError::IsALink { .. }) => {
                continue;
            }
            Err(error) => return Err(error.into()),
        };
        if found != empty {
            gone.entry(found).or_default().push(path);
        }
    }

    let mut renames = Vec::new();
    for (found, from) in &gone {
        let Some(to) = by_content.get(found) else {
            continue;
        };
        if let ([from], [to]) = (from.as_slice(), to.as_slice()) {
            renames.push(((*from).to_owned(), (*to).to_owned()));
        }
    }
    Ok(renames)
}

/// Work out what recording would state, without writing anything.
///
/// The survey with an identifier minted per added path, which is the whole of
/// the difference between describing a folder and recording one.
pub fn plan<F: Filesystem>(
    store: &Store<F>,
    working: &Working<F>,
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
fn plan_with<F: Filesystem>(
    store: &Store<F>,
    working: &Working<F>,
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
        &recording.only,
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
    if !surveyed.emptied.is_empty() {
        return Err(RecordError::EmptiedByMerge {
            paths: surveyed.emptied.clone(),
        });
    }
    let unaccepted: Vec<String> = surveyed
        .contested_bytes
        .difference(&recording.accepted)
        .cloned()
        .collect();
    if !unaccepted.is_empty() {
        return Err(RecordError::UnacceptedAttachments { paths: unaccepted });
    }
    let unnecessary: Vec<String> = recording
        .accepted
        .difference(&surveyed.contested_bytes)
        .cloned()
        .collect();
    if !unnecessary.is_empty() {
        return Err(RecordError::NothingToAccept { paths: unnecessary });
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

    let mut modes = BTreeMap::new();
    for (path, mode) in &surveyed.modes {
        let file = minted
            .get(path)
            .or_else(|| surveyed.held.get(path))
            .copied();
        if let Some(file) = file {
            modes.insert(file, *mode);
        }
    }

    // Decision 0040: a reference the survey held as a path becomes the file at
    // that path, which is where the identifiers minted above are what makes a
    // link to a file arriving in the same record spellable at all.
    let mut links = BTreeMap::new();
    for (path, target) in &surveyed.links {
        let file = minted
            .get(path)
            .or_else(|| surveyed.held.get(path))
            .copied();
        let Some(file) = file else { continue };
        let target = match target {
            Targeted::Verbatim(spelling) => LinkTarget::Verbatim(spelling.clone()),
            Targeted::Reference(at) => match minted.get(at).or_else(|| surveyed.held.get(at)) {
                Some(named) => LinkTarget::Reference(*named),
                // A path no single file answers to — two claim it, and this
                // record is not the one settling that. There is no identity
                // to point at, so the string is the honest record.
                None => LinkTarget::Verbatim(at.clone()),
            },
        };
        links.insert(file, target);
    }

    Ok(Plan {
        added,
        moved: surveyed.moved.clone(),
        dropped: surveyed.dropped.keys().copied().collect(),
        edited,
        modes,
        links,
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
pub fn record<F: Filesystem>(
    store: &mut Store<F>,
    working: &Working<F>,
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
        change,
        parents: recording.parents.iter().copied().collect(),
        supersedes: BTreeSet::new(),
        author: recording.author.clone(),
        when: recording.when.clone(),
        revised_by: None,
        revised: None,
        added: plan.added.clone(),
        moved: plan.moved.clone(),
        modes: plan.modes.clone(),
        links: plan.links.clone(),
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
        store.documents()?.into_iter().map(|(_, held)| held),
    );
    file_content(store, working, &plan, &content, &stem)?;
    let revision = store.insert_at(&document, &format!("{stem}{REVISION_SUFFIX}"))?;

    // Decision 0011: a bookmark that named the parent's change follows the
    // work forward. A `revision` bookmark is the pin that must not move.
    let mut advanced = Vec::new();
    let followed: BTreeSet<ChangeId> = recording
        .parents
        .iter()
        .filter_map(|parent| store.revision(parent).map(|revision| revision.change))
        .collect();
    let following: Vec<String> = store
        .names()
        .iter()
        .filter(|(_, bookmark)| match bookmark.target {
            Name::Change(change) => followed.contains(&change),
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
pub fn amendment_plan<F: Filesystem>(
    store: &Store<F>,
    working: &Working<F>,
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
pub fn amend<F: Filesystem>(
    store: &mut Store<F>,
    working: &Working<F>,
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
        store.documents()?.into_iter().map(|(_, held)| held),
    );
    file_content(store, working, &plan, &content, &stem)?;
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

fn rewrite<F: Filesystem>(
    store: &Store<F>,
    working: &Working<F>,
    amendment: &Amendment,
    entropy: &mut impl Entropy,
) -> Result<Rewrite, RecordError> {
    let (previous, recording, kept) = rewriting(store, amendment)?;
    let plan = plan_with(store, working, &recording, entropy, &kept)?;

    let content = content_of(&plan);
    let document = RevisionDocument {
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
        modes: plan.modes.clone(),
        links: plan.links.clone(),
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
fn rewriting<F: Filesystem>(
    store: &Store<F>,
    amendment: &Amendment,
) -> Result<(RevisionDocument, Recording, BTreeMap<String, FileId>), RecordError> {
    let previous = store
        .get(&amendment.revision)?
        .cloned()
        .ok_or(RecordError::NotHeld {
            revision: amendment.revision,
        })?;

    let standing: Vec<RevisionId> = store
        .revisions()
        .filter(|(_, revision)| revision.parents.contains(&amendment.revision))
        .map(|(id, _)| *id)
        .collect();
    if !standing.is_empty() {
        return Err(RecordError::Followed {
            revision: amendment.revision,
            standing,
        });
    }

    let successors: Vec<RevisionId> = store
        .revisions()
        .filter(|(_, revision)| revision.supersedes.contains(&amendment.revision))
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
        accepted: BTreeSet::new(),
        // Decision 0023: an amendment restates the whole of what its
        // predecessor said, so there is no half of the folder it could be
        // asked about.
        only: Restriction::Everything,
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
pub fn abandonment_plan<F: Filesystem>(
    store: &Store<F>,
    revision: &RevisionId,
) -> Result<Vec<RevisionId>, RecordError> {
    let mut run: Vec<RevisionId> = Vec::new();
    let mut current = *revision;
    loop {
        let document = store
            .revision(&current)
            .ok_or(RecordError::NotHeld { revision: current })?;

        // A run member something already rewrote has a successor of its own,
        // and a tombstone would leave one piece of work superseded twice.
        let successors: Vec<RevisionId> = store
            .revisions()
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
            .revisions()
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
pub fn abandon<F: Filesystem>(
    store: &mut Store<F>,
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
    // A tombstone stands where the abandoned revision stood, which is a fact
    // about the graph and not about what that revision did.
    let first = store
        .revision(&abandoning.revision)
        .expect("the plan held it")
        .clone();

    let change = entropy.change()?;
    let document = RevisionDocument {
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
        modes: BTreeMap::new(),
        links: BTreeMap::new(),
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
        store.documents()?.into_iter().map(|(_, held)| held),
    );
    let revision = store.insert_at(&document, &format!("{stem}{REVISION_SUFFIX}"))?;

    // The tombstone stands where the abandoned revision stood, so a bookmark
    // that named the abandoned work follows it there — the rule `record`
    // applies to parents, applied to what was superseded. A pin stays put.
    let mut advanced = Vec::new();
    let followed: BTreeSet<ChangeId> = run
        .iter()
        .filter_map(|abandoned| store.revision(abandoned).map(|held| held.change))
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
            Change::Resolution(document) => digest(&document.write()),
            Change::Created(payload) => digest(payload),
            Change::Whole(payload) => *payload,
        };
        match held {
            // Decision 0032: an `edit` line names either grammar, because
            // both say what the file is at this revision.
            Change::Operations(_) | Change::Resolution(_) => content.edited.insert(*file, held_id),
            Change::Created(_) => content.text.insert(*file, held_id),
            Change::Whole(_) => content.bytes.insert(*file, held_id),
        };
        if let Some(path) = plan.paths.get(file) {
            content.filings.push(naming::Filing {
                held: held_id,
                path: path.clone(),
                document: matches!(held, Change::Operations(_) | Change::Resolution(_)),
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
/// A `bytes` payload is the one thing here that is not already in memory, and
/// decision 0067 keeps it that way: the folder's own copy is streamed into the
/// store at this moment, hashed on the way past, and never assembled. That is
/// why this takes the working copy — the survey said which digest each file
/// holds, and the file holding it is still where the survey found it.
fn file_content<F: Filesystem>(
    store: &mut Store<F>,
    working: &Working<F>,
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
    for (file, held) in &plan.edited {
        match held {
            Change::Operations(document) => {
                store.insert_operation_at(document, &name(&digest(&document.write())))?;
            }
            Change::Resolution(document) => {
                store.insert_resolution_at(document, &name(&digest(&document.write())))?;
            }
            Change::Created(payload) => {
                store.insert_payload_at(payload, &name(&digest(payload)))?;
            }
            Change::Whole(payload) => {
                // Where the folder holds it, in the folder's own spelling —
                // decision 0033's reason, and the walk already found it.
                let at = plan
                    .paths
                    .get(file)
                    .ok_or(RecordError::NoPathForContent { file: *file })?;
                let on_disk = working.on_disk(at);
                store.insert_payload_from(
                    working.filesystem(),
                    &on_disk,
                    payload,
                    &name(payload),
                )?;
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
    /// A file whose content is in the folder, and which the plan puts nowhere.
    ///
    /// Decision 0067: a `bytes` payload is streamed out of the working copy as
    /// it is filed, so a plan that states one without saying where the file
    /// sits states content nothing can fetch. Nothing produces this — every
    /// path in `edited` is a path the survey walked — and it is an error
    /// rather than a `debug_assert` because the alternative is writing a
    /// revision that names bytes no one has.
    NoPathForContent {
        /// The file in question.
        file: FileId,
    },
    /// A merge that would leave a contested file with nothing in it.
    ///
    /// Decision 0032: a resolution states what the file *is*, and the grammar
    /// has no spelling for a file that is nothing.
    EmptiedByMerge {
        /// The paths in question.
        paths: Vec<String>,
    },
    /// A `drop` that would leave a link this record is not looking at
    /// pointing at a file the tree no longer holds.
    ///
    /// Decision 0040: the survey restates such a link verbatim in the same
    /// revision, and can do so for every link it is looking at. A restriction
    /// that names the target and not the link is the one way to ask for the
    /// drop without the restatement.
    WouldDangle {
        /// The link, where it sits.
        link: String,
        /// The file it points at, where that sat.
        target: String,
    },
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
    /// Contested byte payloads a person has not explicitly accepted.
    UnacceptedAttachments {
        /// Every path requiring `--accept`.
        paths: Vec<String>,
    },
    /// An acceptance naming a path whose selected parents do not contest bytes.
    NothingToAccept {
        /// Every unnecessary path.
        paths: Vec<String>,
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
    /// A named path neither the folder nor the history holds.
    NothingAtPath {
        /// Every path nothing answers to.
        paths: Vec<String>,
    },
    /// A named path a `skip` rule covers.
    ///
    /// Naming a path says which of the observable files to observe, and a
    /// skipped file is not one of them. Decision 0011: what history takes is
    /// the repository's rule rather than one command line's.
    NamedButSkipped {
        /// Every named path a rule covers.
        paths: Vec<String>,
    },
    /// A merge restricted to some of the files it joins.
    PartialMerge {
        /// The paths that were named.
        paths: Vec<String>,
    },
    /// A stated rename with one end outside the paths being surveyed.
    HalfARename {
        /// Where the file was.
        from: String,
        /// Where it is now.
        to: String,
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
            RecordError::NoPathForContent { file } => write!(
                f,
                "{file} states whole content and no path, so there is nowhere \
                 to read its bytes from"
            ),
            RecordError::WouldDangle { link, target } => write!(
                f,
                "`{target}` is going, and `{link}` is a link to it that this record is not \
                 looking at; name `{link}` too, so its target can be written down as the \
                 string it will be"
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
            RecordError::EmptiedByMerge { paths } => write!(
                f,
                "a merge states what each contested file is, and there is no way to state \
                 that one is empty; leave {} something and remove it in the revision \
                 after, or drop it here:{}",
                if paths.len() == 1 { "it" } else { "them" },
                paths
                    .iter()
                    .map(|path| format!("\n  {path}"))
                    .collect::<String>()
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
            RecordError::UnacceptedAttachments { paths } => write!(
                f,
                "concurrent work states different bytes for {}; inspect {} and \
                 explicitly accept what the folder holds:{}",
                if paths.len() == 1 {
                    "one attachment"
                } else {
                    "these attachments"
                },
                if paths.len() == 1 { "it" } else { "them" },
                paths
                    .iter()
                    .map(|path| format!("\n  --accept {path}"))
                    .collect::<String>()
            ),
            RecordError::NothingToAccept { paths } => write!(
                f,
                "{}; remove the unnecessary acceptance:{}",
                if paths.len() == 1 {
                    "this path is not a contested attachment"
                } else {
                    "these paths are not contested attachments"
                },
                paths
                    .iter()
                    .map(|path| format!("\n  --accept {path}"))
                    .collect::<String>()
            ),
            RecordError::Refused { files } => write!(
                f,
                "{} the folder holds {} not something this format can record; \
                 rename or `skip` {} in `{}/{}/`:{}",
                if files.len() == 1 {
                    "one file".to_owned()
                } else {
                    format!("{} files", files.len())
                },
                if files.len() == 1 { "is" } else { "are" },
                if files.len() == 1 { "it" } else { "them" },
                crate::store::STORE_DIR,
                crate::working::SKIPPED_DIR,
                files
                    .iter()
                    .map(|(path, because)| format!("\n  {path} ({because})"))
                    .collect::<String>()
            ),
            RecordError::SkipsTracked { paths } => write!(
                f,
                "`{}/{}/` skips {} history already holds, so recording would \
                 spell {} as a deletion; delete the {} first and record that, \
                 or drop the rule — history holds what it holds, and `forget` \
                 is what removes recorded content:{}",
                crate::store::STORE_DIR,
                crate::working::SKIPPED_DIR,
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
            RecordError::NothingAtPath { paths } => write!(
                f,
                "{} neither in the folder nor in this history, so there is \
                 nothing there to observe; check the spelling, or name no \
                 paths at all and record everything the folder says:{}",
                if paths.len() == 1 {
                    "this path is"
                } else {
                    "these paths are"
                },
                paths
                    .iter()
                    .map(|path| format!("\n  {path}"))
                    .collect::<String>()
            ),
            RecordError::NamedButSkipped { paths } => write!(
                f,
                "`{}/{}/` says history does not take {}, and naming {} here \
                 does not make {} an exception; remove the rule if {} to be \
                 recorded:{}",
                crate::store::STORE_DIR,
                crate::working::SKIPPED_DIR,
                if paths.len() == 1 { "this" } else { "these" },
                if paths.len() == 1 { "it" } else { "them" },
                if paths.len() == 1 { "it" } else { "them" },
                if paths.len() == 1 {
                    "it is"
                } else {
                    "they are"
                },
                paths
                    .iter()
                    .map(|path| format!("\n  {path}"))
                    .collect::<String>()
            ),
            RecordError::PartialMerge { paths } => write!(
                f,
                "a merge states what every contested file is, and a merge of \
                 some of them would leave the rest joined and unstated; record \
                 the merge with no paths named, and restrict the record after \
                 it:{}",
                paths
                    .iter()
                    .map(|path| format!("\n  {path}"))
                    .collect::<String>()
            ),
            RecordError::HalfARename { from, to } => write!(
                f,
                "`{from}` and `{to}` are one rename, and only one of them is \
                 among the paths this would record, which would spell the \
                 other end as a file appearing or disappearing; name both \
                 `{from}` and `{to}`, or record with no paths named"
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
