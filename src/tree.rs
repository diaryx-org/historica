//! The file set at a revision, and what a revision did to it.
//!
//! Specified by `docs/decisions/0008-tree.md`. A revision records what it did
//! to the files — `add`, `move`, `drop`, `edit` — in the shape decision 0007
//! chose for content, so the tree at a revision is what you get by replaying
//! those facts from the root, exactly as a file is.
//!
//! Files are identified, and a path is a fact about a file rather than the
//! file's name. That is what keeps a rename from breaking the operation chain
//! recorded against it, and it is why [`Tree`] is a map from a file to where it
//! sits rather than the other way round.
//!
//! There are no directories here, because 0008 says there are none anywhere: a
//! directory exists exactly when some file's path names it.
//!
//! An entry also says what it points at, which is 0008's question and decision
//! 0017's answer: a file is lines, accumulated by the operation documents its
//! chain names, or it is one payload whole. Which of the two is fixed when the
//! file is added, so that no operation chain can become unreplayable
//! underneath the identity that names it.
//!
//! Like [`crate::replay`], this does the linear case. Merging concurrent tree
//! facts — where a `drop` loses to an edit, and two files may legitimately
//! claim one path — is decided in 0008 and not built.

use std::collections::BTreeMap;
use std::fmt;

use crate::ancestry::Ancestry;
use crate::core::{FileId, RevisionId};
use crate::format::RevisionDocument;

/// What a file's entry points at.
///
/// Decision 0008 asked the question and left the second answer unbuilt; 0017
/// builds it. A file is one kind or the other for its whole life, and changing
/// kind is `drop` and `add`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Kind {
    /// Lines, which merge: the operation chain the revisions name.
    Lines,
    /// One payload, whole, which never merges.
    Whole,
}

impl fmt::Display for Kind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Kind::Lines => write!(f, "lines"),
            Kind::Whole => write!(f, "bytes"),
        }
    }
}

/// One file's entry: where it sits, and what its content is.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Entry {
    /// Where the file sits.
    pub path: String,
    /// Lines or bytes, fixed when the file was added.
    pub kind: Kind,
    /// The payload a file of bytes holds.
    ///
    /// `Some` for every `Kind::Whole` file a linear history reaches, and
    /// `None` only where concurrent revisions each stated one: 0008 calls that
    /// a divergence to report, and refuses to pick a winner.
    pub payload: Option<RevisionId>,
}

/// The files that exist at one revision, and where each of them sits.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Tree {
    files: BTreeMap<FileId, Entry>,
}

impl Tree {
    /// The file set a root revision starts from: no files at all.
    pub fn empty() -> Self {
        Self::default()
    }

    /// Where a file sits, or `None` if it does not exist here.
    pub fn path(&self, file: &FileId) -> Option<&str> {
        self.files.get(file).map(|entry| entry.path.as_str())
    }

    /// One file's whole entry: its path, its kind, and what it points at.
    pub fn entry(&self, file: &FileId) -> Option<&Entry> {
        self.files.get(file)
    }

    /// Whether a file is lines or bytes, or `None` if it does not exist here.
    pub fn kind(&self, file: &FileId) -> Option<Kind> {
        self.files.get(file).map(|entry| entry.kind)
    }

    /// The files at a path.
    ///
    /// A list rather than an option, because 0008 makes two files claiming one
    /// path a legitimate state that a merge can produce and a person resolves.
    /// A tree replayed along one line of history never has more than one.
    pub fn at(&self, path: &str) -> Vec<FileId> {
        self.files
            .iter()
            .filter(|(_, held)| held.path == path)
            .map(|(file, _)| *file)
            .collect()
    }

    /// Every file and its path, in the order a revision document writes them.
    pub fn files(&self) -> impl Iterator<Item = (&FileId, &str)> {
        self.files
            .iter()
            .map(|(file, entry)| (file, entry.path.as_str()))
    }

    /// Every file and its whole entry, in the order a revision writes them.
    pub fn entries(&self) -> impl Iterator<Item = (&FileId, &Entry)> {
        self.files.iter()
    }

    /// How many files exist here.
    pub fn len(&self) -> usize {
        self.files.len()
    }

    /// Whether no file exists here.
    pub fn is_empty(&self) -> bool {
        self.files.is_empty()
    }

    /// The file set after one revision, given the set at its parent.
    ///
    /// The moves are applied together rather than one at a time, so that a
    /// revision swapping two files' paths is ordinary rather than a collision
    /// with itself. The revision's content facts are read only for what the
    /// tree is responsible for: that they name a file that exists, and that
    /// they address it as the kind it was added as.
    pub fn apply(&self, revision: &RevisionDocument) -> Result<Self, TreeError> {
        let mut files = self.files.clone();

        for (file, path) in &revision.added {
            if files.contains_key(file) {
                return Err(TreeError::AddedTwice { file: *file });
            }
            // Decision 0017: the kind is decided here and never again. A file
            // added with `bytes` is bytes; anything else is lines, an empty
            // file included.
            let payload = revision.bytes.get(file).copied();
            files.insert(
                *file,
                Entry {
                    path: path.clone(),
                    kind: match payload {
                        Some(_) => Kind::Whole,
                        None => Kind::Lines,
                    },
                    payload,
                },
            );
        }
        for (file, path) in &revision.moved {
            match files.get_mut(file) {
                Some(entry) => entry.path = path.clone(),
                None => {
                    return Err(TreeError::Unknown {
                        key: "move",
                        file: *file,
                    });
                }
            }
        }
        for file in &revision.dropped {
            if files.remove(file).is_none() {
                return Err(TreeError::Unknown {
                    key: "drop",
                    file: *file,
                });
            }
        }
        for file in revision.edited.keys() {
            match files.get(file) {
                Some(entry) if entry.kind != Kind::Lines => {
                    return Err(TreeError::WrongKind {
                        key: "edit",
                        file: *file,
                        kind: entry.kind,
                    });
                }
                Some(_) => {}
                None => {
                    return Err(TreeError::Unknown {
                        key: "edit",
                        file: *file,
                    });
                }
            }
        }
        for (file, payload) in &revision.bytes {
            if revision.added.contains_key(file) {
                continue;
            }
            match files.get_mut(file) {
                Some(entry) if entry.kind != Kind::Whole => {
                    return Err(TreeError::WrongKind {
                        key: "bytes",
                        file: *file,
                        kind: entry.kind,
                    });
                }
                Some(entry) => entry.payload = Some(*payload),
                None => {
                    return Err(TreeError::Unknown {
                        key: "bytes",
                        file: *file,
                    });
                }
            }
        }

        // Held to the result rather than to each line, so that two files
        // exchanging paths in one revision is not a collision on the way past.
        let mut held: BTreeMap<&str, FileId> = BTreeMap::new();
        for (file, entry) in &files {
            if let Some(other) = held.insert(entry.path.as_str(), *file) {
                return Err(TreeError::PathTaken {
                    path: entry.path.clone(),
                    file: *file,
                    other,
                });
            }
        }

        Ok(Self { files })
    }
}

/// Replay a linear chain of revisions into the file set they leave behind.
///
/// The revisions must be one line of ancestry, oldest first, as
/// [`crate::replay::replay`] requires of the documents inside it.
pub fn replay<'a>(
    revisions: impl IntoIterator<Item = &'a RevisionDocument>,
) -> Result<Tree, TreeError> {
    let mut tree = Tree::empty();
    for revision in revisions {
        tree = tree.apply(revision)?;
    }
    Ok(tree)
}

/// The operation documents one file accumulates along a chain, oldest first.
///
/// This is the bridge between the two halves: the tree says which document
/// belongs to which file, and [`crate::replay`] turns that list into content.
/// The digests are what a store loads; nothing here reads a store.
pub fn operations_for<'a>(
    revisions: impl IntoIterator<Item = &'a RevisionDocument>,
    file: &FileId,
) -> Vec<RevisionId> {
    revisions
        .into_iter()
        .filter_map(|revision| revision.edited.get(file).copied())
        .collect()
}

/// One revision's contribution to the file set, with its place in the graph.
///
/// The same shape [`crate::merge::Event`] has, and for the same reason: a
/// revision that said nothing about the tree still appears, because its causal
/// edges are what decide whether anything else is concurrent.
#[derive(Debug, Clone, Copy)]
pub struct Event<'a> {
    /// The revision this is.
    pub revision: RevisionId,
    /// What it says about the file set.
    pub document: &'a RevisionDocument,
}

/// The file set at a set of heads, and where concurrent work met deciding it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MergedTree {
    /// The file set.
    pub tree: Tree,
    /// What was decided by rule rather than by agreement.
    pub contested: Vec<TreeContest>,
}

/// A tree fact two branches disagreed about.
///
/// Decision 0008 resolves each of these by rule and reports it, on the same
/// division 0007 draws: the algorithm never fails, and the tool may.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
#[non_exhaustive]
pub enum TreeContest {
    /// A `drop` lost to concurrent work, so the file survives with the edits.
    Dropped {
        /// The file that stayed.
        file: FileId,
        /// The revisions that dropped it.
        by: Vec<RevisionId>,
    },
    /// Concurrent `move`s, resolved to the lower digest's path.
    Moved {
        /// The file that moved twice.
        file: FileId,
        /// Every path claimed, with the revision claiming it, in digest order.
        paths: Vec<(RevisionId, String)>,
    },
    /// Concurrent whole content, which 0008 refuses to choose between.
    ///
    /// The one contest with no resolution: two branches each stated a file's
    /// whole bytes, there is nothing to merge, and inventing a winner would be
    /// picking one person's work over another's by digest order. The file has
    /// no content at these heads until somebody records which.
    Content {
        /// The file both stated.
        file: FileId,
        /// Every payload claimed, with the revision claiming it, in digest
        /// order.
        payloads: Vec<(RevisionId, RevisionId)>,
    },
    /// Two files claiming one path. Neither is renamed: 0008 forbids that.
    Path {
        /// The path both hold.
        path: String,
        /// The files holding it.
        files: Vec<FileId>,
    },
}

/// The file set the whole graph leaves behind.
///
/// Replaying tree facts in causal order, with decision 0008's rules where two
/// branches disagree: a `drop` concurrent with an edit or a move loses, two
/// concurrent `move`s resolve to the lower digest, two concurrent `drop`s
/// agree, and two files claiming one path both keep their identities.
///
/// Nothing here is written down. Like [`crate::merge`], the structure that
/// resolves concurrency lives for the length of this call.
pub fn merge<'a>(events: impl IntoIterator<Item = Event<'a>>) -> Result<MergedTree, TreeError> {
    let events: Vec<Event<'a>> = events.into_iter().collect();
    let ancestors = ancestry(&events)?;

    // Every fact anybody stated about every file, gathered by file.
    let mut facts: BTreeMap<FileId, Facts> = BTreeMap::new();
    for event in &events {
        let document = event.document;
        for (file, path) in &document.added {
            let held = facts.entry(*file).or_default();
            held.placements.push((event.revision, path.clone()));
            held.touches.push(event.revision);
            held.added.push(event.revision);
            held.whole = document.bytes.contains_key(file);
        }
        for (file, path) in &document.moved {
            let held = facts.entry(*file).or_default();
            held.placements.push((event.revision, path.clone()));
            held.touches.push(event.revision);
        }
        for file in &document.dropped {
            facts.entry(*file).or_default().drops.push(event.revision);
        }
        for file in document.edited.keys() {
            facts.entry(*file).or_default().touches.push(event.revision);
        }
        for (file, payload) in &document.bytes {
            let held = facts.entry(*file).or_default();
            held.wholes.push((event.revision, *payload));
            held.touches.push(event.revision);
        }
    }

    let mut files = BTreeMap::new();
    let mut contested = Vec::new();

    for (file, held) in facts {
        if held.added.is_empty() {
            // Every fact about a file is recorded against its `add`, so this
            // is an ancestor nobody has delivered rather than a disagreement.
            return Err(TreeError::Unknown { key: "move", file });
        }

        // A `drop` wins only where nothing concurrent says the file matters.
        let mut lost = Vec::new();
        let mut gone = false;
        for drop in &held.drops {
            let concurrent: Vec<RevisionId> = held
                .touches
                .iter()
                .copied()
                .filter(|touch| touch != drop && !ancestors.is_ancestor(touch, drop))
                .collect();
            if concurrent.is_empty() {
                gone = true;
            } else {
                lost.push(*drop);
            }
        }
        if gone {
            continue;
        }
        if !lost.is_empty() {
            lost.sort();
            contested.push(TreeContest::Dropped { file, by: lost });
        }

        // The path comes from the placements nothing later replaced.
        let mut latest: Vec<(RevisionId, String)> =
            held.placements
                .iter()
                .filter(|(revision, _)| {
                    !held.placements.iter().any(|(other, _)| {
                        other != revision && ancestors.is_ancestor(revision, other)
                    })
                })
                .cloned()
                .collect();
        latest.sort();
        latest.dedup();

        let (_, path) = latest
            .first()
            .expect("a file has at least its `add`")
            .clone();
        if latest.len() > 1 {
            // Decision 0008: by digest, because a timestamp is not trusted and
            // a change ID is an unverifiable claim.
            contested.push(TreeContest::Moved {
                file,
                paths: latest,
            });
        }

        // The same walk for content stated whole, and a different ending:
        // 0008 reports two concurrent `bytes` as a divergence and never picks
        // one, so a contested file holds no payload until somebody records it.
        let kind = if held.whole { Kind::Whole } else { Kind::Lines };
        let mut current: Vec<(RevisionId, RevisionId)> =
            held.wholes
                .iter()
                .filter(|(revision, _)| {
                    !held.wholes.iter().any(|(other, _)| {
                        other != revision && ancestors.is_ancestor(revision, other)
                    })
                })
                .copied()
                .collect();
        current.sort();
        current.dedup();
        let payload = match current.len() {
            0 => None,
            1 => Some(current[0].1),
            _ => {
                contested.push(TreeContest::Content {
                    file,
                    payloads: current,
                });
                None
            }
        };

        files.insert(
            file,
            Entry {
                path,
                kind,
                payload,
            },
        );
    }

    // Two files at one path is a legitimate state a person resolves, so it is
    // reported rather than refused, and neither file is renamed to fit.
    let mut by_path: BTreeMap<&str, Vec<FileId>> = BTreeMap::new();
    for (file, entry) in &files {
        by_path.entry(entry.path.as_str()).or_default().push(*file);
    }
    for (path, holders) in by_path {
        if holders.len() > 1 {
            contested.push(TreeContest::Path {
                path: path.to_owned(),
                files: holders,
            });
        }
    }

    contested.sort();
    Ok(MergedTree {
        tree: Tree { files },
        contested,
    })
}

/// What one file's revisions said about it.
#[derive(Debug, Default)]
struct Facts {
    /// `add` and `move`, with the path each stated.
    placements: Vec<(RevisionId, String)>,
    /// Revisions that said the file matters: added, moved, or edited it.
    touches: Vec<RevisionId>,
    /// Revisions that dropped it.
    drops: Vec<RevisionId>,
    /// Revisions that added it.
    added: Vec<RevisionId>,
    /// `bytes`, with the payload each stated.
    wholes: Vec<(RevisionId, RevisionId)>,
    /// Whether the `add` said this file is bytes rather than lines.
    whole: bool,
}

/// Who had seen whom, over the revisions a caller supplied.
///
/// [`crate::ancestry`] answers by index, because that is what lets a chain
/// cost a position per revision instead of a set; this is the digests those
/// indices stand for.
struct Ancestors {
    /// Where each revision sits in the indexed graph.
    index: BTreeMap<RevisionId, usize>,
    /// What each of those had seen.
    ancestry: Ancestry,
}

impl Ancestors {
    /// Whether `earlier` is an ancestor of `later`, itself excluded.
    fn is_ancestor(&self, earlier: &RevisionId, later: &RevisionId) -> bool {
        match (self.index.get(earlier), self.index.get(later)) {
            (Some(earlier), Some(later)) => self.ancestry.saw(*later, *earlier),
            _ => false,
        }
    }
}

/// Every revision's ancestors, which is what makes concurrency decidable.
///
/// A parent outside the set is one the caller did not supply — a store hands
/// over a whole ancestry — so it is an undelivered ancestor rather than a root.
fn ancestry(events: &[Event<'_>]) -> Result<Ancestors, TreeError> {
    let held: BTreeMap<RevisionId, &RevisionDocument> = events
        .iter()
        .map(|event| (event.revision, event.document))
        .collect();
    let index: BTreeMap<RevisionId, usize> = held
        .keys()
        .enumerate()
        .map(|(at, revision)| (*revision, at))
        .collect();

    let mut parents: Vec<Vec<usize>> = Vec::with_capacity(held.len());
    let mut children: Vec<Vec<usize>> = vec![Vec::new(); held.len()];
    let mut waiting: Vec<usize> = Vec::with_capacity(held.len());
    for (at, (revision, document)) in held.iter().enumerate() {
        let mut of = Vec::with_capacity(document.parents.len());
        for parent in &document.parents {
            let found = index.get(parent).ok_or(TreeError::Undelivered {
                parent: *parent,
                named_by: *revision,
            })?;
            children[*found].push(at);
            of.push(*found);
        }
        waiting.push(of.len());
        parents.push(of);
    }

    let mut ready: Vec<usize> = waiting
        .iter()
        .enumerate()
        .filter(|(_, count)| **count == 0)
        .map(|(at, _)| at)
        .collect();
    let mut order = Vec::with_capacity(held.len());
    while let Some(revision) = ready.pop() {
        order.push(revision);
        for child in &children[revision] {
            waiting[*child] -= 1;
            if waiting[*child] == 0 {
                ready.push(*child);
            }
        }
    }

    if order.len() != held.len() {
        // Unreachable for digests, which cannot name a descendant.
        return Err(TreeError::Cyclic);
    }
    Ok(Ancestors {
        ancestry: Ancestry::new(&order, &parents),
        index,
    })
}

/// Why a revision could not be applied to the file set it names.
///
/// As in [`crate::replay`], none of these mean the model failed. They mean the
/// store contradicts itself: a revision was applied to a tree it was not
/// recorded against.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum TreeError {
    /// An `add` named a file that already exists.
    AddedTwice {
        /// The file named twice.
        file: FileId,
    },
    /// A header addressed a file as the kind it is not.
    WrongKind {
        /// The header that named it.
        key: &'static str,
        /// The file it named.
        file: FileId,
        /// What that file actually is.
        kind: Kind,
    },
    /// A header named a file that does not exist here.
    Unknown {
        /// The header that named it.
        key: &'static str,
        /// The file it named.
        file: FileId,
    },
    /// A parent nobody delivered, so concurrency cannot be decided.
    Undelivered {
        /// The parent nothing here holds.
        parent: RevisionId,
        /// The revision that names it.
        named_by: RevisionId,
    },
    /// A parent edge naming a descendant, which digests make impossible.
    Cyclic,
    /// Two files would hold one path after this revision.
    PathTaken {
        /// The contested path.
        path: String,
        /// One file claiming it.
        file: FileId,
        /// The other.
        other: FileId,
    },
}

impl fmt::Display for TreeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TreeError::AddedTwice { file } => write!(
                f,
                "the file {file} already exists here and this revision adds it; \
                 a file that comes back after being dropped is a new file with a new ID"
            ),
            TreeError::WrongKind { key, file, kind } => write!(
                f,
                "`{key}` addresses the file {file} as the kind it is not: it holds {kind}, \
                 and a file's kind is fixed when it is added; \
                 a file whose content model changed is a `drop` and an `add`"
            ),
            TreeError::Unknown { key, file } => write!(
                f,
                "`{key}` names the file {file}, which does not exist at this revision's parent; \
                 check that the parents are the ones this revision was recorded against"
            ),
            TreeError::Undelivered { parent, named_by } => write!(
                f,
                "{named_by} names the parent {parent}, which this store does \
                 not hold yet, so what is concurrent with what cannot be decided"
            ),
            TreeError::Cyclic => write!(
                f,
                "a parent edge names a descendant, which a digest cannot do"
            ),
            TreeError::PathTaken { path, file, other } => write!(
                f,
                "the files {file} and {other} would both hold `{path}` after this revision; \
                 one line of history cannot produce that, so move one of them"
            ),
        }
    }
}

impl std::error::Error for TreeError {}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::format::{PREAMBLE, RevisionDocument};

    const CHANGE: &str = "change qpvuntsmwlrkzxonmvtplsyq";
    const AUTHOR: &str = "author Adam Harris <adam@example.com>";
    const WHEN: &str = "when 2025-08-19T00:47:11-06:00";
    const ONE: &str = "lqxstvnmpkwyzrolvtsqnkxm";
    const TWO: &str = "ptkwnrvzlmyxqsotnkwlpvzr";
    const DIGEST: &str = "1e4e224e93380a25d4cd1be85d35db37f4064be4388822eba250894c6d6daa0d";

    fn revision(tree: &[String]) -> RevisionDocument {
        let mut text = format!("{PREAMBLE}\n{CHANGE}\n{AUTHOR}\n{WHEN}\n");
        for line in tree {
            text.push_str(line);
            text.push('\n');
        }
        text.push_str("\nm");
        RevisionDocument::parse(text.as_bytes()).expect("a revision the parser accepts")
    }

    fn line(text: &str) -> String {
        text.to_owned()
    }

    fn file(id: &str) -> FileId {
        id.parse().expect("a file ID")
    }

    #[test]
    fn a_root_revision_starts_from_no_files_at_all() {
        let tree =
            replay([&revision(&[line(&format!("add {ONE} notes/one.md"))])]).expect("a root");
        assert_eq!(tree.len(), 1);
        assert_eq!(tree.path(&file(ONE)), Some("notes/one.md"));
        assert_eq!(tree.at("notes/one.md"), vec![file(ONE)]);
        assert!(Tree::empty().is_empty());
    }

    #[test]
    fn a_rename_keeps_the_file_and_moves_the_path() {
        let history = [
            revision(&[
                line(&format!("add {ONE} notes/one.md")),
                line(&format!("text {ONE} {DIGEST}")),
            ]),
            revision(&[line(&format!("edit {ONE} {DIGEST}"))]),
            revision(&[line(&format!("move {ONE} archive/one.md"))]),
        ];
        let tree = replay(&history).expect("a rename");
        assert_eq!(tree.path(&file(ONE)), Some("archive/one.md"));
        assert!(tree.at("notes/one.md").is_empty());

        // The operations recorded before the rename still belong to the file,
        // which is the whole reason a path is not an identity.
        assert_eq!(operations_for(&history, &file(ONE)).len(), 1);
    }

    #[test]
    fn two_files_may_exchange_their_paths_in_one_revision() {
        let history = [
            revision(&[
                line(&format!("add {ONE} a.md")),
                line(&format!("add {TWO} b.md")),
            ]),
            revision(&[
                line(&format!("move {ONE} b.md")),
                line(&format!("move {TWO} a.md")),
            ]),
        ];
        let tree = replay(&history).expect("a swap");
        assert_eq!(tree.path(&file(ONE)), Some("b.md"));
        assert_eq!(tree.path(&file(TWO)), Some("a.md"));
    }

    #[test]
    fn a_dropped_file_stops_existing() {
        let history = [
            revision(&[line(&format!("add {ONE} a.md"))]),
            revision(&[line(&format!("drop {ONE}"))]),
        ];
        let tree = replay(&history).expect("a drop");
        assert!(tree.is_empty());

        // And the path it held is free for a different file.
        let mut history = history.to_vec();
        history.push(revision(&[line(&format!("add {TWO} a.md"))]));
        assert_eq!(
            replay(&history).expect("reuse").path(&file(TWO)),
            Some("a.md")
        );
    }

    #[test]
    fn a_revision_applied_to_the_wrong_tree_is_refused() {
        let orphan = revision(&[line(&format!("move {ONE} b.md"))]);
        assert_eq!(
            replay([&orphan]).expect_err("no such file"),
            TreeError::Unknown {
                key: "move",
                file: file(ONE),
            }
        );

        let edited = revision(&[line(&format!("edit {ONE} {DIGEST}"))]);
        assert_eq!(
            replay([&edited]).expect_err("no such file"),
            TreeError::Unknown {
                key: "edit",
                file: file(ONE),
            }
        );

        let added = revision(&[line(&format!("add {ONE} a.md"))]);
        assert_eq!(
            replay([&added, &added]).expect_err("twice"),
            TreeError::AddedTwice { file: file(ONE) }
        );
    }

    #[test]
    fn one_line_of_history_never_puts_two_files_at_one_path() {
        // Concurrency can, and 0008 says that is a legitimate state. A chain
        // cannot, so this is the store contradicting itself.
        let history = [
            revision(&[line(&format!("add {ONE} a.md"))]),
            revision(&[line(&format!("add {TWO} a.md"))]),
        ];
        assert!(matches!(
            replay(&history).expect_err("a collision"),
            TreeError::PathTaken { .. }
        ));
    }
    /// A revision with stated parents, so a graph can be built by hand.
    fn revision_with(parents: &[RevisionId], facts: &[String]) -> RevisionDocument {
        let mut text = format!("{PREAMBLE}\n{CHANGE}\n");
        let mut sorted: Vec<String> = parents.iter().map(|p| format!("parent {p}\n")).collect();
        sorted.sort();
        for line in sorted {
            text.push_str(&line);
        }
        text.push_str(&format!("{AUTHOR}\n{WHEN}\n"));
        for line in facts {
            text.push_str(line);
            text.push('\n');
        }
        text.push_str("\nm");
        RevisionDocument::parse(text.as_bytes()).expect("a revision the parser accepts")
    }

    /// The merged tree of a hand-built graph, oldest first.
    fn merged(documents: &[RevisionDocument]) -> MergedTree {
        merge(documents.iter().map(|document| Event {
            revision: document.id(),
            document,
        }))
        .expect("a graph the merge accepts")
    }

    #[test]
    fn a_drop_concurrent_with_an_edit_loses_and_is_reported() {
        let root = revision_with(&[], &[line(&format!("add {ONE} notes.md"))]);
        let dropped = revision_with(&[root.id()], &[line(&format!("drop {ONE}"))]);
        let edited = revision_with(&[root.id()], &[line(&format!("edit {ONE} {DIGEST}"))]);

        let merged = merged(&[root, dropped.clone(), edited]);
        assert_eq!(
            merged.tree.path(&file(ONE)),
            Some("notes.md"),
            "losing work is the worse failure, so the file survives"
        );
        assert_eq!(
            merged.contested,
            [TreeContest::Dropped {
                file: file(ONE),
                by: vec![dropped.id()],
            }]
        );
    }

    #[test]
    fn a_drop_nothing_contests_takes_the_file() {
        let root = revision_with(&[], &[line(&format!("add {ONE} notes.md"))]);
        let dropped = revision_with(&[root.id()], &[line(&format!("drop {ONE}"))]);

        let merged = merged(&[root, dropped]);
        assert!(merged.tree.is_empty());
        assert!(merged.contested.is_empty(), "nobody disagreed");
    }

    #[test]
    fn two_concurrent_moves_resolve_to_the_lower_digest() {
        let root = revision_with(&[], &[line(&format!("add {ONE} notes.md"))]);
        let here = revision_with(&[root.id()], &[line(&format!("move {ONE} here.md"))]);
        let there = revision_with(&[root.id()], &[line(&format!("move {ONE} there.md"))]);

        let merged = merged(&[root, here.clone(), there.clone()]);
        let (lower, path) = if here.id() < there.id() {
            (here.id(), "here.md")
        } else {
            (there.id(), "there.md")
        };
        assert_eq!(merged.tree.path(&file(ONE)), Some(path));
        assert!(matches!(
            &merged.contested[..],
            [TreeContest::Moved { file: contested, paths }]
                if *contested == file(ONE) && paths.len() == 2 && paths[0].0 == lower
        ));
    }

    #[test]
    fn a_later_move_replaces_an_earlier_one_without_contest() {
        let root = revision_with(&[], &[line(&format!("add {ONE} notes.md"))]);
        let moved = revision_with(&[root.id()], &[line(&format!("move {ONE} here.md"))]);
        let again = revision_with(&[moved.id()], &[line(&format!("move {ONE} there.md"))]);

        let merged = merged(&[root, moved, again]);
        assert_eq!(merged.tree.path(&file(ONE)), Some("there.md"));
        assert!(merged.contested.is_empty(), "causality is not disagreement");
    }

    #[test]
    fn two_files_claiming_one_path_both_keep_their_identities() {
        let root = revision_with(&[], &[line(&format!("add {ONE} notes.md"))]);
        let mine = revision_with(&[root.id()], &[line(&format!("add {TWO} theirs.md"))]);
        let theirs = revision_with(&[root.id()], &[line(&format!("move {ONE} theirs.md"))]);

        let merged = merged(&[root, mine, theirs]);
        assert_eq!(merged.tree.at("theirs.md").len(), 2);
        assert!(matches!(
            &merged.contested[..],
            [TreeContest::Path { path, files }] if path == "theirs.md" && files.len() == 2
        ));
    }

    #[test]
    fn an_undelivered_parent_stops_the_merge_rather_than_guessing() {
        let root = revision_with(&[], &[line(&format!("add {ONE} notes.md"))]);
        let child = revision_with(&[root.id()], &[line(&format!("move {ONE} here.md"))]);

        let refused = merge([Event {
            revision: child.id(),
            document: &child,
        }])
        .expect_err("a parent nobody delivered");
        assert!(matches!(refused, TreeError::Undelivered { .. }));
    }
}
