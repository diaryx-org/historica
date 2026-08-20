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
//! Like [`crate::replay`], this does the linear case. Merging concurrent tree
//! facts — where a `drop` loses to an edit, and two files may legitimately
//! claim one path — is decided in 0008 and not built.

use std::collections::BTreeMap;
use std::fmt;

use crate::core::{FileId, RevisionId};
use crate::format::RevisionDocument;

/// The files that exist at one revision, and where each of them sits.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Tree {
    files: BTreeMap<FileId, String>,
}

impl Tree {
    /// The file set a root revision starts from: no files at all.
    pub fn empty() -> Self {
        Self::default()
    }

    /// Where a file sits, or `None` if it does not exist here.
    pub fn path(&self, file: &FileId) -> Option<&str> {
        self.files.get(file).map(String::as_str)
    }

    /// The files at a path.
    ///
    /// A list rather than an option, because 0008 makes two files claiming one
    /// path a legitimate state that a merge can produce and a person resolves.
    /// A tree replayed along one line of history never has more than one.
    pub fn at(&self, path: &str) -> Vec<FileId> {
        self.files
            .iter()
            .filter(|(_, held)| held.as_str() == path)
            .map(|(file, _)| *file)
            .collect()
    }

    /// Every file and its path, in the order a revision document writes them.
    pub fn files(&self) -> impl Iterator<Item = (&FileId, &str)> {
        self.files.iter().map(|(file, path)| (file, path.as_str()))
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
    /// with itself. Nothing here reads the revision's content facts beyond
    /// checking that an `edit` names a file that exists.
    pub fn apply(&self, revision: &RevisionDocument) -> Result<Self, TreeError> {
        let mut files = self.files.clone();

        for (file, path) in &revision.added {
            if files.contains_key(file) {
                return Err(TreeError::AddedTwice { file: *file });
            }
            files.insert(*file, path.clone());
        }
        for (file, path) in &revision.moved {
            if !files.contains_key(file) {
                return Err(TreeError::Unknown {
                    key: "move",
                    file: *file,
                });
            }
            files.insert(*file, path.clone());
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
            if !files.contains_key(file) {
                return Err(TreeError::Unknown {
                    key: "edit",
                    file: *file,
                });
            }
        }

        // Held to the result rather than to each line, so that two files
        // exchanging paths in one revision is not a collision on the way past.
        let mut held: BTreeMap<&str, FileId> = BTreeMap::new();
        for (file, path) in &files {
            if let Some(other) = held.insert(path.as_str(), *file) {
                return Err(TreeError::PathTaken {
                    path: path.clone(),
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
    /// A header named a file that does not exist here.
    Unknown {
        /// The header that named it.
        key: &'static str,
        /// The file it named.
        file: FileId,
    },
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
            TreeError::Unknown { key, file } => write!(
                f,
                "`{key}` names the file {file}, which does not exist at this revision's parent; \
                 check that the parents are the ones this revision was recorded against"
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
                line(&format!("edit {ONE} {DIGEST}")),
            ]),
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
}
