//! Turning what a person typed into something the store holds.
//!
//! Decision 0001 spends a whole section on this argument position: change IDs
//! are spelled in `k`–`z` and digests in hex, "so one command-line argument
//! position can accept either without ambiguity". This is that position. It
//! also accepts a bookmark, because a bookmark is the name a person actually
//! keeps, and bookmarks win where the spellings could be confused — a store
//! with a bookmark called `ba5e` means the bookmark.

use std::fmt::Write as _;

use historica::core::{ChangeId, ChangeState, FileId, RevisionId};
use historica::store::{Name, Store};

use super::Failure;

/// The revision a target names.
pub fn resolve(store: &Store, spelling: &str) -> Result<RevisionId, Failure> {
    if spelling.is_empty() {
        return Err(Failure::usage("a target cannot be empty"));
    }

    // Decision 0011 makes the head the position, so a person may name it.
    // A bookmark called `head` still wins, because a name somebody chose beats
    // a word the tool reserved.
    if spelling == "head" && store.name(spelling).is_none() {
        return head(store);
    }

    if let Some(bookmark) = store.name(spelling) {
        return match bookmark {
            Name::Revision(id) => held(store, id, &format!("the bookmark `{spelling}`")),
            Name::Change(change) => current(store, change, &format!("the bookmark `{spelling}`")),
        };
    }

    if spelling
        .chars()
        .all(|character| character.is_ascii_hexdigit())
    {
        return revision_by_prefix(store, spelling);
    }
    if spelling
        .chars()
        .all(|character| ('k'..='z').contains(&character))
    {
        let change = change_by_prefix(store, spelling)?;
        return current(store, change, &format!("`{spelling}`"));
    }

    Err(Failure::error(format!(
        "`{spelling}` is not a bookmark here, and it is spelled as neither a \
         change ID (`k`–`z`) nor a digest (`0`–`9`, `a`–`f`)"
    )))
}

/// The file one path names at one revision.
///
/// A file ID is accepted here too: after a rename there are two paths for one
/// file and only one name that never moved.
pub fn file_in(store: &Store, revision: &RevisionId, path: &str) -> Result<FileId, Failure> {
    let tree = store.tree(revision).map_err(Failure::error)?;

    if let Ok(file) = path.parse::<FileId>()
        && tree.path(&file).is_some()
    {
        return Ok(file);
    }

    match tree.at(path).as_slice() {
        [] => Err(Failure::error(format!(
            "{} holds no file at {path}; `historica files {}` lists what it holds",
            revision.abbreviate(12),
            revision.abbreviate(12)
        ))),
        [only] => Ok(*only),
        several => {
            // Decision 0008 allows two files to claim one path when concurrent
            // work put them there. The path is then not a name, and saying so
            // is better than picking one.
            let mut message = format!(
                "{} has {} files at {path}, so the path does not name one of them:",
                revision.abbreviate(12),
                several.len()
            );
            for file in several {
                let _ = write!(message, "\n  {file}");
            }
            Err(Failure::error(message))
        }
    }
}

/// The one head, or a refusal naming the choice a person has to make.
fn head(store: &Store) -> Result<RevisionId, Failure> {
    let heads = store.history().heads();
    match heads.len() {
        0 => Err(Failure::error("this store holds no revisions yet")),
        1 => Ok(heads.into_iter().next().expect("one head")),
        several => Err(Failure::error(format!(
            "this store has {several} heads, so `head` names none of them:{}",
            listed(heads.iter().map(|head| head.abbreviate(12)))
        ))),
    }
}

/// A revision the store holds, or a message about the one it does not.
fn held(store: &Store, id: RevisionId, named_by: &str) -> Result<RevisionId, Failure> {
    if store.get(&id).is_some() {
        Ok(id)
    } else {
        Err(Failure::error(format!(
            "{named_by} names the revision {id}, which this store does not hold yet"
        )))
    }
}

/// The current revision of a change, or the reason there is not exactly one.
///
/// Divergence and abandonment are legitimate states rather than corruption —
/// decision 0001 is explicit — so both are reported as situations a person
/// resolves, not as a broken store.
fn current(store: &Store, change: ChangeId, named_by: &str) -> Result<RevisionId, Failure> {
    match store.history().change_state(&change) {
        ChangeState::Resolved(revision) => Ok(revision.id),
        ChangeState::Unknown => Err(Failure::error(format!(
            "{named_by} names the change {change}, which no revision here claims"
        ))),
        ChangeState::Abandoned => Err(Failure::error(format!(
            "every revision of {change} was superseded by revisions of other \
             changes, so {named_by} has no current revision"
        ))),
        ChangeState::Divergent(revisions) => Err(Failure::error(format!(
            "{change} has {} current revisions, none superseding the others; \
             name one of them:{}",
            revisions.len(),
            listed(revisions.iter().copied())
        ))),
    }
}

/// The one revision whose digest starts with `prefix`.
fn revision_by_prefix(store: &Store, prefix: &str) -> Result<RevisionId, Failure> {
    let matches: Vec<RevisionId> = store
        .iter()
        .map(|(id, _)| *id)
        .filter(|id| id.to_string().starts_with(prefix))
        .collect();

    match matches.as_slice() {
        [] => Err(Failure::error(format!(
            "no revision here has a digest starting `{prefix}`"
        ))),
        [only] => Ok(*only),
        several => Err(Failure::error(format!(
            "`{prefix}` could be {} revisions:{}",
            several.len(),
            listed(several.iter().copied())
        ))),
    }
}

/// The one change whose ID starts with `prefix`.
fn change_by_prefix(store: &Store, prefix: &str) -> Result<ChangeId, Failure> {
    let matches: Vec<ChangeId> = store
        .history()
        .changes()
        .into_iter()
        .filter(|change| change.to_string().starts_with(prefix))
        .collect();

    match matches.as_slice() {
        [] => Err(Failure::error(format!(
            "no change here has an ID starting `{prefix}`"
        ))),
        [only] => Ok(*only),
        several => Err(Failure::error(format!(
            "`{prefix}` could be {} changes:{}",
            several.len(),
            listed(several.iter().copied())
        ))),
    }
}

/// Candidates, one per line, indented under the sentence that introduced them.
fn listed(items: impl IntoIterator<Item = impl std::fmt::Display>) -> String {
    let mut out = String::new();
    for item in items {
        let _ = write!(out, "\n  {item}");
    }
    out
}
