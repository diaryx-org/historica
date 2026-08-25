//! Turning what a person typed into something the store holds.
//!
//! Decision 0001 spends a whole section on this argument position: change IDs
//! are spelled in `k`–`z` and digests in hex, "so one command-line argument
//! position can accept either without ambiguity". This is that position. It
//! also accepts a bookmark, because a bookmark is the name a person actually
//! keeps, and bookmarks win where the spellings could be confused — a store
//! with a bookmark called `ba5e` means the bookmark.
//!
//! The position beside it names a file, and decision 0024 is why that one
//! cannot work the same way: a path is a value a person chose rather than a
//! name the tool minted, so no alphabet partitions it and the identifier is
//! spelled `file:` instead.

use std::collections::BTreeSet;
use std::fmt::Write as _;

use historica::core::{ChangeId, ChangeState, FileId, RevisionId};
use historica::store::{Name, Store};
use historica::tree::Tree;

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
            // Decision 0024: a file bookmark says which file, never which
            // version, so there is no revision for it to mean here.
            Name::File(file) => Err(Failure::error(format!(
                "the bookmark `{spelling}` names the file {file}, and a file is \
                 not a revision; a file is addressed at one, as \
                 `cat <target> file:{spelling}`"
            ))),
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

/// Whether a spelling could name a target at all.
///
/// Decision 0001's disjoint alphabets, asked as a question rather than
/// answered as a lookup: a change ID is `k`–`z` and a digest is `0`–`9`,
/// `a`–`f`, so a string outside both that no bookmark claims is not a target
/// somebody mistyped — it is not a target. That is what lets one argument
/// position hold either a target or a path without either having to be
/// guessed at: `diff notes.md` is a path because nothing else could name it,
/// and `diff kxry` is a target because nothing else could, whether or not
/// this store happens to hold one.
pub fn could_be_target(store: &Store, spelling: &str) -> bool {
    if spelling.is_empty() {
        return false;
    }
    if spelling == "head" || store.name(spelling).is_some() {
        return true;
    }
    spelling
        .chars()
        .all(|character| character.is_ascii_hexdigit())
        || spelling
            .chars()
            .all(|character| ('k'..='z').contains(&character))
}

/// The spelling that introduces a file identifier where a path is expected.
///
/// Decision 0024: the format's own word for this thing, with a colon where the
/// revision document has a space, because a shell argument is one word.
pub const FILE_PREFIX: &str = "file:";
/// The spelling that says the rest is a path, whatever it looks like.
pub const PATH_PREFIX: &str = "path:";

/// The file one argument names at one revision.
///
/// A path, or `file:` and an identifier — which is what a person wants after a
/// rename, when there are two paths for one file and only one name that never
/// moved. A path is arbitrary UTF-8 and a file may be called anything, so a
/// bare identifier is not accepted here: `path:` says the rest is a path
/// exactly, for the file whose own name would otherwise be read as a spelling.
pub fn file_in(store: &Store, revision: &RevisionId, spelling: &str) -> Result<FileId, Failure> {
    let tree = store.tree(revision).map_err(Failure::error)?;

    if let Some(named) = spelling.strip_prefix(FILE_PREFIX) {
        return file_named(store, &tree, revision, named);
    }
    // Decision 0033: a store spells a path in normal form C, and a person's
    // keyboard, shell, and tab completion may not.
    let path = historica::format::nfc(spelling.strip_prefix(PATH_PREFIX).unwrap_or(spelling));
    let path = path.as_ref();

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
                let _ = write!(message, "\n  {FILE_PREFIX}{file}");
            }
            Err(Failure::error(message))
        }
    }
}

/// The file a `file:` spelling names at one revision.
///
/// A bookmark first, because a name somebody chose beats a spelling the tool
/// reserved — the rule the target position already keeps, and the reason
/// decision 0024 refuses a bookmark spelled as an identifier. Then a prefix,
/// resolved over the file set at this revision: the identifiers in scope are
/// the ones `historica files <target>` prints, so the prefix a person can see
/// is the prefix that resolves.
fn file_named(
    store: &Store,
    tree: &Tree,
    revision: &RevisionId,
    spelling: &str,
) -> Result<FileId, Failure> {
    if spelling.is_empty() {
        return Err(Failure::usage(
            "`file:` wants an identifier or a bookmark after it",
        ));
    }

    if let Some(bookmark) = store.name(spelling) {
        let Name::File(file) = bookmark else {
            return Err(Failure::error(format!(
                "the bookmark `{spelling}` names a {}, and this position names a file",
                bookmark.kind()
            )));
        };
        return if tree.path(&file).is_some() {
            Ok(file)
        } else {
            Err(Failure::error(format!(
                "the bookmark `{spelling}` names the file {file}, which {} does \
                 not hold; `historica files {}` lists what it holds",
                revision.abbreviate(12),
                revision.abbreviate(12)
            )))
        };
    }

    if !spelling
        .chars()
        .all(|character| ('k'..='z').contains(&character))
    {
        return Err(Failure::error(format!(
            "`{spelling}` is not a file bookmark here, and a file identifier is \
             spelled in `k`–`z`"
        )));
    }

    let matches: Vec<FileId> = tree
        .files()
        .map(|(file, _)| *file)
        .filter(|file| file.to_string().starts_with(spelling))
        .collect();
    match matches.as_slice() {
        [] => Err(Failure::error(format!(
            "no file at {} has an identifier starting `{spelling}`; \
             `historica files {}` lists them",
            revision.abbreviate(12),
            revision.abbreviate(12)
        ))),
        [only] => Ok(*only),
        several => {
            let mut message = format!(
                "`{spelling}` could be {} files at {}:",
                several.len(),
                revision.abbreviate(12)
            );
            for file in several {
                let path = tree.path(file).unwrap_or_default();
                let _ = write!(message, "\n  {FILE_PREFIX}{file}  {path}");
            }
            Err(Failure::error(message))
        }
    }
}

/// The file an `--at` value names, which is an identifier or a bookmark.
///
/// No prefix: `--at` names a file against a survey rather than against a
/// revision, so there is no stated set to abbreviate over, and an abbreviation
/// whose meaning depended on what the folder happened to hold is the ambiguity
/// decision 0024 exists to remove.
pub fn file_by_name(store: &Store, spelling: &str) -> Result<FileId, Failure> {
    if let Some(bookmark) = store.name(spelling) {
        return match bookmark {
            Name::File(file) => Ok(file),
            other => Err(Failure::usage(format!(
                "the bookmark `{spelling}` names a {}, and this position names a file",
                other.kind()
            ))),
        };
    }
    spelling
        .parse::<FileId>()
        .map_err(|_| Failure::usage(format!("`{spelling}` is not a file identifier")))
}

/// The revisions a command is taken against.
///
/// Decision 0015 moves this out of `record` so that `status` resolves its
/// position by exactly the rule the record it is previewing will use. The rule
/// is subtler than it looks: the head is derived only where it is needed, so
/// `--onto` alone means that revision, `--merge` alone means that revision
/// *and* the head, and the two together mean what was named and nothing else.
pub fn parents(
    store: &Store,
    onto: Option<&str>,
    merging: &[String],
) -> Result<Vec<RevisionId>, Failure> {
    let mut parents: Vec<RevisionId> = Vec::new();
    if let Some(spelling) = onto {
        parents.push(resolve(store, spelling)?);
    }
    for spelling in merging {
        let other = resolve(store, spelling)?;
        if parents.contains(&other) {
            return Err(Failure::error(format!(
                "`{spelling}` is named twice, and a revision is its own parent \
                 exactly never"
            )));
        }
        parents.push(other);
    }

    let wants_the_head =
        parents.is_empty() || (parents.len() == 1 && !merging.is_empty() && onto.is_none());
    if wants_the_head
        && let Some(head) = the_head(store)?
        && !parents.contains(&head)
    {
        parents.push(head);
    }
    parents.sort();
    parents.dedup();
    Ok(parents)
}

/// The heads a person is standing on: the ones nothing has rewritten.
///
/// Decision 0001 keeps head discovery a pure graph question over parent edges
/// and leaves it to a caller to decide whether superseded revisions are shown;
/// decision 0023 is that caller deciding. An amended revision is still a head
/// by parent edges — nothing names it as a parent, because its successor took
/// its parents rather than it — so a store with one line of work in it and one
/// amendment would otherwise have two heads forever.
///
/// Where filtering leaves nothing, every head is returned: a store holding a
/// revision whose successor has not been delivered should be described as it
/// is rather than as an empty one.
pub fn current_heads(store: &Store) -> BTreeSet<RevisionId> {
    let history = store.history();
    let heads = history.heads();
    let superseded = history.superseded();
    let current: BTreeSet<RevisionId> = heads.difference(&superseded).copied().collect();
    if current.is_empty() { heads } else { current }
}

/// The one head to work against, or a refusal naming the choice.
///
/// `None` where a store holds no revisions yet, which is a root about to be
/// recorded rather than a problem.
pub fn the_head(store: &Store) -> Result<Option<RevisionId>, Failure> {
    let heads = current_heads(store);
    match heads.len() {
        0 => Ok(None),
        1 => Ok(heads.into_iter().next()),
        several => Err(Failure::error(format!(
            "this store has {several} heads, so nothing here is `the` latest; \
             name one with --onto, or join them with `historica merge`:\n{}",
            described(store, &heads)
        ))),
    }
}

/// Every head, said in enough detail to choose between them.
///
/// A person meeting this list is choosing between lines of work, and the
/// digest is the one thing about a revision that tells them nothing about
/// which line it is. The change ID, any bookmark, who wrote it, when, and the
/// first line of the message are what they recognise — so this prints what
/// `log` prints, for the heads and nothing else.
pub fn described(store: &Store, heads: &BTreeSet<RevisionId>) -> String {
    let mut out = String::new();
    for head in heads {
        let mut first = head.abbreviate(12);
        if let Some(revision) = store.revision(head) {
            let _ = write!(first, "  {}", revision.change);
        }
        for name in bookmarks(store, head) {
            let _ = write!(first, "  {name}");
        }
        let _ = writeln!(out, "  {first}");
        // The author and the moment are the document's, so a head whose
        // document will not parse is described by its digest and its change.
        let Some(document) = store.get(head).ok().flatten() else {
            continue;
        };
        let _ = writeln!(out, "      {}  {}", document.author, document.when);
        if let Some(summary) = document.message.lines().next()
            && !summary.is_empty()
        {
            let _ = writeln!(out, "      {summary}");
        }
    }
    // The caller's message ends with this, and a trailing blank line after a
    // list is a line nobody wrote.
    while out.ends_with('\n') {
        out.pop();
    }
    out
}

/// A revision abbreviated, with any bookmark that resolves to it.
///
/// A person choosing between two heads is choosing between two lines of work,
/// and the name they gave one is what tells them which is which.
pub fn spelled(store: &Store, id: &RevisionId) -> String {
    let mut out = id.abbreviate(12);
    for name in bookmarks(store, id) {
        let _ = write!(out, "  {name}");
    }
    out
}

/// Every bookmark resolving to this revision.
pub fn bookmarks(store: &Store, id: &RevisionId) -> Vec<String> {
    let history = store.history();
    store
        .names()
        .iter()
        .filter(|(_, bookmark)| match bookmark.target {
            Name::Revision(revision) => revision == *id,
            Name::Change(change) => matches!(
                history.change_state(&change),
                ChangeState::Resolved(revision) if revision.id == *id
            ),
            // A file bookmark names no revision, so it never marks one.
            Name::File(_) => false,
        })
        .map(|(name, _)| name.clone())
        .collect()
}

/// The one head, or a refusal naming the choice a person has to make.
fn head(store: &Store) -> Result<RevisionId, Failure> {
    let heads = current_heads(store);
    match heads.len() {
        0 => Err(Failure::error("this store holds no revisions yet")),
        1 => Ok(heads.into_iter().next().expect("one head")),
        several => Err(Failure::error(format!(
            "this store has {several} heads, so `head` names none of them; \
             name one, or join them with `historica merge`:\n{}",
            described(store, &heads)
        ))),
    }
}

/// A revision the store holds, or a message about the one it does not.
fn held(store: &Store, id: RevisionId, named_by: &str) -> Result<RevisionId, Failure> {
    if store.holds(&id) {
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
        .revisions()
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
pub fn listed(items: impl IntoIterator<Item = impl std::fmt::Display>) -> String {
    let mut out = String::new();
    for item in items {
        let _ = write!(out, "\n  {item}");
    }
    out
}
