//! Rendering a store for a person.
//!
//! Nothing here is authority: every line is derived from files that say the
//! same thing more completely, and `show` prints those files unchanged. What
//! this module owes is that its abbreviations resolve and its order is
//! deterministic — a log that reordered itself between two runs of the same
//! store would be a worse lie than a long one.

use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::fmt::Display;
use std::io::{self, Write};
use std::path::Path;

use historica::core::{ChangeId, ChangeState, History, RevisionId};
use historica::format::{RevisionDocument, Timestamp};
use historica::record::Survey;
use historica::store::{Name, Report, Store};
use historica::tree::{Tree, TreeContest};

use super::target;

/// Digest characters shown where a digest is shown at all.
///
/// A floor rather than a fixed width: prefixes grow to stay unique, and
/// decision 0001 wants them abbreviated to the shortest that is.
const DIGEST_FLOOR: usize = 8;
/// Change ID characters shown, on the same terms.
pub(super) const CHANGE_FLOOR: usize = 8;

/// `log`: every revision, or one revision's ancestry, newest first.
pub fn log(out: &mut impl Write, store: &Store, from: Option<RevisionId>) -> io::Result<()> {
    let history = store.history();
    let heads = history.heads();
    let superseded = history.superseded();
    let divergent: BTreeSet<ChangeId> = history.divergent_changes().into_keys().collect();

    let shown = match from {
        Some(id) => ancestry(store, id),
        None => store.iter().map(|(id, _)| *id).collect(),
    };
    if shown.is_empty() {
        return writeln!(out, "no revisions here yet");
    }

    let digests = abbreviations(store.iter().map(|(id, _)| *id), DIGEST_FLOOR);
    let changes = abbreviations(history.changes(), CHANGE_FLOOR);

    for (index, id) in presentation(store, &shown).iter().enumerate() {
        let Some(document) = store.get(id) else {
            continue;
        };
        if index > 0 {
            writeln!(out)?;
        }
        entry(
            out,
            document,
            &digests[id],
            &changes[&document.change],
            &parenthesised(&marks(document, id, &heads, &superseded, &divergent)),
        )?;
    }
    Ok(())
}

/// One revision, as three or four lines.
fn entry(
    out: &mut impl Write,
    document: &RevisionDocument,
    digest: &str,
    change: &str,
    markers: &str,
) -> io::Result<()> {
    writeln!(out, "{change}  {digest}{markers}")?;
    writeln!(out, "    {}  {}", document.author, document.when)?;
    if let (Some(reviser), Some(when)) = (&document.revised_by, &document.revised) {
        writeln!(out, "    revised by {reviser}  {when}")?;
    }

    let facts = tree_facts(document);
    if !facts.is_empty() {
        writeln!(out, "    {facts}")?;
    }

    if document.message.trim().is_empty() {
        return writeln!(out, "    (no message)");
    }
    for line in document.message.lines() {
        if line.is_empty() {
            writeln!(out)?;
        } else {
            writeln!(out, "    {line}")?;
        }
    }
    Ok(())
}

/// What a revision says it did to the file set, counted.
fn tree_facts(document: &RevisionDocument) -> String {
    [
        ("added", document.added.len()),
        ("moved", document.moved.len()),
        // Decision 0034, counted apart from an edit because it is not one. A
        // file created executable says so with its `add` and is not counted
        // twice.
        (
            "mode",
            document
                .modes
                .keys()
                .filter(|file| !document.added.contains_key(*file))
                .count(),
        ),
        ("dropped", document.dropped.len()),
        ("edited", document.edited.len()),
        // Decision 0017: content stated whole, counted apart from an edit
        // because it is not one. A creation is already counted by `added`.
        (
            "stored",
            document
                .bytes
                .keys()
                .filter(|file| !document.added.contains_key(*file))
                .count(),
        ),
    ]
    .into_iter()
    .filter(|(_, count)| *count > 0)
    .map(|(what, count)| format!("{what} {count}"))
    .collect::<Vec<_>>()
    .join("  ")
}

/// The states worth saying out loud beside a revision.
fn marks(
    document: &RevisionDocument,
    id: &RevisionId,
    heads: &BTreeSet<RevisionId>,
    superseded: &BTreeSet<RevisionId>,
    divergent: &BTreeSet<ChangeId>,
) -> Vec<String> {
    let mut marks = Vec::new();
    if heads.contains(id) {
        marks.push("head".to_owned());
    }
    if document.parents.len() > 1 {
        marks.push("merge".to_owned());
    }
    if superseded.contains(id) {
        marks.push("superseded".to_owned());
    }
    if !document.supersedes.is_empty() {
        marks.push(format!("rewrites {}", document.supersedes.len()));
    }
    if divergent.contains(&document.change) {
        marks.push("divergent".to_owned());
    }

    marks
}

/// Marks as they sit after a digest, or nothing where there are none.
fn parenthesised(marks: &[String]) -> String {
    if marks.is_empty() {
        String::new()
    } else {
        format!("  ({})", marks.join(", "))
    }
}

/// `status`: where the folder is, and what it differs by.
///
/// Decision 0015. Nothing printed here was stored: the position is derived
/// from the graph, the facts from a survey nothing wrote down, and the names
/// from the one file in a store that is rewritten in place.
pub fn status(
    out: &mut impl Write,
    store: &Store,
    parents: &[RevisionId],
    survey: &Survey,
) -> io::Result<()> {
    position(out, store, parents)?;

    for (fact, path) in survey.facts() {
        writeln!(out, "{fact:<7} {path}")?;
    }
    for (path, because) in &survey.refused {
        writeln!(out, "{:<7} {path}: {because}", "refused")?;
    }
    for (path, files) in &survey.unsettled {
        writeln!(
            out,
            "{:<7} {path}: {} files claim it; say where each goes with --at",
            "claimed",
            files.len()
        )?;
    }
    for (path, lines) in &survey.standing {
        writeln!(out, "{:<7} {path} ({lines} left)", "marked")?;
    }
    for path in &survey.contested_bytes {
        writeln!(
            out,
            "{:<7} {path}: selected revisions state different bytes; \
             record with --accept {path}",
            "accept"
        )?;
    }

    // Only where a person said they were joining work. A contest deeper in the
    // graph was settled when its merge was recorded, and repeating it under
    // every status would be noise about a decision nobody is making now.
    if parents.len() > 1 {
        for contest in &survey.contested {
            if !matches!(contest, TreeContest::Path { .. }) {
                writeln!(out, "{}", contest_line(contest))?;
            }
        }
    }

    if survey.is_empty()
        && survey.refused.is_empty()
        && survey.unsettled.is_empty()
        && survey.contested_bytes.is_empty()
    {
        writeln!(out, "nothing here differs from what is recorded")?;
    }

    // Beside the facts and never instead of them: what `record` would state is
    // still an `added` and a `dropped` until a person says otherwise.
    for (from, to) in &survey.renames {
        writeln!(out)?;
        writeln!(
            out,
            "{from} and {to} hold the same bytes; if that is a rename,"
        )?;
        writeln!(out, "say so with --move {from}={to}")?;
    }
    Ok(())
}

/// The revisions the folder is being compared with, named as `log` names them.
fn position(out: &mut impl Write, store: &Store, parents: &[RevisionId]) -> io::Result<()> {
    if parents.is_empty() {
        return writeln!(out, "no revisions here yet");
    }

    let history = store.history();
    let heads = history.heads();
    let superseded = history.superseded();
    let divergent: BTreeSet<ChangeId> = history.divergent_changes().into_keys().collect();
    // Abbreviated against every revision the store holds, as `log` does, so
    // that the prefix printed here is one `show` and `--onto` will resolve.
    let digests = abbreviations(store.iter().map(|(id, _)| *id), DIGEST_FLOOR);
    let changes = abbreviations(history.changes(), CHANGE_FLOOR);

    for id in parents {
        let Some(document) = store.get(id) else {
            continue;
        };
        let mut marks = marks(document, id, &heads, &superseded, &divergent);
        marks.extend(target::bookmarks(store, id));
        writeln!(
            out,
            "{}  {}{}",
            changes[&document.change],
            digests[id],
            parenthesised(&marks)
        )?;
    }
    Ok(())
}

/// One tree contest, as a person needs to hear it.
pub fn contest_line(contest: &TreeContest) -> String {
    match contest {
        TreeContest::Dropped { file, by } => format!(
            "kept {} : {} dropped it, and concurrent work did not",
            file.abbreviate(8),
            by.iter()
                .map(|revision| revision.abbreviate(8))
                .collect::<Vec<_>>()
                .join(", ")
        ),
        TreeContest::Moved { file, paths } => format!(
            "moved {} to {}, which is the lower digest of {}",
            file.abbreviate(8),
            paths[0].1,
            paths
                .iter()
                .map(|(_, path)| path.as_str())
                .collect::<Vec<_>>()
                .join(" and ")
        ),
        TreeContest::Mode { file, modes } => format!(
            "{} is {}, which is the lower digest of {}",
            file.abbreviate(8),
            modes[0].1,
            modes
                .iter()
                .map(|(_, mode)| mode.spelling())
                .collect::<Vec<_>>()
                .join(" and ")
        ),
        TreeContest::Content { file, payloads } => format!(
            "{} was stated whole by {} concurrent revisions, and bytes do not merge; \
             put the version you mean in the folder",
            file.abbreviate(8),
            payloads.len()
        ),
        TreeContest::Path { path, files } => format!(
            "{} files claim {path}; say where each goes with --at:{}",
            files.len(),
            files
                .iter()
                .map(|file| format!("\n  --at {file}=<path>"))
                .collect::<String>()
        ),
        // `TreeContest` may grow; a contest nobody here knows about is still
        // worth saying out loud rather than passing over in silence.
        other => format!("{other:?}"),
    }
}

/// `files`: the file set at one revision, by path.
pub fn files(out: &mut impl Write, tree: &Tree) -> io::Result<()> {
    if tree.is_empty() {
        return writeln!(out, "no files here");
    }

    let mut rows: Vec<(&str, String)> = tree
        .files()
        .map(|(file, path)| (path, file.to_string()))
        .collect();
    rows.sort();

    let width = rows.iter().map(|(path, _)| path.len()).max().unwrap_or(0);
    for (path, file) in rows {
        writeln!(out, "{path:width$}  {file}")?;
    }
    Ok(())
}

/// `names`: each bookmark, what its file says, and what that resolves to.
pub fn names(out: &mut impl Write, store: &Store) -> io::Result<()> {
    let bookmarks = store.names();
    if bookmarks.is_empty() {
        return writeln!(out, "no bookmarks here yet");
    }

    let history = store.history();
    let digests = abbreviations(store.iter().map(|(id, _)| *id), DIGEST_FLOOR);
    let width = bookmarks.keys().map(String::len).max().unwrap_or(0);
    // Decision 0024: a file bookmark deliberately records no revision, so what
    // it resolves to is where that file sits now — which is the question a
    // person made the bookmark to stop having to ask.
    let here = store
        .merged_tree_of(&target::current_heads(store).into_iter().collect::<Vec<_>>())
        .ok();

    for (name, target) in bookmarks {
        let resolution = match target {
            Name::Revision(id) => match digests.get(id) {
                Some(digest) => digest.clone(),
                None => "(not here yet)".to_owned(),
            },
            Name::Change(change) => resolution(&history, *change, &digests),
            Name::File(file) => here
                .as_ref()
                .and_then(|merged| merged.tree.path(file))
                .map_or_else(|| "(no file here has it)".to_owned(), str::to_owned),
        };
        writeln!(out, "{name:width$}  {target}  ->  {resolution}")?;
    }
    Ok(())
}

/// What a change currently means, in one phrase.
fn resolution(
    history: &History,
    change: ChangeId,
    digests: &BTreeMap<RevisionId, String>,
) -> String {
    match history.change_state(&change) {
        ChangeState::Resolved(revision) => digests
            .get(&revision.id)
            .cloned()
            .unwrap_or_else(|| revision.id.abbreviate(DIGEST_FLOOR)),
        ChangeState::Unknown => "(no revision here claims it)".to_owned(),
        ChangeState::Abandoned => "(abandoned: every revision was superseded)".to_owned(),
        ChangeState::Divergent(revisions) => {
            format!("({} current revisions; divergent)", revisions.len())
        }
    }
}

/// `check`: errors, then notes, then a line saying how it went.
pub fn report(out: &mut impl Write, root: &Path, report: &Report) -> io::Result<()> {
    for finding in report.errors() {
        writeln!(out, "error: {finding}")?;
    }
    for finding in report.notes() {
        writeln!(out, "note: {finding}")?;
    }

    let errors = report.errors().count();
    let notes = report.notes().count();
    let summary = if errors == 0 && notes == 0 {
        "nothing to report".to_owned()
    } else {
        format!("{}, {}", counted(errors, "error"), counted(notes, "note"))
    };
    writeln!(out, "{}: {summary}", root.display())?;

    // Said after the summary rather than counted into it: an incomplete store
    // is not a broken one, and `--complete` is the caller who has decided that
    // for this particular store, at this particular moment, it is.
    if !report.is_complete() {
        let heads = report.incomplete().count();
        writeln!(
            out,
            "{}: {} here cannot be produced from what is here",
            root.display(),
            counted(heads, "head")
        )?;
    }
    Ok(())
}

/// `1 error`, `2 errors`, `no errors`.
fn counted(count: usize, thing: &str) -> String {
    match count {
        0 => format!("no {thing}s"),
        1 => format!("1 {thing}"),
        many => format!("{many} {thing}s"),
    }
}

/// Every revision reachable from `head` through parent edges.
///
/// Unlike materialising a file, walking the graph is defined for a merge, so
/// this follows every parent rather than refusing the second one.
fn ancestry(store: &Store, head: RevisionId) -> BTreeSet<RevisionId> {
    let mut seen = BTreeSet::new();
    let mut queue = VecDeque::from([head]);
    while let Some(id) = queue.pop_front() {
        if !seen.insert(id) {
            continue;
        }
        let Some(document) = store.get(&id) else {
            // An undelivered parent is a legitimate state, per decision 0006.
            continue;
        };
        queue.extend(document.parents.iter().copied());
    }
    seen.retain(|id| store.get(id).is_some());
    seen
}

/// `shown`, children before parents: a log reads from the work back.
///
/// Causality decides everything this can decide: a revision appears only once
/// every revision that names it as a parent has appeared. Where the graph
/// leaves two revisions unordered — concurrent work, or two roots — the tie is
/// broken by `when` as written and then by digest.
///
/// That is presentation and nothing else. Decision 0002 keeps timestamps out
/// of identity, causality, and ordering, and none of them is being computed
/// here; the timestamps are compared as spelled, which is the day each author
/// had rather than an instant on a clock they shared. The digest is what makes
/// the result the same on every machine even when two of them disagree.
fn presentation(store: &Store, shown: &BTreeSet<RevisionId>) -> Vec<RevisionId> {
    let mut waiting: BTreeMap<RevisionId, usize> = shown.iter().map(|id| (*id, 0)).collect();
    let mut parents: BTreeMap<RevisionId, Vec<RevisionId>> = BTreeMap::new();

    for id in shown {
        let named: Vec<RevisionId> = store
            .get(id)
            .into_iter()
            .flat_map(|document| document.parents.iter().copied())
            .filter(|parent| shown.contains(parent))
            .collect();
        for parent in &named {
            *waiting.get_mut(parent).expect("a revision in the set") += 1;
        }
        parents.insert(*id, named);
    }

    let mut ready: BTreeSet<(Option<Timestamp>, RevisionId)> = waiting
        .iter()
        .filter(|(_, children)| **children == 0)
        .map(|(id, _)| (when(store, id), *id))
        .collect();

    let mut order = Vec::with_capacity(shown.len());
    while let Some((_, id)) = ready.pop_last() {
        order.push(id);
        waiting.remove(&id);
        for parent in parents.get(&id).into_iter().flatten() {
            if let Some(children) = waiting.get_mut(parent) {
                *children -= 1;
                if *children == 0 {
                    ready.insert((when(store, parent), *parent));
                }
            }
        }
    }

    // A cycle cannot happen: a parent edge names a digest of bytes that
    // already existed. If one ever did, showing the revisions is better than
    // dropping them.
    order.extend(waiting.into_keys());
    order
}

/// The timestamp a revision carries, for the tie it breaks and nothing else.
///
/// `None` only for a revision that left the store between two reads of it,
/// which sorts it last rather than inventing a date for it.
fn when(store: &Store, id: &RevisionId) -> Option<Timestamp> {
    store.get(id).map(|document| document.when.clone())
}

/// The shortest prefix of each spelling that names only itself.
///
/// Decision 0001 asks for exactly this, and for the reason that change ID
/// prefixes survive rewriting. Digests get the same treatment because the
/// alternative is a fixed width that is either noise or ambiguous.
pub(super) fn abbreviations<T: Copy + Ord + Display>(
    ids: impl IntoIterator<Item = T>,
    floor: usize,
) -> BTreeMap<T, String> {
    let mut spellings: Vec<(String, T)> = ids
        .into_iter()
        .map(|id| (id.to_string(), id))
        .collect::<BTreeMap<_, _>>()
        .into_iter()
        .collect();
    spellings.sort();

    let mut out = BTreeMap::new();
    for (index, (spelling, id)) in spellings.iter().enumerate() {
        let before = index
            .checked_sub(1)
            .map_or(0, |previous| shared(spelling, &spellings[previous].0));
        let after = spellings
            .get(index + 1)
            .map_or(0, |(next, _)| shared(spelling, next));
        let needed = before.max(after) + 1;
        let width = needed.max(floor).min(spelling.chars().count());
        out.insert(*id, spelling.chars().take(width).collect());
    }
    out
}

/// How many leading characters two spellings share.
fn shared(left: &str, right: &str) -> usize {
    left.chars()
        .zip(right.chars())
        .take_while(|(left, right)| left == right)
        .count()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn id(byte: u8) -> RevisionId {
        let mut bytes = [0u8; 32];
        bytes[0] = byte;
        RevisionId::from_bytes(bytes)
    }

    #[test]
    fn abbreviations_grow_only_as_far_as_they_must() {
        let short = abbreviations([id(0x00), id(0xff)], 4);
        assert_eq!(short[&id(0x00)], "0000");
        assert_eq!(short[&id(0xff)], "ff00");

        // Two digests sharing eight characters need a ninth to be told apart.
        let mut left = [0u8; 32];
        let mut right = [0u8; 32];
        right[4] = 0x10;
        let close = abbreviations(
            [RevisionId::from_bytes(left), RevisionId::from_bytes(right)],
            4,
        );
        left[0] = 0;
        assert_eq!(close[&RevisionId::from_bytes(left)].len(), 9);
        assert_eq!(close[&RevisionId::from_bytes(right)].len(), 9);
    }

    #[test]
    fn a_lone_revision_gets_the_floor() {
        let only = abbreviations([id(0x0a)], 6);
        assert_eq!(only[&id(0x0a)], "0a0000");
    }
}
