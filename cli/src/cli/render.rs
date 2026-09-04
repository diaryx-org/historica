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

use historica::core::{ChangeId, ChangeState, FileId, History, RevisionId};
use historica::format::{RevisionDocument, Timestamp};
use historica::record::Survey;
use historica::store::{Name, Report, Store};
use historica::tree::{Tree, TreeContest};
use historica::wrote::{self, Statement};

use super::target;

/// Digest characters shown where a digest is shown at all.
///
/// A floor rather than a fixed width: prefixes grow to stay unique, and
/// decision 0001 wants them abbreviated to the shortest that is.
const DIGEST_FLOOR: usize = 8;
/// Change ID characters shown, on the same terms.
pub(super) const CHANGE_FLOOR: usize = 8;

/// Characters of a timestamp before its offset: `2025-08-19T00:47:11`.
const WALL: usize = 19;

/// A timestamp's wall clock, which is the date and time its author read.
///
/// Decision 0002 keeps timestamps out of identity, causality, and ordering, so
/// there is no shared instant here for a bound to be compared against. What is
/// left is the fact the format kept deliberately: the day and hour each author
/// had, in the offset they were in.
pub fn wall(spelled: &str) -> &str {
    spelled.get(..WALL).unwrap_or(spelled)
}

/// What `log` was asked to leave out.
///
/// Every field is a reason to skip a revision, so an empty filter keeps
/// everything, and several compose by keeping only what satisfies all of them.
/// The limit is not one of those reasons: it counts what survived them.
#[derive(Debug, Default)]
pub struct Filter {
    /// Stop after this many entries.
    pub limit: Option<usize>,
    /// Keep a revision whose author line holds this text.
    pub author: Option<String>,
    /// Keep a revision whose message holds this text.
    pub grep: Option<String>,
    /// Keep a revision recorded at or after this wall clock.
    pub since: Option<String>,
    /// Keep a revision recorded at or before this wall clock.
    pub until: Option<String>,
    /// Keep a revision stating any fact about this file.
    pub file: Option<FileId>,
}

impl Filter {
    /// Whether anything but the limit was asked for.
    fn selects(&self) -> bool {
        self.author.is_some()
            || self.grep.is_some()
            || self.since.is_some()
            || self.until.is_some()
            || self.file.is_some()
    }

    /// Whether this revision survives every filter but the limit.
    fn keeps(&self, document: &RevisionDocument) -> bool {
        if let Some(author) = &self.author
            && !document.author.contains(author.as_str())
        {
            return false;
        }
        if let Some(text) = &self.grep
            && !document.message.contains(text.as_str())
        {
            return false;
        }
        if let Some(since) = &self.since
            && wall(document.when.as_str()) < since.as_str()
        {
            return false;
        }
        if let Some(until) = &self.until
            && wall(document.when.as_str()) > until.as_str()
        {
            return false;
        }
        if let Some(file) = &self.file
            && !historica::tree::touches(document, file)
        {
            return false;
        }
        true
    }
}

/// Which revisions a `log` covers: an ancestry, a range, or the whole store.
///
/// Separate from the rendering so that the command can hold every document it
/// covers to the parser before printing any of it — decision 0061 defers that
/// parse to here, and a revision skipped for want of it would be a history
/// printed with a hole in it rather than an error.
pub fn shown(store: &Store, reach: Option<&target::Reach>) -> BTreeSet<RevisionId> {
    match reach {
        None => store.revisions().map(|(id, _)| *id).collect(),
        Some(target::Reach::From(id)) => ancestry(store, *id),
        // Decision 0063: what `to` has behind it and `from` does not. One
        // ancestry taken out of another, which is defined for two revisions
        // the graph leaves concurrent as readily as for two along a chain —
        // the chain is only the case with nothing on the other side.
        Some(target::Reach::Between { from, to }) => {
            let had = ancestry(store, *from);
            let mut shown = ancestry(store, *to);
            shown.retain(|id| !had.contains(id));
            shown
        }
    }
}

/// `log`: every revision, or one revision's ancestry, newest first.
///
/// A filter takes entries out of the list and changes nothing about the ones
/// that stay: `(head)` is a fact about the graph rather than about this
/// listing, so a head stays marked as one whether or not its children were
/// asked for.
pub fn log(
    out: &mut impl Write,
    store: &Store,
    shown: &BTreeSet<RevisionId>,
    filter: &Filter,
) -> io::Result<()> {
    let history = store.history();
    let heads = history.heads();
    let superseded = history.superseded();
    let divergent: BTreeSet<ChangeId> = history.divergent_changes().into_keys().collect();

    let digests = abbreviations(store.revisions().map(|(id, _)| *id), DIGEST_FLOOR);
    let changes = abbreviations(history.changes(), CHANGE_FLOOR);

    let kept = kept(store, shown, filter);
    if kept.is_empty() && filter.selects() {
        return writeln!(out, "no revision here matches all of those");
    }

    for (index, id) in kept
        .iter()
        .take(filter.limit.unwrap_or(usize::MAX))
        .enumerate()
    {
        // Every one of these parsed when the command held them to the
        // parser, before a byte was printed.
        let Some(document) = store.get(id).ok().flatten() else {
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

/// The revisions a listing shows, in order, with the filters applied.
///
/// The limit is not applied here: it counts what the filters left, and both
/// renderings take it from the front of this.
fn kept(store: &Store, shown: &BTreeSet<RevisionId>, filter: &Filter) -> Vec<RevisionId> {
    presentation(store, shown)
        .into_iter()
        .filter(|id| {
            store
                .get(id)
                .ok()
                .flatten()
                .is_some_and(|document| filter.keeps(document))
        })
        .collect()
}

/// The header a machine-read listing begins with.
///
/// Numbered, for the reason decision 0048 numbers an offer's: a document is
/// permanent and a store's grammar is a promise, and this is neither. A reader
/// that meets a spelling it does not know discards the listing whole rather
/// than guessing at the fields — which is the whole reason the line is there,
/// since the listing is otherwise indistinguishable from a shell's idea of
/// five words.
pub const FIELDS_HEADER: &str = "historica-log-1";

/// The header the writing half's statements begin with, decision 0074.
///
/// The sibling of [`FIELDS_HEADER`], and the whole of what this module holds
/// of that grammar. The writer and the parser are `historica::wrote`, in the
/// library: `historica-minisign` and `historica-git` read this format from the
/// far side of a pipe, and a parser in here is one neither of them can link.
pub const WROTE_HEADER: &str = wrote::HEADER;

/// Print what a command wrote, for something that is not a person.
///
/// The statement is assembled by the command, from the values the library
/// returned it, and printed here so that the two `--fields` outputs are
/// reached the same way.
pub fn wrote(out: &mut impl Write, statement: &Statement) -> io::Result<()> {
    statement.write(out)
}

/// `log --fields`: the same listing, for something that is not a person.
///
/// Decision 0064. One line per revision, single spaces between fields, and
/// nothing escaped because no field here can hold a space. What is *not* here
/// is anything a person wrote: `show` prints the document those live in, byte
/// for byte, and a second rendering of a message is a second answer that could
/// disagree with the first.
///
/// ```text
/// historica-log-1
/// <digest> <change> <when> <marks|-> <parent>...
/// ```
pub fn fields(
    out: &mut impl Write,
    store: &Store,
    shown: &BTreeSet<RevisionId>,
    filter: &Filter,
) -> io::Result<()> {
    let history = store.history();
    let heads = history.heads();
    let superseded = history.superseded();
    let divergent: BTreeSet<ChangeId> = history.divergent_changes().into_keys().collect();

    writeln!(out, "{FIELDS_HEADER}")?;
    for id in kept(store, shown, filter)
        .iter()
        .take(filter.limit.unwrap_or(usize::MAX))
    {
        let Some(document) = store.get(id).ok().flatten() else {
            continue;
        };
        // Spelled whole, where the reading for a person abbreviates. An
        // abbreviation is a fact about what else the store holds today
        // (decision 0001), so a caller that wrote one down would find it
        // ambiguous after a fetch — through no change to the revision it
        // named.
        write!(out, "{id} {} {}", document.change, document.when)?;
        write!(
            out,
            " {}",
            found(id, document, &heads, &superseded, &divergent)
        )?;
        for parent in &document.parents {
            write!(out, " {parent}")?;
        }
        writeln!(out)?;
    }
    Ok(())
}

/// The marks, as the machine reading spells them.
///
/// Only what the graph found: whether nothing stands on this revision,
/// whether something rewrote it, and whether its change has more than one
/// revision anybody could mean. `merge` and `rewrites` are not here, because
/// the document says both outright — `parent` twice and `supersedes` at all —
/// and this listing does not restate what the file it points at already says.
fn found(
    id: &RevisionId,
    document: &RevisionDocument,
    heads: &BTreeSet<RevisionId>,
    superseded: &BTreeSet<RevisionId>,
    divergent: &BTreeSet<ChangeId>,
) -> String {
    let mut found = Vec::new();
    if heads.contains(id) {
        found.push("head");
    }
    if superseded.contains(id) {
        found.push("superseded");
    }
    if divergent.contains(&document.change) {
        found.push("divergent");
    }
    if found.is_empty() {
        // A field is never empty, because an empty one would be two spaces
        // where a reader splitting on one expects a word.
        return "-".to_owned();
    }
    found.join(",")
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
        // Decision 0040, counted the same way and for the same reason: a link
        // arriving says so with its `add`, and a retarget is its own fact.
        (
            "link",
            document
                .links
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
    let digests = abbreviations(store.revisions().map(|(id, _)| *id), DIGEST_FLOOR);
    let changes = abbreviations(history.changes(), CHANGE_FLOOR);

    for id in parents {
        let Some(document) = store.get(id).ok().flatten() else {
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
        TreeContest::Target { file, targets } => format!(
            "{} points at {}, which is the lower digest of {}",
            file.abbreviate(8),
            targets[0].1,
            targets
                .iter()
                .map(|(_, target)| target.to_string())
                .collect::<Vec<_>>()
                .join(" and ")
        ),
        TreeContest::Referenced { file, by, links } => format!(
            "kept {} : {} dropped it, and {} still {} at it",
            file.abbreviate(8),
            by.iter()
                .map(|revision| revision.abbreviate(8))
                .collect::<Vec<_>>()
                .join(", "),
            links
                .iter()
                .map(|link| link.abbreviate(8))
                .collect::<Vec<_>>()
                .join(", "),
            if links.len() == 1 { "points" } else { "point" }
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
    let digests = abbreviations(store.revisions().map(|(id, _)| *id), DIGEST_FLOOR);
    let width = bookmarks.keys().map(String::len).max().unwrap_or(0);
    // Decision 0024: a file bookmark deliberately records no revision, so what
    // it resolves to is where that file sits now — which is the question a
    // person made the bookmark to stop having to ask.
    let here = store
        .merged_tree_of(&target::current_heads(store).into_iter().collect::<Vec<_>>())
        .ok();

    for (name, bookmark) in bookmarks {
        let resolution = match bookmark.target {
            Name::Revision(id) => match digests.get(&id) {
                Some(digest) => digest.clone(),
                None => "(not here yet)".to_owned(),
            },
            Name::Change(change) => resolution(&history, change, &digests),
            Name::File(file) => here
                .as_ref()
                .and_then(|merged| merged.tree.path(&file))
                .map_or_else(|| "(no file here has it)".to_owned(), str::to_owned),
        };
        // Decision 0062's axis, printed: the listing is where a person checks
        // what an export would carry, and a bookmark that did not say which it
        // was would be one they had to `cat` to find out.
        writeln!(out, "{name:width$}  {bookmark}  ->  {resolution}")?;
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
///
/// `complete` says whether the caller already asked the completeness
/// question, which decides only whether the flag is named back to them.
pub fn report(
    out: &mut impl Write,
    root: &Path,
    report: &Report,
    complete: bool,
) -> io::Result<()> {
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
        // The flag is named where the state it exists for is being reported,
        // and only to a caller who did not already ask for it: a backup being
        // trusted is exactly the reader who has to be told this can fail.
        if !complete {
            writeln!(out, "`check --complete` is the run that fails on that")?;
        }
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
        let Some(revision) = store.revision(&id) else {
            // An undelivered parent is a legitimate state, per decision 0006.
            continue;
        };
        queue.extend(revision.parents.iter().copied());
    }
    seen.retain(|id| store.holds(id));
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
            .revision(id)
            .into_iter()
            .flat_map(|revision| revision.parents.iter().copied())
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
    store
        .get(id)
        .ok()
        .flatten()
        .map(|document| document.when.clone())
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
