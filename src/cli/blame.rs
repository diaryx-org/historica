//! `blame` — who wrote each line, read rather than guessed at.
//!
//! Decision 0038. Every other tool answers this question with a resemblance:
//! it diffs each pair of adjacent revisions and decides, line by line, which
//! line of the child was which line of the parent. The knobs that grew around
//! that — `-M`, `-C`, `-w`, `--ignore-rev` — are all arguments with a guess.
//!
//! There is no guess here. Decision 0007 records the items a revision
//! *inserted*, 0032 records which items a merge *kept* and under whose names,
//! and [`historica::merge::Merged::origins`] — the revision that wrote each
//! item, in file order — has been derived on every materialisation since 0012
//! needed it to label the runs inside a contested span. This command prints
//! that vector, and its whole implementation is the printing.
//!
//! Two consequences worth saying out loud. A line keeps its author across a
//! merge, because a resolution keeps items under their own names rather than
//! restating them — so a merge authors only the lines somebody actually typed
//! into it. And a rename is not a question at all: 0008 hangs paths off a
//! file identifier, so a file is one file for its whole life and there is
//! nothing for a `--follow` to follow.

use std::collections::BTreeMap;
use std::path::Path;

use historica::core::{FileId, RevisionId};
use historica::replay::State;
use historica::store::Store;
use historica::tree::{Kind, Tree};
use historica::working::{self, Working};

use super::diff::laid;
use super::{Failure, locate, printing, render, span, target};

/// `blame [<target>] <path> [--lines <first>..<last>]`
///
/// With a target, the file as that revision leaves it. With none, the file as
/// the folder holds it — the same right-hand side `diff` takes, and the lines
/// the folder has added are marked rather than attributed.
pub fn blame_command(base: &Path, arguments: Vec<String>) -> Result<u8, Failure> {
    let mut lines: Option<String> = None;
    let mut rest: Vec<String> = Vec::new();

    let mut arguments = arguments.into_iter();
    while let Some(argument) = arguments.next() {
        match argument.as_str() {
            "--lines" => {
                lines = Some(arguments.next().ok_or_else(|| {
                    Failure::usage("`--lines` wants a span, as `<first>..<last>`")
                })?);
            }
            other if other.starts_with('-') => {
                return Err(Failure::usage(format!(
                    "`{other}` is not an argument `blame` takes"
                )));
            }
            _ => rest.push(argument),
        }
    }
    let mut rest = rest.into_iter();
    let first = rest.next();
    let second = rest.next();
    if let Some(extra) = rest.next() {
        return Err(Failure::usage(format!(
            "`blame` takes a target and a path, and `{extra}` is a third argument"
        )));
    }

    let root = locate(base)?;
    let store = Store::open(&root)?;

    // 0001's disjoint alphabets again, and for 0037's reason: one argument is
    // a target or a path because nothing else could name either, and `path:`
    // is there for the file whose own name is spelled like a change.
    let (named, only) = match (first, second) {
        (Some(first), None) if !target::could_be_target(&store, &first) => (None, Some(first)),
        (first, second) => (first, second),
    };
    let Some(spelling) = only else {
        return Err(Failure::usage(
            "`blame` wants a path: it answers who wrote each line of one file",
        ));
    };

    let wanted = match &lines {
        Some(spelled) => {
            let (first, last) = span(spelled)?;
            if first == 0 || first > last {
                return Err(Failure::usage(
                    "a span runs from a first line to a last one, counting from 1",
                ));
            }
            Some((first, last))
        }
        None => None,
    };

    let rows = match named {
        Some(target) => recorded(&store, &target, &spelling)?,
        None => folder(&store, &root, &spelling)?,
    };
    let shown = limited(&rows, wanted)?;

    printing(|out| write(out, &store, &rows, shown))
}

/// One line of the file, and what the store says about it.
struct Row {
    /// The revision that wrote it, or `None` for a line only the folder has.
    by: Option<RevisionId>,
    /// What the item shows a reader — the marker, for a forgotten one.
    text: String,
    /// Whether it ends with a newline.
    terminated: bool,
}

/// One file as a revision leaves it, attributed.
///
/// The whole of the work is [`Store::merged_content`], which already answers
/// this: the state and the revision that wrote each of its items, derived
/// from the operations rather than recovered from the bytes.
fn recorded(store: &Store, target: &str, spelling: &str) -> Result<Vec<Row>, Failure> {
    let id = target::resolve(store, target)?;
    let file = target::file_in(store, &id, spelling)?;
    let tree = store.tree(&id).map_err(Failure::error)?;
    let path = tree.path(&file).unwrap_or(spelling).to_owned();
    lines_only(tree.kind(&file), &path)?;

    let merged = store.merged_content(&id, &file).map_err(Failure::error)?;
    let origins = merged.origins;
    Ok(merged
        .state
        .items()
        .iter()
        .enumerate()
        .map(|(at, item)| Row {
            by: origins.get(at).copied(),
            text: item.shown().to_owned(),
            terminated: item.terminated,
        })
        .collect())
}

/// One file as the folder holds it, attributed as far as the store can.
fn folder(store: &Store, root: &Path, spelling: &str) -> Result<Vec<Row>, Failure> {
    let repository = root
        .parent()
        .ok_or_else(|| Failure::error("this store has no repository around it"))?;
    let working = Working::read(repository, store.skipped()).map_err(Failure::error)?;

    let head = target::the_head(store)?;
    let tree = match head {
        Some(id) => store.tree(&id).map_err(Failure::error)?,
        None => Tree::empty(),
    };
    let (file, path) = names(store, &tree, head, spelling)?;

    if !working.holds(&path) {
        return Err(Failure::error(format!(
            "the folder holds no {path}; `historica blame <target> {path}` reads it \
             as a revision left it"
        )));
    }
    let bytes = working.bytes(&path).map_err(Failure::error)?;
    // A file the tree holds keeps the kind it was added with (0017); one the
    // tree does not is whatever the recorder would call it.
    match file.and_then(|file| tree.kind(&file)) {
        Some(kind) => lines_only(Some(kind), &path)?,
        None => lines_only(
            Some(if working::is_text(&bytes) {
                Kind::Lines
            } else {
                Kind::Whole
            }),
            &path,
        )?,
    }

    let (before, origins) = match (file, head) {
        (Some(file), Some(id)) => {
            let merged = store.merged_content(&id, &file).map_err(Failure::error)?;
            (merged.state, merged.origins)
        }
        // A file history has never heard of, which is every line unrecorded.
        _ => (State::empty(), Vec::new()),
    };
    let after = State::from_text(&String::from_utf8_lossy(&bytes));
    Ok(overlay(&before, &origins, &after))
}

/// Which file the argument names, and where the folder keeps it.
///
/// A `file:` spelling names an identifier, which the folder does not have, so
/// it is resolved against the position and the path comes back from the tree.
fn names(
    store: &Store,
    tree: &Tree,
    head: Option<RevisionId>,
    spelling: &str,
) -> Result<(Option<FileId>, String), Failure> {
    if spelling.starts_with(target::FILE_PREFIX) {
        let id = head
            .ok_or_else(|| Failure::error("there are no revisions here to name a file against"))?;
        let file = target::file_in(store, &id, spelling)?;
        let path = tree
            .path(&file)
            .ok_or_else(|| Failure::error("the position holds no path for that file"))?;
        return Ok((Some(file), path.to_owned()));
    }
    // Decision 0033: a store spells a path in normal form C, and a person's
    // keyboard, shell, and tab completion may not.
    let path = historica::format::nfc(
        spelling
            .strip_prefix(target::PATH_PREFIX)
            .unwrap_or(spelling),
    )
    .into_owned();
    let file = match tree.at(&path).as_slice() {
        // A file the folder has and history does not: every line is the
        // folder's own, and nothing here is an error.
        [] => None,
        [only] => Some(*only),
        // Two files claiming one path, which is `file_in`'s refusal to word.
        _ => Some(target::file_in(
            store,
            &head.ok_or_else(|| Failure::error("this store holds no position"))?,
            &path,
        )?),
    };
    Ok((file, path))
}

/// The folder's lines, attributed.
///
/// The lines history holds keep the revision that wrote them; the rest are the
/// folder's own and belong to nobody yet. Which is which comes from
/// `crate::diff`'s decomposition — the same one `record` would write down and
/// the same one `diff` prints — so the two commands cannot disagree about
/// what the folder has changed.
fn overlay(before: &State, origins: &[RevisionId], after: &State) -> Vec<Row> {
    let Some(document) = historica::diff::diff(before, after) else {
        return before
            .items()
            .iter()
            .enumerate()
            .map(|(at, item)| Row {
                by: origins.get(at).copied(),
                text: item.shown().to_owned(),
                terminated: item.terminated,
            })
            .collect();
    };

    let mut rows = Vec::new();
    let mut at = 0usize;
    for line in laid(before, &document) {
        match line.sign {
            '+' => rows.push(Row {
                by: None,
                text: line.text,
                terminated: line.terminated,
            }),
            '-' => at += 1,
            _ => {
                rows.push(Row {
                    by: origins.get(at).copied(),
                    text: line.text,
                    terminated: line.terminated,
                });
                at += 1;
            }
        }
    }
    rows
}

/// A file of bytes has no lines to attribute, per decision 0017.
fn lines_only(kind: Option<Kind>, path: &str) -> Result<(), Failure> {
    match kind {
        Some(Kind::Whole) => Err(Failure::error(format!(
            "{path} is a file of bytes: decision 0017 gives it no lines, and there \
             is nothing to attribute line by line"
        ))),
        _ => Ok(()),
    }
}

/// Which rows `--lines` asked for, as a range into all of them.
fn limited(rows: &[Row], wanted: Option<(usize, usize)>) -> Result<(usize, usize), Failure> {
    let Some((first, last)) = wanted else {
        return Ok((0, rows.len()));
    };
    if first > rows.len() {
        return Err(Failure::error(format!(
            "that span begins past the end: the file has {} lines",
            rows.len()
        )));
    }
    Ok((first - 1, last.min(rows.len())))
}

/// The rows, in columns as wide as they have to be.
///
/// The change ID rather than the digest, because 0001 makes the change the
/// name that survives amendment and rebase — and a person reading this is
/// about to type it into `show`. The author is the name half of what the
/// revision recorded: `log` prints the whole identity, and a column of email
/// addresses beside every line of a file is not a rendering anybody reads.
fn write(
    out: &mut impl std::io::Write,
    store: &Store,
    rows: &[Row],
    (start, end): (usize, usize),
) -> std::io::Result<()> {
    let changes = render::abbreviations(store.history().changes(), render::CHANGE_FLOOR);

    let mut said: BTreeMap<RevisionId, (String, String, String)> = BTreeMap::new();
    let mut column = |by: Option<RevisionId>| -> (String, String, String) {
        let Some(id) = by else {
            // A line the folder has and history does not. Attributing it would
            // be attributing work nobody has recorded.
            return ("-".to_owned(), "(the folder)".to_owned(), "-".to_owned());
        };
        said.entry(id)
            .or_insert_with(|| {
                let Some(document) = store.get(&id) else {
                    return (id.abbreviate(8), String::new(), String::new());
                };
                let when = document.when.to_string();
                (
                    changes
                        .get(&document.change)
                        .cloned()
                        .unwrap_or_else(|| document.change.to_string()),
                    author(&document.author).to_owned(),
                    when.get(..10).unwrap_or(&when).to_owned(),
                )
            })
            .clone()
    };

    let shown: Vec<(usize, (String, String, String), &Row)> = rows[start..end]
        .iter()
        .enumerate()
        .map(|(offset, row)| (start + offset + 1, column(row.by), row))
        .collect();

    let width = |pick: fn(&(String, String, String)) -> &String| {
        shown
            .iter()
            .map(|(_, columns, _)| pick(columns).chars().count())
            .max()
            .unwrap_or(0)
    };
    let change = width(|columns| &columns.0);
    let who = width(|columns| &columns.1);
    let day = width(|columns| &columns.2);
    let number = shown
        .last()
        .map_or(0, |(line, _, _)| line.to_string().len());

    for (line, columns, row) in &shown {
        writeln!(
            out,
            "{:>change$}  {:<who$}  {:<day$}  {:>number$}  {}",
            columns.0, columns.1, columns.2, line, row.text
        )?;
        // The same fact `diff` states, in the same words: a file whose last
        // line carries no terminator is a file this would otherwise print as
        // though it did.
        if !row.terminated {
            writeln!(out, "\\ no newline at end of file")?;
        }
    }
    Ok(())
}

/// The name half of a recorded author, which is what a column has room for.
fn author(recorded: &str) -> &str {
    recorded
        .split_once(" <")
        .map_or(recorded, |(name, _)| name)
        .trim()
}
