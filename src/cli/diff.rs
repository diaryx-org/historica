//! `diff` — what changed, rendered for a person to read.
//!
//! Decision 0037. Everything else that reads a store prints what the store
//! holds: `show` prints a document byte for byte, because the readable file is
//! the authority and a rendering of it is not. This command is the rendering,
//! said out loud — nothing here is stored, nothing reads it back, and the
//! shape it prints in is borrowed from a format other tools already read.
//!
//! What it compares is two sides, and the two sides are not alike. A revision
//! records identity: 0008 hangs paths off a file identifier, so a rename
//! between two revisions is a fact this reads rather than a resemblance it
//! guesses at, and a file that moved twice and was edited in between is still
//! one file. The folder has no identifiers at all — 0011 makes a rename the
//! one thing a person has to state — so a moved file there is a drop and an
//! add until somebody says `--move`, exactly as `status` reports it. Rendering
//! those two cases the same way would mean either inventing a rename the
//! folder cannot see or discarding one the store wrote down.

use std::collections::{BTreeMap, BTreeSet};
use std::io::Write;
use std::path::Path;

use historica::core::{FileId, RevisionId};
use historica::diff;
use historica::format::Mode;
use historica::replay::State;
use historica::store::{Content, Store};
use historica::tree::{Kind, Tree};
use historica::working::{self, Working};

use super::{Failure, locate, printing, target};

/// How many unchanged lines to show around a change.
///
/// Three, which is what every tool that reads this format defaults to.
const CONTEXT: usize = 3;

/// `diff [<target>] [<path>] [--onto <target>]`
///
/// The left side is `--onto` where it is given. Where it is not, it is the
/// named revision's parent — so `diff <target>` is "what that revision did",
/// which is the question `log` leaves a person holding. The right side is the
/// named revision, or the folder when nothing is named.
pub fn diff_command(base: &Path, arguments: Vec<String>) -> Result<u8, Failure> {
    let mut onto: Option<String> = None;
    let mut rest: Vec<String> = Vec::new();

    let mut arguments = arguments.into_iter();
    while let Some(argument) = arguments.next() {
        match argument.as_str() {
            "--onto" => {
                onto = Some(
                    arguments
                        .next()
                        .ok_or_else(|| Failure::usage("`--onto` wants a value"))?,
                );
            }
            _ => rest.push(argument),
        }
    }
    let mut rest = rest.into_iter();
    let first = rest.next();
    let second = rest.next();
    if let Some(extra) = rest.next() {
        return Err(Failure::usage(format!(
            "`diff` takes a target and a path, and `{extra}` is a third argument"
        )));
    }

    let root = locate(base)?;
    let store = Store::open(&root)?;

    // One argument is a target or a path, and 0001's disjoint alphabets are
    // what decide which without guessing: `diff notes.md` is the folder's own
    // file, and `diff kxry` is a revision. Two arguments are always a target
    // and then a path, as `show` and `cat` already spell it, and `path:` is
    // there for the file whose name is spelled like a change.
    let (named, only) = match (first, second) {
        (Some(first), None) if !target::could_be_target(&store, &first) => (None, Some(first)),
        (first, second) => (first, second),
    };

    // The right side, and with it the revision a `file:` spelling is resolved
    // against: a file identifier abbreviates against a stated set, and the set
    // is the one being looked at.
    let right = match &named {
        Some(spelling) => Some(target::resolve(&store, spelling)?),
        None => None,
    };

    let left = match (&onto, right) {
        // Stated, and it wins in both directions.
        (Some(spelling), _) => Some(target::resolve(&store, spelling)?),
        // What that revision did: its parent, which is the comparison a
        // person reading `log` is already making in their head.
        (None, Some(id)) => sole_parent(&store, &id)?,
        // The folder against the position, which is what `status` counts —
        // and refused in the same words when a person has to choose.
        (None, None) => target::the_head(&store)?,
    };

    // A path limits everything below to one file. Resolved against whichever
    // side names a file set — decision 0024's `file:` reaches through a
    // rename, which is the thing a path cannot spell.
    let limit = match &only {
        Some(spelling) => Some(one_file(&store, right, left, spelling)?),
        None => None,
    };

    let pairs = match right {
        Some(id) => recorded(&store, left, id, limit.as_ref())?,
        None => folder(&store, &root, left, limit.as_ref())?,
    };

    printing(|out| {
        if pairs.is_empty() {
            return writeln!(out, "nothing differs");
        }
        for pair in &pairs {
            render(out, pair)?;
        }
        Ok(())
    })
}

/// Which file a path or `file:` spelling names, on whichever side has one.
fn one_file(
    store: &Store,
    right: Option<RevisionId>,
    left: Option<RevisionId>,
    spelling: &str,
) -> Result<Named, Failure> {
    // A `file:` spelling names an identifier, which both sides share and a
    // rename does not change. Everything else is a path, which belongs to a
    // side and may differ between them.
    if spelling.starts_with("file:") {
        let against = right
            .or(left)
            .ok_or_else(|| Failure::error("there is no revision here to name a file against"))?;
        return Ok(Named::File(target::file_in(store, &against, spelling)?));
    }
    let path = spelling.strip_prefix("path:").unwrap_or(spelling);
    Ok(Named::Path(historica::format::nfc(path).into_owned()))
}

/// One file a comparison limits itself to.
enum Named {
    /// An identifier, which survives every rename between the two sides.
    File(FileId),
    /// A path, which is a name one side gave a file at one moment.
    Path(String),
}

impl Named {
    fn wants(&self, file: Option<&FileId>, paths: [Option<&String>; 2]) -> bool {
        match self {
            Named::File(wanted) => file == Some(wanted),
            Named::Path(wanted) => paths.iter().flatten().any(|path| *path == wanted),
        }
    }
}

/// The one parent of a revision, for the "what did this do" comparison.
fn sole_parent(store: &Store, id: &RevisionId) -> Result<Option<RevisionId>, Failure> {
    let document = store
        .get(id)
        .ok_or_else(|| Failure::error(format!("{} is not a revision here", id.abbreviate(12))))?;
    match document
        .parents
        .iter()
        .copied()
        .collect::<Vec<_>>()
        .as_slice()
    {
        [] => Ok(None),
        [only] => Ok(Some(*only)),
        // A merge did something different to each side, and which of them a
        // reader means is a question this cannot answer for them.
        several => Err(Failure::error(format!(
            "{} is a merge, so what it did depends on which side you are asking about; \
             name one with --onto:{}",
            id.abbreviate(12),
            several
                .iter()
                .map(|parent| format!(
                    "\n  historica diff {} --onto {}",
                    id.abbreviate(12),
                    parent.abbreviate(12)
                ))
                .collect::<String>()
        ))),
    }
}

/// One file, as the two sides hold it.
struct Pair {
    /// Where it sat on the left, or `None` where the left does not hold it.
    from: Option<String>,
    /// Where it sits on the right, or `None` where the right does not.
    to: Option<String>,
    before: Option<Content>,
    after: Option<Content>,
    /// The mode on each side, where they differ. Decision 0034.
    modes: Option<(Mode, Mode)>,
}

impl Pair {
    /// Whether anything about this file differs between the sides.
    fn differs(&self) -> bool {
        self.from != self.to
            || self.modes.is_some()
            || match (&self.before, &self.after) {
                (Some(before), Some(after)) => before.bytes() != after.bytes(),
                (None, None) => false,
                _ => true,
            }
    }
}

/// Two revisions, paired by identifier.
///
/// This is the half decision 0008 pays for. Files carry identifiers and paths
/// hang off them, so the same file under two names is one row here and a
/// rename is stated rather than inferred — including a rename with an edit in
/// it, which resemblance could not have recovered.
fn recorded(
    store: &Store,
    left: Option<RevisionId>,
    right: RevisionId,
    limit: Option<&Named>,
) -> Result<Vec<Pair>, Failure> {
    let before = match left {
        Some(id) => store.tree(&id).map_err(Failure::error)?,
        None => Tree::empty(),
    };
    let after = store.tree(&right).map_err(Failure::error)?;

    let files: BTreeSet<FileId> = before
        .files()
        .map(|(file, _)| *file)
        .chain(after.files().map(|(file, _)| *file))
        .collect();

    let mut pairs = Vec::new();
    for file in files {
        let was = before.entry(&file);
        let now = after.entry(&file);
        if let Some(limit) = limit
            && !limit.wants(
                Some(&file),
                [was.map(|entry| &entry.path), now.map(|entry| &entry.path)],
            )
        {
            continue;
        }
        let pair = Pair {
            from: was.map(|entry| entry.path.clone()),
            to: now.map(|entry| entry.path.clone()),
            before: match (was, left) {
                (Some(_), Some(id)) => Some(store.content_at(&id, &file).map_err(Failure::error)?),
                _ => None,
            },
            after: now
                .map(|_| store.content_at(&right, &file))
                .transpose()
                .map_err(Failure::error)?,
            modes: match (was, now) {
                (Some(was), Some(now)) if was.mode != now.mode => Some((was.mode, now.mode)),
                _ => None,
            },
        };
        if pair.differs() {
            pairs.push(pair);
        }
    }
    Ok(pairs)
}

/// A revision and the folder, paired by path.
///
/// The folder holds no identifiers, so this is every rename it cannot see:
/// decision 0011 makes stating one a person's job, and a comparison that
/// guessed would be inventing a fact the store would then not record.
fn folder(
    store: &Store,
    root: &Path,
    left: Option<RevisionId>,
    limit: Option<&Named>,
) -> Result<Vec<Pair>, Failure> {
    let repository = root
        .parent()
        .ok_or_else(|| Failure::error("this store has no repository around it"))?
        .to_path_buf();
    let working = Working::read(&repository, store.skipped()).map_err(Failure::error)?;

    let tree = match left {
        Some(id) => store.tree(&id).map_err(Failure::error)?,
        None => Tree::empty(),
    };
    let held: BTreeMap<&str, FileId> = tree.files().map(|(file, path)| (path, *file)).collect();

    let paths: BTreeSet<String> = held
        .keys()
        .map(|path| (*path).to_owned())
        .chain(working.iter().map(|(path, _)| path.clone()))
        .collect();

    let mut pairs = Vec::new();
    for path in paths {
        let file = held.get(path.as_str()).copied();
        let there = working.holds(&path);
        if let Some(limit) = limit
            && !limit.wants(file.as_ref(), [Some(&path), Some(&path)])
        {
            continue;
        }
        let before = match (file, left) {
            (Some(file), Some(id)) => Some(store.content_at(&id, &file).map_err(Failure::error)?),
            _ => None,
        };
        let after = if there {
            let bytes = working.bytes(&path).map_err(Failure::error)?;
            // A file the tree holds keeps the kind it was added with (0017);
            // one the tree does not is whatever the recorder would call it.
            let lines = match file.and_then(|file| tree.kind(&file)) {
                Some(kind) => kind == Kind::Lines,
                None => working::is_text(&bytes),
            };
            Some(if lines {
                Content::Lines(State::from_text(&String::from_utf8_lossy(&bytes)))
            } else {
                Content::Whole(bytes)
            })
        } else {
            None
        };
        // Decision 0034: a filesystem that cannot see the bit answers `None`,
        // and a reader that gets `None` states nothing — the same rule that
        // stops two machines flipping the bit at each other forever.
        let modes = match (
            file.and_then(|file| tree.entry(&file))
                .map(|entry| entry.mode),
            there,
        ) {
            (Some(recorded), true) => match working.executable(&path).map_err(Failure::error)? {
                Some(held) if Mode::of(held) != recorded => Some((recorded, Mode::of(held))),
                _ => None,
            },
            _ => None,
        };
        let pair = Pair {
            from: file.map(|_| path.clone()),
            to: there.then(|| path.clone()),
            before,
            after,
            modes,
        };
        if pair.differs() {
            pairs.push(pair);
        }
    }
    Ok(pairs)
}

/// One file's difference, in the shape other tools read.
///
/// The facts about the file come first and the content after, so that a
/// reader meets "this was renamed" or "this arrived" before the hunks that
/// would otherwise be the only clue. A file whose content did not change
/// prints no `---`/`+++` pair at all: there is nothing under it, and a header
/// with nothing under it reads like something went wrong.
fn render(out: &mut impl Write, pair: &Pair) -> std::io::Result<()> {
    match (&pair.from, &pair.to) {
        (None, Some(path)) => writeln!(out, "new file {path}")?,
        (Some(path), None) => writeln!(out, "deleted file {path}")?,
        // Decision 0008 records identity, so this is read rather than
        // guessed at — and on the folder side it never happens, because the
        // folder has no identifiers to read it from.
        (Some(from), Some(to)) if from != to => {
            writeln!(out, "rename from {from}")?;
            writeln!(out, "rename to {to}")?;
        }
        _ => {}
    }
    // Named on its own line, because a mode is the one difference that can be
    // the whole of what changed — and two bare `mode` lines between two other
    // files' hunks would belong to neither of them.
    if let Some((was, now)) = pair.modes {
        let path = pair.to.as_deref().or(pair.from.as_deref()).unwrap_or("?");
        writeln!(out, "mode {path} {was} -> {now}")?;
    }

    let left = pair
        .from
        .as_deref()
        .map_or_else(|| "/dev/null".to_owned(), |path| format!("a/{path}"));
    let right = pair
        .to
        .as_deref()
        .map_or_else(|| "/dev/null".to_owned(), |path| format!("b/{path}"));

    // Decision 0017: a file of bytes has no lines, and a photograph written
    // between two `@@` markers is a mess rather than an answer.
    let lines = |content: Option<&Content>| match content {
        Some(Content::Lines(state)) => Some(state.clone()),
        Some(Content::Whole(_)) => None,
        None => Some(State::empty()),
    };
    let (Some(before), Some(after)) = (lines(pair.before.as_ref()), lines(pair.after.as_ref()))
    else {
        writeln!(out, "--- {left}")?;
        writeln!(out, "+++ {right}")?;
        return writeln!(out, "binary files differ");
    };

    // The same decomposition `record` would write down, rendered — so what a
    // person is shown here and what the store would state are one answer
    // computed once, rather than two that can disagree. `None` is a file whose
    // content did not change, which a rename or a mode has already accounted
    // for above.
    let Some(document) = diff::diff(&before, &after) else {
        return Ok(());
    };
    writeln!(out, "--- {left}")?;
    writeln!(out, "+++ {right}")?;
    for hunk in hunks(&before, &document) {
        writeln!(out, "{}", hunk.header())?;
        for line in &hunk.lines {
            writeln!(out, "{}{}", line.sign, line.text)?;
            if !line.terminated {
                writeln!(out, "\\ no newline at end of file")?;
            }
        }
    }
    Ok(())
}

/// One line of a comparison: a context line, a removal, or an arrival.
pub(super) struct Line {
    /// ` `, `-`, or `+`.
    pub sign: char,
    /// What the item shows a reader, which is the marker for a forgotten one.
    pub text: String,
    /// Whether it ends with a newline.
    pub terminated: bool,
}

/// A run of changed lines with context around it.
struct Hunk {
    before: usize,
    before_count: usize,
    after: usize,
    after_count: usize,
    lines: Vec<Line>,
}

impl Hunk {
    fn header(&self) -> String {
        format!(
            "@@ -{},{} +{},{} @@",
            self.before, self.before_count, self.after, self.after_count
        )
    }
}

/// The whole comparison, cut into hunks with context around each run.
fn hunks(before: &State, document: &historica::format::OperationDocument) -> Vec<Hunk> {
    group(laid(before, document))
}

/// The operations, laid back over the parent as ` `, `-` and `+` lines.
///
/// Positions are counted into the parent (decision 0007), which is what makes
/// this arithmetic rather than a second diff: every operation names where in
/// `before` it applies, so walking `before` once and consulting them in order
/// produces the whole comparison.
///
/// This is that comparison, before it is cut into hunks — which is what `blame`
/// wants too (decision 0038), because "which of the folder's lines are not
/// recorded yet" is the same question as "which of them are `+`". Shared, so
/// the two commands cannot answer it differently.
pub(super) fn laid(before: &State, document: &historica::format::OperationDocument) -> Vec<Line> {
    use historica::format::OperationKind;

    let mut deleted: BTreeMap<usize, usize> = BTreeMap::new();
    let mut inserted: BTreeMap<usize, Vec<&historica::format::Item>> = BTreeMap::new();
    for operation in &document.operations {
        match operation.kind {
            OperationKind::Delete => {
                *deleted.entry(operation.at).or_default() += operation.items.len();
            }
            OperationKind::Insert => inserted
                .entry(operation.at)
                .or_default()
                .extend(operation.items.iter()),
        }
    }

    let items = before.items();
    let mut lines: Vec<Line> = Vec::new();
    let mut at = 0usize;
    // Emitted in the order the format reads in: at a position where a run was
    // replaced, what left comes before what arrived. `diff` anchors a
    // replacement's insert at the removed run's start (0009), so both are
    // stated at one position and only this decides which is printed first.
    let arrivals = |lines: &mut Vec<Line>, at: usize| {
        if let Some(items) = inserted.get(&at) {
            for item in items {
                lines.push(Line {
                    sign: '+',
                    text: item.shown().to_owned(),
                    terminated: item.terminated,
                });
            }
        }
    };
    while at < items.len() {
        let removing = deleted.get(&at).copied().unwrap_or_default();
        if removing == 0 {
            arrivals(&mut lines, at);
            let item = &items[at];
            lines.push(Line {
                sign: ' ',
                text: item.shown().to_owned(),
                terminated: item.terminated,
            });
            at += 1;
            continue;
        }
        // A delete names a run, and the run is the parent's next lines.
        for item in &items[at..(at + removing).min(items.len())] {
            lines.push(Line {
                sign: '-',
                text: item.shown().to_owned(),
                terminated: item.terminated,
            });
        }
        arrivals(&mut lines, at);
        at += removing;
    }
    // An insert at the end counts into the parent's length, which is one past
    // its last line.
    arrivals(&mut lines, items.len());

    lines
}

/// Cut the whole comparison into hunks with [`CONTEXT`] lines around each run.
fn group(lines: Vec<Line>) -> Vec<Hunk> {
    let changed: Vec<usize> = lines
        .iter()
        .enumerate()
        .filter(|(_, line)| line.sign != ' ')
        .map(|(index, _)| index)
        .collect();
    if changed.is_empty() {
        return Vec::new();
    }

    // Runs of changed lines, joined where their context would overlap: two
    // hunks that would print the same line twice are one hunk.
    let mut spans: Vec<(usize, usize)> = Vec::new();
    for index in changed {
        let start = index.saturating_sub(CONTEXT);
        let end = (index + CONTEXT + 1).min(lines.len());
        match spans.last_mut() {
            Some((_, last)) if *last >= start => *last = end.max(*last),
            _ => spans.push((start, end)),
        }
    }

    // Line numbers are one-based and count each side separately, which is
    // what the format means by `-l,c +l,c`.
    let mut before = 1usize;
    let mut after = 1usize;
    let mut counted: Vec<(usize, usize)> = Vec::with_capacity(lines.len());
    for line in &lines {
        counted.push((before, after));
        match line.sign {
            '-' => before += 1,
            '+' => after += 1,
            _ => {
                before += 1;
                after += 1;
            }
        }
    }

    spans
        .into_iter()
        .map(|(start, end)| {
            let span = &lines[start..end];
            let before_count = span.iter().filter(|line| line.sign != '+').count();
            let after_count = span.iter().filter(|line| line.sign != '-').count();
            Hunk {
                // An empty side is numbered 0, which is what a file created or
                // deleted whole prints.
                before: if before_count == 0 {
                    0
                } else {
                    counted[start].0
                },
                before_count,
                after: if after_count == 0 {
                    0
                } else {
                    counted[start].1
                },
                after_count,
                lines: span
                    .iter()
                    .map(|line| Line {
                        sign: line.sign,
                        text: line.text.clone(),
                        terminated: line.terminated,
                    })
                    .collect(),
            }
        })
        .collect()
}
