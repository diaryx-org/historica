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

use std::borrow::Cow;
use std::collections::{BTreeMap, BTreeSet};
use std::io::{IsTerminal, Write};
use std::ops::Range;
use std::path::Path;

use historica::core::{FileId, RevisionId};
use historica::diff;
use historica::format::Mode;
use historica::replay::State;
use historica::store::{Content, Store};
use historica::tree::{Kind, Tree};
use historica::working::{self, Working};
use similar::{Algorithm, DiffOp, capture_diff_slices};

use super::{Failure, locate, printing, target};

/// How many unchanged lines to show around a change.
///
/// Three, which is what every tool that reads this format defaults to.
const CONTEXT: usize = 3;

/// `diff [<target>] [<path>] [--onto <target>] [--color <when>]`
///
/// The left side is `--onto` where it is given. Where it is not, it is the
/// named revision's parent — so `diff <target>` is "what that revision did",
/// which is the question `log` leaves a person holding. The right side is the
/// named revision, or the folder when nothing is named.
pub fn diff_command(base: &Path, arguments: Vec<String>) -> Result<u8, Failure> {
    let mut onto: Option<String> = None;
    let mut when = When::Auto;
    let mut rest: Vec<String> = Vec::new();

    let mut arguments = arguments.into_iter();
    while let Some(argument) = arguments.next() {
        // Both spellings, because `--color=always` is the one every other tool
        // takes and a person who types it here has not made a mistake worth an
        // error message.
        if let Some(value) = argument.strip_prefix("--color=") {
            when = When::parse(value)?;
            continue;
        }
        match argument.as_str() {
            "--onto" => {
                onto = Some(
                    arguments
                        .next()
                        .ok_or_else(|| Failure::usage("`--onto` wants a value"))?,
                );
            }
            "--color" => {
                let value = arguments.next().ok_or_else(|| {
                    Failure::usage("`--color` wants `auto`, `always`, or `never`")
                })?;
                when = When::parse(&value)?;
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

    // Decided once, before anything is written, so that every line of one run
    // agrees about whether it is decorated.
    let paint = Paint(when.decorates());

    printing(|out| {
        if pairs.is_empty() {
            return writeln!(out, "nothing differs");
        }
        for pair in &pairs {
            render(out, pair, paint)?;
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
    /// Where a link pointed on each side, where they differ. Decision 0040.
    ///
    /// Either half is `None` where that side holds no link at all, which is
    /// how a link arriving or leaving says where it pointed.
    targets: Option<(Option<Shown>, Option<Shown>)>,
}

/// The two sides' targets, where they are worth saying out loud.
fn retargeting(was: Option<Shown>, now: Option<Shown>) -> Option<(Option<Shown>, Option<Shown>)> {
    if was == now {
        return None;
    }
    Some((was, now))
}

/// A link's target, as a person reads it.
///
/// Decision 0040: `diff` renders a `file:` target by the path it resolves to
/// at that revision, beside the identity, since a person reads paths — and the
/// identity is what makes it survive the rename the path would not.
struct Shown {
    at: String,
    file: Option<FileId>,
}

impl std::fmt::Display for Shown {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.file {
            Some(file) => write!(f, "{} (file:{})", self.at, file.abbreviate(8)),
            None => f.write_str(&self.at),
        }
    }
}

impl PartialEq for Shown {
    fn eq(&self, other: &Self) -> bool {
        self.at == other.at && self.file == other.file
    }
}

impl Pair {
    /// Whether anything about this file differs between the sides.
    fn differs(&self) -> bool {
        self.from != self.to
            || self.modes.is_some()
            || self.targets.is_some()
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
        // Decision 0040: a link holds a target instead of content, so asking
        // for its content would be asking a question it has no answer to.
        let content = |entry: Option<&historica::tree::Entry>, at: RevisionId| {
            match entry {
                Some(entry) if entry.kind != Kind::Link => {
                    Some(store.content_at(&at, &file).map_err(Failure::error))
                }
                _ => None,
            }
            .transpose()
        };
        let pair = Pair {
            from: was.map(|entry| entry.path.clone()),
            to: now.map(|entry| entry.path.clone()),
            before: match left {
                Some(id) => content(was, id)?,
                None => None,
            },
            after: content(now, right)?,
            modes: match (was, now) {
                (Some(was), Some(now)) if was.mode != now.mode => Some((was.mode, now.mode)),
                _ => None,
            },
            targets: retargeting(
                was.and_then(|was| shown(&before, was)),
                now.and_then(|now| shown(&after, now)),
            ),
        };
        if pair.differs() {
            pairs.push(pair);
        }
    }
    Ok(pairs)
}

/// One entry's target, spelled the way a person reads it at that revision.
///
/// `None` for anything that is not a link, which is what makes "did the target
/// change" a comparison rather than a case analysis.
fn shown(tree: &Tree, entry: &historica::tree::Entry) -> Option<Shown> {
    let target = entry.target.as_ref()?;
    Some(Shown {
        at: historica::update::materialise(tree, &entry.path, target)
            .unwrap_or_else(|| target.to_string()),
        file: target.reference(),
    })
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
        let entry = file.and_then(|file| tree.entry(&file));
        let recorded_link = entry.filter(|entry| entry.kind == Kind::Link);
        let before = match (file, left) {
            (Some(file), Some(id)) if recorded_link.is_none() => {
                Some(store.content_at(&id, &file).map_err(Failure::error)?)
            }
            _ => None,
        };
        // Decision 0040: a link on either side has a target instead of
        // content, and the two are compared as targets on their own line.
        let targets = retargeting(
            recorded_link.and_then(|entry| shown(&tree, entry)),
            working.link_target(&path).map(|held| Shown {
                at: held.to_owned(),
                file: None,
            }),
        );
        let after = if there && !working.is_link(&path) {
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
            entry
                .filter(|entry| entry.kind != Kind::Link)
                .map(|entry| entry.mode),
            there && !working.is_link(&path),
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
            targets,
        };
        if pair.differs() {
            pairs.push(pair);
        }
    }
    Ok(pairs)
}

/// When to decorate, as `--color` spells it.
#[derive(Clone, Copy)]
enum When {
    /// Decorated where a person is looking at it, and never into a pipe.
    Auto,
    Always,
    Never,
}

impl When {
    fn parse(value: &str) -> Result<Self, Failure> {
        match value {
            "auto" => Ok(When::Auto),
            "always" => Ok(When::Always),
            "never" => Ok(When::Never),
            other => Err(Failure::usage(format!(
                "`{other}` is not a `--color` setting; it is `auto`, which \
                 decorates a terminal and nothing else, `always`, or `never`"
            ))),
        }
    }

    /// Whether this run decorates.
    ///
    /// `NO_COLOR` is answered here rather than in [`When::parse`] because it is
    /// what a person means by "unless I say otherwise": it settles `auto` and
    /// leaves `--color always` alone, which is the whole point of having said
    /// `always` out loud.
    fn decorates(self) -> bool {
        match self {
            When::Always => true,
            When::Never => false,
            When::Auto => {
                std::io::stdout().is_terminal()
                    && !std::env::var_os("NO_COLOR").is_some_and(|value| !value.is_empty())
            }
        }
    }
}

/// Bold, which is what `git diff` prints a fact about a file in.
const META: &str = "\x1b[1m";
/// Cyan, for a hunk header.
const FRAGMENT: &str = "\x1b[36m";
const REMOVED: &str = "\x1b[31m";
const ARRIVED: &str = "\x1b[32m";
/// Inverse video, for the part of a line that differs from the line it
/// replaced — which is what `diff-highlight` has drawn it in for a decade.
const EMPHASIS: &str = "\x1b[7m";
/// Inverse video off, and only that: the line's own colour outlives it.
const PLAINLY: &str = "\x1b[27m";
const OFF: &str = "\x1b[0m";

/// Whether this rendering is decorated.
///
/// Off, every escape below is the empty string, so the bytes are the ones this
/// command wrote before there was a `--color` at all. That is the property the
/// tests hold it to, and the reason colour is a decoration rather than a
/// change: `historica diff | patch` sees exactly what it always saw.
#[derive(Clone, Copy)]
struct Paint(bool);

impl Paint {
    fn pick(self, code: &'static str) -> &'static str {
        if self.0 { code } else { "" }
    }

    /// What a `-`, `+`, or context line is drawn in.
    fn sign(self, sign: char) -> &'static str {
        match sign {
            '-' => self.pick(REMOVED),
            '+' => self.pick(ARRIVED),
            _ => "",
        }
    }
}

/// What closes a decoration, and nothing at all where there was none.
///
/// Derived from the opening escape rather than from [`Paint`] so that an
/// undecorated line — a context line, in a run that is otherwise coloured —
/// cannot end with a stray reset.
fn ends(code: &str) -> &'static str {
    if code.is_empty() { "" } else { OFF }
}

/// One file's difference, in the shape other tools read.
///
/// The facts about the file come first and the content after, so that a
/// reader meets "this was renamed" or "this arrived" before the hunks that
/// would otherwise be the only clue. A file whose content did not change
/// prints no `---`/`+++` pair at all: there is nothing under it, and a header
/// with nothing under it reads like something went wrong.
fn render(out: &mut impl Write, pair: &Pair, paint: Paint) -> std::io::Result<()> {
    let meta = paint.pick(META);
    let off = ends(meta);
    match (&pair.from, &pair.to) {
        (None, Some(path)) => writeln!(out, "{meta}new file {path}{off}")?,
        (Some(path), None) => writeln!(out, "{meta}deleted file {path}{off}")?,
        // Decision 0008 records identity, so this is read rather than
        // guessed at — and on the folder side it never happens, because the
        // folder has no identifiers to read it from.
        (Some(from), Some(to)) if from != to => {
            writeln!(out, "{meta}rename from {from}{off}")?;
            writeln!(out, "{meta}rename to {to}{off}")?;
        }
        _ => {}
    }
    // Named on its own line, because a mode is the one difference that can be
    // the whole of what changed — and two bare `mode` lines between two other
    // files' hunks would belong to neither of them.
    if let Some((was, now)) = pair.modes {
        let path = pair.to.as_deref().or(pair.from.as_deref()).unwrap_or("?");
        writeln!(out, "{meta}mode {path} {was} -> {now}{off}")?;
    }
    // Decision 0040: one line, before and after. A target change is the whole
    // of what a revision can say about a link, and there are no hunks under
    // it — a link has a target where a file has content.
    if let Some((was, now)) = &pair.targets {
        let path = pair.to.as_deref().or(pair.from.as_deref()).unwrap_or("?");
        let spelled = |side: &Option<Shown>| {
            side.as_ref()
                .map_or_else(String::new, |shown| format!(" {shown}"))
        };
        writeln!(
            out,
            "{meta}link {path}{} ->{}{off}",
            spelled(was),
            spelled(now)
        )?;
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
        writeln!(out, "{meta}--- {left}{off}")?;
        writeln!(out, "{meta}+++ {right}{off}")?;
        return writeln!(out, "{meta}binary files differ{off}");
    };

    // The same decomposition `record` would write down, rendered — so what a
    // person is shown here and what the store would state are one answer
    // computed once, rather than two that can disagree. `None` is a file whose
    // content did not change, which a rename or a mode has already accounted
    // for above.
    let Some(document) = diff::diff(&before, &after) else {
        return Ok(());
    };
    writeln!(out, "{meta}--- {left}{off}")?;
    writeln!(out, "{meta}+++ {right}{off}")?;
    let fragment = paint.pick(FRAGMENT);
    for hunk in hunks(&before, &document) {
        writeln!(out, "{fragment}{}{}", hunk.header(), ends(fragment))?;
        // Only when there is colour: emphasis has no plain-text spelling that
        // would not change the bytes, and changing them is the one thing this
        // may not do.
        let emphasis = if paint.0 {
            differing(&hunk.lines)
        } else {
            vec![Vec::new(); hunk.lines.len()]
        };
        for (line, spans) in hunk.lines.iter().zip(&emphasis) {
            let code = paint.sign(line.sign);
            let shut = ends(code);
            let text = marked(&line.text, spans);
            writeln!(out, "{code}{}{text}{shut}", line.sign)?;
            if !line.terminated {
                writeln!(out, "{code}\\ no newline at end of file{shut}")?;
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

/// Which byte spans of each line differ from the line it replaced.
///
/// This is a second comparison, and decision 0037 declined one — so it is
/// worth saying exactly why this is not the thing that was declined. What 0037
/// rules out is a second *decomposition*: an answer about what changed that
/// could disagree with the one `record` would write down. By the time this
/// runs that answer is settled — which lines are here, in which order, carrying
/// which bytes — and nothing below can move a line, add one, or alter a byte of
/// one. All it decides is which part of a line to draw brighter, which is also
/// why it may only run when there is colour to draw it in: emphasis has no
/// plain-text spelling that would not change the output.
fn differing(lines: &[Line]) -> Vec<Vec<Range<usize>>> {
    let mut spans: Vec<Vec<Range<usize>>> = vec![Vec::new(); lines.len()];
    let mut at = 0;
    while at < lines.len() {
        let removed = run(lines, at, '-');
        let arrived = run(lines, at + removed, '+');
        // A run replaced one-for-one pairs up without anybody guessing which
        // line became which. An unequal run has no such pairing, and inventing
        // one here would be the resemblance 0037 refuses for renames — cheaper
        // to be wrong about, but wrong in the same way.
        if removed > 0 && removed == arrived {
            for offset in 0..removed {
                let (was, now) = (&lines[at + offset], &lines[at + removed + offset]);
                if let Some((left, right)) = apart(&was.text, &now.text) {
                    spans[at + offset] = left;
                    spans[at + removed + offset] = right;
                }
            }
        }
        at += (removed + arrived).max(1);
    }
    spans
}

/// How many lines from `at` carry `sign`.
fn run(lines: &[Line], at: usize, sign: char) -> usize {
    lines[at..]
        .iter()
        .take_while(|line| line.sign == sign)
        .count()
}

/// The most tokens either line may be compared in.
///
/// A generated file is one enormous line and the matcher is quadratic in the
/// worst case, so this is what stops a decoration deciding how long the
/// command takes.
const LONGEST: usize = 1024;

/// Where one pair of lines differs: the removal's byte spans, then the
/// arrival's.
type Sides = (Vec<Range<usize>>, Vec<Range<usize>>);

/// The byte spans in which two lines differ, or `None` where saying so would
/// tell a reader nothing.
///
/// Nothing where the two share no word: emphasis covering the whole of both
/// lines says only what the `-` and the `+` already said, and a line drawn
/// entirely in inverse video is harder to read than one drawn plainly. That is
/// `diff-highlight`'s rule as well, arrived at the same way.
fn apart(was: &str, now: &str) -> Option<Sides> {
    let old = words(was);
    let new = words(now);
    if old.len() > LONGEST || new.len() > LONGEST {
        return None;
    }

    // The tokens tile their line exactly, so a token index becomes a byte
    // offset by adding up the lengths before it.
    let span = |tokens: &[&str], from: usize, len: usize| {
        let start: usize = tokens[..from].iter().map(|word| word.len()).sum();
        let width: usize = tokens[from..from + len].iter().map(|word| word.len()).sum();
        start..start + width
    };

    let mut left: Vec<Range<usize>> = Vec::new();
    let mut right: Vec<Range<usize>> = Vec::new();
    let mut shared = false;
    for operation in capture_diff_slices(Algorithm::Myers, &old, &new) {
        match operation {
            DiffOp::Equal { old_index, len, .. } => {
                shared = shared
                    || old[old_index..old_index + len]
                        .iter()
                        .any(|word| !word.trim().is_empty());
            }
            DiffOp::Delete {
                old_index, old_len, ..
            } => left.push(span(&old, old_index, old_len)),
            DiffOp::Insert {
                new_index, new_len, ..
            } => right.push(span(&new, new_index, new_len)),
            DiffOp::Replace {
                old_index,
                old_len,
                new_index,
                new_len,
            } => {
                left.push(span(&old, old_index, old_len));
                right.push(span(&new, new_index, new_len));
            }
        }
    }
    if !shared || (left.is_empty() && right.is_empty()) {
        return None;
    }
    Some((left, right))
}

/// One line cut into the units a person would call changed or unchanged.
///
/// A run of letters and digits is one token and every other character is one
/// on its own, so `v1` becoming `v2` is two characters of emphasis rather than
/// a whole identifier of it, and a space that arrived is visible.
fn words(line: &str) -> Vec<&str> {
    let mut words = Vec::new();
    let mut start = 0;
    let mut lettered = false;
    for (index, character) in line.char_indices() {
        if character.is_alphanumeric() {
            if !lettered {
                start = index;
                lettered = true;
            }
            continue;
        }
        if lettered {
            words.push(&line[start..index]);
            lettered = false;
        }
        words.push(&line[index..index + character.len_utf8()]);
    }
    if lettered {
        words.push(&line[start..]);
    }
    words
}

/// One line's text with its differing spans wrapped in inverse video.
fn marked<'a>(text: &'a str, spans: &[Range<usize>]) -> Cow<'a, str> {
    if spans.is_empty() {
        return Cow::Borrowed(text);
    }
    let mut marked = String::with_capacity(text.len() + spans.len() * 8);
    let mut at = 0;
    for span in spans {
        marked.push_str(&text[at..span.start]);
        marked.push_str(EMPHASIS);
        marked.push_str(&text[span.start..span.end]);
        marked.push_str(PLAINLY);
        at = span.end;
    }
    marked.push_str(&text[at..]);
    Cow::Owned(marked)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn line(sign: char, text: &str) -> Line {
        Line {
            sign,
            text: text.to_owned(),
            terminated: true,
        }
    }

    /// What a reader sees, with the emphasis written where a test can read it.
    fn shown(lines: &[Line]) -> Vec<String> {
        differing(lines)
            .iter()
            .zip(lines)
            .map(|(spans, line)| {
                marked(&line.text, spans)
                    .replace(EMPHASIS, "[")
                    .replace(PLAINLY, "]")
            })
            .collect()
    }

    #[test]
    fn a_line_keeps_the_words_it_shares_with_the_one_it_replaced() {
        let lines = [line('-', "alpha beta gamma"), line('+', "alpha BETA gamma")];
        assert_eq!(shown(&lines), ["alpha [beta] gamma", "alpha [BETA] gamma"]);
    }

    /// Every other character is a token of its own, so a version number is two
    /// characters of emphasis rather than a whole identifier of it.
    fn version(text: &str) -> String {
        shown(&[line('-', "let v = \"v1\";"), line('+', text)])[1].clone()
    }

    #[test]
    fn punctuation_is_a_boundary_and_a_run_of_letters_is_not() {
        assert_eq!(version("let v = \"v2\";"), "let v = \"[v2]\";");
    }

    /// `diff-highlight`'s rule, arrived at the same way: emphasis covering the
    /// whole of both lines says only what the `-` and the `+` already said.
    #[test]
    fn two_lines_with_nothing_in_common_are_left_plain() {
        let lines = [line('-', "beta"), line('+', "BETA")];
        assert_eq!(shown(&lines), ["beta", "BETA"]);
    }

    /// A run of one length becoming a run of another has no pairing, and one
    /// invented here would be a resemblance rather than a reading.
    #[test]
    fn an_unequal_run_is_not_paired_up() {
        let lines = [
            line('-', "alpha one"),
            line('+', "alpha two"),
            line('+', "alpha three"),
        ];
        assert_eq!(shown(&lines), ["alpha one", "alpha two", "alpha three"]);
    }

    #[test]
    fn a_removal_with_no_arrival_is_left_alone() {
        let lines = [line(' ', "alpha"), line('-', "beta"), line(' ', "gamma")];
        assert_eq!(shown(&lines), ["alpha", "beta", "gamma"]);
    }

    /// Each pair is its own comparison, so the second run below is emphasised
    /// against the line it replaced rather than against the first one.
    #[test]
    fn a_run_pairs_line_by_line() {
        let lines = [
            line('-', "one alpha"),
            line('-', "two beta"),
            line('+', "one ALPHA"),
            line('+', "two BETA"),
        ];
        assert_eq!(
            shown(&lines),
            ["one [alpha]", "two [beta]", "one [ALPHA]", "two [BETA]"]
        );
    }

    /// The tokens tile the line, which is what makes a token index a byte
    /// offset — and what stops a multi-byte character being cut in half.
    #[test]
    fn tokens_tile_the_line_they_came_from() {
        for text in ["", "a", " ", "élan vital — ok", "a1_b2", "  x  "] {
            assert_eq!(words(text).concat(), text, "{text:?}");
        }
    }

    #[test]
    fn emphasis_lands_between_characters_rather_than_inside_one() {
        let lines = [line('-', "café noir"), line('+', "café blanc")];
        assert_eq!(shown(&lines), ["café [noir]", "café [blanc]"]);
    }

    /// Off, nothing here is reachable at all — but the escapes are still the
    /// empty string, which is the property the piped output depends on.
    #[test]
    fn an_undecorated_run_writes_no_escapes() {
        let paint = Paint(false);
        for code in [paint.pick(META), paint.pick(FRAGMENT), paint.sign('-')] {
            assert_eq!(code, "");
            assert_eq!(ends(code), "");
        }
    }

    #[test]
    fn a_color_setting_is_one_of_three_words() {
        assert!(matches!(When::parse("always"), Ok(When::Always)));
        assert!(matches!(When::parse("never"), Ok(When::Never)));
        assert!(matches!(When::parse("auto"), Ok(When::Auto)));
        assert!(When::parse("yes").is_err());
        // Whatever the terminal is, these two answer without asking it.
        assert!(When::Always.decorates());
        assert!(!When::Never.decorates());
    }
}
