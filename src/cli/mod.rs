//! Parsing a command line, and doing what it says.
//!
//! The argument grammar is small enough to read in one sitting, which is why
//! it is hand-written: a dependency here would be a dependency the format's
//! promise — that the files can be read with what is already installed —
//! never asked for.

use std::env;
use std::fmt;
use std::io::{self, Write as _};
use std::path::{Path, PathBuf};

use historica::format::Timestamp;
use historica::record::{Restriction, survey};
use historica::store::{
    Body, Bookmark, Forgetting, HEADER_FILE, MutableConflict, Name, Placement, STORE_DIR, Store,
    StoreError,
};
use historica::working::{Pattern, Rule, SKIPPED_DIR, Scope, Working};

mod arrange;
mod blame;
mod diff;
mod export;
#[cfg(feature = "http")]
mod fetch;
mod offer;
mod record;
mod render;
mod target;
mod update;

/// What `historica help` prints, and what a usage error prints after itself.
///
/// Three pieces rather than one string, because one command is only in some
/// builds: decision 0057 puts the transport behind a feature, and a usage text
/// that named a command this binary does not have would be the one line in it
/// that is not true.
pub fn usage() -> String {
    format!("{COMMANDS}{FETCHING}{REST}")
}

/// The `fetch` entry, in a build that has a transport.
#[cfg(feature = "http")]
const FETCHING: &str = "  fetch <url> [--join-unrelated]
                           take what a published copy holds and this store
                           lacks: the URL is the manifest `offer` wrote, and
                           every path in it resolves against the directory
                           that manifest sits in. adds history and stops —
                           `update` is the folder's catch-up
";

/// Nothing, in a build without one. Such a build fetches through the library's
/// `Source` trait, which is where a host that has its own transport brings it.
#[cfg(not(feature = "http"))]
const FETCHING: &str = "";

const COMMANDS: &str = "\
usage: historica [-C <dir>] <command> [<arguments>]

reading a store
  status [--onto <target>] [--merge <target>]
                           how the folder differs from what is recorded
  log [<target>|<from>..<to>] [--limit <count>] [--author <text>]
      [--grep <text>] [--since <when>] [--until <when>] [--path <path>]
                           the history, newest first; the filters compose and
                           --limit counts what they left. a range covers what
                           <to> has behind it and <from> does not, which is
                           defined for two revisions the graph left concurrent
                           as readily as for two along a chain. --path follows
                           the file rather than the name, so a rename is not a
                           break in it, and a range reads it at <to>. --since
                           and --until are read in each revision's own offset,
                           and a bare `YYYY-MM-DD` is that whole day there
  show <target> [<path>]   one document as stored: a revision, or what it
                           did to one file
  files <target>           the file set at a revision
  cat <target> <path>      one file's content at a revision
  diff [<target>] [<path>] [--onto <target>] [--color <when>]
                           what changed: the folder against the position,
                           or what a revision did. A rendering, not the
                           stored document — `show` is that. A rename
                           between two revisions is stated, because the
                           store recorded it; one in the folder is a drop
                           and an add, because the folder cannot see it.
                           <when> is `auto`, which colours a terminal and
                           nothing else, `always`, or `never`
  blame [<target>] <path> [--lines <first>..<last>]
                           who wrote each line: the change, the author, and
                           the day. Read from the operations rather than
                           guessed at, so a line keeps its author through a
                           rename and through a merge that did not touch it
  names                    the bookmarks, and what they point at
  skip                     the rules saying what history does not take

writing a store
  record [<path>...] [-m <message>]
                           record what the folder now says; with paths, only
                           what those say, the rest being left unlooked at
         [--onto <target>] [--merge <target>] [--move <old>=<new>]
         [--at <file>=<path>] [--accept <path>] [--dry-run]
  amend [<target>]         rewrite the head as the folder now stands
        [-m <message>] [--move <old>=<new>] [--dry-run]
  merge [<target>...]      write what two lines of work say together:
                           what is named, and every head that is not
  update [<target>] [--dry-run]
                           make the folder hold a head: write what it
                           records, remove what it does not, touch nothing
                           unrecorded
  abandon <target> [-m <why>] [--dry-run]
                           supersede this revision, and everything standing
                           on it, with a tombstone that says why
  carry [<target>] [--dry-run]
                           restate work standing on a rewritten revision
                           against the rewrite; with no target, every such
                           revision. nothing is stamped or minted, so two
                           replicas repairing one history write the same
                           bytes
  prune [--dry-run]        delete superseded revisions nothing stands on, and
                           content only they name, printing every file
  receive <dir> [--dry-run] [--join-unrelated]
                           import immutable history from another local store
  export <dir> [<target>] [--files-only] [--dry-run]
                           write a fresh repository at <dir>: the folder as
                           <target> has it, and the history that leads there.
                           bookmarks and the cache stay here, the shared
                           rules travel and the private ones do not, and
                           nothing unrecorded or skipped can travel, because
                           the copy is assembled rather than mirrored.
                           compressing it is tar's job. --files-only writes
                           the same folder and no history under it, which is
                           for looking at a revision rather than working on
                           one, and wants an empty directory
  offer <dir>              list the transferable files of a published copy, to
                           standard output, for a reader that cannot list the
                           directory it is fetching from: a kind, a digest,
                           what the entry forgets, and the path. writes
                           nothing — redirect it beside the copy, as
                           `offer.txt`, after the `export` that made it
";

const REST: &str = "  forget <target> <path> --lines <first>..<last> [--dry-run]
                           destroy those lines everywhere history quotes
                           them, leaving their shape; the file's paths,
                           authors, and times stay recorded
  identity <author>        say who you are, once, for every repository
  init [<dir>]             make a store in <dir>/history
  check [<dir>] [--complete]
                           read a store and report every fault; --complete
                           also fails when a head's history is not all here
  arrange [-n] [--refile]  rename revision files to readable ones, where they
                           sit: a folder you put a revision in is one you
                           meant. --refile moves them under `YYYY-MM/` too,
                           which is how a store written flat catches up
  name <bookmark> <target> [<path>] [--revision] [--private|--shared]
                           point a bookmark at a change, pin a revision, or
                           name the file that <path> holds. --private keeps
                           the bookmark's own name out of an `export`; with
                           neither flag, a bookmark keeps the axis it has
  skip [--private] <path>... [--name <name>]
                           stop history taking a path, a directory, or a
                           name in which `*` is any run of characters.
                           --private keeps the rule's own text out of an
                           `export`; with no arguments, print the rules

a <target> is `head`, a bookmark, a change ID, or a revision digest; the last
two may
be abbreviated to any unambiguous prefix, and their alphabets do not overlap,
so one argument accepts either. `log` also takes two of them as
`<from>..<to>`; a bookmark whose own name holds `..` is looked up whole first,
so it still names itself.

a <path> is a path, or `file:` and a file identifier or a file bookmark — an
identifier abbreviates to any prefix unique among the files at that revision.
`path:` says the rest is a path, for a file whose own name begins `file:`.
";

/// Why a command stopped, and what the process should exit with.
///
/// A command that has already said its piece on stdout — `check`, which
/// reports faults rather than raising them — returns a code instead.
#[derive(Debug)]
pub struct Failure {
    message: Option<String>,
    code: u8,
    usage: bool,
}

impl Failure {
    /// Something went wrong: exit 1, having said why.
    pub fn error(message: impl fmt::Display) -> Self {
        Self {
            message: Some(message.to_string()),
            code: 1,
            usage: false,
        }
    }

    /// The command line itself was wrong: exit 2, and print the usage.
    pub fn usage(message: impl fmt::Display) -> Self {
        Self {
            message: Some(message.to_string()),
            code: 2,
            usage: true,
        }
    }

    /// What to print, if anything.
    pub fn message(&self) -> Option<&str> {
        self.message.as_deref()
    }

    /// Whether the usage text belongs after the message.
    pub fn wants_usage(&self) -> bool {
        self.usage
    }

    /// The process exit code.
    pub fn code(&self) -> u8 {
        self.code
    }
}

impl From<StoreError> for Failure {
    fn from(error: StoreError) -> Self {
        Self::error(error)
    }
}

/// Run one command line, returning the code to exit with.
pub fn run(arguments: impl IntoIterator<Item = String>) -> Result<u8, Failure> {
    let mut arguments = arguments.into_iter();
    let mut base: Option<PathBuf> = None;

    let command = loop {
        let Some(argument) = arguments.next() else {
            return printing(|out| out.write_all(usage().as_bytes()));
        };
        match argument.as_str() {
            "-C" => {
                let directory = arguments
                    .next()
                    .ok_or_else(|| Failure::usage("`-C` wants a directory"))?;
                base = Some(PathBuf::from(directory));
            }
            "-h" | "--help" | "help" => {
                return printing(|out| out.write_all(usage().as_bytes()));
            }
            "-V" | "--version" => {
                return printing(|out| writeln!(out, "historica {}", env!("CARGO_PKG_VERSION")));
            }
            other if other.starts_with('-') => {
                return Err(Failure::usage(format!("`{other}` is not an option here")));
            }
            _ => break argument,
        }
    };

    let rest: Vec<String> = arguments.collect();
    let base = match base {
        Some(directory) => directory,
        None => env::current_dir().map_err(|error| Failure::error(format!("$PWD: {error}")))?,
    };

    match command.as_str() {
        "init" => init(&base, rest),
        "check" => check(&base, rest),
        "arrange" => arrange(&base, rest),
        "status" => status(&base, rest),
        "log" => log(&base, rest),
        "show" => show(&base, rest),
        "files" => files(&base, rest),
        "cat" => cat(&base, rest),
        "diff" => diff::diff_command(&base, rest),
        "blame" => blame::blame_command(&base, rest),
        "names" => names(&base, rest),
        "name" => name(&base, rest),
        "skip" => skip(&base, rest),
        "record" => record::record(&base, locate(&base)?, rest),
        "amend" => record::amend(locate(&base)?, rest),
        "abandon" => record::abandon(&base, locate(&base)?, rest),
        "carry" => record::carry(locate(&base)?, rest),
        "prune" => prune(&base, rest),
        "receive" => receive(&base, rest),
        "export" => export::export(&base, locate(&base)?, rest),
        "offer" => offer::offer(&base, rest),
        #[cfg(feature = "http")]
        "fetch" => fetch::fetch(&base, rest),
        // Named rather than left to fall through, because "there is no `fetch`
        // command" would be true of this binary and false of historica.
        #[cfg(not(feature = "http"))]
        "fetch" => Err(Failure::usage(
            "this build of historica has no transport in it, so it has no \
             `fetch`. the library's `Source` trait is where a host brings its \
             own; without one, `export`, an archive, and `receive` are the way \
             a store travels",
        )),
        "forget" => forget(&base, rest),
        "merge" => record::merge(locate(&base)?, rest),
        "update" => update::update(locate(&base)?, rest),
        "identity" => record::set_identity(rest),
        other => Err(Failure::usage(format!("there is no `{other}` command"))),
    }
}

/// `init [<dir>]` — write the layout decision 0006 settled on.
fn init(base: &Path, arguments: Vec<String>) -> Result<u8, Failure> {
    let mut arguments = arguments.into_iter();
    let directory = match arguments.next() {
        Some(path) => base.join(path),
        None => base.to_path_buf(),
    };
    if let Some(extra) = arguments.next() {
        return Err(Failure::usage(format!(
            "`init` takes one directory, and `{extra}` is a second"
        )));
    }

    let store = Store::init(directory.join(STORE_DIR))?;
    let root = store
        .root()
        .canonicalize()
        .unwrap_or_else(|_| store.root().to_path_buf());
    printing(|out| writeln!(out, "made a store at {}", root.display()))
}

/// `check [<dir>]` — every fault at once, errors and notes kept apart.
fn check(base: &Path, arguments: Vec<String>) -> Result<u8, Failure> {
    let mut complete = false;
    let mut rest = Vec::new();
    for argument in arguments {
        match argument.as_str() {
            "--complete" => complete = true,
            other => rest.push(other.to_owned()),
        }
    }

    let mut rest = rest.into_iter();
    let root = match rest.next() {
        Some(path) => named(base, &path),
        None => locate(base)?,
    };
    if let Some(extra) = rest.next() {
        return Err(Failure::usage(format!(
            "`check` takes one directory, and `{extra}` is a second"
        )));
    }

    let report = Store::check(&root);
    // Canonical for the report's last line: `check .` should name the store,
    // not repeat the punctuation that found it.
    let shown = root.canonicalize().unwrap_or(root);
    printing(|out| render::report(out, &shown, &report, complete))?;
    // Decision 0006: notes never fail, so this can be run in anger without
    // teaching anyone to ignore it. `--complete` asks the second question —
    // whether delivery has finished — and only that question fails on a note.
    Ok(u8::from(
        !report.is_ok() || (complete && !report.is_complete()),
    ))
}

/// `arrange [-n] [--refile]` — advisory names, deterministically.
///
/// `--refile` is the only thing that overrules a person's own filing, which is
/// why it is a flag rather than the default: decision 0041 files a revision
/// under its month, and decision 0016 says a name — or a folder — that differs
/// is usually somebody arranging their own history.
fn arrange(base: &Path, arguments: Vec<String>) -> Result<u8, Failure> {
    let mut dry_run = false;
    let mut placement = Placement::Kept;
    let mut rest = Vec::new();
    for argument in arguments {
        match argument.as_str() {
            "-n" | "--dry-run" => dry_run = true,
            "--refile" => placement = Placement::Refiled,
            other => rest.push(other.to_owned()),
        }
    }
    if let Some(extra) = rest.first() {
        return Err(Failure::usage(format!(
            "`arrange` takes no arguments, and `{extra}` is one"
        )));
    }

    arrange::arrange(&locate(base)?, dry_run, placement)
}

/// `prune [--dry-run]` — the disk half of decision 0013.
///
/// Abandoning is the graph and pruning is disk. What may go is exactly what
/// [`Store::prunable`] names, and every file removed is printed, because
/// pruning is the undo history and the loss should be visible while it is
/// still one `cp` away from being reversed.
fn prune(base: &Path, arguments: Vec<String>) -> Result<u8, Failure> {
    let mut dry_run = false;
    for argument in arguments {
        match argument.as_str() {
            "-n" | "--dry-run" => dry_run = true,
            other => {
                return Err(Failure::usage(format!(
                    "`{other}` is not an argument `prune` takes"
                )));
            }
        }
    }

    let root = locate(base)?;
    // Decision 0013: prune refuses to run on a store `check` calls broken.
    // Deletion is the one act that must not be aimed by files that cannot be
    // trusted, and notes never fail here as they never fail anywhere.
    let report = Store::check(&root);
    if !report.is_ok() {
        return Err(Failure::error(
            "this store does not pass `check`, and prune deletes nothing from \
             a store it cannot trust; `historica check` says what is wrong",
        ));
    }

    let mut store = Store::open(&root)?;
    let pruned = if dry_run {
        store.prunable()?
    } else {
        store.prune()?
    };

    printing(|out| {
        if pruned.is_empty() {
            return writeln!(
                out,
                "nothing here is prunable: nothing superseded is unreferenced"
            );
        }
        let verb = if dry_run { "would remove" } else { "removed" };
        for file in &pruned.files {
            writeln!(out, "{verb} {STORE_DIR}/{}", file.display())?;
        }
        Ok(())
    })
}

/// `receive <dir> [--dry-run] [--join-unrelated]`.
///
/// Copying remains transport. Receiving is the content-aware union needed
/// after two copies have changed independently: immutable documents are added,
/// mutable disagreements stop the operation, and neither working copy moves.
fn receive(base: &Path, arguments: Vec<String>) -> Result<u8, Failure> {
    let mut dry_run = false;
    let mut join_unrelated = false;
    let mut source = None;
    for argument in arguments {
        match argument.as_str() {
            "-n" | "--dry-run" => dry_run = true,
            "--join-unrelated" => join_unrelated = true,
            other if other.starts_with('-') => {
                return Err(Failure::usage(format!(
                    "`{other}` is not an argument `receive` takes"
                )));
            }
            other if source.is_none() => source = Some(other.to_owned()),
            other => {
                return Err(Failure::usage(format!(
                    "`receive` wants one source directory, not `{other}`"
                )));
            }
        }
    }
    let source = source.ok_or_else(|| Failure::usage("`receive` wants a source directory"))?;
    let root = locate(base)?;
    let mut here = Store::open(root)?;
    let there = Store::open(named(base, &source))?;

    if dry_run {
        let plan = here
            .receive_plan(&there, join_unrelated)
            .map_err(Failure::error)?;
        let conflicts = !plan.conflicts().is_empty();
        printing(|out| {
            writeln!(out, "would receive {} revisions", plan.revisions().len())?;
            writeln!(
                out,
                "would receive {} content documents",
                plan.documents().len()
            )?;
            writeln!(out, "would receive {} payloads", plan.payloads().len())?;
            // Decision 0062: the bookmark rather than the name, because a
            // plan now holds one both stores state and disagree the axis of,
            // and `would receive name main` where the receiver has `main`
            // would read as a contradiction.
            for (name, bookmark) in plan.names() {
                writeln!(out, "would receive bookmark {name} -> {bookmark}")?;
            }
            if !plan.skipped().is_empty() {
                writeln!(out, "would receive {} rules", plan.skipped().len())?;
            }
            // Decision 0053: a class, not a tool, so this says what these
            // files are rather than whose they are.
            if !plan.reserved().is_empty() {
                writeln!(
                    out,
                    "would receive {} files another tool wrote",
                    plan.reserved().len()
                )?;
            }
            if !plan.destroys().is_empty() {
                writeln!(
                    out,
                    "would destroy {} forgotten originals",
                    plan.destroys().len()
                )?;
            }
            for conflict in plan.conflicts() {
                match conflict {
                    MutableConflict::Name { name, here, there } => {
                        writeln!(
                            out,
                            "conflict: name {name} is {here} here and {there} there"
                        )?;
                    }
                }
            }
            Ok(())
        })?;
        return Ok(u8::from(conflicts));
    }

    let received = here
        .receive(&there, join_unrelated)
        .map_err(Failure::error)?;
    printing(|out| {
        writeln!(out, "received {} revisions", received.revisions)?;
        writeln!(out, "received {} content documents", received.documents)?;
        writeln!(out, "received {} payloads", received.payloads)?;
        if received.names != 0 {
            writeln!(out, "received {} bookmarks", received.names)?;
        }
        if received.skipped != 0 {
            writeln!(out, "received {} rules", received.skipped)?;
        }
        if received.reserved != 0 {
            writeln!(
                out,
                "received {} files another tool wrote",
                received.reserved
            )?;
        }
        if received.destroyed != 0 {
            writeln!(out, "destroyed {} forgotten originals", received.destroyed)?;
        }
        Ok(())
    })
}

/// `forget <target> <path> --lines <first>..<last> [--dry-run]`.
///
/// Decision 0014: destroy the payload, preserve the shape. The span is
/// resolved at the named revision and every document quoting those items is
/// rewritten as a forgetting document — which is why there is no `-m` here:
/// the reason for a redaction is usually the redacted thing.
fn forget(base: &Path, arguments: Vec<String>) -> Result<u8, Failure> {
    let mut lines: Option<String> = None;
    let mut dry_run = false;
    let mut rest: Vec<String> = Vec::new();
    let mut arguments = arguments.into_iter();
    while let Some(argument) = arguments.next() {
        match argument.as_str() {
            "--lines" => {
                lines = Some(arguments.next().ok_or_else(|| {
                    Failure::usage("`--lines` wants a span, as `<first>..<last>`")
                })?);
            }
            "-n" | "--dry-run" => dry_run = true,
            other if other.starts_with('-') => {
                return Err(Failure::usage(format!(
                    "`{other}` is not an argument `forget` takes"
                )));
            }
            other => rest.push(other.to_owned()),
        }
    }
    let mut rest = rest.into_iter();
    let spelling = rest
        .next()
        .ok_or_else(|| Failure::usage("`forget` wants a revision to read the span at"))?;
    let path = rest
        .next()
        .ok_or_else(|| Failure::usage("`forget` wants a path"))?;
    if let Some(extra) = rest.next() {
        return Err(Failure::usage(format!(
            "`forget` takes a target and one path, and `{extra}` is a third argument"
        )));
    }
    let Some(lines) = lines else {
        return Err(Failure::usage(
            "`forget` wants `--lines <first>..<last>`: a redaction is exact, \
             and the span is the whole request",
        ));
    };
    let (first, last) = span(&lines)?;

    let mut store = open(base)?;
    let revision = target::resolve(&store, &spelling)?;
    let file = target::file_in(&store, &revision, &path)?;
    let forgetting = Forgetting {
        revision,
        file,
        first,
        last,
    };

    let plan = if dry_run {
        store.forget_plan(&forgetting)
    } else {
        store.forget(&forgetting)
    }
    .map_err(Failure::error)?;

    printing(|out| {
        if plan.is_empty() {
            return writeln!(
                out,
                "those lines are already forgotten everywhere they are quoted"
            );
        }
        let (wrote, destroyed) = if dry_run {
            ("would write", "would destroy")
        } else {
            ("wrote", "destroyed")
        };
        for document in &plan.writes {
            writeln!(
                out,
                "{wrote} a forgetting document for {}",
                document
                    .forgets()
                    .expect("a stand-in names its target")
                    .abbreviate(12)
            )?;
        }
        for file in &plan.destroys {
            writeln!(out, "{destroyed} {STORE_DIR}/{}", file.display())?;
        }
        // Decision 0014's "what forgetting cannot hide", said where the
        // person is: a tool that implied otherwise would be worse than one
        // that says nothing.
        writeln!(
            out,
            "the shape and place of those lines, and the revisions around \
             them, are still recorded; only the text is destroyed — and only \
             on this replica until the forgetting documents sync"
        )
    })
}

/// A span of lines, as `--lines` spells it.
pub(super) fn span(spelled: &str) -> Result<(usize, usize), Failure> {
    let malformed = || Failure::usage("a span is `<first>..<last>`, or one line number");
    match spelled.split_once("..") {
        Some((first, last)) => Ok((
            first.parse().map_err(|_| malformed())?,
            last.parse().map_err(|_| malformed())?,
        )),
        None => {
            let line: usize = spelled.parse().map_err(|_| malformed())?;
            Ok((line, line))
        }
    }
}

/// `status [--onto <target>] [--merge <target>]` — the folder against the store.
///
/// Decision 0015. Reads the folder and the store, writes nothing, and mints
/// nothing: two runs over an unchanged folder print the same bytes.
fn status(base: &Path, arguments: Vec<String>) -> Result<u8, Failure> {
    let mut onto: Option<String> = None;
    let mut joining: Vec<String> = Vec::new();

    let mut arguments = arguments.into_iter();
    while let Some(argument) = arguments.next() {
        let mut value = |flag: &str| {
            arguments
                .next()
                .ok_or_else(|| Failure::usage(format!("`{flag}` wants a value")))
        };
        match argument.as_str() {
            "--onto" => onto = Some(value("--onto")?),
            "--merge" => joining.push(value("--merge")?),
            other => {
                return Err(Failure::usage(format!(
                    "`{other}` is not an argument `status` takes"
                )));
            }
        }
    }

    let root = locate(base)?;
    let store = Store::open(&root)?;
    let repository = root
        .parent()
        .ok_or_else(|| Failure::error("this store has no repository around it"))?
        .to_path_buf();

    // Decision 0011: a rename is stated, and status states nothing, so a
    // folder somebody typed `mv` in shows an `added` and a `dropped` — and the
    // suggestion beside them is where the survey says it noticed.
    let parents = target::parents(&store, onto.as_deref(), &joining)?;
    let working = Working::read(&repository, store.skipped()).map_err(Failure::error)?;
    // The whole folder: `status` says how the folder and the store differ, and
    // a report of some of that difference is a report a person has to
    // remember the shape of.
    let surveyed = survey(
        &store,
        &working,
        &parents,
        &[],
        &[],
        &Restriction::Everything,
    )
    .map_err(Failure::error)?;

    printing(|out| render::status(out, &store, &parents, &surveyed))
}

/// `log [<target>|<from>..<to>]` — the graph, newest first, and what to leave
/// out of it.
///
/// The filters compose by keeping only what satisfies all of them, and
/// `--limit` counts what they left rather than what they were given: a limit
/// applied first would silently mean "of the newest N revisions, the ones that
/// match", which is a different question and never the one asked.
///
/// Decision 0063 puts a range in the same argument position, because it
/// answers the same question about a smaller part of the graph. The filters
/// compose with it as they compose with each other.
fn log(base: &Path, arguments: Vec<String>) -> Result<u8, Failure> {
    let store = open(base)?;
    let mut spelling: Option<String> = None;
    let mut path: Option<String> = None;
    let mut filter = render::Filter::default();

    let mut arguments = arguments.into_iter();
    while let Some(argument) = arguments.next() {
        let mut value = |flag: &str| {
            arguments
                .next()
                .ok_or_else(|| Failure::usage(format!("`{flag}` wants a value")))
        };
        match argument.as_str() {
            "--limit" => {
                let count = value("--limit")?;
                filter.limit = Some(count.parse().map_err(|_| {
                    Failure::usage(format!(
                        "`--limit` wants how many entries to stop after, and \
                         `{count}` is not a count"
                    ))
                })?);
            }
            "--author" => filter.author = Some(value("--author")?),
            "--grep" => filter.grep = Some(value("--grep")?),
            "--since" => filter.since = Some(bound("--since", &value("--since")?, "00:00:00")?),
            "--until" => filter.until = Some(bound("--until", &value("--until")?, "23:59:59")?),
            "--path" => path = Some(value("--path")?),
            other if other.starts_with('-') => {
                return Err(Failure::usage(format!(
                    "`{other}` is not an argument `log` takes"
                )));
            }
            other if spelling.is_none() => spelling = Some(other.to_owned()),
            other => {
                return Err(Failure::usage(format!(
                    "`log` takes one target or one range, and `{other}` is a \
                     second"
                )));
            }
        }
    }

    let reach = match &spelling {
        Some(spelling) => Some(target::reach(&store, spelling)?),
        None => None,
    };
    if let Some(path) = &path {
        // Decision 0008: a path is a fact about a file rather than the file's
        // name, so what a person typed is read once, at one revision, and the
        // file it named is what the log then follows — through the `move` that
        // renamed it as readily as through the edits either side.
        let at = read_at(&store, position(reach.as_ref()), path)?;
        filter.file = Some(target::file_in(&store, &at, path)?);
    }

    let shown = render::shown(&store, reach.as_ref());
    if shown.is_empty() {
        // An empty range is an answer rather than a fault, and a different
        // answer from an empty store: it says the work asked about is already
        // behind the revision it was held up against.
        let said = match &reach {
            Some(target::Reach::Between { from, to }) => format!(
                "{} holds nothing {} does not",
                target::spelled(&store, to),
                target::spelled(&store, from)
            ),
            _ => "no revisions here yet".to_owned(),
        };
        return printing(|out| writeln!(out, "{said}"));
    }

    // Decision 0061: an author, a moment and a message all live in the part of
    // a document that opening the store no longer reads, so `log` is where
    // they are parsed. Every document it covers is held to the parser here,
    // before a byte is printed — a history rendered with a revision quietly
    // missing from it would be the tool disagreeing with the files.
    for id in &shown {
        store.get(id)?;
    }
    printing(|out| render::log(out, &store, &shown, &filter))
}

/// The revision a target argument names, where it named one at all.
///
/// A range names a position at its far end. That is the end a `--path` is
/// read at, and the choice is the same one [`read_at`] makes for a lone
/// target: the file a person typed the name of is the file it is now.
fn position(reach: Option<&target::Reach>) -> Option<historica::core::RevisionId> {
    match reach {
        None => None,
        Some(target::Reach::From(id)) => Some(*id),
        Some(target::Reach::Between { to, .. }) => Some(*to),
    }
}

/// The revision a `--path` value is read at.
///
/// The revision `log` was given, and the head where it was given none, which is
/// the position every other command works from. Where there are several heads
/// there is no such position, and inventing one would mean answering about a
/// line of work nobody named.
fn read_at(
    store: &Store,
    from: Option<historica::core::RevisionId>,
    path: &str,
) -> Result<historica::core::RevisionId, Failure> {
    if let Some(id) = from {
        return Ok(id);
    }
    let heads = target::current_heads(store);
    match heads.len() {
        0 => Err(Failure::error("this store holds no revisions yet")),
        1 => Ok(heads.into_iter().next().expect("one head")),
        several => Err(Failure::error(format!(
            "this store has {several} heads, so there is no one place to read \
             `{path}` at; say which revision to read it at, as \
             `historica log <target> --path {path}`:\n{}",
            target::described(store, &heads)
        ))),
    }
}

/// The wall clock a `--since` or `--until` value bounds.
///
/// The format keeps the offset each author was in and decision 0002 keeps
/// timestamps out of identity, causality, and ordering alike, so there is no
/// shared instant here for a bound to name. What a bound compares against is
/// therefore the date and time the author read, in their own offset — and a
/// bare date is that whole day there, which is why the two flags fill in a
/// different time of day for one.
fn bound(flag: &str, value: &str, time: &str) -> Result<String, Failure> {
    if let Ok(timestamp) = value.parse::<Timestamp>() {
        return Ok(render::wall(timestamp.as_str()).to_owned());
    }
    // Held to being a real date by the parser that already knows about leap
    // years, with an offset supplied only to give it something to check.
    if format!("{value}T00:00:00+00:00")
        .parse::<Timestamp>()
        .is_ok()
    {
        return Ok(format!("{value}T{time}"));
    }
    Err(Failure::usage(format!(
        "`{flag}` wants a date, as `YYYY-MM-DD`, or a whole time, as \
         `YYYY-MM-DDThh:mm:ss±hh:mm`; `{value}` is neither"
    )))
}

/// `show <target> [<path>]` — a stored document, byte for byte.
fn show(base: &Path, arguments: Vec<String>) -> Result<u8, Failure> {
    let store = open(base)?;
    let mut arguments = arguments.into_iter();
    let spelling = arguments
        .next()
        .ok_or_else(|| Failure::usage("`show` wants a target"))?;
    let path = arguments.next();
    if let Some(extra) = arguments.next() {
        return Err(Failure::usage(format!(
            "`show` takes a target and one path, and `{extra}` is a third argument"
        )));
    }

    let id = target::resolve(&store, &spelling)?;
    let document = store
        .get(&id)?
        .ok_or_else(|| Failure::error(format!("this store does not hold the revision {id}")))?;

    let document_bytes = match path {
        None => document.write(),
        Some(path) => {
            let file = target::file_in(&store, &id, &path)?;
            // Decision 0017 gives a revision three ways to say what one file
            // holds, and `show` prints whichever it used, byte for byte,
            // because the readable file is the authority.
            if let Some(named) = document.edited.get(&file) {
                // Decision 0032: an `edit` line names either grammar, and
                // `show` prints what is stored — so it asks which grammar
                // rather than assuming the older one. A merge is exactly
                // where a person most wants the stored bytes.
                match store.body(named).map_err(Failure::error)? {
                    Some(Body::Operation(document)) => document.write(),
                    Some(Body::Resolution(document)) => document.write(),
                    // Decision 0014: the bytes were destroyed, and what is
                    // stored — and printed, byte for byte — is what stands
                    // in for them.
                    None => stands_in(&store, named)?.ok_or_else(|| {
                        Failure::error(format!(
                            "{} names the content document {named}, \
                             which this store does not hold yet",
                            id.abbreviate(12)
                        ))
                    })?,
                }
            } else if let Some(payload) = document
                .text
                .get(&file)
                .or_else(|| document.bytes.get(&file))
            {
                match store.payload(payload).map_err(Failure::error)? {
                    Some(bytes) => bytes,
                    None => stands_in(&store, payload)?.ok_or_else(|| {
                        Failure::error(format!(
                            "{} names the content {payload}, \
                             which this store does not hold yet",
                            id.abbreviate(12)
                        ))
                    })?,
                }
            } else {
                return Err(Failure::error(format!(
                    "{} said nothing about {path}; `show {spelling}` lists what it did",
                    id.abbreviate(12)
                )));
            }
        }
    };

    printing(|out| out.write_all(&document_bytes))
}

/// The stored bytes of whatever stands in for a destroyed document.
///
/// Several forgetting documents may name one digest — replicas redact
/// independently — and each is a real file of the store, so each is printed.
fn stands_in(
    store: &Store,
    target: &historica::core::RevisionId,
) -> Result<Option<Vec<u8>>, Failure> {
    // Either grammar, because a resolution's minted items are destroyed by a
    // stand-in written as a resolution — decision 0032's second grammar
    // reaching 0014, and a stand-in has the shape of what it stands in for.
    let mut bytes: Vec<u8> = Vec::new();
    for document in store.forgetting(target).map_err(Failure::error)? {
        bytes.extend(document.write());
    }
    for document in store
        .forgetting_resolution(target)
        .map_err(Failure::error)?
    {
        bytes.extend(document.write());
    }
    if bytes.is_empty() {
        return Ok(None);
    }
    Ok(Some(bytes))
}

/// `files <target>` — the file set, which is what the tree facts replay to.
fn files(base: &Path, arguments: Vec<String>) -> Result<u8, Failure> {
    let store = open(base)?;
    let mut arguments = arguments.into_iter();
    let spelling = arguments
        .next()
        .ok_or_else(|| Failure::usage("`files` wants a target"))?;
    if let Some(extra) = arguments.next() {
        return Err(Failure::usage(format!(
            "`files` takes one target, and `{extra}` is a second"
        )));
    }

    let id = target::resolve(&store, &spelling)?;
    let tree = store.tree(&id).map_err(Failure::error)?;
    printing(|out| render::files(out, &tree))
}

/// `cat <target> <path>` — one file, materialised.
fn cat(base: &Path, arguments: Vec<String>) -> Result<u8, Failure> {
    let store = open(base)?;
    let mut arguments = arguments.into_iter();
    let spelling = arguments
        .next()
        .ok_or_else(|| Failure::usage("`cat` wants a target"))?;
    let path = arguments
        .next()
        .ok_or_else(|| Failure::usage("`cat` wants a path"))?;
    if let Some(extra) = arguments.next() {
        return Err(Failure::usage(format!(
            "`cat` takes a target and a path, and `{extra}` is a third argument"
        )));
    }

    let id = target::resolve(&store, &spelling)?;
    let file = target::file_in(&store, &id, &path)?;
    // Decision 0040: a link has no bytes, and printing the target where the
    // content goes would be a rendering standing in for a file. Named here
    // rather than left to the store's own refusal so that the reader is told
    // what it points at, which is the question they were asking.
    let tree = store.tree(&id).map_err(Failure::error)?;
    if let Some(target) = tree.target(&file) {
        return Err(Failure::error(format!(
            "`{path}` is a link to `{}`, so there is nothing to print; \
             what it holds is where it points",
            historica::update::materialise(&tree, tree.path(&file).unwrap_or(&path), target)
                .unwrap_or_else(|| target.to_string())
        )));
    }
    // Decision 0017: whichever kind of file it is, byte for byte. A picture
    // written to a terminal is a mess and a picture written to a pipe is a
    // picture, and choosing between those is the shell's business.
    let content = store.content_at(&id, &file).map_err(Failure::error)?;
    printing(|out| out.write_all(&content.bytes()))
}

/// `names` — the only mutable files in a store, and what they resolve to.
fn names(base: &Path, arguments: Vec<String>) -> Result<u8, Failure> {
    let store = open(base)?;
    if let Some(extra) = arguments.first() {
        return Err(Failure::usage(format!(
            "`names` takes no arguments, and `{extra}` is one"
        )));
    }

    printing(|out| render::names(out, &store))
}

/// `name <bookmark> <target> [<path>] [--revision] [--private|--shared]` —
/// move a bookmark.
///
/// Decision 0024 gives this the third argument `show` already takes, and means
/// by it what `show` means: this revision, and one file in it. With two
/// arguments the bookmark points at the work, with three it points at a file.
///
/// Decision 0062 adds the travel axis, and makes stating it deliberate in both
/// directions: neither flag keeps whatever the bookmark already had, because
/// the common caller of the move is `record`.
fn name(base: &Path, arguments: Vec<String>) -> Result<u8, Failure> {
    let mut pin = false;
    // Decision 0062's axis, and `None` is *keep whatever it has*: a bookmark
    // that un-privatised itself because somebody moved it would be the leak
    // the axis exists to prevent, and moving one is what `record` does on
    // every commit.
    let mut axis: Option<bool> = None;
    let mut rest = Vec::new();
    for argument in arguments {
        match argument.as_str() {
            "--revision" => pin = true,
            "--change" => pin = false,
            "--private" => axis = Some(true),
            "--shared" => axis = Some(false),
            other => rest.push(other.to_owned()),
        }
    }
    let mut rest = rest.into_iter();
    let bookmark = rest
        .next()
        .ok_or_else(|| Failure::usage("`name` wants a bookmark"))?;
    let spelling = rest
        .next()
        .ok_or_else(|| Failure::usage("`name` wants a target"))?;
    let path = rest.next();
    if let Some(extra) = rest.next() {
        return Err(Failure::usage(format!(
            "`name` takes a bookmark, a target, and one path, and `{extra}` is a \
             fourth argument"
        )));
    }
    if pin && path.is_some() {
        return Err(Failure::usage(
            "a file bookmark has nothing to pin: a file identifier is minted \
             once and survives every rename and every amendment, so `--revision` \
             names nothing here",
        ));
    }

    let mut store = open(base)?;
    let id = target::resolve(&store, &spelling)?;
    let target = match (path, pin) {
        // A file is resolved at the revision named, and the bookmark holds only
        // what it resolved to: which file, never which version of it.
        (Some(path), _) => Name::File(target::file_in(&store, &id, &path)?),
        (None, true) => Name::Revision(id),
        (None, false) => {
            // Decision 0006 makes `change` the default: a bookmark that follows
            // amend and rebase is the one a person wants nearly always.
            let revision = store.revision(&id).ok_or_else(|| {
                Failure::error(format!("this store does not hold the revision {id}"))
            })?;
            Name::Change(revision.change)
        }
    };

    let private = match axis {
        Some(stated) => stated,
        None => store.bookmark(&bookmark).is_some_and(|had| had.private),
    };
    let stated = Bookmark { target, private };
    store.set_bookmark(&bookmark, stated)?;
    printing(|out| {
        writeln!(out, "{bookmark} -> {stated}")?;
        // Decision 0062's deferred item, said where a person would otherwise
        // find out by syncing: the axis unions toward private, so a replica
        // that has not heard puts the flag back.
        if axis == Some(false) {
            writeln!(
                out,
                "note: a replica still calling `{bookmark}` private will make \
                 it private again on the next receive"
            )?;
        }
        Ok(())
    })
}

/// `skip [--private] <path>... [--name <name>]` — what history does not take.
///
/// The file is four keys and a value, so this command is a convenience and
/// says so by refusing to be anything more: it appends the line a person
/// would have typed, and every rule it writes is one `Skipped::rule_in` reads
/// back. What it adds over an editor is the refusal — decision 0011's rule
/// that a rule may not cover a file the tree already holds, checked here
/// before the file is written rather than at the next `record`, because the
/// person is standing in front of the answer now.
///
/// `--private` is decision 0051's travel axis, and it applies to the whole
/// invocation rather than to the argument after it: a person writing one
/// command means one thing by it, and a flag that moved rule by rule would be
/// a precedence to read, which is what the rule file exists not to have.
///
/// With no arguments it prints the rules, as `names` prints the bookmarks.
fn skip(base: &Path, arguments: Vec<String>) -> Result<u8, Failure> {
    let mut scopes: Vec<Scope> = Vec::new();
    let mut private = false;
    let mut arguments = arguments.into_iter();
    while let Some(argument) = arguments.next() {
        match argument.as_str() {
            "--private" => private = true,
            "--name" => {
                let name = arguments
                    .next()
                    .ok_or_else(|| Failure::usage("`--name` wants a name to match"))?;
                scopes.push(name_scope(&name)?);
            }
            // Decision 0051 retires the key, so the flag that wrote it goes
            // with it, and says what to type instead rather than what it is
            // not.
            "--suffix" => {
                return Err(Failure::usage(
                    "`--suffix` is retired: an ending is `--name` and `*` and the \
                     ending, matched against a file's own name",
                ));
            }
            other if other.starts_with("--") => {
                return Err(Failure::usage(format!(
                    "`{other}` is not an argument `skip` takes"
                )));
            }
            path => scopes.push(path_scope(base, path)?),
        }
    }
    let wanted: Vec<Rule> = scopes
        .into_iter()
        .map(|scope| match private {
            true => Rule::private(scope),
            false => Rule::shared(scope),
        })
        .collect();

    let mut store = open(base)?;
    if wanted.is_empty() {
        // The rules, each with the file stating it, since decision 0045 makes
        // that file the whole of what deleting a rule means. `cat` was the
        // preview 0016 asked for while there was one file to cat.
        //
        // Decision 0051 puts the kind on the second line: `export` treats the
        // two differently and the word is what makes that visible without the
        // reader having to know which of four keys travels.
        let rules: Vec<(String, &'static str, String)> = store
            .skipped()
            .stating()
            .map(|(rule, file)| {
                let kind = match rule.travels() {
                    true => "shared",
                    false => "private",
                };
                (rule.to_string(), kind, file.unwrap_or_default().to_owned())
            })
            .collect();
        return printing(|out| {
            for (rule, kind, file) in &rules {
                writeln!(out, "{rule}\n  {kind}  {STORE_DIR}/{SKIPPED_DIR}/{file}")?;
            }
            Ok(())
        });
    }

    // Decision 0011, checked against every head rather than one: a rule is a
    // fact about the repository, so a path any line of work holds is a path
    // this cannot cover — and refusing here means never asking for `--onto`
    // to answer a question that has the same answer at both heads anyway.
    let mut covered: Vec<String> = Vec::new();
    for head in store.history().heads() {
        let tree = store
            .merged_tree_of(&[head])
            .map_err(|error| Failure::error(error.to_string()))?;
        for (_, path) in tree.tree.files() {
            if wanted.iter().any(|rule| rule.covers(path)) && !covered.iter().any(|had| had == path)
            {
                covered.push(path.to_owned());
            }
        }
    }
    if !covered.is_empty() {
        covered.sort();
        return Err(Failure::error(format!(
            "history already holds {}, and a rule cannot take back what is \
             recorded; delete the {} and record that, which is what removing a \
             file from the tree means, and `forget` is what removes recorded \
             content:{}",
            if covered.len() == 1 {
                "a file this would skip".to_owned()
            } else {
                format!("{} files this would skip", covered.len())
            },
            if covered.len() == 1 { "file" } else { "files" },
            covered
                .iter()
                .map(|path| format!("\n  {path}"))
                .collect::<String>()
        )));
    }

    // A rule the file already states is said so rather than written twice:
    // two identical lines mean what one does, and the person asking has
    // already got what they asked for.
    let mut fresh: Vec<Rule> = Vec::new();
    let mut already: Vec<String> = Vec::new();
    for rule in wanted {
        if store.skipped().rules().any(|had| *had == rule) || fresh.contains(&rule) {
            already.push(rule.to_string());
        } else {
            fresh.push(rule);
        }
    }
    let written = store.add_skipped(&fresh)?;

    printing(|out| {
        for (rule, label) in fresh.iter().zip(&written) {
            writeln!(out, "{rule}\n  {STORE_DIR}/{SKIPPED_DIR}/{label}")?;
        }
        for line in &already {
            writeln!(out, "already there: {line}")?;
        }
        Ok(())
    })
}

/// What a path on the command line matches.
///
/// A directory is spelled with the trailing slash the parser wants, which is
/// the one thing a person is likely to leave off and the one place leaving it
/// off changes the meaning — `skip target` matches a file called `target` and
/// nothing beneath it.
fn path_scope(base: &Path, path: &str) -> Result<Scope, Failure> {
    let root = locate(base)?
        .parent()
        .ok_or_else(|| Failure::error("this store has no repository around it"))?
        .to_path_buf();
    let trimmed = path.trim_end_matches('/');
    let relative = relative_to(&root, trimmed)?;
    let directory = trimmed != path || root.join(&relative).is_dir();
    let value = usable(&relative)?;
    Ok(if directory {
        Scope::Under(value)
    } else {
        Scope::Path(value)
    })
}

/// What a `--name` on the command line matches.
///
/// The same parting the paths make: without the trailing slash the value is a
/// file's own name, with it a directory's and everything beneath. Refused here
/// rather than written and re-read, so the message names the argument the
/// person typed.
fn name_scope(name: &str) -> Result<Scope, Failure> {
    let trimmed = name.strip_suffix('/');
    let value = usable(trimmed.unwrap_or(name))?;
    let pattern = Pattern::parse(&value).map_err(|because| {
        Failure::usage(format!("`{name}` cannot be a name to match: {because}"))
    })?;
    Ok(match trimmed.is_some() {
        true => Scope::NameUnder(pattern),
        false => Scope::Name(pattern),
    })
}

/// Where a path a person typed sits, relative to the repository root.
fn relative_to(root: &Path, path: &str) -> Result<String, Failure> {
    let given = Path::new(path);
    let full = if given.is_absolute() {
        given.to_path_buf()
    } else {
        root.join(given)
    };
    // Only canonicalised where it exists: a rule may name what is not there
    // yet, which is most of what a person writes one for.
    let settled = full.canonicalize().unwrap_or(full);
    let root = root.canonicalize().unwrap_or_else(|_| root.to_path_buf());
    let inside = settled.strip_prefix(&root).map_err(|_| {
        Failure::error(format!(
            "`{path}` is not inside this repository, and a rule names what \
             history would otherwise take"
        ))
    })?;
    let spelled = inside
        .components()
        .map(|part| part.as_os_str().to_string_lossy().into_owned())
        .collect::<Vec<_>>()
        .join("/");
    if spelled.is_empty() {
        return Err(Failure::error(
            "that is the repository itself, and skipping all of it would leave \
             history nothing to hold",
        ));
    }
    Ok(spelled)
}

/// A value the file can hold, refused here rather than written and re-read.
fn usable(value: &str) -> Result<String, Failure> {
    if value.is_empty() || value != value.trim() {
        return Err(Failure::usage(format!(
            "`{value}` cannot be a rule: a value is not empty and carries no \
             leading or trailing space"
        )));
    }
    if value.contains('\n') {
        return Err(Failure::usage(
            "a rule is one line, and this value holds a line break",
        ));
    }
    Ok(value.to_owned())
}

/// Open the store containing `base`.
fn open(base: &Path) -> Result<Store, Failure> {
    Ok(Store::open(locate(base)?)?)
}

/// The store a person pointed `check` at.
///
/// Either the store directory itself or the repository holding one: pointing
/// at `history` and pointing at what contains it are both things a person
/// means, and the difference is not worth an error message.
fn named(base: &Path, path: &str) -> PathBuf {
    let given = base.join(path);
    if given.join(HEADER_FILE).is_file() || given.file_name().is_some_and(|name| name == STORE_DIR)
    {
        given
    } else {
        given.join(STORE_DIR)
    }
}

/// The store directory containing `base`, found by walking up.
///
/// Deliberately laxer than [`Store::discover`], which wants a readable
/// `historica` file: `check` exists to describe a store whose header is
/// missing or from a future version, and it cannot describe what it refuses to
/// find. Every other command hands the directory to [`Store::open`], which
/// says so in those words.
fn locate(base: &Path) -> Result<PathBuf, Failure> {
    let start = base
        .canonicalize()
        .map_err(|error| Failure::error(format!("{}: {error}", base.display())))?;
    for directory in start.ancestors() {
        let candidate = directory.join(STORE_DIR);
        if candidate.is_dir() {
            return Ok(candidate);
        }
    }
    Err(Failure::error(format!(
        "no `{STORE_DIR}` directory here or above {}; `historica init` makes one",
        start.display()
    )))
}

/// Print, to a stdout that may be a pipe somebody closed.
///
/// Everything a command says goes through here rather than through `println!`,
/// which panics when the reader has gone: `historica log | head` is an
/// ordinary thing to type and an ordinary thing to stop reading.
pub(crate) fn printing(
    render: impl FnOnce(&mut io::StdoutLock<'static>) -> io::Result<()>,
) -> Result<u8, Failure> {
    let mut out = io::stdout().lock();
    match render(&mut out).and_then(|()| out.flush()) {
        Ok(()) => Ok(0),
        Err(error) if error.kind() == io::ErrorKind::BrokenPipe => Ok(0),
        Err(error) => Err(Failure::error(format!("stdout: {error}"))),
    }
}
