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

use historica::store::{HEADER_FILE, Name, STORE_DIR, Store, StoreError};

mod arrange;
mod render;
mod target;

/// What `historica help` prints, and what a usage error prints after itself.
pub const USAGE: &str = "\
usage: historica [-C <dir>] <command> [<arguments>]

reading a store
  log [<target>]           the history, newest first
  show <target> [<path>]   one document as stored: a revision, or what it
                           did to one file
  files <target>           the file set at a revision
  cat <target> <path>      one file's content at a revision
  names                    the bookmarks, and what they point at

writing a store
  init [<dir>]             make a store in <dir>/history
  check [<dir>]            read a store and report every fault
  arrange [-n]             rename revision files to readable ones
  name <bookmark> <target> [--revision]
                           point a bookmark at a change, or pin a revision

a <target> is a bookmark, a change ID, or a revision digest; the last two may
be abbreviated to any unambiguous prefix, and their alphabets do not overlap,
so one argument accepts either.
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
            return printing(|out| out.write_all(USAGE.as_bytes()));
        };
        match argument.as_str() {
            "-C" => {
                let directory = arguments
                    .next()
                    .ok_or_else(|| Failure::usage("`-C` wants a directory"))?;
                base = Some(PathBuf::from(directory));
            }
            "-h" | "--help" | "help" => {
                return printing(|out| out.write_all(USAGE.as_bytes()));
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
        "log" => log(&base, rest),
        "show" => show(&base, rest),
        "files" => files(&base, rest),
        "cat" => cat(&base, rest),
        "names" => names(&base, rest),
        "name" => name(&base, rest),
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
    let mut arguments = arguments.into_iter();
    let root = match arguments.next() {
        Some(path) => named(base, &path),
        None => locate(base)?,
    };
    if let Some(extra) = arguments.next() {
        return Err(Failure::usage(format!(
            "`check` takes one directory, and `{extra}` is a second"
        )));
    }

    let report = Store::check(&root);
    // Canonical for the report's last line: `check .` should name the store,
    // not repeat the punctuation that found it.
    let shown = root.canonicalize().unwrap_or(root);
    printing(|out| render::report(out, &shown, &report))?;
    // Decision 0006: notes never fail, so this can be run in anger without
    // teaching anyone to ignore it.
    Ok(u8::from(!report.is_ok()))
}

/// `arrange [-n]` — advisory names, deterministically.
fn arrange(base: &Path, arguments: Vec<String>) -> Result<u8, Failure> {
    let mut dry_run = false;
    let mut rest = Vec::new();
    for argument in arguments {
        match argument.as_str() {
            "-n" | "--dry-run" => dry_run = true,
            other => rest.push(other.to_owned()),
        }
    }
    if let Some(extra) = rest.first() {
        return Err(Failure::usage(format!(
            "`arrange` takes no arguments, and `{extra}` is one"
        )));
    }

    arrange::arrange(&locate(base)?, dry_run)
}

/// `log [<target>]` — the graph, newest first.
fn log(base: &Path, arguments: Vec<String>) -> Result<u8, Failure> {
    let store = open(base)?;
    let mut arguments = arguments.into_iter();
    let from = match arguments.next() {
        Some(spelling) => Some(target::resolve(&store, &spelling)?),
        None => None,
    };
    if let Some(extra) = arguments.next() {
        return Err(Failure::usage(format!(
            "`log` takes one target, and `{extra}` is a second"
        )));
    }

    printing(|out| render::log(out, &store, from))
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
        .get(&id)
        .ok_or_else(|| Failure::error(format!("this store does not hold the revision {id}")))?;

    let document_bytes = match path {
        None => document.write(),
        Some(path) => {
            let file = target::file_in(&store, &id, &path)?;
            let operations = document.edited.get(&file).ok_or_else(|| {
                Failure::error(format!(
                    "{} did not edit {path}; `show {spelling}` lists what it did",
                    id.abbreviate(12)
                ))
            })?;
            store
                .operation(operations)
                .ok_or_else(|| {
                    Failure::error(format!(
                        "{} names the operation document {operations}, \
                         which this store does not hold yet",
                        id.abbreviate(12)
                    ))
                })?
                .write()
        }
    };

    printing(|out| out.write_all(&document_bytes))
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
    let state = store.content(&id, &file).map_err(Failure::error)?;
    printing(|out| out.write_all(state.text().as_bytes()))
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

/// `name <bookmark> <target> [--revision]` — move a bookmark.
fn name(base: &Path, arguments: Vec<String>) -> Result<u8, Failure> {
    let mut pin = false;
    let mut rest = Vec::new();
    for argument in arguments {
        match argument.as_str() {
            "--revision" => pin = true,
            "--change" => pin = false,
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
    if let Some(extra) = rest.next() {
        return Err(Failure::usage(format!(
            "`name` takes a bookmark and a target, and `{extra}` is a third argument"
        )));
    }

    let mut store = open(base)?;
    let id = target::resolve(&store, &spelling)?;
    let target = if pin {
        Name::Revision(id)
    } else {
        // Decision 0006 makes `change` the default: a bookmark that follows
        // amend and rebase is the one a person wants nearly always.
        let document = store
            .get(&id)
            .ok_or_else(|| Failure::error(format!("this store does not hold the revision {id}")))?;
        Name::Change(document.change)
    };

    store.set_name(&bookmark, target)?;
    printing(|out| writeln!(out, "{bookmark} -> {target}"))
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
fn printing(
    render: impl FnOnce(&mut io::StdoutLock<'static>) -> io::Result<()>,
) -> Result<u8, Failure> {
    let mut out = io::stdout().lock();
    match render(&mut out).and_then(|()| out.flush()) {
        Ok(()) => Ok(0),
        Err(error) if error.kind() == io::ErrorKind::BrokenPipe => Ok(0),
        Err(error) => Err(Failure::error(format!("stdout: {error}"))),
    }
}
