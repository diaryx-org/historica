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

use historica::record::survey;
use historica::store::{HEADER_FILE, Name, STORE_DIR, Store, StoreError};
use historica::working::{Rule, SKIPPED_FILE, Working};

mod arrange;
mod record;
mod render;
mod target;

/// What `historica help` prints, and what a usage error prints after itself.
pub const USAGE: &str = "\
usage: historica [-C <dir>] <command> [<arguments>]

reading a store
  status [--onto <target>] [--merge <target>]
                           how the folder differs from what is recorded
  log [<target>]           the history, newest first
  show <target> [<path>]   one document as stored: a revision, or what it
                           did to one file
  files <target>           the file set at a revision
  cat <target> <path>      one file's content at a revision
  names                    the bookmarks, and what they point at
  skip                     the rules saying what history does not take

writing a store
  record [-m <message>]    record what the folder now says
         [--onto <target>] [--merge <target>] [--move <old>=<new>]
         [--at <file>=<path>] [--dry-run]
  merge <target>           write what two lines of work say together
  identity <author>        say who you are, once, for every repository
  init [<dir>]             make a store in <dir>/history
  check [<dir>]            read a store and report every fault
  arrange [-n]             rename revision files to readable ones
  name <bookmark> <target> [--revision]
                           point a bookmark at a change, or pin a revision
  skip <path>... [--suffix <suffix>]
                           stop history taking a path, a directory, or an
                           ending; with no arguments, print the rules

a <target> is `head`, a bookmark, a change ID, or a revision digest; the last
two may
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
        "status" => status(&base, rest),
        "log" => log(&base, rest),
        "show" => show(&base, rest),
        "files" => files(&base, rest),
        "cat" => cat(&base, rest),
        "names" => names(&base, rest),
        "name" => name(&base, rest),
        "skip" => skip(&base, rest),
        "record" => record::record(&base, locate(&base)?, rest),
        "merge" => record::merge(locate(&base)?, rest),
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
    let surveyed = survey(&store, &working, &parents, &[], &[]).map_err(Failure::error)?;

    printing(|out| render::status(out, &store, &parents, &surveyed))
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
            // Decision 0017 gives a revision three ways to say what one file
            // holds, and `show` prints whichever it used, byte for byte,
            // because the readable file is the authority.
            if let Some(operations) = document.edited.get(&file) {
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
            } else if let Some(payload) = document
                .text
                .get(&file)
                .or_else(|| document.bytes.get(&file))
            {
                store
                    .payload(payload)
                    .map_err(Failure::error)?
                    .ok_or_else(|| {
                        Failure::error(format!(
                            "{} names the content {payload}, \
                             which this store does not hold yet",
                            id.abbreviate(12)
                        ))
                    })?
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

/// `skip <path>... [--suffix <suffix>]` — write what history does not take.
///
/// The file is two keys and a value, so this command is a convenience and
/// says so by refusing to be anything more: it appends the line a person
/// would have typed, and every rule it writes is one `Skipped::parse` reads
/// back. What it adds over an editor is the refusal — decision 0011's rule
/// that a rule may not cover a file the tree already holds, checked here
/// before the file is written rather than at the next `record`, because the
/// person is standing in front of the answer now.
///
/// With no arguments it prints the rules, as `names` prints the bookmarks.
fn skip(base: &Path, arguments: Vec<String>) -> Result<u8, Failure> {
    let mut wanted: Vec<Rule> = Vec::new();
    let mut arguments = arguments.into_iter();
    while let Some(argument) = arguments.next() {
        match argument.as_str() {
            "--suffix" => {
                let suffix = arguments
                    .next()
                    .ok_or_else(|| Failure::usage("`--suffix` wants an ending"))?;
                wanted.push(Rule::Suffix(usable(&suffix)?));
            }
            other if other.starts_with("--") => {
                return Err(Failure::usage(format!(
                    "`{other}` is not an argument `skip` takes"
                )));
            }
            path => wanted.push(rule_for(base, path)?),
        }
    }

    let mut store = open(base)?;
    if wanted.is_empty() {
        return printing(|out| {
            for rule in store.skipped().rules() {
                writeln!(out, "{rule}")?;
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
             file from the tree means:{}",
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
    store.append_skipped(&fresh)?;

    printing(|out| {
        for line in fresh.iter().map(Rule::to_string).collect::<Vec<_>>() {
            writeln!(out, "{STORE_DIR}/{SKIPPED_FILE}: {line}")?;
        }
        for line in &already {
            writeln!(out, "already there: {line}")?;
        }
        Ok(())
    })
}

/// The rule a path on the command line means.
///
/// A directory is spelled with the trailing slash the parser wants, which is
/// the one thing a person is likely to leave off and the one place leaving it
/// off changes the meaning — `skip target` matches a file called `target` and
/// nothing beneath it.
fn rule_for(base: &Path, path: &str) -> Result<Rule, Failure> {
    let root = locate(base)?
        .parent()
        .ok_or_else(|| Failure::error("this store has no repository around it"))?
        .to_path_buf();
    let trimmed = path.trim_end_matches('/');
    let relative = relative_to(&root, trimmed)?;
    let directory = trimmed != path || root.join(&relative).is_dir();
    let value = usable(&relative)?;
    Ok(if directory {
        Rule::Under(value)
    } else {
        Rule::Path(value)
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
