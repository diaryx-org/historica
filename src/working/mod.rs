//! The folder beside the store, and what it does not take.
//!
//! Specified by `docs/decisions/0011-working-copy.md`. The working copy is the
//! directory holding `history/`, everything in it is tracked, and
//! `history/skipped.txt` names the exceptions. Nothing here is remembered between
//! commands: reading a working copy is a walk of the filesystem, every time.
//!
//! Decision 0043 leaves that sentence standing and makes it cheaper to keep.
//! [`Working::digest`] is what a comparison against the store actually asks
//! for, and `history/cache/working.txt` says what each path hashed to last
//! time — believed only where the directory still reports the size and the
//! modification time that digest was taken at, and only where that time is
//! strictly older than the catalogue's own. It is not an index and holds no
//! content: delete it and every command says exactly what it said before,
//! having read the folder, which is what it would have done anyway.

use std::cell::RefCell;
use std::collections::BTreeMap;
use std::fmt;
use std::io;
use std::path::{Path, PathBuf};

use crate::core::RevisionId;
use crate::format::check_path;
use crate::fs::{Disk, Entry, Filesystem, Stamp, read_to_string};
use crate::store::STORE_DIR;

mod catalogue;

/// The file in the store that says what history does not take.
pub const SKIPPED_FILE: &str = "skipped.txt";

/// What `history/skipped.txt` says.
///
/// Two keys, and deliberately no pattern language: decision 0011 argues that
/// the part people get wrong about gitignore is never the pattern but which of
/// five files won.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Skipped {
    rules: Vec<Rule>,
}

/// One line of `history/skipped.txt`.
///
/// Public because writing the file is a thing a command does, and a rule that
/// renders itself is what keeps the writer from spelling a line the reader
/// would refuse.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Rule {
    /// One exact path.
    Path(String),
    /// A directory and everything beneath it. Held without its trailing `/`.
    Under(String),
    /// A trailing string, matched against the last component.
    Suffix(String),
}

impl Rule {
    /// Whether this rule covers a path.
    pub fn covers(&self, path: &str) -> bool {
        match self {
            Rule::Path(exact) => path == exact,
            Rule::Under(prefix) => path
                .strip_prefix(prefix.as_str())
                .is_some_and(|rest| rest.starts_with('/')),
            Rule::Suffix(suffix) => path
                .rsplit('/')
                .next()
                .unwrap_or(path)
                .ends_with(suffix.as_str()),
        }
    }
}

impl fmt::Display for Rule {
    /// The line the file holds, which [`Skipped::parse`] reads back.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Rule::Path(path) => write!(f, "skip {path}"),
            Rule::Under(path) => write!(f, "skip {path}/"),
            Rule::Suffix(suffix) => write!(f, "skip-suffix {suffix}"),
        }
    }
}

/// What `init` writes into `history/skipped.txt`.
///
/// Decision 0027: the file explains the rule syntax and states no rules.
/// Defaults belong to a host or project that knows what its files mean; the
/// history library does not silently leave anything out.
pub const DEFAULT_SKIPPED: &str = "\
# What recording does not take. One rule a line: `skip <path>`, `skip <path>/`
# for everything under it, or `skip-suffix <ending>`. A `#` line says nothing.
";

impl Skipped {
    /// Skip nothing, which is what a store with no such file says.
    pub fn none() -> Self {
        Self::default()
    }

    /// Read the file's text.
    ///
    /// An unknown key is an error rather than something to ignore. Decision
    /// 0011: a reader that ignored a key it had not heard of would record
    /// files somebody asked it to keep out, into a history that is
    /// append-only, and refusing to record is the recoverable half of that.
    pub fn parse(text: &str) -> Result<Self, MalformedSkip> {
        let mut rules = Vec::new();
        for (index, line) in text.lines().enumerate() {
            let at = index + 1;
            if line.is_empty() {
                continue;
            }
            // Decision 0022: a comment states nothing, so 0011's reason for
            // refusing an unknown key — that a reader which ignored one would
            // record files somebody asked it to keep out — does not reach it.
            if line.starts_with('#') {
                continue;
            }
            let (key, value) = line.split_once(' ').ok_or(MalformedSkip {
                at,
                because: "a line is a key, a space, and a value",
            })?;
            if value.is_empty() || value != value.trim() {
                return Err(MalformedSkip {
                    at,
                    because: "a value is not empty and carries no leading or trailing space",
                });
            }
            rules.push(match key {
                "skip" if value.ends_with('/') => {
                    Rule::Under(crate::format::nfc(value.trim_end_matches('/')).into_owned())
                }
                "skip" => Rule::Path(crate::format::nfc(value).into_owned()),
                "skip-suffix" => Rule::Suffix(crate::format::nfc(value).into_owned()),
                _ => {
                    return Err(MalformedSkip {
                        at,
                        because: "the keys are `skip` and `skip-suffix`",
                    });
                }
            });
        }
        Ok(Self { rules })
    }

    /// Whether history takes this path.
    pub fn skips(&self, path: &str) -> bool {
        self.rules.iter().any(|rule| rule.covers(path))
    }

    /// Whether a directory is skipped whole, so that walking it is pointless.
    ///
    /// Public because a path a person typed may name the directory rather than
    /// a file in it, and a command that could not tell "no such path" from
    /// "a rule keeps that path out" would say the wrong one of the two.
    pub fn skips_directory(&self, path: &str) -> bool {
        self.rules.iter().any(|rule| match rule {
            Rule::Under(prefix) | Rule::Path(prefix) => path == prefix,
            Rule::Suffix(_) => false,
        })
    }

    /// Every rule, in the order the file states them.
    pub fn rules(&self) -> impl Iterator<Item = &Rule> {
        self.rules.iter()
    }

    /// How many rules the file states.
    pub fn len(&self) -> usize {
        self.rules.len()
    }

    /// Whether the file states no rules.
    pub fn is_empty(&self) -> bool {
        self.rules.is_empty()
    }
}

/// A line of `history/skipped.txt` that was not one rule.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MalformedSkip {
    /// The line, counted from one.
    pub at: usize,
    /// What was wanted there.
    pub because: &'static str,
}

impl fmt::Display for MalformedSkip {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "line {}: {}", self.at, self.because)
    }
}

impl std::error::Error for MalformedSkip {}

/// The tracked files, by path, as the folder stands.
///
/// Holds the filesystem it was read from, so that [`Working::text`] and
/// [`Working::bytes`] read the same folder the walk saw. A working copy read
/// from one filesystem and read back through another would be describing a
/// folder it had never looked at — and because the filesystem is a type
/// parameter, [`crate::record::record`] can insist that a working copy and the
/// store it is recorded into are the same kind of folder.
#[derive(Debug, Clone)]
pub struct Working<F = Disk> {
    filesystem: F,
    /// The folder this is, which is also where `history/cache/` is found.
    root: PathBuf,
    files: BTreeMap<String, PathBuf>,
    /// Which tracked paths are links, and what each points at.
    ///
    /// Decision 0040: read during the walk, with the walk's own promise that
    /// nothing is followed. `None` against a path is the filesystem saying it
    /// cannot read the target — 0034's answer, doing 0034's work — and a
    /// recorder that gets it states nothing about that link.
    links: BTreeMap<String, Option<String>>,
    /// What the directory said about each tracked regular file, where it says
    /// anything at all.
    ///
    /// Decision 0043. Empty on a filesystem that reports no
    /// [`Stamp`](crate::fs::Stamp), which is the whole of what such a
    /// filesystem loses: every digest below is worked out by reading.
    stamps: BTreeMap<String, Stamp>,
    /// The digest of each tracked file, once anything has asked for it.
    ///
    /// Seeded from `history/cache/working.txt` with the entries the stamps
    /// above allow, and filled in by reading for everything else. Behind a
    /// cell because a working copy is read through a shared reference while it
    /// answers questions about itself — the same reason the store's own reads
    /// are.
    known: RefCell<Known>,
    refused: Vec<(String, String)>,
}

/// What this pass knows about the folder's content, and whether it learned any
/// of it the expensive way.
#[derive(Debug, Clone, Default)]
struct Known {
    digests: BTreeMap<String, RevisionId>,
    /// Whether anything here was worked out rather than taken from the
    /// catalogue. A folder nobody has touched learns nothing, and rewriting
    /// the file for it would be the whole catalogue's bytes for no change at
    /// all, on every command.
    learned: bool,
}

#[cfg(feature = "disk")]
impl Working<Disk> {
    /// Walk `root` on disk, taking every file the rules leave.
    pub fn read(root: &Path, skipped: &Skipped) -> Result<Self, WorkingError> {
        Self::read_on(Disk, root, skipped)
    }
}

impl<F: Filesystem> Working<F> {
    /// Walk `root` on `filesystem`, taking every file the rules leave.
    ///
    /// `history/` is never tracked and needs no rule. A name that is not UTF-8,
    /// or anything that is neither a regular file nor a link, is refused by
    /// name rather than skipped quietly: decision 0011 puts the difference
    /// between losing work and not at one error message.
    ///
    /// Decision 0040 takes symbolic links off that list. A link is a thing a
    /// folder holds, so the walk *reads* it — with
    /// [`Filesystem::link_target`], which follows nothing — and takes it as a
    /// tracked path whose content is a target rather than bytes.
    ///
    /// Decision 0015: the refusals are collected rather than raised one at a
    /// time, so that `status` can list a folder's whole set and a person can
    /// write the `skip` rules in one pass. `record` raises the collection,
    /// which is the same refusal on the same files. What still returns here is
    /// [`WorkingError::Io`] — a directory that cannot be read is not a fact
    /// about the folder, it is not knowing, and a walk that collected it would
    /// describe a folder while quietly missing part of it.
    pub fn read_on(filesystem: F, root: &Path, skipped: &Skipped) -> Result<Self, WorkingError> {
        let mut found = Found::default();
        walk(&filesystem, root, "", skipped, &mut found)?;
        // Decision 0043: what the last command hashed, kept only where the
        // directory still reports the size and the time it hashed it at. A
        // filesystem that reports neither hands back nothing here, and every
        // digest below is worked out by reading — which is what every command
        // did before this existed.
        let digests = catalogue::believed(&filesystem, &root.join(STORE_DIR), &found.stamps);
        Ok(Self {
            filesystem,
            root: root.to_path_buf(),
            files: found.files,
            links: found.links,
            stamps: found.stamps,
            known: RefCell::new(Known {
                digests,
                learned: false,
            }),
            refused: found.refused,
        })
    }

    /// The filesystem this working copy was read from.
    pub fn filesystem(&self) -> &F {
        &self.filesystem
    }

    /// Every path the walk would not take, with the short reason.
    pub fn refused(&self) -> &[(String, String)] {
        &self.refused
    }

    /// Every tracked path, in order, with where it is on disk.
    pub fn iter(&self) -> impl Iterator<Item = (&String, &PathBuf)> {
        self.files.iter()
    }

    /// Where one tracked path is on disk.
    pub fn get(&self, path: &str) -> Option<&PathBuf> {
        self.files.get(path)
    }

    /// Whether the folder holds this path.
    pub fn holds(&self, path: &str) -> bool {
        self.files.contains_key(path)
    }

    /// How many files are tracked.
    pub fn len(&self) -> usize {
        self.files.len()
    }

    /// Whether nothing is tracked.
    pub fn is_empty(&self) -> bool {
        self.files.is_empty()
    }

    /// One file's text, refused if it is not UTF-8.
    ///
    /// 0007's items are lines of text, so this is the boundary a file already
    /// recorded as lines is held to. A file nobody has recorded yet is offered
    /// to [`kind_of`] instead, which decides what kind it is rather than
    /// refusing it.
    pub fn text(&self, path: &str) -> Result<String, WorkingError> {
        let on_disk = self.regular(path)?;
        match read_to_string(&self.filesystem, on_disk) {
            Ok(text) => Ok(text),
            Err(error) if error.kind() == io::ErrorKind::InvalidData => {
                Err(WorkingError::NotText {
                    path: path.to_owned(),
                })
            }
            Err(error) => Err(WorkingError::io(on_disk, error)),
        }
    }

    /// One file's bytes, whatever they are.
    ///
    /// Decision 0017: a file that is not text is content that arrives whole
    /// rather than content this format cannot hold.
    pub fn bytes(&self, path: &str) -> Result<Vec<u8>, WorkingError> {
        let on_disk = self.regular(path)?;
        self.filesystem
            .read(on_disk)
            .map_err(|error| WorkingError::io(on_disk, error))
    }

    /// What one tracked file's bytes hash to.
    ///
    /// Decision 0043, and the question `status` and `record` ask before they
    /// ask for a file's content: identity comes from content, so *has this
    /// changed* is a comparison of digests, and the digest the store already
    /// states is on the other side of it.
    ///
    /// Answered from `history/cache/working.txt` where the directory says the
    /// file has not been written to since that digest was taken, and by
    /// reading the file otherwise — in pieces where the filesystem offers
    /// them, so a photograph costs a buffer rather than its own size. Which of
    /// the two happened changes how long this took and nothing else.
    pub fn digest(&self, path: &str) -> Result<RevisionId, WorkingError> {
        let on_disk = self.regular(path)?;
        if let Some(known) = self.known.borrow().digests.get(path).copied() {
            return Ok(known);
        }
        let digest = crate::fs::digest_of(&self.filesystem, on_disk)
            .map_err(|error| WorkingError::io(on_disk, error))?;
        let mut known = self.known.borrow_mut();
        known.digests.insert(path.to_owned(), digest);
        known.learned = true;
        Ok(digest)
    }

    /// One file's bytes, and the digest this read found them to have.
    ///
    /// Decision 0036's rule, applied one level up: *a lookup hashes what it
    /// reads before believing it*. The catalogue says where to look and never
    /// what is there, so whatever it said about this path, these bytes are
    /// what the path holds — and a catalogue that was wrong about a file is
    /// corrected by the read it caused rather than costing that read on every
    /// command afterwards.
    pub fn bytes_and_digest(&self, path: &str) -> Result<(Vec<u8>, RevisionId), WorkingError> {
        let bytes = self.bytes(path)?;
        let found = crate::format::digest(&bytes);
        self.correct(path, found);
        Ok((bytes, found))
    }

    /// One file's text, and the digest this read found its bytes to have.
    ///
    /// [`Working::bytes_and_digest`] for the files that are lines.
    pub fn text_and_digest(&self, path: &str) -> Result<(String, RevisionId), WorkingError> {
        let text = self.text(path)?;
        let found = crate::format::digest(text.as_bytes());
        self.correct(path, found);
        Ok((text, found))
    }

    /// Replace what is known about a path with what a read of it found.
    fn correct(&self, path: &str, found: RevisionId) {
        let mut known = self.known.borrow_mut();
        if known.digests.insert(path.to_owned(), found) != Some(found) {
            known.learned = true;
        }
    }

    /// Write down what this pass worked out, so the next one need not.
    ///
    /// Called once, by whatever has finished asking — the catalogue is
    /// rewritten whole, and a caller that wrote it after every question would
    /// be quadratic in the size of the folder. Nothing is reported: a folder
    /// on a read-only filesystem and a `cache/` somebody deleted mid-command
    /// are both conditions under which describing a folder must still succeed,
    /// and nothing was lost, because nothing here was information.
    ///
    /// A folder that learned nothing writes nothing, so a `status` on a folder
    /// nobody has touched leaves `cache/` exactly as it found it.
    pub fn remember(&self) {
        let known = self.known.borrow();
        if !known.learned || self.stamps.is_empty() {
            return;
        }
        catalogue::write(
            &self.filesystem,
            &self.root.join(STORE_DIR),
            &known.digests,
            &self.stamps,
        );
    }

    /// Whether one tracked file can be run, or `None` where this filesystem
    /// has no such bit.
    ///
    /// Decision 0034: `None` is not `false`. A recorder that cannot see the
    /// bit states nothing about it and leaves the recorded value standing,
    /// which is what stops two machines flipping it at each other.
    pub fn executable(&self, path: &str) -> Result<Option<bool>, WorkingError> {
        let on_disk = self.files.get(path).ok_or_else(|| WorkingError::Missing {
            path: path.to_owned(),
        })?;
        self.filesystem
            .executable(on_disk)
            .map_err(|error| WorkingError::io(on_disk, error))
    }

    /// Whether one tracked path is a symbolic link.
    pub fn is_link(&self, path: &str) -> bool {
        self.links.contains_key(path)
    }

    /// What one tracked link points at, as the folder spells it.
    ///
    /// `None` for a path that is not a link, and for a link on a filesystem
    /// that reports links and cannot read one — which a caller tells apart
    /// with [`Working::is_link`], and which decision 0040 makes the same
    /// answer either way: state nothing.
    pub fn link_target(&self, path: &str) -> Option<&str> {
        self.links.get(path)?.as_deref()
    }

    /// Every tracked link, with what it points at.
    pub fn links(&self) -> impl Iterator<Item = (&String, Option<&str>)> {
        self.links
            .iter()
            .map(|(path, target)| (path, target.as_deref()))
    }

    /// Where a tracked *regular* file is on disk.
    ///
    /// The one guard that keeps decision 0040's standing rule true by
    /// construction: a link is tracked now, and reading its path through
    /// `read` would open what it points at rather than the link. A caller that
    /// wants a link asks for its target.
    fn regular(&self, path: &str) -> Result<&PathBuf, WorkingError> {
        if self.links.contains_key(path) {
            return Err(WorkingError::IsALink {
                path: path.to_owned(),
            });
        }
        self.files.get(path).ok_or_else(|| WorkingError::Missing {
            path: path.to_owned(),
        })
    }
}

/// Which kind of file a person has just put in the folder.
///
/// Decision 0017 puts this rule in the tool rather than in the format: text is
/// valid UTF-8 with no NUL byte, and everything else is bytes. The format's
/// own rule is narrower — a `text` payload is valid UTF-8, because a later
/// `edit` has to quote its items — and NUL is the oldest and most reliable
/// signal that a person did not write this file as prose. A recorder is
/// allowed signals the format may not use.
///
/// Sniffed once, when a file is added, and never again: after that the kind
/// belongs to the file's identity and changing it is `drop` and `add`.
pub fn is_text(bytes: &[u8]) -> bool {
    !bytes.contains(&0) && std::str::from_utf8(bytes).is_ok()
}

/// What one walk of the folder turned up.
#[derive(Default)]
struct Found {
    files: BTreeMap<String, PathBuf>,
    links: BTreeMap<String, Option<String>>,
    stamps: BTreeMap<String, Stamp>,
    refused: Vec<(String, String)>,
}

/// One directory, then its subdirectories, in name order.
fn walk<F: Filesystem + ?Sized>(
    filesystem: &F,
    directory: &Path,
    prefix: &str,
    skipped: &Skipped,
    found: &mut Found,
) -> Result<(), WorkingError> {
    let mut entries = filesystem
        .entries(directory)
        .map_err(|error| WorkingError::io(directory, error))?;
    // The trait promises no order, and this walk's order is the order a
    // refusal list is printed in.
    entries.sort();

    for Entry {
        path: on_disk,
        kind,
    } in entries
    {
        let Some(name) = on_disk
            .file_name()
            .and_then(|name| name.to_str())
            .map(str::to_owned)
        else {
            // A name that cannot be spelled cannot be walked into either, so a
            // directory refused here is one refusal rather than one per file
            // beneath it.
            let path = on_disk.to_string_lossy().into_owned();
            let because = WorkingError::NotUtf8 { path: path.clone() }.because();
            found.refused.push((path, because));
            continue;
        };
        // Decision 0033: the store spells a path in normal form C, and this
        // is where a name the filesystem handed back decomposed becomes the
        // path it was recorded as. `on_disk` keeps the spelling the folder
        // actually uses, because that is what has to be opened.
        let name = crate::format::nfc(&name).into_owned();
        let path = if prefix.is_empty() {
            name
        } else {
            format!("{prefix}/{name}")
        };

        // The store is not tracked, and says so without a rule.
        if prefix.is_empty() && path == STORE_DIR {
            continue;
        }

        if kind.is_directory() {
            if !skipped.skips_directory(&path) {
                walk(filesystem, &on_disk, &path, skipped, found)?;
            }
            continue;
        }
        if skipped.skips(&path) {
            continue;
        }
        if !kind.is_file() && !kind.is_symlink() {
            let because = WorkingError::NotAFile { path: path.clone() }.because();
            found.refused.push((path, because));
            continue;
        }
        if let Err(unusable) = check_path(&path) {
            let because = WorkingError::Unusable {
                path: path.clone(),
                because: unusable.to_string(),
            }
            .because();
            found.refused.push((path, because));
            continue;
        }
        // Decision 0040: read here, once, with the walk — because this is
        // where the entry is known to be a link, and asking later would mean
        // asking a folder that has moved on. A filesystem that reports a link
        // and cannot say where it points answers `None`, and the recorder
        // leaves whatever is recorded standing.
        if kind.is_symlink() {
            let target = match filesystem.link_target(&on_disk) {
                Ok(target) => target,
                Err(error) if error.kind() == io::ErrorKind::InvalidData => {
                    let because = WorkingError::LinkNotUtf8 { path: path.clone() }.because();
                    found.refused.push((path, because));
                    continue;
                }
                Err(error) => return Err(WorkingError::io(&on_disk, error)),
            };
            found.links.insert(path.clone(), target);
        } else if let Ok(Some(stamp)) = filesystem.stamp(&on_disk) {
            // Decision 0043: taken here, with the walk, because this is where
            // the entry is known to be a regular file and because a stamp
            // taken later would be a stamp of a folder that has moved on.
            // A filesystem with no such thing to report, and a file that
            // vanished between the listing and the question, are the same
            // answer: nothing is remembered about it and the next command that
            // wants its digest reads it.
            found.stamps.insert(path.clone(), stamp);
        }
        found.files.insert(path, on_disk);
    }
    Ok(())
}

/// Why a working copy could not be read.
#[derive(Debug)]
#[non_exhaustive]
pub enum WorkingError {
    /// A filename whose bytes are not UTF-8, which 0008 refuses.
    NotUtf8 {
        /// The name, rendered as best it can be.
        path: String,
    },
    /// A path the format cannot hold, for a reason it can state.
    Unusable {
        /// The path.
        path: String,
        /// What is wrong with it.
        because: String,
    },
    /// A device, a socket, or anything else that is neither a file nor a link.
    NotAFile {
        /// The path.
        path: String,
    },
    /// A link whose target is not UTF-8, which this store cannot write down.
    LinkNotUtf8 {
        /// The path.
        path: String,
    },
    /// A link asked for as though it held bytes.
    ///
    /// Decision 0040's standing rule, made structural: reading a link's path
    /// would open what it points at, so nothing here does.
    IsALink {
        /// The path.
        path: String,
    },
    /// A file recorded as lines whose bytes are no longer UTF-8.
    NotText {
        /// The path.
        path: String,
    },
    /// A path asked for that the folder does not hold.
    Missing {
        /// The path.
        path: String,
    },
    /// The filesystem refused.
    Io {
        /// What was being read.
        path: PathBuf,
        /// The underlying failure.
        error: io::Error,
    },
}

impl WorkingError {
    fn io(path: impl AsRef<Path>, error: io::Error) -> Self {
        Self::Io {
            path: path.as_ref().to_path_buf(),
            error,
        }
    }

    /// The reason alone, for a list of refusals rather than a single failure.
    ///
    /// [`fmt::Display`] says the reason and then what to do about it, which is
    /// right when one file stops a command and repetitive when twelve are
    /// listed together. The caller listing them says the fix once.
    pub fn because(&self) -> String {
        match self {
            WorkingError::NotUtf8 { .. } => "not a name this format can hold".to_owned(),
            WorkingError::Unusable { because, .. } => because.clone(),
            WorkingError::NotAFile { .. } => "not a regular file".to_owned(),
            WorkingError::LinkNotUtf8 { .. } => {
                "a link pointing at a name that is not UTF-8".to_owned()
            }
            WorkingError::IsALink { .. } => {
                "a link, which holds a target rather than bytes".to_owned()
            }
            WorkingError::NotText { .. } => {
                "recorded as lines and no longer UTF-8 text; drop it and add it again".to_owned()
            }
            WorkingError::Missing { .. } => "not in the working copy".to_owned(),
            WorkingError::Io { error, .. } => error.to_string(),
        }
    }
}

impl fmt::Display for WorkingError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            WorkingError::NotUtf8 { path } => write!(
                f,
                "{path} is not a name this format can hold: a path is UTF-8; \
                 rename it, or `skip` it in `{STORE_DIR}/{SKIPPED_FILE}`"
            ),
            WorkingError::Unusable { path, because } => write!(
                f,
                "`{path}` cannot be a path here: {because}; rename it, or `skip` \
                 it in `{STORE_DIR}/{SKIPPED_FILE}`"
            ),
            WorkingError::NotAFile { path } => write!(
                f,
                "`{path}` is neither a regular file nor a link, and this format \
                 spells nothing else; `skip` it in `{STORE_DIR}/{SKIPPED_FILE}`"
            ),
            WorkingError::LinkNotUtf8 { path } => write!(
                f,
                "`{path}` points at a name that is not UTF-8, and this store is \
                 UTF-8 text; point it somewhere spellable, or `skip` it in \
                 `{STORE_DIR}/{SKIPPED_FILE}`"
            ),
            WorkingError::IsALink { path } => write!(
                f,
                "`{path}` is a link, which holds a target rather than bytes; \
                 nothing reads through a link, so ask it where it points"
            ),
            WorkingError::NotText { path } => write!(
                f,
                "`{path}` was recorded as lines and is no longer UTF-8 text; \
                 a file's kind is fixed when it is added, so this is a `drop` \
                 and an `add` rather than an edit"
            ),
            WorkingError::Missing { path } => {
                write!(f, "`{path}` is not in the working copy")
            }
            WorkingError::Io { path, error } => write!(f, "{}: {error}", path.display()),
        }
    }
}

impl std::error::Error for WorkingError {}

#[cfg(test)]
mod tests {
    use super::*;

    fn skipped(text: &str) -> Skipped {
        Skipped::parse(text).expect("rules the reader accepts")
    }

    #[test]
    fn a_path_rule_names_one_file_and_a_slash_names_a_directory() {
        let rules = skipped("skip target/\nskip .DS_Store\n");
        assert!(rules.skips("target/debug/notes.md"));
        assert!(!rules.skips("targets.md"));
        assert!(!rules.skips("target"), "the directory itself is not a file");
        assert!(rules.skips(".DS_Store"));
        assert!(!rules.skips("docs/.DS_Store"), "an exact path is exact");
    }

    #[test]
    fn a_suffix_rule_matches_the_last_component() {
        let rules = skipped("skip-suffix .tmp\n");
        assert!(rules.skips("docs/draft.tmp"));
        assert!(!rules.skips("docs.tmp/draft.md"));
    }

    #[test]
    fn an_unknown_key_is_an_error_naming_the_line() {
        let refused = Skipped::parse("skip target/\nignore secrets\n").expect_err("refused");
        assert_eq!(refused.at, 2);
        assert!(refused.to_string().contains("`skip` and `skip-suffix`"));
    }

    #[test]
    fn a_line_that_is_not_a_rule_is_an_error() {
        assert!(Skipped::parse("skip\n").is_err());
        assert!(Skipped::parse("skip \n").is_err());
        assert!(Skipped::parse("skip  padded\n").is_err());
    }
}
