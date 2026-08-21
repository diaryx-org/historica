//! The folder beside the store, and what it does not take.
//!
//! Specified by `docs/decisions/0011-working-copy.md`. The working copy is the
//! directory holding `history/`, everything in it is tracked, and
//! `history/skipped.txt` names the exceptions. Nothing here is remembered between
//! commands: reading a working copy is a walk of the filesystem, every time.

use std::collections::BTreeMap;
use std::fmt;
use std::fs;
use std::io;
use std::path::{Path, PathBuf};

use crate::format::check_path;
use crate::store::STORE_DIR;

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
/// Decision 0022: these are the files an operating system leaves in a folder
/// without being asked, and a history that is append-only is the wrong place
/// for them. A default a person can see and delete is the smaller imposition.
pub const DEFAULT_SKIPPED: &str = "\
# What recording does not take. One rule a line: `skip <path>`, `skip <path>/`
# for everything under it, or `skip-suffix <ending>`. A `#` line says nothing.
#
# These are written by an operating system rather than by anyone, and this is a
# default rather than a decision — delete any line you disagree with.
skip-suffix .DS_Store
skip-suffix Thumbs.db
skip-suffix desktop.ini
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
                    Rule::Under(value.trim_end_matches('/').to_owned())
                }
                "skip" => Rule::Path(value.to_owned()),
                "skip-suffix" => Rule::Suffix(value.to_owned()),
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
    fn skips_directory(&self, path: &str) -> bool {
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
#[derive(Debug, Clone, Default)]
pub struct Working {
    files: BTreeMap<String, PathBuf>,
    refused: Vec<(String, String)>,
}

impl Working {
    /// Walk `root`, taking every file the rules leave.
    ///
    /// `history/` is never tracked and needs no rule. A name that is not UTF-8,
    /// a symlink, or anything that is not a regular file is refused by name
    /// rather than skipped quietly: decision 0011 puts the difference between
    /// losing work and not at one error message.
    ///
    /// Decision 0015: the refusals are collected rather than raised one at a
    /// time, so that `status` can list a folder's whole set and a person can
    /// write the `skip` rules in one pass. `record` raises the collection,
    /// which is the same refusal on the same files. What still returns here is
    /// [`WorkingError::Io`] — a directory that cannot be read is not a fact
    /// about the folder, it is not knowing, and a walk that collected it would
    /// describe a folder while quietly missing part of it.
    pub fn read(root: &Path, skipped: &Skipped) -> Result<Self, WorkingError> {
        let mut files = BTreeMap::new();
        let mut refused = Vec::new();
        walk(root, "", skipped, &mut files, &mut refused)?;
        Ok(Self { files, refused })
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
        let on_disk = self.files.get(path).ok_or_else(|| WorkingError::Missing {
            path: path.to_owned(),
        })?;
        match fs::read_to_string(on_disk) {
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
        let on_disk = self.files.get(path).ok_or_else(|| WorkingError::Missing {
            path: path.to_owned(),
        })?;
        fs::read(on_disk).map_err(|error| WorkingError::io(on_disk, error))
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

/// One directory, then its subdirectories, in name order.
fn walk(
    directory: &Path,
    prefix: &str,
    skipped: &Skipped,
    files: &mut BTreeMap<String, PathBuf>,
    refused: &mut Vec<(String, String)>,
) -> Result<(), WorkingError> {
    let mut entries: Vec<_> = fs::read_dir(directory)
        .map_err(|error| WorkingError::io(directory, error))?
        .collect::<Result<_, _>>()
        .map_err(|error| WorkingError::io(directory, error))?;
    entries.sort_by_key(std::fs::DirEntry::file_name);

    for entry in entries {
        let on_disk = entry.path();
        let Some(name) = entry.file_name().to_str().map(str::to_owned) else {
            // A name that cannot be spelled cannot be walked into either, so a
            // directory refused here is one refusal rather than one per file
            // beneath it.
            let path = on_disk.to_string_lossy().into_owned();
            let because = WorkingError::NotUtf8 { path: path.clone() }.because();
            refused.push((path, because));
            continue;
        };
        let path = if prefix.is_empty() {
            name
        } else {
            format!("{prefix}/{name}")
        };

        // The store is not tracked, and says so without a rule.
        if prefix.is_empty() && path == STORE_DIR {
            continue;
        }

        let kind = entry
            .file_type()
            .map_err(|error| WorkingError::io(&on_disk, error))?;
        if kind.is_dir() {
            if !skipped.skips_directory(&path) {
                walk(&on_disk, &path, skipped, files, refused)?;
            }
            continue;
        }
        if skipped.skips(&path) {
            continue;
        }
        if !kind.is_file() {
            let because = WorkingError::NotAFile { path: path.clone() }.because();
            refused.push((path, because));
            continue;
        }
        if let Err(unusable) = check_path(&path) {
            let because = WorkingError::Unusable {
                path: path.clone(),
                because: unusable.to_string(),
            }
            .because();
            refused.push((path, because));
            continue;
        }
        files.insert(path, on_disk);
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
    /// A symlink, a device, or anything else that is not a regular file.
    NotAFile {
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
                "`{path}` is not a regular file, and nothing in this format \
                 spells a symlink; `skip` it in `{STORE_DIR}/{SKIPPED_FILE}`"
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
