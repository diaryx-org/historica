//! Who a person says they are, read from their own configuration.
//!
//! Decision 0010: an author is a claim (0005), so the writer's whole job here
//! is making sure the claim is the person's own. Nothing is guessed from an
//! account name or a hostname, because 0005 copies `author` into every later
//! revision of the change and every digest covers it — a guess made once is
//! repeated for as long as the work goes on, and correcting it rewrites
//! history rather than editing a field.

use std::fmt;
use std::io;
use std::path::{Path, PathBuf};

use crate::fs::{Filesystem, read_to_string};

/// The environment variable that beats the file.
pub const AUTHOR_VARIABLE: &str = "HISTORICA_AUTHOR";
/// The file, under the platform's configuration directory.
pub const IDENTITY_FILE: &str = "historica/identity";

/// A person's configuration: a default author, and any per-path ones.
///
/// Blocks exist so that a path and a name never share a line. This format has
/// no quoting anywhere, and a directory may hold a space.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Identities {
    default: Option<String>,
    under: Vec<(String, String)>,
}

impl Identities {
    /// Read the file's text.
    pub fn parse(text: &str) -> Result<Self, MalformedIdentity> {
        let mut identities = Self::default();
        let mut heading: Option<String> = None;
        let mut author: Option<String> = None;
        let mut started = 0usize;

        let refuse = |at: usize, because: &'static str| MalformedIdentity { at, because };

        let close = |heading: &mut Option<String>,
                     author: &mut Option<String>,
                     at: usize,
                     identities: &mut Self|
         -> Result<(), MalformedIdentity> {
            let Some(author) = author.take() else {
                if heading.is_some() {
                    return Err(refuse(at, "a block naming a directory states no author"));
                }
                return Ok(());
            };
            match heading.take() {
                None => {
                    if identities.default.is_some() {
                        return Err(refuse(at, "two blocks state a default author"));
                    }
                    identities.default = Some(author);
                }
                Some(directory) => {
                    if identities.under.iter().any(|(held, _)| held == &directory) {
                        return Err(refuse(at, "two blocks claim one directory"));
                    }
                    identities.under.push((directory, author));
                }
            }
            Ok(())
        };

        for (index, line) in text.lines().enumerate() {
            let at = index + 1;
            if line.is_empty() {
                close(&mut heading, &mut author, started.max(1), &mut identities)?;
                // The next block reports against its own first line.
                started = 0;
                continue;
            }
            let (key, value) = line
                .split_once(' ')
                .ok_or_else(|| refuse(at, "a line is a key, a space, and a value"))?;
            if value.is_empty() || value != value.trim() || value.chars().any(char::is_control) {
                return Err(refuse(
                    at,
                    "a value is not empty, carries no leading or trailing space, \
                     and holds no control character",
                ));
            }
            if started == 0 {
                started = at;
            }
            match key {
                "under" => {
                    if heading.is_some() {
                        return Err(refuse(at, "a block names one directory"));
                    }
                    if author.is_some() {
                        return Err(refuse(at, "`under` heads a block, so it comes first"));
                    }
                    heading = Some(value.trim_end_matches('/').to_owned());
                }
                "author" => {
                    if author.is_some() {
                        return Err(refuse(at, "a block states one author"));
                    }
                    author = Some(value.to_owned());
                }
                _ => return Err(refuse(at, "the keys are `author` and `under`")),
            }
        }
        close(&mut heading, &mut author, started.max(1), &mut identities)?;
        Ok(identities)
    }

    /// The author for work recorded in `directory`.
    ///
    /// The longest matching prefix wins, compared by path component, so
    /// `~/work` matches `~/work/journal` and never `~/workshop`.
    pub fn author_for(&self, directory: &Path) -> Option<&str> {
        self.author_under(directory, home().as_deref())
    }

    /// The same, with `~` spelled out, which is what makes it testable.
    fn author_under(&self, directory: &Path, home: Option<&Path>) -> Option<&str> {
        let mut best: Option<(usize, &str)> = None;
        for (prefix, author) in &self.under {
            let Some(expanded) = expand(prefix, home) else {
                continue;
            };
            if beneath(directory, &expanded) {
                let depth = expanded.components().count();
                if best.is_none_or(|(held, _)| depth > held) {
                    best = Some((depth, author.as_str()));
                }
            }
        }
        best.map(|(_, author)| author).or(self.default.as_deref())
    }
}

/// Whether `directory` is `prefix` or sits beneath it.
fn beneath(directory: &Path, prefix: &Path) -> bool {
    directory == prefix || directory.starts_with(prefix)
}

/// `~/work` as the person meant it.
fn expand(prefix: &str, home: Option<&Path>) -> Option<PathBuf> {
    match prefix.strip_prefix("~/") {
        Some(rest) => home.map(|home| home.join(rest)),
        None if prefix == "~" => home.map(Path::to_path_buf),
        None => Some(PathBuf::from(prefix)),
    }
}

fn home() -> Option<PathBuf> {
    std::env::var_os("HOME")
        .or_else(|| std::env::var_os("USERPROFILE"))
        .map(PathBuf::from)
}

/// Where a person's identity file lives on this platform.
///
/// Reached through `std::env` alone, which is what keeps this from costing a
/// dependency — and what keeps it out of [`crate::fs::Filesystem`]. Decision
/// 0025 puts the folder behind a trait and leaves the environment where it is:
/// "which directory does this operating system keep configuration in" is a
/// question about the process, not about the store, and a host that answers it
/// differently reads its own file and hands the author over.
pub fn identity_path() -> Option<PathBuf> {
    if let Some(xdg) = std::env::var_os("XDG_CONFIG_HOME").filter(|value| !value.is_empty()) {
        return Some(PathBuf::from(xdg).join(IDENTITY_FILE));
    }
    if cfg!(windows)
        && let Some(appdata) = std::env::var_os("APPDATA").filter(|value| !value.is_empty())
    {
        return Some(PathBuf::from(appdata).join(IDENTITY_FILE));
    }
    home().map(|home| home.join(".config").join(IDENTITY_FILE))
}

/// The author to record work in `directory` under, read from disk.
#[cfg(feature = "disk")]
pub fn author_for(directory: &Path) -> Result<String, IdentityError> {
    author_for_on(&crate::fs::Disk, directory)
}

/// The author to record work in `directory` under, read from `files`.
///
/// The environment first, for scripts, tests, and machines where a file is
/// inconvenient; then the identity file; then a refusal that names the file
/// and the line to put in it.
///
/// The environment is read whichever filesystem is passed, because
/// [`identity_path`] is a question about the machine rather than about the
/// folder — see its own note. A host that keeps identity somewhere else does
/// not call this: it parses [`Identities`] itself and hands the answer to the
/// writer, which is what `Identities` is separate for.
pub fn author_for_on(files: &dyn Filesystem, directory: &Path) -> Result<String, IdentityError> {
    if let Some(author) = std::env::var(AUTHOR_VARIABLE)
        .ok()
        .filter(|a| !a.is_empty())
    {
        return check(author, None);
    }

    let path = identity_path().ok_or(IdentityError::Nowhere)?;
    let text = match read_to_string(files, &path) {
        Ok(text) => text,
        Err(error) if error.kind() == io::ErrorKind::NotFound => {
            return Err(IdentityError::NoIdentity { file: path });
        }
        Err(error) => return Err(IdentityError::Io { file: path, error }),
    };
    let identities = Identities::parse(&text).map_err(|error| IdentityError::Malformed {
        file: path.clone(),
        error,
    })?;
    let author = identities
        .author_for(directory)
        .ok_or_else(|| IdentityError::NoAuthorHere { file: path.clone() })?;
    check(author.to_owned(), Some(path))
}

/// An author must be something a revision document can hold.
fn check(author: String, file: Option<PathBuf>) -> Result<String, IdentityError> {
    if author.is_empty() || author != author.trim() || author.chars().any(char::is_control) {
        return Err(IdentityError::Unusable { author, file });
    }
    Ok(author)
}

/// Why the writer does not know who is recording.
#[derive(Debug)]
#[non_exhaustive]
pub enum IdentityError {
    /// No identity file exists yet.
    NoIdentity {
        /// Where one was looked for.
        file: PathBuf,
    },
    /// The file exists and says nothing about this directory.
    NoAuthorHere {
        /// The file.
        file: PathBuf,
    },
    /// The file is not blocks of keys and values.
    Malformed {
        /// The file.
        file: PathBuf,
        /// Which line, and what was wanted.
        error: MalformedIdentity,
    },
    /// An author line a revision document could not hold.
    Unusable {
        /// The author as given.
        author: String,
        /// Where it came from, if it came from a file.
        file: Option<PathBuf>,
    },
    /// This platform has no configuration directory to look in.
    Nowhere,
    /// The filesystem refused.
    Io {
        /// The file.
        file: PathBuf,
        /// The underlying failure.
        error: io::Error,
    },
}

impl fmt::Display for IdentityError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            IdentityError::NoIdentity { file } => write!(
                f,
                "nobody has said who you are, and nothing is guessed: write \
                 `author Your Name <you@example.com>` in {}, or run \
                 `historica identity \"Your Name <you@example.com>\"`",
                file.display()
            ),
            IdentityError::NoAuthorHere { file } => write!(
                f,
                "{} states no author for this directory and no default one",
                file.display()
            ),
            IdentityError::Malformed { file, error } => {
                write!(f, "{}: {error}", file.display())
            }
            IdentityError::Unusable { author, file } => match file {
                Some(file) => write!(
                    f,
                    "`{author}` in {} cannot be an author: a header value is not \
                     empty, carries no leading or trailing space, and holds no \
                     control character",
                    file.display()
                ),
                None => write!(
                    f,
                    "`{author}` in ${AUTHOR_VARIABLE} cannot be an author: a \
                     header value is not empty, carries no leading or trailing \
                     space, and holds no control character"
                ),
            },
            IdentityError::Nowhere => write!(
                f,
                "this platform has no configuration directory; set \
                 ${AUTHOR_VARIABLE} instead"
            ),
            IdentityError::Io { file, error } => write!(f, "{}: {error}", file.display()),
        }
    }
}

impl std::error::Error for IdentityError {}

/// A line of the identity file that was not what was wanted there.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub struct MalformedIdentity {
    /// The line, counted from one.
    pub at: usize,
    /// What was wanted.
    pub because: &'static str,
}

impl fmt::Display for MalformedIdentity {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "line {}: {}", self.at, self.because)
    }
}

impl std::error::Error for MalformedIdentity {}

#[cfg(test)]
mod tests {
    use super::*;

    const FILE: &str = "\
author Adam Harris <adam@example.com>

under ~/work/
author Adam Harris <adam@company.example>

under ~/work/secret
author A <a@b.example>
";

    /// The home directory a test states, rather than the one it runs under.
    const HOME: &str = "/home/adam";

    #[test]
    fn the_longest_matching_prefix_wins() {
        let identities = Identities::parse(FILE).expect("a file the reader accepts");
        let author_for =
            |path: &str| identities.author_under(Path::new(path), Some(Path::new(HOME)));

        assert_eq!(
            author_for("/home/adam/journal"),
            Some("Adam Harris <adam@example.com>")
        );
        assert_eq!(
            author_for("/home/adam/work/thing"),
            Some("Adam Harris <adam@company.example>")
        );
        assert_eq!(
            author_for("/home/adam/work/secret/thing"),
            Some("A <a@b.example>")
        );
        assert_eq!(
            author_for("/home/adam/workshop"),
            Some("Adam Harris <adam@example.com>"),
            "a prefix is compared by component, never by characters"
        );
    }

    #[test]
    fn a_file_with_no_default_answers_only_where_it_speaks() {
        let identities =
            Identities::parse("under ~/work/\nauthor A <a@b.example>\n").expect("a file");
        let home = Some(Path::new(HOME));
        assert!(
            identities
                .author_under(Path::new("/home/adam/journal"), home)
                .is_none()
        );
        assert!(
            identities
                .author_under(Path::new("/home/adam/work"), home)
                .is_some()
        );
    }

    #[test]
    fn the_file_is_refused_line_by_line() {
        for (text, at) in [
            ("autor A <a@b>\n", 1),
            ("author A <a@b>\nauthor B <b@c>\n", 2),
            ("author A <a@b>\n\nunder ~/x\nunder ~/y\n", 4),
            ("author A <a@b>\n\nunder ~/x\n", 3),
            ("author  padded <a@b>\n", 1),
        ] {
            let refused = Identities::parse(text).expect_err("refused");
            assert_eq!(refused.at, at, "{text:?}");
        }
    }
}
