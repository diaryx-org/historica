//! The trust policy: whose word this copy accepts.
//!
//! ```text
//! trust-0
//! key RWTd8LRCGA9i53mlYecO4IzT51TGPpvWucNSCh1CBM0QTaLn73Y7GFO3
//! who Adam Harris <adam@example.com>
//! ```
//!
//! One key to a file under `history/trust/`, on Historica's decision 0045's
//! container: the filename is a label for whoever opens the folder, and the
//! content is the fact. Entries are written with `create_new`, so two additions
//! on one machine cannot lose one; removing an entry is deleting its file.
//!
//! **Nothing here ever travels.** Decision 0046 argues that at length and this
//! module does not revisit it, but the shape of the argument is worth having
//! beside the code: a trust entry arriving from another store is authority
//! flowing from the party the policy exists to judge. A skip rule that arrives
//! means *record less*, which fails closed; a trust entry that arrives means
//! *believe more*. And union without tombstones structurally cannot make
//! removal win, which is the one thing revoking a key requires. So no operation
//! of this tool, and no operation of Historica, writes this directory from
//! another store.
//!
//! `who` is free text and this tool never matches on it. It is a label for a
//! person, not an identity — pretending otherwise would invite somebody to
//! trust the string instead of the key.
//!
//! # A key's history
//!
//! A person holds a key for each device, and a key on a lost laptop has to stop
//! counting without unseating what it signed while it was theirs. So an entry
//! may also say when its key was added and when it was revoked, under its own
//! preamble:
//!
//! ```text
//! trust-1
//! key RWTd8LRCGA9i53mlYecO4IzT51TGPpvWucNSCh1CBM0QTaLn73Y7GFO3
//! who Adam Harris <adam@example.com>
//! added 2026-03-02T10:00:00-07:00
//! revoked 2026-10-19T08:30:00-06:00
//! ```
//!
//! A claim by a revoked key counts when it says it was made before `revoked`,
//! and not otherwise ([`Entry::counts_at`]). `added` is recorded and bounds
//! nothing; [`Entry::added`] says why. Both are optional, and a `trust-1`
//! states at least one.
//!
//! A new preamble rather than two more headers under `trust-0`, as decision
//! 0001 grows the claim grammar: a narrowing is a new preamble. A reader built
//! before `trust-1` refuses the entry and believes the key not at all. That is
//! the safe direction: it can under-count a revoked key, and never count what
//! the key signed after it was revoked. An entry with neither line is written
//! `trust-0`, so one entry has one spelling.
//!
//! Several entries may name one person, one per key, and nothing groups them
//! but the reader's own choice of which entries to hand
//! [`crate::following::Vouched`]: `who` stays a label.

use std::collections::BTreeMap;
use std::fmt;
use std::io;
use std::path::{Path, PathBuf};

use historica::format::Timestamp;
use historica::fs::{Filesystem, Guarded, Kind, read_to_string};

use crate::claim::Key;
use crate::layout::{TRUST_SUFFIX, trust as trust_dir};

/// The preamble a trust entry with no history begins with.
pub const PREAMBLE: &str = "trust-0";

/// The preamble a trust entry that says when its key was added or revoked
/// begins with.
pub const HISTORY_PREAMBLE: &str = "trust-1";

/// What the tool writes when it first makes the directory: the grammar,
/// explained where the files are, stating no rule at all.
///
/// Historica's decision 0027 has a default explain itself and state nothing,
/// and 0045 inherits it. So does this: a file of nothing but comments is a
/// comment-only file in every reader, with no special case anywhere.
pub const EXPLANATION: &str = "\
# This directory is whose word this copy of the store accepts. One key to a
# file; the filename is a label for you, and nothing reads it. A file looks
# like this, with no `#` in front:
#
# trust-0
# key RWTd8LRCGA9i53mlYecO4IzT51TGPpvWucNSCh1CBM0QTaLn73Y7GFO3
# who Adam Harris <adam@example.com>
#
# Nothing ever writes this directory from another store: receiving a store
# receives its history and its claims, never its opinion of who to believe.
# Adding a key is `historica-minisign trust add`, or writing a file like the
# above. Removing one is deleting its file.
#
# A key can also carry its history. A file beginning `trust-1` may say when
# the key was added, and when it was revoked:
#
# trust-1
# key RWTd8LRCGA9i53mlYecO4IzT51TGPpvWucNSCh1CBM0QTaLn73Y7GFO3
# who Adam Harris <adam@example.com>
# added 2026-03-02T10:00:00-07:00
# revoked 2026-10-19T08:30:00-06:00
#
# A claim the key made before `revoked` still counts, and one made at or after
# it does not. `historica-minisign trust revoke` writes the line.
";

/// The name the explanation is written under.
const EXPLANATION_FILE: &str = "how-this-works.txt";

/// One key, the person this copy takes it to speak for, and the key's history.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Entry {
    /// The key.
    pub key: Key,
    /// Who it speaks for, as free text.
    pub who: String,
    /// When the key was added, if somebody said.
    ///
    /// A record for the person reading the folder, and never a bound. A
    /// claim's `when` is written by whoever holds the key, so a lower bound
    /// stops nobody who holds it from writing an earlier time. And it would
    /// refuse an honest claim made before somebody got round to adding the
    /// key here.
    pub added: Option<Timestamp>,
    /// When the key stopped speaking for anyone, if it has.
    ///
    /// A claim made at or after this moment does not count, and one made
    /// before it still does. [`Entry::counts_at`] says what that can and
    /// cannot stop.
    pub revoked: Option<Timestamp>,
}

impl Entry {
    /// An entry with no history: its key counts at every moment.
    pub fn new(key: Key, who: impl Into<String>) -> Self {
        Self {
            key,
            who: who.into(),
            added: None,
            revoked: None,
        }
    }

    /// Whether a claim this key says it made at `when` counts.
    ///
    /// True unless the key was revoked at or before `when`. Moments are
    /// compared as instants, so one moment in two offsets is one moment.
    ///
    /// What this stops is everything the key signs after its revocation that
    /// states its true time: an old laptop still syncing, a script nobody
    /// turned off, a thief who does not think to lie. What it cannot stop is a
    /// thief who writes an earlier `when`, because the key signs whatever time
    /// it is given. That is why the date is one the person names. Revoking a
    /// key as of when it may first have leaked, rather than when the leak was
    /// noticed, gives up the claims in between and keeps the rest.
    pub fn counts_at(&self, when: &Timestamp) -> bool {
        self.revoked
            .as_ref()
            .is_none_or(|revoked| instant(when) < instant(revoked))
    }

    /// The entry, as the bytes of its file.
    ///
    /// `trust-0` when it states no history and `trust-1` when it does, so one
    /// entry has one spelling.
    pub fn render(&self) -> String {
        if self.added.is_none() && self.revoked.is_none() {
            return format!("{PREAMBLE}\nkey {}\nwho {}\n", self.key, self.who);
        }
        let mut text = format!("{HISTORY_PREAMBLE}\nkey {}\nwho {}\n", self.key, self.who);
        if let Some(added) = &self.added {
            text.push_str(&format!("added {added}\n"));
        }
        if let Some(revoked) = &self.revoked {
            text.push_str(&format!("revoked {revoked}\n"));
        }
        text
    }

    /// Read one entry, or say that this file states nothing.
    ///
    /// `Ok(None)` is a file of comments and blank lines — the explanation this
    /// tool writes, or one somebody commented out — which is a file stating
    /// nothing rather than a file that is wrong.
    pub fn parse(text: &str) -> Result<Option<Self>, EntryError> {
        let mut lines = text
            .lines()
            .enumerate()
            .filter(|(_, line)| !line.trim_start().starts_with('#') && !line.trim().is_empty());

        let Some((index, preamble)) = lines.next() else {
            return Ok(None);
        };
        let history = match preamble {
            PREAMBLE => false,
            HISTORY_PREAMBLE => true,
            found => {
                return Err(EntryError::Preamble {
                    at: index + 1,
                    found: found.to_owned(),
                });
            }
        };

        let mut key = None;
        let mut who = None;
        let mut added = None;
        let mut revoked = None;
        let moment = |at: usize, header: &'static str, value: &str| {
            value
                .parse::<Timestamp>()
                .map_err(|error| EntryError::Malformed {
                    at,
                    header,
                    because: error.to_string(),
                })
        };
        for (index, line) in lines {
            let at = index + 1;
            let (header, value) = line.split_once(' ').unwrap_or((line, ""));
            let slot = match header {
                "key" => {
                    let parsed = value
                        .parse::<Key>()
                        .map_err(|error| EntryError::Malformed {
                            at,
                            header: "key",
                            because: error.to_string(),
                        })?;
                    key.replace(parsed).map(|_| "key")
                }
                "who" => {
                    if value.is_empty() {
                        return Err(EntryError::Malformed {
                            at,
                            header: "who",
                            because: "it says nobody".to_owned(),
                        });
                    }
                    who.replace(value.to_owned()).map(|_| "who")
                }
                // Only under `trust-1`. The preamble picks the grammar, so a
                // `trust-0` that states either is refused here as it is by a
                // reader built before `trust-1`.
                "added" if history => added.replace(moment(at, "added", value)?).map(|_| "added"),
                "revoked" if history => revoked
                    .replace(moment(at, "revoked", value)?)
                    .map(|_| "revoked"),
                other => {
                    return Err(EntryError::Unknown {
                        at,
                        found: other.to_owned(),
                    });
                }
            };
            if let Some(header) = slot {
                return Err(EntryError::Repeated { at, header });
            }
        }

        let (key, who) = match (key, who) {
            (Some(key), Some(who)) => (key, who),
            (None, _) => return Err(EntryError::Missing { header: "key" }),
            (_, None) => return Err(EntryError::Missing { header: "who" }),
        };
        if history && added.is_none() && revoked.is_none() {
            return Err(EntryError::NoHistory);
        }
        if let (Some(added), Some(revoked)) = (&added, &revoked)
            && instant(revoked) < instant(added)
        {
            return Err(EntryError::RevokedBeforeAdded);
        }
        Ok(Some(Self {
            key,
            who,
            added,
            revoked,
        }))
    }
}

/// Seconds since 1970 in UTC: the instant a timestamp names.
///
/// Historica's [`Timestamp`] keeps its text and compares as text, on purpose:
/// no Historica timestamp takes part in ordering. Revocation is the one place
/// here that orders two moments, and one moment spelled in two offsets must be
/// one moment, so the comparison is of instants. The text was validated when
/// it was parsed, so every field is digits, in range.
pub(crate) fn instant(timestamp: &Timestamp) -> i64 {
    let text = timestamp.as_str();
    let number = |from: usize, to: usize| -> i64 { text[from..to].parse().unwrap_or(0) };
    let (year, month, day) = (number(0, 4), number(5, 7), number(8, 10));
    let seconds = number(11, 13) * 3600 + number(14, 16) * 60 + number(17, 19);
    let offset = number(20, 22) * 3600 + number(23, 25) * 60;
    let offset = if &text[19..20] == "-" {
        -offset
    } else {
        offset
    };

    // Days from 1970-01-01 to the civil date: Howard Hinnant's
    // `days_from_civil`, with March as the first month so that a leap day is
    // the last day of its year.
    let year = if month <= 2 { year - 1 } else { year };
    let era = year.div_euclid(400);
    let of_era = year - era * 400;
    let of_year = (153 * ((month + 9) % 12) + 2) / 5 + day - 1;
    let of_cycle = of_era * 365 + of_era / 4 - of_era / 100 + of_year;
    let days = era * 146_097 + of_cycle - 719_468;

    days * 86_400 + seconds - offset
}

/// Every key this copy accepts, and every file in the directory that is not one.
#[derive(Debug, Clone, Default)]
pub struct Trust {
    entries: BTreeMap<String, Entry>,
    malformed: Vec<(PathBuf, EntryError)>,
}

impl Trust {
    /// Read the policy, keeping what is wrong with it rather than stopping at
    /// the first fault.
    ///
    /// A directory that is not there is a policy that holds nothing, which is
    /// what an unconfigured copy has and is not an error: a tool that failed
    /// every store it had not yet met would teach people not to run it.
    pub fn read<F: Filesystem + ?Sized>(files: &F, root: &Path) -> io::Result<Self> {
        let directory = trust_dir(root);
        let mut policy = Self::default();
        let entries = match files.entries(&directory) {
            Ok(entries) => entries,
            Err(error) if error.kind() == io::ErrorKind::NotFound => return Ok(policy),
            Err(error) => return Err(error),
        };

        for entry in entries {
            if !matches!(files.look(&entry.path)?, Some(Kind::File)) {
                continue;
            }
            let Some(label) = label_of(&entry.path) else {
                continue;
            };
            let text = read_to_string(files, &entry.path)?;
            match Entry::parse(&text) {
                Ok(Some(held)) => {
                    policy.entries.insert(label, held);
                }
                Ok(None) => {}
                Err(error) => policy.malformed.push((entry.path, error)),
            }
        }
        Ok(policy)
    }

    /// The person this policy takes a key to speak for at `when`: who it
    /// holds the key for, unless the key was revoked by then.
    ///
    /// Where two entries hold one key, a revocation in either wins. Decision
    /// 0046 keeps trust at home because removal has to win, and so it does
    /// here.
    pub fn speaks_for(&self, key: &Key, when: &Timestamp) -> Option<&str> {
        let mut holding = self.entries.values().filter(|entry| &entry.key == key);
        let first = holding.clone().next()?;
        holding
            .all(|entry| entry.counts_at(when))
            .then_some(first.who.as_str())
    }

    /// The person this policy takes a key to speak for, if it holds it,
    /// revoked or not.
    pub fn who(&self, key: &Key) -> Option<&str> {
        self.entries
            .values()
            .find(|entry| &entry.key == key)
            .map(|entry| entry.who.as_str())
    }

    /// Whether this policy holds a key.
    pub fn holds(&self, key: &Key) -> bool {
        self.who(key).is_some()
    }

    /// Every entry, by the label its file is named with.
    pub fn entries(&self) -> impl Iterator<Item = (&str, &Entry)> {
        self.entries
            .iter()
            .map(|(label, entry)| (label.as_str(), entry))
    }

    /// Whether this copy has stated any policy at all.
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// Files in the directory that are not entries, and why.
    pub fn malformed(&self) -> impl Iterator<Item = (&Path, &EntryError)> {
        self.malformed
            .iter()
            .map(|(path, error)| (path.as_path(), error))
    }
}

/// The longest a label this tool chooses for itself may be.
///
/// Historica's decision 0006 cuts a summary at sixty characters so that a name
/// has room for a date and an extension inside the 255 bytes every filesystem
/// in use allows, even where it is entirely non-ASCII. A label carries neither,
/// so sixty is already more than a person's name needs.
const LABEL_CHARS: usize = 60;

/// The label a key gets when nobody chose one: who it speaks for.
///
/// Decisions 0001 and 0046 both say the filename here is a label for whoever
/// opens the folder and that nothing reads it — so it should be the one thing
/// the person opening the folder wants to know, which is whose key it is. A
/// digest satisfied the letter of "nothing reads it" and none of the point.
///
/// `who` is free text, so what comes back is scrubbed rather than trusted: the
/// part before any `<`, with path separators and control characters turned to
/// spaces, runs of spaces collapsed, and leading dots removed. Where nothing
/// usable survives — a `who` of punctuation, or one that lands on the name the
/// explanation file already has — the answer is the digest of the key's text,
/// which is a filename whatever the key and the person are called.
///
/// Nothing about this has to agree with any other copy. `trust/` never crosses
/// a store boundary, which is 0046 at length, so unlike [`crate::naming`] there
/// is no replica to compute the same name and no `arrange` to reconcile one.
///
/// A label the tool chose is still only a label: renaming the file changes
/// nothing, and two keys for one person are told apart by whatever the caller
/// appends.
pub fn default_label(key: &Key, who: &str) -> String {
    let named = who.split('<').next().unwrap_or(who).trim();
    let candidate = if named.is_empty() {
        who.trim_matches(['<', '>']).trim()
    } else {
        named
    };

    let mut label = String::new();
    let mut pending = false;
    for character in candidate.chars().take(LABEL_CHARS) {
        let character = match character {
            character if character.is_control() => ' ',
            '/' | '\\' | ':' => ' ',
            character => character,
        };
        if character == ' ' {
            // A run of spaces is one space, and a leading one is none: a name
            // is being made, not transcribed.
            pending = !label.is_empty();
            continue;
        }
        if pending {
            label.push(' ');
            pending = false;
        }
        label.push(character);
    }
    // A leading dot hides the file on every Unix, and a trailing dot or space
    // is a name Windows will not keep as written. Both are trimmed together
    // rather than in turn, or a `who` of `../../etc/passwd` scrubs to a space
    // in front of the dots and keeps them.
    let label = label.trim_matches(|character| character == '.' || character == ' ');

    let explanation = EXPLANATION_FILE
        .strip_suffix(TRUST_SUFFIX)
        .unwrap_or(EXPLANATION_FILE);
    if label.is_empty() || !is_a_label(label) || label == explanation {
        return historica::format::digest(key.as_str().as_bytes()).abbreviate(12);
    }
    label.to_owned()
}

/// Whether a label is one filename.
///
/// The rule is deliberately about what a filesystem will take rather than about
/// what looks tidy: `..` and a path separator are the two spellings that would
/// have this tool write outside the directory it means to.
pub fn is_a_label(label: &str) -> bool {
    !label.is_empty()
        && label != "."
        && label != ".."
        && !label.contains(['/', '\\'])
        && !label.contains('\0')
}

/// Add one key to the policy, under `label`.
///
/// Written with `create_new`: a label already taken is refused rather than
/// overwritten, which is what stops two additions on one machine from losing
/// one. The directory and its explanation are made if they are not there.
///
/// Returns where the entry was written.
pub fn add<F: Filesystem + ?Sized>(
    files: &F,
    root: &Path,
    label: &str,
    entry: &Entry,
) -> Result<PathBuf, TrustError> {
    let directory = trust_dir(root);
    files
        .create_directory(&directory)
        .map_err(|error| TrustError::io(&directory, error))?;

    let explanation = directory.join(EXPLANATION_FILE);
    match files.create_new(&explanation, EXPLANATION.as_bytes()) {
        Ok(()) => {}
        // Already there, which is the ordinary case after the first add.
        Err(error) if error.kind() == io::ErrorKind::AlreadyExists => {}
        Err(error) => return Err(TrustError::io(&explanation, error)),
    }

    if !is_a_label(label) {
        return Err(TrustError::NotALabel {
            label: label.to_owned(),
        });
    }

    let path = directory.join(format!("{label}{TRUST_SUFFIX}"));
    match files.create_new(&path, entry.render().as_bytes()) {
        Ok(()) => Ok(path),
        Err(error) if error.kind() == io::ErrorKind::AlreadyExists => Err(TrustError::Taken {
            label: label.to_owned(),
            path,
        }),
        Err(error) => Err(TrustError::io(&path, error)),
    }
}

/// Revoke one key, by the label its file is named with, as of `when`.
///
/// The entry is rewritten as `trust-1` with a `revoked` line, and nothing else
/// in it changes. A key already revoked keeps the earlier of the two moments.
/// Revocation only moves earlier, because a later date would bring back claims
/// somebody already decided not to count.
///
/// This is the one place this tool rewrites a trust file rather than adding
/// one. It writes only if the file still holds what was read, so an edit made
/// in between is not lost. Returns where the entry is, and the entry as it now
/// stands.
pub fn revoke<F: Filesystem + ?Sized>(
    files: &F,
    root: &Path,
    label: &str,
    when: &Timestamp,
) -> Result<(PathBuf, Entry), TrustError> {
    if !is_a_label(label) {
        return Err(TrustError::NotALabel {
            label: label.to_owned(),
        });
    }
    let path = trust_dir(root).join(format!("{label}{TRUST_SUFFIX}"));
    let bytes = match files.read(&path) {
        Ok(bytes) => bytes,
        Err(error) if error.kind() == io::ErrorKind::NotFound => {
            return Err(TrustError::NoSuchLabel {
                label: label.to_owned(),
            });
        }
        Err(error) => return Err(TrustError::io(&path, error)),
    };
    let not_an_entry = |because| TrustError::NotAnEntry {
        path: path.clone(),
        because,
    };
    let text = String::from_utf8(bytes.clone()).map_err(|_| not_an_entry(None))?;
    let mut entry = match Entry::parse(&text) {
        Ok(Some(entry)) => entry,
        Ok(None) => return Err(not_an_entry(None)),
        Err(because) => return Err(not_an_entry(Some(because))),
    };

    if entry.counts_at(when) {
        entry.revoked = Some(when.clone());
    }
    if let Some(added) = &entry.added
        && instant(when) < instant(added)
    {
        return Err(not_an_entry(Some(EntryError::RevokedBeforeAdded)));
    }

    match files.write_if(&path, Some(&bytes), entry.render().as_bytes()) {
        Ok(Guarded::Written) => Ok((path, entry)),
        Ok(Guarded::Drifted) => Err(TrustError::Drifted { path }),
        Err(error) => Err(TrustError::io(&path, error)),
    }
}

/// Remove one key from the policy, by the label its file is named with.
pub fn remove<F: Filesystem + ?Sized>(
    files: &F,
    root: &Path,
    label: &str,
) -> Result<PathBuf, TrustError> {
    let path = trust_dir(root).join(format!("{label}{TRUST_SUFFIX}"));
    match files.remove_file(&path) {
        Ok(()) => Ok(path),
        Err(error) if error.kind() == io::ErrorKind::NotFound => Err(TrustError::NoSuchLabel {
            label: label.to_owned(),
        }),
        Err(error) => Err(TrustError::io(&path, error)),
    }
}

/// The label a trust file's name states.
fn label_of(path: &Path) -> Option<String> {
    let name = path.file_name()?.to_str()?;
    Some(name.strip_suffix(TRUST_SUFFIX).unwrap_or(name).to_owned())
}

/// Why a trust entry could not be read.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum EntryError {
    /// The first line that says anything was not [`PREAMBLE`].
    Preamble {
        /// Which line.
        at: usize,
        /// What it said.
        found: String,
    },
    /// A header this grammar does not name.
    Unknown {
        /// Which line.
        at: usize,
        /// What it called itself.
        found: String,
    },
    /// A header stated twice.
    Repeated {
        /// Which line.
        at: usize,
        /// Which header.
        header: &'static str,
    },
    /// A header whose value is not what that header holds.
    Malformed {
        /// Which line.
        at: usize,
        /// Which header.
        header: &'static str,
        /// What is wrong with it.
        because: String,
    },
    /// A header this grammar requires is not there.
    Missing {
        /// Which one.
        header: &'static str,
    },
    /// A `trust-1` that states neither `added` nor `revoked`, which would be a
    /// second spelling of a `trust-0`.
    NoHistory,
    /// A key revoked before it was added.
    RevokedBeforeAdded,
}

impl fmt::Display for EntryError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Preamble { at, found } => write!(
                f,
                "line {at} says `{found}`; a trust entry begins `{PREAMBLE}`"
            ),
            Self::Unknown { at, found } => write!(
                f,
                "line {at} states `{found}`, which a trust entry does not name"
            ),
            Self::Repeated { at, header } => {
                write!(f, "line {at} states `{header}` a second time")
            }
            Self::Malformed {
                at,
                header,
                because,
            } => write!(f, "line {at}'s `{header}` is wrong: {because}"),
            Self::Missing { header } => write!(f, "it states no `{header}`"),
            Self::NoHistory => write!(
                f,
                "it begins `{HISTORY_PREAMBLE}` and states neither `added` nor \
                 `revoked`; an entry with no history begins `{PREAMBLE}`"
            ),
            Self::RevokedBeforeAdded => f.write_str("its key is revoked before it was added"),
        }
    }
}

impl std::error::Error for EntryError {}

/// Why the policy could not be written.
#[derive(Debug)]
#[non_exhaustive]
pub enum TrustError {
    /// A label another entry already holds.
    Taken {
        /// The label.
        label: String,
        /// The file already under it.
        path: PathBuf,
    },
    /// Something that is not one filename.
    NotALabel {
        /// What was offered.
        label: String,
    },
    /// A label no entry holds.
    NoSuchLabel {
        /// The label.
        label: String,
    },
    /// A file that is not an entry, or an entry the change would make
    /// malformed.
    NotAnEntry {
        /// The file.
        path: PathBuf,
        /// What is wrong, or `None` for a file that states nothing.
        because: Option<EntryError>,
    },
    /// The file changed between being read and being rewritten, and was left
    /// as it is.
    Drifted {
        /// The file.
        path: PathBuf,
    },
    /// The filesystem refused.
    Io {
        /// What was being read or written.
        path: PathBuf,
        /// What it said.
        error: io::Error,
    },
}

impl TrustError {
    fn io(path: &Path, error: io::Error) -> Self {
        Self::Io {
            path: path.to_path_buf(),
            error,
        }
    }
}

impl fmt::Display for TrustError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Taken { label, path } => write!(
                f,
                "`{label}` is already a label here, at {}; a key is added \
                 rather than replaced, so that two additions cannot lose one",
                path.display()
            ),
            Self::NotALabel { label } => write!(
                f,
                "`{label}` is not one filename, and a label is: it holds no \
                 `/`, and is not empty, `.`, or `..`"
            ),
            Self::NoSuchLabel { label } => {
                write!(f, "no key here is labelled `{label}`")
            }
            Self::NotAnEntry { path, because } => match because {
                Some(because) => write!(f, "{} is not an entry: {because}", path.display()),
                None => write!(f, "{} states no key", path.display()),
            },
            Self::Drifted { path } => write!(
                f,
                "{} changed while it was being rewritten, and was left as it \
                 is; run the command again",
                path.display()
            ),
            Self::Io { path, error } => write!(f, "{}: {error}", path.display()),
        }
    }
}

impl std::error::Error for TrustError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Io { error, .. } => Some(error),
            _ => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const KEY: &str = "RWTd8LRCGA9i53mlYecO4IzT51TGPpvWucNSCh1CBM0QTaLn73Y7GFO3";

    fn entry() -> Entry {
        Entry::new(
            KEY.parse().expect("the example key parses"),
            "Adam Harris <adam@example.com>",
        )
    }

    fn at(text: &str) -> Timestamp {
        text.parse().expect("a timestamp")
    }

    fn revoked(when: &str) -> Entry {
        Entry {
            added: Some(at("2026-03-02T10:00:00-07:00")),
            revoked: Some(at(when)),
            ..entry()
        }
    }

    #[test]
    fn an_entry_with_a_history_renders_as_trust_1_and_reads_back() {
        let entry = revoked("2026-10-19T08:30:00-06:00");
        let text = entry.render();
        assert!(text.starts_with("trust-1\n"));
        assert_eq!(Entry::parse(&text), Ok(Some(entry)));
    }

    #[test]
    fn an_entry_with_no_history_is_still_trust_0() {
        assert!(entry().render().starts_with("trust-0\n"));
    }

    /// The preamble picks the grammar: `revoked` under `trust-0` is a header
    /// that grammar does not name, as it is to a reader built before
    /// `trust-1`.
    #[test]
    fn a_revocation_under_trust_0_is_refused() {
        let text = format!("{}revoked 2026-10-19T08:30:00-06:00\n", entry().render());
        assert!(matches!(
            Entry::parse(&text),
            Err(EntryError::Unknown { .. })
        ));
    }

    #[test]
    fn a_trust_1_with_no_history_is_refused() {
        let text = format!("{HISTORY_PREAMBLE}\nkey {KEY}\nwho Adam\n");
        assert_eq!(Entry::parse(&text), Err(EntryError::NoHistory));
    }

    #[test]
    fn a_key_revoked_before_it_was_added_is_refused() {
        let text = revoked("2026-01-01T00:00:00+00:00").render();
        assert_eq!(Entry::parse(&text), Err(EntryError::RevokedBeforeAdded));
    }

    #[test]
    fn a_second_revocation_is_refused_rather_than_taken() {
        let text = format!(
            "{}revoked 2026-10-20T00:00:00+00:00\n",
            revoked("2026-10-19T08:30:00-06:00").render()
        );
        assert!(matches!(
            Entry::parse(&text),
            Err(EntryError::Repeated {
                header: "revoked",
                ..
            })
        ));
    }

    #[test]
    fn a_claim_counts_before_revocation_and_not_at_or_after_it() {
        let entry = revoked("2026-10-19T08:30:00-06:00");
        assert!(entry.counts_at(&at("2026-10-19T08:29:59-06:00")));
        assert!(!entry.counts_at(&at("2026-10-19T08:30:00-06:00")));
        assert!(!entry.counts_at(&at("2026-10-20T00:00:00-06:00")));
        // `added` bounds nothing.
        assert!(entry.counts_at(&at("2020-01-01T00:00:00+00:00")));
    }

    /// One moment in two offsets is one moment: 14:30 UTC is 08:30 at -06:00.
    #[test]
    fn revocation_compares_instants_and_not_text() {
        let entry = revoked("2026-10-19T08:30:00-06:00");
        assert!(!entry.counts_at(&at("2026-10-19T14:30:00+00:00")));
        assert!(entry.counts_at(&at("2026-10-19T14:29:59+00:00")));
        // As text this sorts after the revocation, and as a moment it is
        // before it.
        assert!(entry.counts_at(&at("2026-10-19T09:00:00-05:00")));
    }

    #[test]
    fn an_instant_is_seconds_since_1970() {
        assert_eq!(instant(&at("1970-01-01T00:00:00+00:00")), 0);
        assert_eq!(instant(&at("1970-01-01T01:00:00+01:00")), 0);
        assert_eq!(instant(&at("2000-03-01T00:00:00+00:00")), 951_868_800);
        assert_eq!(instant(&at("2026-10-19T14:30:00+00:00")), 1_792_420_200);
    }

    #[test]
    fn an_entry_renders_what_it_was_read_from() {
        let text = entry().render();
        assert_eq!(Entry::parse(&text), Ok(Some(entry())));
    }

    #[test]
    fn the_explanation_states_nothing() {
        assert_eq!(Entry::parse(EXPLANATION), Ok(None));
    }

    #[test]
    fn comments_and_blank_lines_are_skipped() {
        let text = format!("# who I believe\n\n{}", entry().render());
        assert_eq!(Entry::parse(&text), Ok(Some(entry())));
    }

    #[test]
    fn a_header_this_grammar_does_not_name_is_refused() {
        let text = format!("{}roles reviewer\n", entry().render());
        assert!(matches!(
            Entry::parse(&text),
            Err(EntryError::Unknown { .. })
        ));
    }

    #[test]
    fn a_second_key_is_refused_rather_than_taken() {
        let text = format!("{}key {KEY}\n", entry().render());
        assert!(matches!(
            Entry::parse(&text),
            Err(EntryError::Repeated { header: "key", .. })
        ));
    }

    /// A key with slashes all through it, which is the shape that made the
    /// digest the fallback: whatever `who` turns out to be, what comes back is
    /// one filename. Found originally by a test that failed one run in four.
    fn slashy() -> Key {
        "RWR1w/Qc/pmAfGpNp/rGIihJys120vcNACuzskkIWVdxuUe3Dzk3MlLz"
            .parse()
            .expect("a key with slashes in it")
    }

    #[test]
    fn a_default_label_is_who_the_key_speaks_for() {
        assert_eq!(
            default_label(&slashy(), "Adam Harris <adam@diaryx.org>"),
            "Adam Harris"
        );
        assert_eq!(default_label(&slashy(), "Adam Harris"), "Adam Harris");
        // A run of spaces is one, and the address is not part of the name.
        assert_eq!(
            default_label(&slashy(), "  Adam   Harris   <adam@diaryx.org>"),
            "Adam Harris"
        );
    }

    /// `who` is free text, so every answer has to be one filename.
    #[test]
    fn a_default_label_is_a_filename_whatever_who_says() {
        for who in [
            "Adam/Harris",
            "../../etc/passwd",
            "C:\\keys\\adam",
            ".hidden",
            "a\u{7}b",
        ] {
            let label = default_label(&slashy(), who);
            assert!(is_a_label(&label), "`{label}` from `{who}`");
            assert!(!label.contains('/'), "`{label}` from `{who}`");
            assert!(!label.starts_with('.'), "`{label}` from `{who}`");
        }
    }

    /// Where nothing usable survives, the digest of the key — which is a
    /// filename whatever the key and the person are called.
    #[test]
    fn a_who_that_names_nobody_falls_back_to_the_key() {
        for who in ["", "...", "<>", "/", "   "] {
            let label = default_label(&slashy(), who);
            assert_eq!(label.len(), 12, "`{label}` from `{who}`");
            assert!(
                label.chars().all(|c| c.is_ascii_hexdigit()),
                "`{label}` from `{who}`"
            );
            assert!(is_a_label(&label));
        }
    }

    /// A `who` landing on the name the explanation file already has would make
    /// `add` refuse for a reason nobody could see.
    #[test]
    fn a_who_that_names_the_explanation_falls_back_to_the_key() {
        let label = default_label(&slashy(), "how-this-works");
        assert_ne!(label, "how-this-works");
        assert_eq!(label.len(), 12);
    }

    /// Long enough for a name, short enough that the file still has one.
    #[test]
    fn a_very_long_who_is_cut() {
        let label = default_label(&slashy(), &"x".repeat(500));
        assert_eq!(label.chars().count(), LABEL_CHARS);
        assert!(is_a_label(&label));
    }

    #[test]
    fn a_label_that_is_a_path_is_refused() {
        assert!(!is_a_label(""));
        assert!(!is_a_label("."));
        assert!(!is_a_label(".."));
        assert!(!is_a_label("a/b"));
        assert!(is_a_label("adam"));
        assert!(is_a_label("adam's laptop"));
    }

    #[test]
    fn an_entry_without_a_person_is_refused() {
        let text = format!("{PREAMBLE}\nkey {KEY}\n");
        assert_eq!(
            Entry::parse(&text),
            Err(EntryError::Missing { header: "who" })
        );
    }
}
