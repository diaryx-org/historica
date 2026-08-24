//! The readable documents a history is stored as, and the digests that name them.
//!
//! A revision is one text file, specified by `docs/decisions/0002-revision-document.md`
//! and made strict by `docs/decisions/0004-parser-contract.md`:
//!
//! ```text
//! historica
//! change qpvuntsmwlrkzxonmvtplsyq
//! author Adam Harris <adam@example.com>
//! when 2025-08-19T00:47:11-06:00
//!
//! Start the readable core
//! ```
//!
//! The parser accepts exactly what [`RevisionDocument::write`] emits, so
//! exactly one byte sequence parses per set of facts. That is what lets the
//! digest cover the file's bytes — see [`digest`] — without a canonical
//! re-serialisation step existing anywhere.
//!
//! Authorship lives here rather than in [`crate::core`] because no part of
//! causality reads it, for the reasons in `docs/decisions/0005-authorship.md`.
//!
//! [`OperationDocument`] is the format's second document, specified by
//! `docs/decisions/0007-content-and-merge.md`: what one revision did to one
//! file. It opens with the same preamble and reads under the same contract, so
//! a person learns one shape and a parser reads a preamble the same way in
//! both.
//!
//! There is a third thing a revision may name and this module does not read: a
//! **payload**, which decision 0017 makes the content a file arrives with. It
//! has no preamble and no grammar, because it is the file itself — see
//! [`crate::store`], which is where bytes with no format of their own live.

use std::borrow::Cow;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

use sha2::{Digest, Sha256};
use unicode_normalization::{IsNormalized, UnicodeNormalization};

use crate::core::{CHANGE_ID_LEN, ChangeId, FileId, Revision, RevisionId};

mod error;
mod operations;
mod resolution;
mod timestamp;

pub use error::{ParseError, ParseErrorKind};
pub use operations::{
    FORGOTTEN, Item, NO_NEWLINE, Operation, OperationDocument, OperationKind, stand_in,
};
pub use resolution::{Piece, ResolutionDocument, is_resolution};
pub use timestamp::{MalformedTimestamp, Timestamp};

/// The preamble every document opens with.
///
/// Not a header: it carries no value, so nothing can read it as `key value`.
/// One spelling, unnumbered, because this format is 1.0's promise kept: the
/// grammar below it does not change. A future format that must break that
/// promise takes a new spelling, and this reader refuses it at this line
/// rather than guessing at what it would be leaving out.
pub const PREAMBLE: &str = "historica";

/// The prefix every preamble spelling shares, used to tell a document in a
/// format this reader lacks apart from a file that is not a document at all.
///
/// The pre-1.0 formats spelled it `historica-v0` through `historica-v5`, one
/// number per grammar change; those read only under a 0.x release.
const PREAMBLE_PREFIX: &str = "historica-";

/// Whether a file can be run.
///
/// Decision 0034 carries one bit and spells it as a word, because `executable`
/// is what the line means and `100755` is a file format's internal constant
/// wearing a document's clothes. Every other POSIX mode bit is deliberately
/// absent: a umask is a fact about a machine rather than about a history, and
/// a format that could say `setuid` would have a merge algorithm with a
/// privilege question in it.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub enum Mode {
    /// An ordinary file. What every file with no `mode` line anywhere in its
    /// history is, which is every file in every store written before 0034.
    #[default]
    Plain,
    /// A file that can be run.
    Executable,
}

impl Mode {
    /// The word this is written as.
    pub const fn spelling(self) -> &'static str {
        match self {
            Mode::Plain => "plain",
            Mode::Executable => "executable",
        }
    }

    /// Whether this is the bit set.
    pub const fn is_executable(self) -> bool {
        matches!(self, Mode::Executable)
    }

    /// The mode a filesystem's answer means.
    pub const fn of(executable: bool) -> Self {
        if executable {
            Mode::Executable
        } else {
            Mode::Plain
        }
    }
}

impl fmt::Display for Mode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.spelling())
    }
}

/// The prefix that tells a link's two spellings apart.
///
/// Decision 0024's spelling, in the format itself and for the same reason it
/// exists in the front end: a position that holds every string a person may
/// name needs a prefix no path a person would write is.
pub const FILE_PREFIX: &str = "file:";

/// What a link points at.
///
/// Decision 0040's two spellings, and the recorder chooses between them by
/// resolution rather than by preference. A target that resolves to a file this
/// history already holds is that file — an identity, which survives the
/// rename that makes every other tool's symlink dangle. Everything else is the
/// string a person chose, recorded as the string it is, because the store
/// knows nothing it could be a reference to.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum LinkTarget {
    /// A file in this history, whatever path it is at now.
    Reference(FileId),
    /// A string, exactly as the folder holds it.
    Verbatim(String),
}

impl LinkTarget {
    /// The file this names, where it names one.
    pub const fn reference(&self) -> Option<FileId> {
        match self {
            LinkTarget::Reference(file) => Some(*file),
            LinkTarget::Verbatim(_) => None,
        }
    }

    /// The string this is written as, which is what the header carries.
    pub fn spelling(&self) -> Cow<'_, str> {
        match self {
            LinkTarget::Reference(file) => Cow::Owned(format!("{FILE_PREFIX}{file}")),
            LinkTarget::Verbatim(target) => Cow::Borrowed(target.as_str()),
        }
    }
}

impl fmt::Display for LinkTarget {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.spelling())
    }
}

/// Whether a string can stand in a `link` header as a verbatim target.
///
/// Decision 0040 refuses three targets by name, and this is where the refusal
/// is decided so that `record` can name the file and the fix rather than a
/// parser meeting bytes nobody has written yet. Two of them — a newline, and
/// the padding that would not survive a round trip — are decision 0002's rules
/// for any header value, met here by a string that came from a folder rather
/// than from a document.
pub fn check_link_target(value: &str) -> Result<(), MalformedTarget> {
    let refuse = |because: &'static str| Err(MalformedTarget(because));
    if value.is_empty() {
        return refuse("it is empty, and a link with no target is not a link");
    }
    if value.starts_with(FILE_PREFIX) {
        return refuse(
            "it begins with `file:`, which is how this format spells a link to a file \
             it holds; rename it, or point it somewhere else",
        );
    }
    if value.starts_with(' ') || value.ends_with(' ') {
        return refuse("it has leading or trailing space, which a header value cannot keep");
    }
    if value.chars().any(char::is_control) {
        return refuse("it holds a control character, and a header is one line");
    }
    Ok(())
}

/// Why a string cannot be a link's target.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MalformedTarget(
    /// What is wrong with it, as a sentence a person can act on.
    pub &'static str,
);

impl fmt::Display for MalformedTarget {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.0)
    }
}

impl std::error::Error for MalformedTarget {}

/// Characters in a change ID's readable spelling.
pub const CHANGE_ID_CHARS: usize = CHANGE_ID_LEN * 2;

/// The SHA-256 of `bytes`, which is the revision ID of a revision document.
///
/// This is what `shasum -a 256` prints, which is the whole point: verification
/// needs no Historica.
pub fn digest(bytes: &[u8]) -> RevisionId {
    let mut hasher = Hasher::new();
    hasher.update(bytes);
    hasher.finish()
}

/// The same digest, over bytes that arrive in pieces.
///
/// What [`digest`] is, with the one buffer left out: a caller that would have
/// concatenated its bytes into a `Vec` purely to hash them can hand them over
/// as they come. The answer is identical — this is SHA-256 either way, and
/// `shasum -a 256` still prints it.
pub struct Hasher(Sha256);

impl Hasher {
    /// A hasher over nothing yet.
    pub fn new() -> Self {
        Self(Sha256::new())
    }

    /// Take the next run of bytes.
    pub fn update(&mut self, bytes: &[u8]) {
        self.0.update(bytes);
    }

    /// The digest of everything taken.
    pub fn finish(self) -> RevisionId {
        let mut out = [0u8; 32];
        out.copy_from_slice(&self.0.finalize());
        RevisionId::from_bytes(out)
    }
}

impl Default for Hasher {
    fn default() -> Self {
        Self::new()
    }
}

impl fmt::Debug for Hasher {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("Hasher")
    }
}

/// One revision document: every header, and the verbatim message.
///
/// Repeated facts are held in sorted sets and `x-` headers in a sorted map,
/// which is lossless precisely because the parser rejects any other order.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RevisionDocument {
    /// The change this revision is a version of.
    pub change: ChangeId,
    /// Causal parents, by digest. Empty means a root.
    pub parents: BTreeSet<RevisionId>,
    /// Revisions this one replaces, by digest.
    pub supersedes: BTreeSet<RevisionId>,
    /// Who did the work. Copied forward across rewrites.
    pub author: String,
    /// When the work was done. Copied forward across rewrites.
    pub when: Timestamp,
    /// Who produced this revision, when that is not the author.
    pub revised_by: Option<String>,
    /// When this revision was produced. Present exactly when `supersedes` is.
    pub revised: Option<Timestamp>,
    /// Files this revision brings into existence, and where it puts them.
    pub added: BTreeMap<FileId, String>,
    /// Files this revision moves, and where to.
    pub moved: BTreeMap<FileId, String>,
    /// Files whose mode this revision changes, and what to.
    ///
    /// Decision 0034: a tree fact stated by the revision that changes it, as
    /// `move` states a path that changed. A file named by no `mode` line
    /// anywhere in its history is [`Mode::Plain`].
    pub modes: BTreeMap<FileId, Mode>,
    /// Files this revision removes.
    pub dropped: BTreeSet<FileId>,
    /// The operation document this revision contributed to each file it edited.
    pub edited: BTreeMap<FileId, RevisionId>,
    /// The payload each file this revision added arrives as, read as lines.
    ///
    /// Decision 0017: exactly the operation document that inserts every line
    /// at 0, spelled as the file itself. Only a file this revision `add`s may
    /// appear here.
    pub text: BTreeMap<FileId, RevisionId>,
    /// The payload that is each named file's whole content, which has no lines.
    ///
    /// Decisions 0008 and 0017: such a file never merges, and two concurrent
    /// `bytes` lines for one file are a divergence to report.
    pub bytes: BTreeMap<FileId, RevisionId>,
    /// What each link this revision states points at.
    ///
    /// Decision 0040: stated by the revision that adds the file, where `text`
    /// or `bytes` would have stated content, and restated by any revision that
    /// changes the target — exactly as `move` restates a path that changed.
    /// A file this names is a link and nothing else, for its whole life.
    pub links: BTreeMap<FileId, LinkTarget>,
    /// Advisory `x-` headers, keyed by their full spelling including the prefix.
    pub extensions: BTreeMap<String, String>,
    /// The message, verbatim. Empty means the file had no separator at all.
    pub message: String,
}

impl RevisionDocument {
    /// Parse one revision document from the bytes of a `.rev` file.
    ///
    /// Every rejection names the line and says what to do about it, because a
    /// strict parser that cannot explain itself is only an obstacle.
    pub fn parse(bytes: &[u8]) -> Result<Self, ParseError> {
        Parser::new(bytes)?.run()
    }

    /// The exact bytes of this document.
    ///
    /// `write(parse(bytes)) == bytes` for every input `parse` accepts.
    pub fn write(&self) -> Vec<u8> {
        let mut out = String::new();
        out.push_str(PREAMBLE);
        out.push('\n');
        out.push_str(&format!("change {}\n", self.change));
        for parent in &self.parents {
            out.push_str(&format!("parent {parent}\n"));
        }
        for superseded in &self.supersedes {
            out.push_str(&format!("supersedes {superseded}\n"));
        }
        out.push_str(&format!("author {}\n", self.author));
        out.push_str(&format!("when {}\n", self.when));
        if let Some(revised_by) = &self.revised_by {
            out.push_str(&format!("revised-by {revised_by}\n"));
        }
        if let Some(revised) = &self.revised {
            out.push_str(&format!("revised {revised}\n"));
        }
        for (file, path) in &self.added {
            out.push_str(&format!("add {file} {path}\n"));
        }
        for (file, path) in &self.moved {
            out.push_str(&format!("move {file} {path}\n"));
        }
        for (file, mode) in &self.modes {
            out.push_str(&format!("mode {file} {mode}\n"));
        }
        for file in &self.dropped {
            out.push_str(&format!("drop {file}\n"));
        }
        for (file, document) in &self.edited {
            out.push_str(&format!("edit {file} {document}\n"));
        }
        for (file, payload) in &self.text {
            out.push_str(&format!("text {file} {payload}\n"));
        }
        for (file, payload) in &self.bytes {
            out.push_str(&format!("bytes {file} {payload}\n"));
        }
        for (file, target) in &self.links {
            out.push_str(&format!("link {file} {target}\n"));
        }
        for (key, value) in &self.extensions {
            out.push_str(&format!("{key} {value}\n"));
        }
        if !self.message.is_empty() {
            out.push('\n');
            out.push_str(&self.message);
        }
        out.into_bytes()
    }

    /// This document's revision ID: the digest of the bytes it writes.
    pub fn id(&self) -> RevisionId {
        digest(&self.write())
    }

    /// The causal facts, as the pure core models them.
    ///
    /// Authorship is dropped deliberately: nothing in head discovery or change
    /// resolution reads it.
    pub fn to_revision(&self) -> Revision {
        Revision {
            id: self.id(),
            change: self.change,
            parents: self.parents.clone(),
            supersedes: self.supersedes.clone(),
            message: self.message.clone(),
        }
    }
}

/// Where a key may appear in the fixed order.
///
/// `x-` headers share the last rank and are ordered against each other by key.
fn rank(key: &str) -> Option<u8> {
    match key {
        "change" => Some(0),
        "parent" => Some(1),
        "supersedes" => Some(2),
        "author" => Some(3),
        "when" => Some(4),
        "revised-by" => Some(5),
        "revised" => Some(6),
        // Decision 0008's tree facts: existence first, then content, each
        // sorted by file because the file comes first on the line. That order
        // is what gives 0007 the total order operation identity needs.
        "add" => Some(7),
        "move" => Some(8),
        // Decision 0034: where a file is, then what it is, then whether it is
        // still here. A mode is a fact about the file rather than its content,
        // so it reads with the facts about the file.
        "mode" => Some(9),
        "drop" => Some(10),
        "edit" => Some(11),
        // Decision 0017's payloads follow the operation document they stand in
        // for, so a file's content is read after its existence either way.
        "text" => Some(12),
        "bytes" => Some(13),
        // Decision 0040: a link's target stands where its content would have,
        // because for a link that is what it is instead of content.
        "link" => Some(14),
        key if key.starts_with("x-") => Some(15),
        _ => None,
    }
}

/// The rank `x-` headers share, which sort against each other by key.
const EXTENSION_RANK: u8 = 15;

/// Whether a rank may appear more than once.
fn repeatable(rank: u8) -> bool {
    matches!(
        rank,
        1 | 2 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | EXTENSION_RANK
    )
}

/// One header line, kept with its position so an error can name it.
struct Header {
    at: usize,
    key: String,
    value: String,
}

/// A cursor over a document's lines, shared by the format's two parsers.
///
/// Every line comes back with whether it was terminated, because a file that
/// stops mid-line is a fault rather than a shorter last line.
struct Lines<'a> {
    text: &'a str,
    cursor: usize,
    /// The 1-based number of the line last returned, or 0 before the first.
    line: usize,
}

impl<'a> Lines<'a> {
    fn new(text: &'a str) -> Self {
        Self {
            text,
            cursor: 0,
            line: 0,
        }
    }

    /// The next line and whether it was terminated, or `None` at end of input.
    fn next(&mut self) -> Option<(&'a str, bool)> {
        if self.cursor >= self.text.len() {
            return None;
        }
        let rest = &self.text[self.cursor..];
        self.line += 1;
        match rest.find('\n') {
            Some(index) => {
                self.cursor += index + 1;
                Some((&rest[..index], true))
            }
            None => {
                self.cursor = self.text.len();
                Some((rest, false))
            }
        }
    }

    /// Everything after the last line returned, unread and uninterpreted.
    fn rest(&self) -> &'a str {
        &self.text[self.cursor..]
    }

    /// Where the cursor stands, so that a lookahead can be undone.
    fn mark(&self) -> (usize, usize) {
        (self.cursor, self.line)
    }

    fn reset(&mut self, (cursor, line): (usize, usize)) {
        self.cursor = cursor;
        self.line = line;
    }
}

/// Refuse a byte order mark, which is part of the digest and invisible.
fn check_byte_order_mark(bytes: &[u8]) -> Result<(), ParseError> {
    if bytes.starts_with(&[0xEF, 0xBB, 0xBF]) {
        return Err(ParseError::new(1, ParseErrorKind::ByteOrderMark));
    }
    Ok(())
}

/// Hold a document's first line to the preamble.
///
/// Both documents in the format open this way, for decision 0004's reasons: a
/// file says how to hash itself, and can be identified by content rather than
/// by the extension it happens to carry.
fn check_preamble(line: &str, terminated: bool) -> Result<(), ParseError> {
    if line != PREAMBLE {
        let kind = if let Some(version) = line.strip_prefix(PREAMBLE_PREFIX) {
            ParseErrorKind::UnknownVersion {
                found: version.to_owned(),
            }
        } else {
            ParseErrorKind::MissingPreamble
        };
        return Err(ParseError::new(1, kind));
    }
    if !terminated {
        return Err(ParseError::new(1, ParseErrorKind::UnterminatedLine));
    }
    Ok(())
}

struct Parser<'a> {
    lines: Lines<'a>,
}

impl<'a> Parser<'a> {
    fn new(bytes: &'a [u8]) -> Result<Self, ParseError> {
        check_byte_order_mark(bytes)?;
        // A carriage return is rejected wherever it appears, body included: it
        // would let an editor silently change a revision's identity.
        if let Some(offset) = bytes.iter().position(|byte| *byte == b'\r') {
            let line = 1 + bytes[..offset].iter().filter(|b| **b == b'\n').count();
            return Err(ParseError::new(line, ParseErrorKind::CarriageReturn));
        }
        let text =
            std::str::from_utf8(bytes).map_err(|_| ParseError::new(0, ParseErrorKind::NotUtf8))?;
        Ok(Self {
            lines: Lines::new(text),
        })
    }

    fn next_line(&mut self) -> Option<(&'a str, bool)> {
        self.lines.next()
    }

    fn run(mut self) -> Result<RevisionDocument, ParseError> {
        self.preamble()?;
        let (headers, message) = self.headers_and_message()?;
        self.assemble(headers, message)
    }

    fn preamble(&mut self) -> Result<(), ParseError> {
        let Some((line, terminated)) = self.next_line() else {
            return Err(ParseError::new(1, ParseErrorKind::Empty));
        };
        check_preamble(line, terminated)
    }

    /// Read the header block, then take the message verbatim to the last byte.
    fn headers_and_message(&mut self) -> Result<(Vec<Header>, String), ParseError> {
        let mut headers = Vec::new();
        while let Some((line, terminated)) = self.next_line() {
            let at = self.lines.line;
            if line.is_empty() {
                // The separator. Everything after it is the message, and there
                // must be some, or an empty message would have two spellings.
                let message = self.lines.rest();
                if message.is_empty() {
                    return Err(ParseError::new(at, ParseErrorKind::EmptyBodyAfterSeparator));
                }
                return Ok((headers, message.to_owned()));
            }
            if !terminated {
                return Err(ParseError::new(at, ParseErrorKind::UnterminatedLine));
            }
            let (key, value) = split_header(line, at)?;
            headers.push(Header { at, key, value });
        }
        Ok((headers, String::new()))
    }

    fn assemble(
        self,
        headers: Vec<Header>,
        message: String,
    ) -> Result<RevisionDocument, ParseError> {
        let mut change: Option<ChangeId> = None;
        let mut parents = BTreeSet::new();
        let mut supersedes = BTreeSet::new();
        let mut author: Option<String> = None;
        let mut when: Option<Timestamp> = None;
        let mut revised_by: Option<String> = None;
        let mut revised: Option<Timestamp> = None;
        let mut added: BTreeMap<FileId, String> = BTreeMap::new();
        let mut moved: BTreeMap<FileId, String> = BTreeMap::new();
        let mut modes: BTreeMap<FileId, Mode> = BTreeMap::new();
        let mut dropped: BTreeSet<FileId> = BTreeSet::new();
        let mut edited: BTreeMap<FileId, RevisionId> = BTreeMap::new();
        let mut text: BTreeMap<FileId, RevisionId> = BTreeMap::new();
        let mut bytes: BTreeMap<FileId, RevisionId> = BTreeMap::new();
        let mut links: BTreeMap<FileId, LinkTarget> = BTreeMap::new();
        let mut extensions: BTreeMap<String, String> = BTreeMap::new();

        let mut previous: Option<(u8, String, String)> = None;

        for Header { at, key, value } in headers {
            let Some(this_rank) = rank(&key) else {
                return Err(ParseError::new(
                    at,
                    ParseErrorKind::UnknownHeader { key: key.clone() },
                ));
            };

            if let Some((last_rank, last_key, last_value)) = &previous {
                if this_rank < *last_rank {
                    return Err(ParseError::new(
                        at,
                        ParseErrorKind::KeysOutOfOrder {
                            key: key.clone(),
                            after: last_key.clone(),
                        },
                    ));
                }
                if this_rank == *last_rank {
                    if !repeatable(this_rank) {
                        return Err(ParseError::new(
                            at,
                            ParseErrorKind::RepeatedHeader { key: key.clone() },
                        ));
                    }
                    // Repeated facts sort by digest, and `x-` headers by key,
                    // so that a deterministic rewrite is deterministic in bytes.
                    let (this_sort, last_sort) = if this_rank == EXTENSION_RANK {
                        (&key, last_key)
                    } else {
                        (&value, last_value)
                    };
                    if this_sort == last_sort {
                        return Err(ParseError::new(
                            at,
                            ParseErrorKind::DuplicateFact { key: key.clone() },
                        ));
                    }
                    if this_sort < last_sort {
                        return Err(ParseError::new(
                            at,
                            ParseErrorKind::RepeatedKeyOutOfOrder { key: key.clone() },
                        ));
                    }
                }
            }
            previous = Some((this_rank, key.clone(), value.clone()));

            match key.as_str() {
                "change" => change = Some(parse_change_id(&value, at)?),
                "parent" => {
                    parents.insert(parse_digest(&value, at, "parent")?);
                }
                "supersedes" => {
                    supersedes.insert(parse_digest(&value, at, "supersedes")?);
                }
                "author" => author = Some(value),
                "when" => when = Some(Timestamp::parse(&value, at)?),
                "revised-by" => revised_by = Some(value),
                "revised" => revised = Some(Timestamp::parse(&value, at)?),
                "add" | "move" => {
                    let adding = key == "add";
                    let key = if adding { "add" } else { "move" };
                    let (file, path) = split_entry(&value, at, key)?;
                    let file = parse_file_id(file, at)?;
                    let path = parse_path(path, at)?;
                    let seen = if adding {
                        added.insert(file, path)
                    } else {
                        moved.insert(file, path)
                    };
                    if seen.is_some() {
                        return Err(ParseError::new(
                            at,
                            ParseErrorKind::FileStatedTwice {
                                key,
                                file: file.to_string(),
                            },
                        ));
                    }
                }
                "mode" => {
                    let (file, spelling) = split_entry(&value, at, "mode")?;
                    let file = parse_file_id(file, at)?;
                    let mode = match spelling {
                        "plain" => Mode::Plain,
                        "executable" => Mode::Executable,
                        other => {
                            return Err(ParseError::new(
                                at,
                                ParseErrorKind::UnknownMode {
                                    found: other.to_owned(),
                                },
                            ));
                        }
                    };
                    if modes.insert(file, mode).is_some() {
                        return Err(ParseError::new(
                            at,
                            ParseErrorKind::FileStatedTwice {
                                key: "mode",
                                file: file.to_string(),
                            },
                        ));
                    }
                }
                "drop" => {
                    let file = parse_file_id(&value, at)?;
                    if !dropped.insert(file) {
                        return Err(ParseError::new(
                            at,
                            ParseErrorKind::FileStatedTwice {
                                key: "drop",
                                file: file.to_string(),
                            },
                        ));
                    }
                }
                "edit" | "text" | "bytes" => {
                    let key: &'static str = match key.as_str() {
                        "edit" => "edit",
                        "text" => "text",
                        _ => "bytes",
                    };
                    let (file, named) = split_entry(&value, at, key)?;
                    let file = parse_file_id(file, at)?;
                    let named = parse_digest(named, at, key)?;
                    let into = match key {
                        "edit" => &mut edited,
                        "text" => &mut text,
                        _ => &mut bytes,
                    };
                    if into.insert(file, named).is_some() {
                        return Err(ParseError::new(
                            at,
                            ParseErrorKind::FileStatedTwice {
                                key,
                                file: file.to_string(),
                            },
                        ));
                    }
                }
                "link" => {
                    let (file, target) = split_entry(&value, at, "link")?;
                    let file = parse_file_id(file, at)?;
                    // Decision 0040: the target is the rest of the line, so a
                    // target holding a space is a target rather than a
                    // malformed pair. The one string the two spellings cannot
                    // share a column with is the one the prefix claims.
                    let target = match target.strip_prefix(FILE_PREFIX) {
                        Some(named) => LinkTarget::Reference(parse_file_id(named, at)?),
                        None => LinkTarget::Verbatim(target.to_owned()),
                    };
                    if links.insert(file, target).is_some() {
                        return Err(ParseError::new(
                            at,
                            ParseErrorKind::FileStatedTwice {
                                key: "link",
                                file: file.to_string(),
                            },
                        ));
                    }
                }
                _ => {
                    extensions.insert(key, value);
                }
            }
        }

        let last = self.lines.line;
        let change = change.ok_or_else(|| {
            ParseError::new(last, ParseErrorKind::MissingHeader { key: "change" })
        })?;
        let author = author.ok_or_else(|| {
            ParseError::new(last, ParseErrorKind::MissingHeader { key: "author" })
        })?;
        let when = when
            .ok_or_else(|| ParseError::new(last, ParseErrorKind::MissingHeader { key: "when" }))?;

        // `revised-by` and `revised` describe this revision, so they appear
        // only once a revision has predecessors.
        if supersedes.is_empty() {
            if revised.is_some() {
                return Err(ParseError::new(
                    last,
                    ParseErrorKind::RevisionMetadataWithoutSupersedes { key: "revised" },
                ));
            }
            if revised_by.is_some() {
                return Err(ParseError::new(
                    last,
                    ParseErrorKind::RevisionMetadataWithoutSupersedes { key: "revised-by" },
                ));
            }
        } else if revised.is_none() {
            return Err(ParseError::new(
                last,
                ParseErrorKind::MissingHeader { key: "revised" },
            ));
        }

        // A fact equal to another fact is a second spelling of it.
        if revised_by.as_deref() == Some(author.as_str()) {
            return Err(ParseError::new(last, ParseErrorKind::RedundantRevisedBy));
        }

        // Decision 0008: one revision says one thing about one file's
        // existence. `add` with `move` states a path twice, `drop` with
        // anything else contradicts itself.
        let contradiction = |first: &'static str, second: &'static str, file: &FileId| {
            ParseError::new(
                last,
                ParseErrorKind::ContradictoryFileFacts {
                    first,
                    second,
                    file: file.to_string(),
                },
            )
        };
        for file in added.keys() {
            if moved.contains_key(file) {
                return Err(contradiction("add", "move", file));
            }
            if dropped.contains(file) {
                return Err(contradiction("add", "drop", file));
            }
            // Decision 0017: an `edit`'s positions are counted into the file at
            // this revision's parents, and a file added here is not there.
            if edited.contains_key(file) {
                return Err(contradiction("add", "edit", file));
            }
        }
        for file in moved.keys() {
            if dropped.contains(file) {
                return Err(contradiction("move", "drop", file));
            }
        }
        for file in &dropped {
            if edited.contains_key(file) {
                return Err(contradiction("drop", "edit", file));
            }
            if bytes.contains_key(file) {
                return Err(contradiction("drop", "bytes", file));
            }
            // Decision 0034: a file leaving the file set has no mode to have.
            // `add` with `mode` is the one pairing that is not a
            // contradiction, because a file may be created executable.
            if modes.contains_key(file) {
                return Err(contradiction("drop", "mode", file));
            }
            // Decision 0040: a file leaving the file set points nowhere.
            if links.contains_key(file) {
                return Err(contradiction("drop", "link", file));
            }
        }
        // Decision 0040: a link is a third kind of file, so a revision that
        // says a file is a link and in the same breath states its content, or
        // its mode, has said two things about what kind of file it is. A link
        // has no bytes to hold and no bit to run.
        for file in links.keys() {
            if text.contains_key(file) {
                return Err(contradiction("link", "text", file));
            }
            if bytes.contains_key(file) {
                return Err(contradiction("link", "bytes", file));
            }
            if edited.contains_key(file) {
                return Err(contradiction("link", "edit", file));
            }
            if modes.contains_key(file) {
                return Err(contradiction("link", "mode", file));
            }
        }
        // Decision 0017: a file's content is stated once, one way. `text`
        // states the lines a creation arrives with, so it says nothing about a
        // file this revision does not add.
        for file in text.keys() {
            if bytes.contains_key(file) {
                return Err(contradiction("text", "bytes", file));
            }
            if !added.contains_key(file) {
                return Err(ParseError::new(
                    last,
                    ParseErrorKind::TextWithoutAdd {
                        file: file.to_string(),
                    },
                ));
            }
        }
        for file in bytes.keys() {
            if edited.contains_key(file) {
                return Err(contradiction("edit", "bytes", file));
            }
        }

        Ok(RevisionDocument {
            change,
            parents,
            supersedes,
            author,
            when,
            revised_by,
            revised,
            added,
            moved,
            modes,
            dropped,
            edited,
            text,
            bytes,
            links,
            extensions,
            message,
        })
    }
}

/// Split `key value`, enforcing the key's shape and the value's.
fn split_header(line: &str, at: usize) -> Result<(String, String), ParseError> {
    let Some(space) = line.find(' ') else {
        // `author` with nothing after it: an absent fact is an absent line.
        return Err(ParseError::new(at, ParseErrorKind::EmptyValue));
    };
    let (key, value) = (&line[..space], &line[space + 1..]);

    if key.is_empty() || !key.bytes().all(|b| b.is_ascii_lowercase() || b == b'-') {
        return Err(ParseError::new(
            at,
            ParseErrorKind::MalformedKey {
                key: key.to_owned(),
            },
        ));
    }
    if value.is_empty() {
        return Err(ParseError::new(at, ParseErrorKind::EmptyValue));
    }
    if value.starts_with(' ') || value.ends_with(' ') {
        return Err(ParseError::new(at, ParseErrorKind::PaddedValue));
    }
    if value.chars().any(|c| c.is_control()) {
        return Err(ParseError::new(at, ParseErrorKind::ControlCharacter));
    }
    Ok((key.to_owned(), value.to_owned()))
}

/// Split `<file> <rest>`, which every tree header but `drop` is shaped like.
fn split_entry<'a>(
    value: &'a str,
    at: usize,
    key: &'static str,
) -> Result<(&'a str, &'a str), ParseError> {
    value
        .split_once(' ')
        .ok_or_else(|| ParseError::new(at, ParseErrorKind::MalformedFileEntry { key }))
}

fn parse_file_id(value: &str, at: usize) -> Result<FileId, ParseError> {
    value.parse().map_err(|_| {
        ParseError::new(
            at,
            ParseErrorKind::MalformedFileId {
                found: value.to_owned(),
            },
        )
    })
}

/// A path under decision 0008: UTF-8, relative, and with no escape.
fn parse_path(value: &str, at: usize) -> Result<String, ParseError> {
    check_path(value).map_err(|because| {
        ParseError::new(
            at,
            ParseErrorKind::MalformedPath {
                found: value.to_owned(),
                because: because.0,
            },
        )
    })?;
    Ok(value.to_owned())
}

/// One path, in Unicode normal form C.
///
/// The store's spelling, per decision 0033. Applied wherever a path arrives
/// from outside — a directory listing, an argument a person typed — so that
/// two replicas whose filesystems disagree about how to spell a name record
/// one path rather than two files.
///
/// Borrowed where the path is already normalised, which is every ASCII path
/// and therefore very nearly all of them.
pub fn nfc(value: &str) -> Cow<'_, str> {
    if value.is_ascii() || unicode_normalization::is_nfc_quick(value.chars()) == IsNormalized::Yes {
        return Cow::Borrowed(value);
    }
    Cow::Owned(value.nfc().collect())
}

/// Whether `value` is a path a revision document may name.
///
/// Decision 0008's rules, and 0002's rules for any header value. A writer
/// checks a path here before composing a document, so that a filename the
/// format cannot hold is refused where a person can still see which file it
/// was — rather than inside a parser reading bytes nobody has written yet.
pub fn check_path(value: &str) -> Result<(), MalformedPath> {
    let refuse = |because: &'static str| Err(MalformedPath(because));
    if value.is_empty() {
        return refuse("it is empty");
    }
    if value.starts_with('/') {
        return refuse("it begins with `/`, and a path is relative to the repository root");
    }
    if value.ends_with('/') {
        return refuse("it ends with `/`, and a path names a file rather than a directory");
    }
    if value.starts_with(' ') || value.ends_with(' ') {
        return refuse("it has leading or trailing space");
    }
    if value.chars().any(char::is_control) {
        return refuse("it holds a control character");
    }
    for component in value.split('/') {
        if component.is_empty() {
            return refuse("it has an empty component");
        }
        if component == "." || component == ".." {
            return refuse("`.` and `..` are not components");
        }
    }
    // Decision 0033: the store spells a path one way, so that a name a
    // filesystem hands back decomposed is the same path it was written as.
    if nfc(value) != value {
        return refuse(
            "it is not in Unicode normal form C, which is the one spelling a store records",
        );
    }
    Ok(())
}

/// A path the format cannot hold, and why.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MalformedPath(&'static str);

impl fmt::Display for MalformedPath {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.0)
    }
}

impl std::error::Error for MalformedPath {}

fn parse_change_id(value: &str, at: usize) -> Result<ChangeId, ParseError> {
    value.parse().map_err(|_| {
        ParseError::new(
            at,
            ParseErrorKind::MalformedChangeId {
                found: value.to_owned(),
            },
        )
    })
}

fn parse_digest(value: &str, at: usize, key: &'static str) -> Result<RevisionId, ParseError> {
    value.parse().map_err(|_| {
        ParseError::new(
            at,
            ParseErrorKind::MalformedDigest {
                key,
                found: value.to_owned(),
            },
        )
    })
}

impl fmt::Display for RevisionDocument {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&String::from_utf8_lossy(&self.write()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const CHANGE: &str = "change qpvuntsmwlrkzxonmvtplsyq";
    const AUTHOR: &str = "author Adam Harris <adam@example.com>";
    const WHEN: &str = "when 2025-08-19T00:47:11-06:00";
    const A: &str = "1e4e224e93380a25d4cd1be85d35db37f4064be4388822eba250894c6d6daa0d";
    const B: &str = "35a85a359d0efae6e402a700a38d32ab57a7efc846e6fba6e88229d9663573eb";

    /// Assemble a file from header lines and an optional message.
    fn file(headers: &[&str], message: Option<&str>) -> Vec<u8> {
        let mut out = format!("{PREAMBLE}\n");
        for header in headers {
            out.push_str(header);
            out.push('\n');
        }
        if let Some(message) = message {
            out.push('\n');
            out.push_str(message);
        }
        out.into_bytes()
    }

    fn refuse(headers: &[&str], message: Option<&str>) -> ParseErrorKind {
        RevisionDocument::parse(&file(headers, message))
            .expect_err("should be refused")
            .kind
    }

    fn accept(headers: &[&str], message: Option<&str>) -> RevisionDocument {
        RevisionDocument::parse(&file(headers, message)).expect("should parse")
    }

    #[test]
    fn the_minimal_revision_is_a_change_an_author_and_a_time() {
        let document = accept(&[CHANGE, AUTHOR, WHEN], Some("Start"));
        assert!(document.parents.is_empty());
        assert_eq!(document.message, "Start");
        assert!(document.revised.is_none());
    }

    #[test]
    fn a_missing_required_header_names_the_one_that_is_missing() {
        assert_eq!(
            refuse(&[AUTHOR, WHEN], Some("m")),
            ParseErrorKind::MissingHeader { key: "change" }
        );
        assert_eq!(
            refuse(&[CHANGE, WHEN], Some("m")),
            ParseErrorKind::MissingHeader { key: "author" }
        );
        assert_eq!(
            refuse(&[CHANGE, AUTHOR], Some("m")),
            ParseErrorKind::MissingHeader { key: "when" }
        );
    }

    #[test]
    fn a_value_is_neither_padded_nor_full_of_control_characters() {
        assert_eq!(
            refuse(&[CHANGE, "author  Adam", WHEN], Some("m")),
            ParseErrorKind::PaddedValue
        );
        assert_eq!(
            refuse(&[CHANGE, "author Adam ", WHEN], Some("m")),
            ParseErrorKind::PaddedValue
        );
        assert_eq!(
            refuse(&[CHANGE, "author Ad\u{7}am", WHEN], Some("m")),
            ParseErrorKind::ControlCharacter
        );
    }

    #[test]
    fn a_key_is_lowercase_letters_and_hyphens() {
        assert!(matches!(
            refuse(&[CHANGE, "author-2 Adam", WHEN], Some("m")),
            ParseErrorKind::MalformedKey { .. }
        ));
        assert!(matches!(
            refuse(&[CHANGE, "Author Adam", WHEN], Some("m")),
            ParseErrorKind::MalformedKey { .. }
        ));
        // The preamble is not a header: it carries no value, and it is not a
        // key the grammar defines.
        assert_eq!(rank(PREAMBLE), None);
    }

    #[test]
    fn one_fact_may_not_be_stated_twice() {
        assert_eq!(
            refuse(&[CHANGE, AUTHOR, WHEN, WHEN], Some("m")),
            ParseErrorKind::RepeatedHeader {
                key: "when".to_owned()
            }
        );
        let parent = format!("parent {A}");
        assert_eq!(
            refuse(&[CHANGE, &parent, &parent, AUTHOR, WHEN], Some("m")),
            ParseErrorKind::DuplicateFact {
                key: "parent".to_owned()
            }
        );
    }

    #[test]
    fn advisory_headers_come_last_and_sort_by_key() {
        let document = accept(&[CHANGE, AUTHOR, WHEN, "x-a one", "x-b two"], Some("m"));
        assert_eq!(document.extensions.len(), 2);
        assert_eq!(
            document.write(),
            file(&[CHANGE, AUTHOR, WHEN, "x-a one", "x-b two"], Some("m"))
        );

        assert_eq!(
            refuse(&[CHANGE, AUTHOR, WHEN, "x-b two", "x-a one"], Some("m")),
            ParseErrorKind::RepeatedKeyOutOfOrder {
                key: "x-a".to_owned()
            }
        );
        assert!(matches!(
            refuse(&[CHANGE, "x-a one", AUTHOR, WHEN], Some("m")),
            ParseErrorKind::KeysOutOfOrder { .. }
        ));
    }

    #[test]
    fn rewrite_metadata_appears_only_on_a_rewrite() {
        let supersedes = format!("supersedes {A}");
        let revised = "revised 2025-08-20T08:14:33+02:00";

        // Present together, this is an ordinary amendment.
        accept(&[CHANGE, &supersedes, AUTHOR, WHEN, revised], Some("m"));

        assert_eq!(
            refuse(&[CHANGE, AUTHOR, WHEN, revised], Some("m")),
            ParseErrorKind::RevisionMetadataWithoutSupersedes { key: "revised" }
        );
        assert_eq!(
            refuse(&[CHANGE, &supersedes, AUTHOR, WHEN], Some("m")),
            ParseErrorKind::MissingHeader { key: "revised" }
        );
        // A reviewer who is the author is a fact spelled twice.
        assert_eq!(
            refuse(
                &[
                    CHANGE,
                    &supersedes,
                    AUTHOR,
                    WHEN,
                    "revised-by Adam Harris <adam@example.com>",
                    revised
                ],
                Some("m")
            ),
            ParseErrorKind::RedundantRevisedBy
        );
    }

    #[test]
    fn a_timestamp_has_exactly_one_spelling() {
        let bad = [
            "when 2025-08-19T00:47:11.5-06:00", // fractional seconds
            "when 2025-08-19T00:47:11Z",        // `Z` is not a spelling
            "when 2025-08-19T00:47:11-00:00",   // RFC 3339: offset unknown
            "when 2025-13-19T00:47:11-06:00",   // no such month
            "when 2025-02-30T00:47:11-06:00",   // no such day
            "when 2025-08-19T24:47:11-06:00",   // no such hour
            "when 2025-08-19 00:47:11-06:00",   // no `T`
        ];
        for header in bad {
            assert!(
                matches!(
                    refuse(&[CHANGE, AUTHOR, header], Some("m")),
                    ParseErrorKind::MalformedTimestamp { .. }
                ),
                "{header} should be refused"
            );
        }
        // A leap day is a real day.
        accept(
            &[CHANGE, AUTHOR, "when 2024-02-29T00:47:11+00:00"],
            Some("m"),
        );
    }

    #[test]
    fn digests_and_change_ids_keep_disjoint_alphabets() {
        assert!(matches!(
            refuse(
                &[CHANGE, "parent qpvuntsmwlrkzxonmvtplsyq", AUTHOR, WHEN],
                Some("m")
            ),
            ParseErrorKind::MalformedDigest { .. }
        ));
        assert!(matches!(
            refuse(
                &["change 1a4f9c2e0b7d6533a8c1f40e", AUTHOR, WHEN],
                Some("m")
            ),
            ParseErrorKind::MalformedChangeId { .. }
        ));
    }

    #[test]
    fn the_file_itself_must_be_well_formed() {
        assert_eq!(
            RevisionDocument::parse(b"").expect_err("empty").kind,
            ParseErrorKind::Empty
        );
        assert_eq!(
            RevisionDocument::parse("\u{feff}historica\n".as_bytes())
                .expect_err("bom")
                .kind,
            ParseErrorKind::ByteOrderMark
        );
        assert_eq!(
            RevisionDocument::parse(b"historica")
                .expect_err("no newline")
                .kind,
            ParseErrorKind::UnterminatedLine
        );
        // A header line that runs to the end of the file without a newline.
        let truncated = format!("{PREAMBLE}\n{CHANGE}\n{AUTHOR}\n{WHEN}");
        assert_eq!(
            RevisionDocument::parse(truncated.as_bytes())
                .expect_err("truncated")
                .kind,
            ParseErrorKind::UnterminatedLine
        );
        assert!(matches!(
            RevisionDocument::parse(&[0xffu8, 0xfe])
                .expect_err("not utf-8")
                .kind,
            ParseErrorKind::NotUtf8
        ));
    }

    #[test]
    fn parents_are_written_in_digest_order_whatever_order_they_arrive_in() {
        // Two replicas that rebase onto the same parents must write one file,
        // which is what makes the result merge by union rather than diverge.
        let one = accept(
            &[
                CHANGE,
                &format!("parent {A}"),
                &format!("parent {B}"),
                AUTHOR,
                WHEN,
            ],
            Some("m"),
        );
        let mut other = one.clone();
        other.parents = one.parents.iter().rev().copied().collect();
        assert_eq!(one.write(), other.write());
        assert_eq!(one.id(), other.id());
    }

    const FILE: &str = "lqxstvnmpkwyzrolvtsqnkxm";
    const OTHER_FILE: &str = "ptkwnrvzlmyxqsotnkwlpvzr";

    #[test]
    fn a_revision_says_what_it_did_to_the_file_set() {
        let headers = [
            CHANGE,
            AUTHOR,
            WHEN,
            &format!("add {FILE} notes/2025-08-19.md"),
            &format!("move {OTHER_FILE} notes/archive/2025-08-01.md"),
            &format!("drop {}", "wnkyzrtlmqvsxopwnztkylrv"),
            &format!("edit {OTHER_FILE} {A}"),
            &format!("text {FILE} {B}"),
        ]
        .map(String::from);
        let lines: Vec<&str> = headers.iter().map(String::as_str).collect();

        let document = accept(&lines, Some("m"));
        assert_eq!(
            document.added.values().next().map(String::as_str),
            Some("notes/2025-08-19.md")
        );
        assert_eq!(document.moved.len(), 1);
        assert_eq!(document.dropped.len(), 1);
        assert_eq!(document.edited.len(), 1);
        assert_eq!(document.text.len(), 1);
        assert_eq!(document.write(), file(&lines, Some("m")));
    }

    #[test]
    fn tree_headers_sort_the_way_a_file_identifier_reads() {
        // The alphabet runs backwards against the bytes it encodes, so a map
        // ordered by bytes would write these two lines in the order the parser
        // refuses. This is that trap, held open.
        let first = "k".repeat(CHANGE_ID_CHARS);
        let last = "z".repeat(CHANGE_ID_CHARS);
        let document = accept(
            &[
                CHANGE,
                AUTHOR,
                WHEN,
                &format!("add {first} a.md"),
                &format!("add {last} b.md"),
            ],
            Some("m"),
        );
        let written = String::from_utf8(document.write()).expect("UTF-8");
        assert!(
            written.find(&first) < written.find(&last),
            "written in the order the parser reads: {written}"
        );
        RevisionDocument::parse(&document.write()).expect("what it writes, it reads");
    }

    #[test]
    fn one_revision_says_one_thing_about_one_files_existence() {
        let add = format!("add {FILE} a.md");
        let moved = format!("move {FILE} b.md");
        let dropped = format!("drop {FILE}");
        let edited = format!("edit {FILE} {A}");

        let text = format!("text {FILE} {A}");
        let bytes = format!("bytes {FILE} {A}");

        // Creating a file with content, and moving one while editing it, are
        // the ordinary combinations. Decision 0017: a creation states its
        // content rather than inserting every line of it.
        accept(&[CHANGE, AUTHOR, WHEN, &add, &text], Some("m"));
        accept(&[CHANGE, AUTHOR, WHEN, &add, &bytes], Some("m"));
        accept(&[CHANGE, AUTHOR, WHEN, &moved, &edited], Some("m"));
        accept(&[CHANGE, AUTHOR, WHEN, &moved, &bytes], Some("m"));

        // A file added here did not exist at the parent to be edited, which is
        // what version 0 spelled a creation as and version 1 refuses.
        assert_eq!(
            refuse(&[CHANGE, AUTHOR, WHEN, &add, &edited], Some("m")),
            ParseErrorKind::ContradictoryFileFacts {
                first: "add",
                second: "edit",
                file: FILE.to_owned(),
            }
        );
        assert_eq!(
            refuse(&[CHANGE, AUTHOR, WHEN, &add, &text, &bytes], Some("m")),
            ParseErrorKind::ContradictoryFileFacts {
                first: "text",
                second: "bytes",
                file: FILE.to_owned(),
            }
        );
        assert_eq!(
            refuse(&[CHANGE, AUTHOR, WHEN, &edited, &bytes], Some("m")),
            ParseErrorKind::ContradictoryFileFacts {
                first: "edit",
                second: "bytes",
                file: FILE.to_owned(),
            }
        );
        assert_eq!(
            refuse(&[CHANGE, AUTHOR, WHEN, &dropped, &bytes], Some("m")),
            ParseErrorKind::ContradictoryFileFacts {
                first: "drop",
                second: "bytes",
                file: FILE.to_owned(),
            }
        );
        // `text` states the lines a file arrives with, so it says nothing
        // about a file this revision does not add.
        assert_eq!(
            refuse(&[CHANGE, AUTHOR, WHEN, &moved, &text], Some("m")),
            ParseErrorKind::TextWithoutAdd {
                file: FILE.to_owned(),
            }
        );

        assert_eq!(
            refuse(&[CHANGE, AUTHOR, WHEN, &add, &moved], Some("m")),
            ParseErrorKind::ContradictoryFileFacts {
                first: "add",
                second: "move",
                file: FILE.to_owned(),
            }
        );
        assert_eq!(
            refuse(&[CHANGE, AUTHOR, WHEN, &add, &dropped], Some("m")),
            ParseErrorKind::ContradictoryFileFacts {
                first: "add",
                second: "drop",
                file: FILE.to_owned(),
            }
        );
        assert_eq!(
            refuse(&[CHANGE, AUTHOR, WHEN, &dropped, &edited], Some("m")),
            ParseErrorKind::ContradictoryFileFacts {
                first: "drop",
                second: "edit",
                file: FILE.to_owned(),
            }
        );
        // The same header twice for one file states one fact twice.
        assert_eq!(
            refuse(
                &[CHANGE, AUTHOR, WHEN, &add, &format!("add {FILE} zz.md")],
                Some("m")
            ),
            ParseErrorKind::FileStatedTwice {
                key: "add",
                file: FILE.to_owned(),
            }
        );
    }

    #[test]
    fn a_pre_1_0_document_is_refused_at_the_preamble_by_name() {
        // The pre-1.0 formats numbered their preambles `historica-v0` through
        // `historica-v5`, one number per grammar change. This reader refuses
        // them at the first line rather than guessing at what it would be
        // leaving out; a 0.x release still reads them.
        let older = format!(
            "historica-v0\nchange {}\nauthor {}\nwhen {}\nadd {FILE} a.md\nedit {FILE} {A}\n\nm",
            &CHANGE[7..],
            &AUTHOR[7..],
            &WHEN[5..],
        );
        assert_eq!(
            RevisionDocument::parse(older.as_bytes())
                .expect_err("a pre-1.0 format")
                .kind,
            ParseErrorKind::UnknownVersion {
                found: "v0".to_owned()
            }
        );
        // A format newer than this reader is refused on the same terms.
        let newer = format!("historica-2\nchange {}\n\nm", &CHANGE[7..]);
        assert_eq!(
            RevisionDocument::parse(newer.as_bytes())
                .expect_err("a later format")
                .kind,
            ParseErrorKind::UnknownVersion {
                found: "2".to_owned()
            }
        );
        // And the spelling 0017 retired — a creation as `add` with `edit` —
        // is a contradiction here, whatever it once was.
        let retired = format!(
            "{PREAMBLE}\nchange {}\nauthor {}\nwhen {}\nadd {FILE} a.md\nedit {FILE} {A}\n\nm",
            &CHANGE[7..],
            &AUTHOR[7..],
            &WHEN[5..],
        );
        assert_eq!(
            RevisionDocument::parse(retired.as_bytes())
                .expect_err("add with edit contradicts itself")
                .kind,
            ParseErrorKind::ContradictoryFileFacts {
                first: "add",
                second: "edit",
                file: FILE.to_owned(),
            }
        );
    }

    #[test]
    fn a_path_is_relative_utf_8_with_no_escape() {
        let good = [
            "a.md",
            "notes/2025-08-19.md",
            "notes/deeply/nested/entry.md",
            "a file with spaces.md",
            "\\backslash-is-an-ordinary-character.md",
            "curly “quotes” and 🌛.md",
        ];
        for path in good {
            accept(
                &[CHANGE, AUTHOR, WHEN, &format!("add {FILE} {path}")],
                Some("m"),
            );
        }

        let bad = [
            "/absolute.md",
            "trailing/",
            "double//slash.md",
            "./relative.md",
            "../escape.md",
            "notes/../escape.md",
            " leading-space.md",
            // Decision 0033: `café` with a combining acute, which is the same
            // name and not the spelling a store records it under.
            "cafe\u{301}.md",
        ];
        for path in bad {
            assert!(
                matches!(
                    refuse(
                        &[CHANGE, AUTHOR, WHEN, &format!("add {FILE} {path}")],
                        Some("m")
                    ),
                    ParseErrorKind::MalformedPath { .. }
                ),
                "`{path}` should be refused"
            );
        }
    }

    /// Decision 0033: one spelling per path, so that two replicas whose
    /// filesystems disagree about how to write a name record one file.
    #[test]
    fn a_path_is_spelled_in_normal_form_c() {
        // The two spellings of `café`: precomposed, and `e` with a combining
        // acute accent. They are the same name and different bytes.
        let composed = "caf\u{e9}.md";
        let decomposed = "cafe\u{301}.md";
        assert_ne!(composed, decomposed);
        assert_eq!(nfc(decomposed), composed);
        assert!(check_path(composed).is_ok());
        assert!(check_path(decomposed).is_err());

        // An ASCII path is already normalised, and normalising it copies
        // nothing — which is very nearly every path there is.
        assert!(matches!(nfc("notes/2026-08-19.md"), Cow::Borrowed(_)));
        assert!(matches!(nfc(composed), Cow::Borrowed(_)));
        assert!(matches!(nfc(decomposed), Cow::Owned(_)));

        // Normalising is idempotent, which is what lets it happen at every
        // boundary without anyone tracking whether it already has.
        for path in ["a.md", composed, decomposed, "🌛/\u{1e9b}\u{323}.md"] {
            let once = nfc(path).into_owned();
            assert_eq!(nfc(&once), once, "{path:?}");
            assert!(check_path(&once).is_ok(), "{path:?}");
        }
    }

    #[test]
    fn a_tree_header_names_a_file_and_one_other_thing() {
        assert_eq!(
            refuse(&[CHANGE, AUTHOR, WHEN, &format!("add {FILE}")], Some("m")),
            ParseErrorKind::MalformedFileEntry { key: "add" }
        );
        assert_eq!(
            refuse(&[CHANGE, AUTHOR, WHEN, &format!("edit {FILE}")], Some("m")),
            ParseErrorKind::MalformedFileEntry { key: "edit" }
        );
        assert!(matches!(
            refuse(&[CHANGE, AUTHOR, WHEN, &format!("drop {A}")], Some("m")),
            ParseErrorKind::MalformedFileId { .. }
        ));
        // A digest where a file ID belongs, and the other way round.
        assert!(matches!(
            refuse(
                &[CHANGE, AUTHOR, WHEN, &format!("edit {FILE} {OTHER_FILE}")],
                Some("m")
            ),
            ParseErrorKind::MalformedDigest { .. }
        ));
    }

    #[test]
    fn the_digest_is_the_digest_of_the_file() {
        // Known-answer check against `shasum -a 256` output for the empty input.
        assert_eq!(
            digest(b"").to_string(),
            "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
        );
        let document = accept(&[CHANGE, AUTHOR, WHEN], Some("m"));
        assert_eq!(document.id(), digest(&document.write()));
    }
}
