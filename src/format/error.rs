//! Rejections that name the line and the fix.
//!
//! Decision 0004 accepts the cost of a strict parser on the condition that
//! refusing is not the same as being unhelpful: every error here says where it
//! happened and what to write instead.

use std::fmt;

/// Why a document was refused.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParseError {
    /// The 1-based line, or 0 when the fault is the whole file.
    pub line: usize,
    /// What was wrong.
    pub kind: ParseErrorKind,
}

impl ParseError {
    pub(crate) fn new(line: usize, kind: ParseErrorKind) -> Self {
        Self { line, kind }
    }
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.line == 0 {
            write!(f, "{}", self.kind)
        } else {
            write!(f, "line {}: {}", self.line, self.kind)
        }
    }
}

impl std::error::Error for ParseError {}

/// The specific fault, one variant per rule a document must keep.
///
/// The first variants are rules both documents keep; the rest belong to one or
/// the other, because only one of them has headers and only one has
/// operations.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum ParseErrorKind {
    /// The file was empty.
    Empty,
    /// The file was not valid UTF-8.
    NotUtf8,
    /// The file began with a byte order mark.
    ByteOrderMark,
    /// A carriage return appeared somewhere in the file.
    CarriageReturn,
    /// A line ran to the end of the file without a newline.
    UnterminatedLine,
    /// The first line was not the preamble.
    MissingPreamble,
    /// The preamble named a format this reader does not have.
    UnknownVersion {
        /// What followed `historica-`, as spelled in the file.
        found: String,
    },
    /// A key was not lowercase letters, hyphens and dots, or held a dot with
    /// nothing on one side of it.
    MalformedKey {
        /// The key as spelled in the file.
        key: String,
    },
    /// A known-looking key this format does not define, with no dot to say whose
    /// it is.
    UnknownHeader {
        /// The key as spelled in the file.
        key: String,
    },
    /// A `mode` whose value is neither `plain` nor `executable`.
    UnknownMode {
        /// What stood where the value should be.
        found: String,
    },
    /// A `keep` that keeps nothing.
    EmptyKeep,
    /// Two `keep`s of one document whose ranges meet, which are one `keep`.
    AdjacentKeeps,
    /// Two `insert` pieces that meet, which are one `insert`.
    AdjacentInserts,
    /// An `insert` with a position, in a document that has no positions.
    ResolutionInsertWithPosition {
        /// What followed the keyword.
        found: String,
    },
    /// A `result` header in a forgetting document.
    ///
    /// Decision 0031: the result of the operations a forgetting document
    /// restates is the destroyed state, and a digest of destroyed content
    /// would let anyone who can guess the sentence confirm it.
    ResultOfForgetting,
    /// A header line carried no value.
    EmptyValue,
    /// A value had leading or trailing space.
    PaddedValue,
    /// A value contained a control character.
    ControlCharacter,
    /// A header appeared after one that must follow it.
    KeysOutOfOrder {
        /// The key that appeared too late.
        key: String,
        /// The key it wrongly followed.
        after: String,
    },
    /// A repeated key's values were not in ascending order.
    RepeatedKeyOutOfOrder {
        /// The repeated key.
        key: String,
    },
    /// One fact was stated twice.
    DuplicateFact {
        /// The repeated key.
        key: String,
    },
    /// A header that may appear once appeared again.
    RepeatedHeader {
        /// The repeated key.
        key: String,
    },
    /// A required header was absent.
    MissingHeader {
        /// The key that should have been present.
        key: &'static str,
    },
    /// A change ID was not 24 characters of `k` to `z`.
    MalformedChangeId {
        /// The value as spelled in the file.
        found: String,
    },
    /// A digest was not 64 lowercase hexadecimal characters.
    MalformedDigest {
        /// The key whose value was wrong.
        key: &'static str,
        /// The value as spelled in the file.
        found: String,
    },
    /// A timestamp was not `YYYY-MM-DDThh:mm:ss±hh:mm`.
    MalformedTimestamp {
        /// The value as spelled in the file.
        found: String,
        /// What specifically was wrong with it.
        because: &'static str,
    },
    /// `revised` or `revised-by` appeared on a revision with no predecessors.
    RevisionMetadataWithoutSupersedes {
        /// The key that should not have been there.
        key: &'static str,
    },
    /// `revised-by` repeated the author.
    RedundantRevisedBy,
    /// A separator with nothing after it.
    EmptyBodyAfterSeparator,
    /// A tree header that did not carry both of its fields.
    MalformedFileEntry {
        /// The header whose line was wrong.
        key: &'static str,
    },
    /// A file identifier was not 24 characters of `k` to `z`.
    MalformedFileId {
        /// The value as spelled in the file.
        found: String,
    },
    /// A path broke one of decision 0008's rules.
    MalformedPath {
        /// The path as spelled in the file.
        found: String,
        /// What specifically was wrong with it.
        because: &'static str,
    },
    /// One header said two things about one file.
    FileStatedTwice {
        /// The header that repeated itself.
        key: &'static str,
        /// The file both lines named.
        file: String,
    },
    /// `text` named a file the revision does not add.
    TextWithoutAdd {
        /// The file it named.
        file: String,
    },
    /// Two headers said things about one file that cannot both hold.
    ContradictoryFileFacts {
        /// The header that came first.
        first: &'static str,
        /// The header that contradicts it.
        second: &'static str,
        /// The file both name.
        file: String,
    },
    /// An operation document without the blank line that follows its preamble.
    MissingSeparator,
    /// An operation document that records no operation.
    NoOperations,
    /// A line that is neither an operation nor content.
    UnknownOperation {
        /// The line as spelled in the file.
        found: String,
    },
    /// An operation line with the wrong number of fields.
    MalformedOperation {
        /// The keyword whose line was wrong.
        keyword: &'static str,
    },
    /// A position or count that was not a plain decimal number.
    MalformedNumber {
        /// The field as spelled in the file.
        found: String,
    },
    /// A `delete` that removes nothing.
    EmptyDelete,
    /// An `insert` that adds nothing.
    EmptyInsert,
    /// A `delete` whose count and `-` lines disagree.
    DeleteCountDisagrees {
        /// What the `delete` line said.
        stated: usize,
        /// How many `-` lines followed it.
        found: usize,
    },
    /// A `-` or `+` line with no operation above it.
    ContentWithoutOperation {
        /// The prefix byte the line opened with.
        prefix: char,
    },
    /// An operation whose position is behind the one before it.
    OperationsOutOfOrder {
        /// This operation's position.
        position: usize,
        /// The position it wrongly followed.
        after: usize,
    },
    /// An operation that begins inside the region of the one before it.
    OverlappingOperations {
        /// This operation's position.
        position: usize,
    },
    /// Two `delete` operations that meet, which remove one run.
    AdjacentDeletes {
        /// Where the merged run begins.
        at: usize,
        /// How many items the merged run removes.
        total: usize,
    },
    /// A `delete` written after an `insert` at one position.
    DeleteAfterInsert {
        /// The contested position.
        position: usize,
    },
    /// Two `insert` operations at one position, which are one insert.
    InsertsAtOnePosition {
        /// The contested position.
        position: usize,
    },
    /// A carriage return in an operation document's own line.
    CarriageReturnInOperation,
    /// A `\ no newline` marker with no item above it.
    NoNewlineWithoutItem,
    /// A `\ no newline` marker on an item that is not the file's last.
    NoNewlineNotLast {
        /// The prefix byte of the items it should have marked the last of.
        prefix: char,
    },
}

impl fmt::Display for ParseErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use ParseErrorKind::*;
        match self {
            Empty => write!(
                f,
                "a Historica document is never empty; it opens with `{}`",
                super::PREAMBLE
            ),
            NotUtf8 => write!(
                f,
                "a Historica document is UTF-8; re-save this file as UTF-8"
            ),
            ByteOrderMark => write!(
                f,
                "a byte order mark is part of the digest; delete the first three bytes"
            ),
            CarriageReturn => write!(
                f,
                "carriage returns change a revision's identity; save this file with LF endings"
            ),
            UnterminatedLine => write!(
                f,
                "every line the parser reads ends with a newline; add one"
            ),
            MissingPreamble => write!(
                f,
                "a Historica document opens with `{}`; add it as the first line",
                super::PREAMBLE
            ),
            UnknownVersion { found } => match found.as_str() {
                "v0" | "v1" | "v2" | "v3" | "v4" | "v5" => write!(
                    f,
                    "this document is `historica-{found}`, a pre-1.0 format this \
                     release no longer reads; a 0.x Historica still reads it"
                ),
                _ => write!(
                    f,
                    "this document is `historica-{found}` and this reader reads \
                     `{}`; upgrade Historica rather than trusting what it would \
                     leave out",
                    super::PREAMBLE
                ),
            },
            EmptyKeep => write!(
                f,
                "a `keep` that keeps nothing states nothing; delete the line"
            ),
            AdjacentKeeps => write!(
                f,
                "two `keep`s of one document whose ranges meet are one `keep`; \
                 join them, so that one byte sequence spells this resolution"
            ),
            AdjacentInserts => write!(
                f,
                "two `insert`s that meet are one `insert`; join them, so that \
                 one byte sequence spells this resolution"
            ),
            ResolutionInsertWithPosition { found } => write!(
                f,
                "a resolution's `insert` takes no position — the pieces are \
                 the file, in order — and `insert {found}` states one; \
                 delete the number"
            ),
            ResultOfForgetting => write!(
                f,
                "a forgetting document states no result: a digest of the \
                 destroyed state would confirm a guess at what was destroyed; \
                 delete the line"
            ),
            MalformedKey { key } => write!(
                f,
                "`{key}` is not a key: keys are lowercase letters and hyphens, and \
                 a dot separates a tool's name from what it named, as in \
                 `diaryx.review-url`"
            ),
            UnknownHeader { key } => write!(
                f,
                "`{key}` is not a header this format knows; \
                 spell it `<tool>.{key}` if a reader may ignore it, or upgrade \
                 Historica if not"
            ),
            UnknownMode { found } => write!(
                f,
                "`{found}` is not a mode; a file is `plain` or `executable`, \
                 and decision 0034 carries no other bit"
            ),
            EmptyValue => write!(
                f,
                "a header with no value is an absent fact spelled ambiguously; \
                 delete the line or give it a value"
            ),
            PaddedValue => write!(f, "a value has no leading or trailing space; trim it"),
            ControlCharacter => write!(f, "a value holds no control characters; remove it"),
            KeysOutOfOrder { key, after } => write!(
                f,
                "`{key}` comes before `{after}` in the fixed key order; move the line up"
            ),
            RepeatedKeyOutOfOrder { key } => write!(
                f,
                "repeated `{key}` lines are sorted; move this one above the line before it"
            ),
            DuplicateFact { key } => {
                write!(
                    f,
                    "this `{key}` line states a fact already stated; delete it"
                )
            }
            RepeatedHeader { key } => {
                write!(
                    f,
                    "`{key}` appears once in a revision; delete the second line"
                )
            }
            MissingHeader { key } => match *key {
                "result" => write!(
                    f,
                    "a content document states the digest of the file it produces; \
                     add the `result` line — `shasum -a 256` on that file prints it"
                ),
                key => write!(f, "a revision states `{key}`; add the line"),
            },
            MalformedChangeId { found } => write!(
                f,
                "`{found}` is not a change ID: {} characters of `k` to `z`, \
                 an alphabet no digest can be mistaken for; \
                 copy the change ID this work already has, or mint a new one",
                super::CHANGE_ID_CHARS
            ),
            MalformedDigest { key, found } => match *key {
                "text" | "bytes" => write!(
                    f,
                    "`{key}` names content by digest, and `{found}` is not \
                     64 lowercase hexadecimal characters; \
                     `shasum -a 256` on the file you mean prints the right one"
                ),
                key => write!(
                    f,
                    "`{key}` names a revision by digest, and `{found}` is not \
                     64 lowercase hexadecimal characters; \
                     `shasum -a 256` on the revision you mean prints the right one"
                ),
            },
            MalformedTimestamp { found, because } => write!(
                f,
                "`{found}` is not a timestamp ({because}); \
                 write `YYYY-MM-DDThh:mm:ss±hh:mm`"
            ),
            RevisionMetadataWithoutSupersedes { key } => write!(
                f,
                "`{key}` describes a rewrite, and this revision supersedes nothing; \
                 delete the line"
            ),
            RedundantRevisedBy => write!(
                f,
                "`revised-by` repeats the author, which is a second spelling of one fact; \
                 delete the line"
            ),
            EmptyBodyAfterSeparator => write!(
                f,
                "an empty message is spelled with no blank line at all; \
                 delete the blank line"
            ),
            TextWithoutAdd { file } => write!(
                f,
                "`text` states the lines a file is created with, and this revision \
                 does not add the file {file}; \
                 write `edit` against the file as it stands, or `add` it here"
            ),
            MalformedFileEntry { key } => match *key {
                "edit" => write!(
                    f,
                    "`edit` names a file and the digest of its operation document; \
                     write both, separated by one space"
                ),
                "text" | "bytes" => write!(
                    f,
                    "`{key}` names a file and the digest of its content; \
                     write both, separated by one space"
                ),
                key => write!(
                    f,
                    "`{key}` names a file and a path; write both, separated by one space"
                ),
            },
            MalformedFileId { found } => write!(
                f,
                "`{found}` is not a file ID: {} characters of `k` to `z`, \
                 the same alphabet a change ID uses and no digest can be mistaken for; \
                 copy the ID this file already has, or mint a new one",
                super::CHANGE_ID_CHARS
            ),
            MalformedPath { found, because } => write!(
                f,
                "`{found}` is not a path ({because}); \
                 write components separated by `/`, relative to the repository root"
            ),
            FileStatedTwice { key, file } => write!(
                f,
                "two `{key}` lines name the file {file}, which states one fact twice; \
                 delete one of them"
            ),
            ContradictoryFileFacts {
                first,
                second,
                file,
            } => write!(
                f,
                "the file {file} is named by both `{first}` and `{second}` in one revision, \
                 and they cannot both hold; keep the one that says what happened"
            ),
            MissingSeparator => write!(
                f,
                "an operation document is a preamble, a blank line, and operations; \
                 add the blank line"
            ),
            NoOperations => write!(
                f,
                "a revision that changes nothing about a file names no operation document; \
                 write what this one did, or delete the file and the line that names it"
            ),
            UnknownOperation { found } => write!(
                f,
                "`{found}` is not an operation; \
                 write `delete P N`, `insert P`, `-item`, `+item`, or `{}`",
                super::NO_NEWLINE
            ),
            MalformedOperation { keyword } => match *keyword {
                "delete" => write!(
                    f,
                    "`delete` takes a position and a count, as in `delete 3 1`; \
                     write both, separated by one space"
                ),
                _ => write!(
                    f,
                    "`insert` takes one position, as in `insert 4`; \
                     the items follow on their own lines"
                ),
            },
            MalformedNumber { found } => write!(
                f,
                "`{found}` is not a position: decimal digits, no sign, and no leading zero, \
                 counted from zero into the parent; write it plainly"
            ),
            EmptyDelete => write!(
                f,
                "a `delete` removes at least one item, and one that removes none is \
                 an absent fact spelled out loud; delete the line"
            ),
            EmptyInsert => write!(
                f,
                "an `insert` adds at least one item; add a `+` line, or delete the `insert`"
            ),
            DeleteCountDisagrees { stated, found } => write!(
                f,
                "this `delete` states {stated} items and {found} follow it; \
                 the `-` lines are what a reader checks the count against, so make them agree"
            ),
            ContentWithoutOperation { prefix } => write!(
                f,
                "a `{prefix}` line is content and belongs to the operation above it, \
                 and there is none; add the `delete` or `insert` line"
            ),
            OperationsOutOfOrder { position, after } => write!(
                f,
                "operations are written in ascending position order, and {position} \
                 follows {after}; move this operation up"
            ),
            OverlappingOperations { position } => write!(
                f,
                "operations describe separate regions of the parent, and this one starts \
                 at {position}, inside the region above it; merge the two, or move this one \
                 past the end of that region"
            ),
            AdjacentDeletes { at, total } => write!(
                f,
                "these two `delete` lines remove one unbroken run, which is one fact; \
                 write them as `delete {at} {total}`"
            ),
            DeleteAfterInsert { position } => write!(
                f,
                "at position {position} a `delete` is written before an `insert`, the way \
                 every diff spells a replacement; move the `delete` and its `-` lines up"
            ),
            InsertsAtOnePosition { position } => write!(
                f,
                "two `insert` lines at position {position} are one insert; \
                 merge their `+` lines into the first"
            ),
            CarriageReturnInOperation => write!(
                f,
                "a carriage return in the format's own line changes this document's identity; \
                 delete it — a `-` or `+` line may hold one, because that is content"
            ),
            NoNewlineWithoutItem => write!(
                f,
                "`{}` describes the line above it, and there is none; delete it",
                super::NO_NEWLINE
            ),
            NoNewlineNotLast { prefix } => write!(
                f,
                "`{}` marks a file's last line, and `{prefix}` lines come after this one; \
                 move it under the last of them, or delete it",
                super::NO_NEWLINE
            ),
        }
    }
}
