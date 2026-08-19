//! Rejections that name the line and the fix.
//!
//! Decision 0004 accepts the cost of a strict parser on the condition that
//! refusing is not the same as being unhelpful: every error here says where it
//! happened and what to write instead.

use std::fmt;

/// Why a revision document was refused.
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

/// The specific fault, one variant per rule a revision document must keep.
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
    /// The preamble named a version this reader does not have.
    UnknownVersion {
        /// The version as spelled in the file.
        found: String,
    },
    /// A key was not lowercase letters and hyphens.
    MalformedKey {
        /// The key as spelled in the file.
        key: String,
    },
    /// A known-looking key this version does not define, without the `x-` prefix.
    UnknownHeader {
        /// The key as spelled in the file.
        key: String,
    },
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
}

impl fmt::Display for ParseErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use ParseErrorKind::*;
        match self {
            Empty => write!(
                f,
                "a revision document is never empty; it opens with `{}`",
                super::PREAMBLE
            ),
            NotUtf8 => write!(
                f,
                "a revision document is UTF-8; re-save this file as UTF-8"
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
                "every line above the message ends with a newline; add one"
            ),
            MissingPreamble => write!(
                f,
                "a revision document opens with `{}`; add it as the first line",
                super::PREAMBLE
            ),
            UnknownVersion { found } => write!(
                f,
                "this revision is version {found} and this is a version 0 reader; \
                 upgrade Historica rather than trusting what it would leave out"
            ),
            MalformedKey { key } => write!(
                f,
                "`{key}` is not a key: keys are lowercase letters and hyphens; \
                 check the spelling"
            ),
            UnknownHeader { key } => write!(
                f,
                "`{key}` is not a header this version knows; \
                 spell it `x-{key}` if a reader may ignore it, or upgrade Historica if not"
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
            MissingHeader { key } => write!(f, "a revision states `{key}`; add the line"),
            MalformedChangeId { found } => write!(
                f,
                "`{found}` is not a change ID: {} characters of `k` to `z`, \
                 an alphabet no digest can be mistaken for; \
                 copy the change ID this work already has, or mint a new one",
                super::CHANGE_ID_CHARS
            ),
            MalformedDigest { key, found } => write!(
                f,
                "`{key}` names a revision by digest, and `{found}` is not \
                 64 lowercase hexadecimal characters; \
                 `shasum -a 256` on the revision you mean prints the right one"
            ),
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
        }
    }
}
