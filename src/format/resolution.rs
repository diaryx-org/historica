//! The readable resolution document: a merge's file, stated whole.
//!
//! Specified by `docs/decisions/0032-a-merge-states-its-resolution.md`. Where
//! a merge revision's parents disagree about a file, the revision's `edit`
//! line names one of these instead of an operation document:
//!
//! ```text
//! historica
//! result 4c6508965080889a0cd0250e5816021ff3b87c1c95891251f9642b67c42c8137
//!
//! keep 8f7256f6a3a4ff6c962ae60514119b901251d6264f3f61e1b8181edfe9e23b1c 0 13
//! insert
//! +the line the person wrote while resolving
//! keep 6da043726d44dd4e5790a415fb5a60ab645bc94f84c2641822d86b9ed3b6fefd 3 5
//! ```
//!
//! A `keep` takes a run of items from an existing document — the items 0007
//! already names `(R, i)`, counted in document order — and an `insert` mints
//! new ones. The assembled sequence *is* the file: no positions, no parent
//! state, no algorithm, concatenation. References rather than restated bytes
//! is the decision's load-bearing choice — a kept item survives under its own
//! name, so a later merge reaching across this one meets each line once.
//!
//! Reading is as strict as the operation document's and for the same reason:
//! pieces are maximal — two `keep`s of one document whose ranges meet are one
//! `keep`, two `insert`s that meet are one `insert` — so exactly one byte
//! sequence parses per resolution and the digest can cover the file.

use std::fmt;

use crate::core::RevisionId;

use super::operations::{NO_NEWLINE, carriage_return, number};
use super::{
    Item, Lines, PREAMBLE, ParseError, ParseErrorKind, check_byte_order_mark, check_preamble,
    digest,
};

/// One piece of a resolved file, in file order.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Piece {
    /// A run of items kept from an existing document, under their own names.
    Keep {
        /// The document the items belong to — an operation document's digest,
        /// or a payload's for a file that arrived whole.
        document: RevisionId,
        /// The first item kept, counted in that document's insertion order.
        first: usize,
        /// How many consecutive items are kept. Never zero.
        count: usize,
    },
    /// Items this resolution mints, named `(R, i)` where `R` is this
    /// document's own digest.
    Insert {
        /// The new items, in file order. Never empty.
        items: Vec<Item>,
    },
}

/// One resolution document: a merge's file, stated whole by reference.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ResolutionDocument {
    /// The digest of the assembled file, which decision 0031 makes every
    /// content document state and this document could not omit: it is the
    /// check a hand-assembled resolution is verified by.
    pub result: RevisionId,
    /// The file, in order. Never empty.
    pub pieces: Vec<Piece>,
}

impl ResolutionDocument {
    /// Parse one resolution document from the bytes of an `.ops` file.
    pub fn parse(bytes: &[u8]) -> Result<Self, ParseError> {
        check_byte_order_mark(bytes)?;
        let text =
            std::str::from_utf8(bytes).map_err(|_| ParseError::new(0, ParseErrorKind::NotUtf8))?;
        Parser {
            lines: Lines::new(text),
        }
        .run()
    }

    /// The exact bytes of this document.
    ///
    /// `write(parse(bytes)) == bytes` for every input `parse` accepts.
    pub fn write(&self) -> Vec<u8> {
        let mut out = String::new();
        out.push_str(PREAMBLE);
        out.push('\n');
        out.push_str(&format!("result {}\n", self.result));
        out.push('\n');
        for piece in &self.pieces {
            match piece {
                Piece::Keep {
                    document,
                    first,
                    count,
                } => {
                    out.push_str(&format!("keep {document} {first} {count}\n"));
                }
                Piece::Insert { items } => {
                    out.push_str("insert\n");
                    for item in items {
                        out.push('+');
                        out.push_str(&item.text);
                        out.push('\n');
                        if !item.terminated {
                            out.push_str(NO_NEWLINE);
                            out.push('\n');
                        }
                    }
                }
            }
        }
        out.into_bytes()
    }

    /// The digest that names this document in a store.
    pub fn id(&self) -> RevisionId {
        digest(&self.write())
    }

    /// How many items the resolution's `insert` pieces mint, in order —
    /// the count `(R, i)` names run over.
    pub fn minted(&self) -> usize {
        self.pieces
            .iter()
            .map(|piece| match piece {
                Piece::Insert { items } => items.len(),
                Piece::Keep { .. } => 0,
            })
            .sum()
    }
}

impl fmt::Display for ResolutionDocument {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&String::from_utf8_lossy(&self.write()))
    }
}

/// Whether these bytes spell a resolution rather than an operation document.
///
/// The two share a preamble and a header block; what distinguishes them is
/// the body, whose first line here is a `keep` or a bare `insert` where an
/// operation document's states a position. Looking is cheap and decides which
/// strict parser the bytes are held to.
pub fn is_resolution(bytes: &[u8]) -> bool {
    let Ok(text) = std::str::from_utf8(bytes) else {
        return false;
    };
    let Some(separator) = text.find("\n\n") else {
        return false;
    };
    let body = &text[separator + 2..];
    let first = body.lines().next().unwrap_or_default();
    first.starts_with("keep ") || first == "insert"
}

struct Parser<'a> {
    lines: Lines<'a>,
}

impl Parser<'_> {
    fn run(mut self) -> Result<ResolutionDocument, ParseError> {
        let Some((line, terminated)) = self.lines.next() else {
            return Err(ParseError::new(1, ParseErrorKind::Empty));
        };
        carriage_return(line, 1)?;
        check_preamble(line, terminated)?;

        let result = self.result()?;

        match self.lines.next() {
            Some(("", _)) => {}
            _ => {
                return Err(ParseError::new(
                    self.lines.line,
                    ParseErrorKind::MissingSeparator,
                ));
            }
        }

        let pieces = self.pieces()?;
        if pieces.is_empty() {
            return Err(ParseError::new(
                self.lines.line,
                ParseErrorKind::NoOperations,
            ));
        }

        Ok(ResolutionDocument { result, pieces })
    }

    /// The mandatory `result` header.
    fn result(&mut self) -> Result<RevisionId, ParseError> {
        let mark = self.lines.mark();
        let Some((line, terminated)) = self.lines.next() else {
            return Err(ParseError::new(
                self.lines.line,
                ParseErrorKind::MissingHeader { key: "result" },
            ));
        };
        let Some(value) = line.strip_prefix("result ") else {
            self.lines.reset(mark);
            return Err(ParseError::new(
                self.lines.line + 1,
                ParseErrorKind::MissingHeader { key: "result" },
            ));
        };
        let at = self.lines.line;
        if !terminated {
            return Err(ParseError::new(at, ParseErrorKind::UnterminatedLine));
        }
        carriage_return(line, at)?;
        value.parse().map_err(|_| {
            ParseError::new(
                at,
                ParseErrorKind::MalformedDigest {
                    key: "result",
                    found: value.to_owned(),
                },
            )
        })
    }

    fn pieces(&mut self) -> Result<Vec<Piece>, ParseError> {
        let mut pieces: Vec<Piece> = Vec::new();
        while let Some((line, terminated)) = self.lines.next() {
            let at = self.lines.line;
            if !terminated {
                return Err(ParseError::new(at, ParseErrorKind::UnterminatedLine));
            }
            carriage_return(line, at)?;
            let piece = if let Some(rest) = line.strip_prefix("keep ") {
                self.keep(rest, at)?
            } else if line == "insert" {
                self.insert(at)?
            } else if let Some(rest) = line.strip_prefix("insert ") {
                return Err(ParseError::new(
                    at,
                    ParseErrorKind::ResolutionInsertWithPosition {
                        found: rest.to_owned(),
                    },
                ));
            } else {
                return Err(ParseError::new(
                    at,
                    ParseErrorKind::UnknownOperation {
                        found: line.to_owned(),
                    },
                ));
            };
            maximal(pieces.last(), &piece, at)?;
            pieces.push(piece);
        }
        Ok(pieces)
    }

    fn keep(&mut self, rest: &str, at: usize) -> Result<Piece, ParseError> {
        let mut fields = rest.split(' ');
        let (Some(document), Some(first), Some(count), None) =
            (fields.next(), fields.next(), fields.next(), fields.next())
        else {
            return Err(ParseError::new(
                at,
                ParseErrorKind::UnknownOperation {
                    found: format!("keep {rest}"),
                },
            ));
        };
        let document = document.parse().map_err(|_| {
            ParseError::new(
                at,
                ParseErrorKind::MalformedDigest {
                    key: "keep",
                    found: document.to_owned(),
                },
            )
        })?;
        let first = number(first, at)?;
        let count = number(count, at)?;
        if count == 0 {
            return Err(ParseError::new(at, ParseErrorKind::EmptyKeep));
        }
        Ok(Piece::Keep {
            document,
            first,
            count,
        })
    }

    fn insert(&mut self, at: usize) -> Result<Piece, ParseError> {
        let mut items: Vec<Item> = Vec::new();
        loop {
            let mark = self.lines.mark();
            let Some((line, terminated)) = self.lines.next() else {
                break;
            };
            if line == NO_NEWLINE {
                let Some(last) = items.last_mut() else {
                    return Err(ParseError::new(
                        self.lines.line,
                        ParseErrorKind::NoNewlineWithoutItem,
                    ));
                };
                if !terminated {
                    return Err(ParseError::new(
                        self.lines.line,
                        ParseErrorKind::UnterminatedLine,
                    ));
                }
                // Only a file's last item may lack a terminator, and whether
                // this insert is the file's end is the assembler's question;
                // the parser records the fact as stated.
                last.terminated = false;
                continue;
            }
            let Some(text) = line.strip_prefix('+') else {
                self.lines.reset(mark);
                break;
            };
            if !terminated {
                return Err(ParseError::new(
                    self.lines.line,
                    ParseErrorKind::UnterminatedLine,
                ));
            }
            items.push(Item::line(text));
        }
        if items.is_empty() {
            return Err(ParseError::new(at, ParseErrorKind::EmptyInsert));
        }
        Ok(Piece::Insert { items })
    }
}

/// Refuse a piece that should have been part of the one before it.
///
/// Two `keep`s of one document whose ranges meet are one `keep`, and two
/// `insert`s that meet are one `insert`: pieces are maximal so that one byte
/// sequence parses per resolution.
fn maximal(last: Option<&Piece>, next: &Piece, at: usize) -> Result<(), ParseError> {
    match (last, next) {
        (
            Some(Piece::Keep {
                document,
                first,
                count,
            }),
            Piece::Keep {
                document: same,
                first: continues,
                ..
            },
        ) if document == same && first + count == *continues => {
            Err(ParseError::new(at, ParseErrorKind::AdjacentKeeps))
        }
        (Some(Piece::Insert { .. }), Piece::Insert { .. }) => {
            Err(ParseError::new(at, ParseErrorKind::AdjacentInserts))
        }
        _ => Ok(()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const DIGEST: &str = "8f7256f6a3a4ff6c962ae60514119b901251d6264f3f61e1b8181edfe9e23b1c";
    const RESULT: &str = "4c6508965080889a0cd0250e5816021ff3b87c1c95891251f9642b67c42c8137";

    fn text(body: &str) -> Vec<u8> {
        format!("historica\nresult {RESULT}\n\n{body}").into_bytes()
    }

    #[test]
    fn a_resolution_parses_and_writes_back_byte_for_byte() {
        let bytes = text(&format!(
            "keep {DIGEST} 0 13\ninsert\n+a resolved line\nkeep {DIGEST} 14 2\n"
        ));
        let document = ResolutionDocument::parse(&bytes).expect("a resolution");
        assert_eq!(document.write(), bytes);
        assert_eq!(document.pieces.len(), 3);
        assert_eq!(document.minted(), 1);
        assert!(is_resolution(&bytes));
    }

    #[test]
    fn an_operation_document_is_not_mistaken_for_one() {
        assert!(!is_resolution(b"historica\n\ninsert 0\n+a\n"));
        assert!(is_resolution(&text(&format!("keep {DIGEST} 0 1\n"))));
    }

    #[test]
    fn the_preamble_and_the_result_are_mandatory() {
        let old = format!("historica-v3\nresult {RESULT}\n\nkeep {DIGEST} 0 1\n");
        assert!(matches!(
            ResolutionDocument::parse(old.as_bytes())
                .expect_err("a pre-1.0 format")
                .kind,
            ParseErrorKind::UnknownVersion { .. }
        ));
        let unstated = format!("historica\n\nkeep {DIGEST} 0 1\n");
        assert!(matches!(
            ResolutionDocument::parse(unstated.as_bytes())
                .expect_err("a resolution states its result")
                .kind,
            ParseErrorKind::MissingHeader { key: "result" }
        ));
    }

    #[test]
    fn pieces_are_maximal_and_never_empty() {
        let adjacent = text(&format!("keep {DIGEST} 0 2\nkeep {DIGEST} 2 3\n"));
        assert!(matches!(
            ResolutionDocument::parse(&adjacent)
                .expect_err("one keep")
                .kind,
            ParseErrorKind::AdjacentKeeps
        ));
        let gap = text(&format!("keep {DIGEST} 0 2\nkeep {DIGEST} 3 3\n"));
        assert!(ResolutionDocument::parse(&gap).is_ok(), "a gap is two runs");
        let touching = text("insert\n+a\ninsert\n+b\n");
        assert!(matches!(
            ResolutionDocument::parse(&touching)
                .expect_err("one insert")
                .kind,
            ParseErrorKind::AdjacentInserts
        ));
        let none = text("");
        assert!(matches!(
            ResolutionDocument::parse(&none)
                .expect_err("no pieces")
                .kind,
            ParseErrorKind::NoOperations
        ));
        let empty = text(&format!("keep {DIGEST} 0 0\n"));
        assert!(matches!(
            ResolutionDocument::parse(&empty)
                .expect_err("keeps nothing")
                .kind,
            ParseErrorKind::EmptyKeep
        ));
    }

    #[test]
    fn a_positioned_insert_is_an_operation_documents_spelling() {
        let positioned = text("insert 0\n+a\n");
        assert!(matches!(
            ResolutionDocument::parse(&positioned)
                .expect_err("no positions here")
                .kind,
            ParseErrorKind::ResolutionInsertWithPosition { .. }
        ));
    }

    #[test]
    fn an_unterminated_last_item_is_recorded_as_stated() {
        let bytes = text("insert\n+last\n\\ no newline\n");
        let document = ResolutionDocument::parse(&bytes).expect("a resolution");
        assert_eq!(document.write(), bytes);
        let Piece::Insert { items } = &document.pieces[0] else {
            panic!("an insert");
        };
        assert!(!items[0].terminated);
    }
}
