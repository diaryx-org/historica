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

use super::operations::{FORGOTTEN, NO_NEWLINE, carriage_return, number};
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
    /// The resolution this one stands in for, whose bytes were destroyed.
    ///
    /// Decision 0014, reaching the second grammar. A `keep` carries a
    /// reference and no text, so there is nothing in it to destroy; what a
    /// resolution holds of its own is the items its `insert` pieces mint, and
    /// those are the only text a merge ever states that exists nowhere else.
    /// A forgetting resolution states the same pieces, keeping every `keep`
    /// exactly and every `insert`'s length, with the items it forgets
    /// replaced by a marker.
    pub forgets: Option<RevisionId>,
    /// The digest of the assembled file, which decision 0031 makes every
    /// content document state: it is the check a hand-assembled resolution is
    /// verified by. Present in every resolution this tool writes, and
    /// forbidden in a forgetting one, whose assembled file is the destroyed
    /// state and whose digest would confirm a guess at it.
    pub result: Option<RevisionId>,
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
        if let Some(forgets) = &self.forgets {
            out.push_str(&format!("forgets {forgets}\n"));
        }
        if let Some(result) = &self.result {
            out.push_str(&format!("result {result}\n"));
        }
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
                        if item.forgotten {
                            // The marker stands where the `+` line stood, one
                            // per destroyed item: shape without payload.
                            out.push_str(FORGOTTEN);
                        } else {
                            out.push('+');
                            out.push_str(&item.text);
                        }
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

        // The same two headers an operation document may carry, read in the
        // same order: which document this one stands in for (decision 0014),
        // and the digest of the file it assembles (decision 0031).
        let forgets = self.forgets()?;
        let result = self.result(forgets.is_some())?;

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

        Ok(ResolutionDocument {
            forgets,
            result,
            pieces,
        })
    }

    /// The `forgets` header, if the next line is one.
    fn forgets(&mut self) -> Result<Option<RevisionId>, ParseError> {
        let mark = self.lines.mark();
        let Some((line, terminated)) = self.lines.next() else {
            return Ok(None);
        };
        let Some(value) = line.strip_prefix("forgets ") else {
            self.lines.reset(mark);
            return Ok(None);
        };
        let at = self.lines.line;
        if !terminated {
            return Err(ParseError::new(at, ParseErrorKind::UnterminatedLine));
        }
        carriage_return(line, at)?;
        let forgets = value.parse().map_err(|_| {
            ParseError::new(
                at,
                ParseErrorKind::MalformedDigest {
                    key: "forgets",
                    found: value.to_owned(),
                },
            )
        })?;
        Ok(Some(forgets))
    }

    /// The `result` header, mandatory unless this resolution forgets one.
    ///
    /// Decision 0031's rule, said of the second grammar: a resolution states
    /// the digest of the file it assembles, and a forgetting one must not,
    /// because that file is the destroyed state and a digest would confirm a
    /// guess at it.
    fn result(&mut self, forgetting: bool) -> Result<Option<RevisionId>, ParseError> {
        let mark = self.lines.mark();
        let next = self.lines.next();
        let Some((line, terminated)) = next else {
            return if forgetting {
                Ok(None)
            } else {
                Err(ParseError::new(
                    self.lines.line,
                    ParseErrorKind::MissingHeader { key: "result" },
                ))
            };
        };
        let Some(value) = line.strip_prefix("result ") else {
            self.lines.reset(mark);
            return if forgetting {
                Ok(None)
            } else {
                Err(ParseError::new(
                    self.lines.line + 1,
                    ParseErrorKind::MissingHeader { key: "result" },
                ))
            };
        };
        let at = self.lines.line;
        if !terminated {
            return Err(ParseError::new(at, ParseErrorKind::UnterminatedLine));
        }
        carriage_return(line, at)?;
        if forgetting {
            return Err(ParseError::new(at, ParseErrorKind::ResultOfForgetting));
        }
        let result = value.parse().map_err(|_| {
            ParseError::new(
                at,
                ParseErrorKind::MalformedDigest {
                    key: "result",
                    found: value.to_owned(),
                },
            )
        })?;
        Ok(Some(result))
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
            // Decision 0014: the marker stands where the `+` line stood, one
            // per destroyed item, so here it is one item. A `\ no newline`
            // after it still applies to it, because a terminator is shape.
            if line == FORGOTTEN {
                if !terminated {
                    return Err(ParseError::new(
                        self.lines.line,
                        ParseErrorKind::UnterminatedLine,
                    ));
                }
                items.push(Item::forgotten());
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

/// The resolution a reader consumes for one digest, given what the store holds.
///
/// Decision 0014's union rule, said of the second grammar and word for word
/// the same: **an item is forgotten if any held forgetting resolution forgets
/// it.** Monotone, order-independent, idempotent, and it fails safe, so a
/// stale replica syncing back a less thorough redaction cannot un-forget
/// anything.
///
/// `base` is the original where the store still holds it; with the original
/// destroyed, the first forgetting resolution is the shape and the rest union
/// into it. One whose shape disagrees is set aside rather than merged, and
/// `check` is where that is reported.
pub fn stand_in(
    base: Option<&ResolutionDocument>,
    forgetting: &[&ResolutionDocument],
) -> Option<ResolutionDocument> {
    let mut effective = match base {
        Some(document) => document.clone(),
        None => (*forgetting.first()?).clone(),
    };
    for document in forgetting {
        if !same_shape(&effective, document) {
            continue;
        }
        for (stated, held) in document.pieces.iter().zip(&mut effective.pieces) {
            let (Piece::Insert { items: stated }, Piece::Insert { items: held }) = (stated, held)
            else {
                continue;
            };
            for (item, kept) in stated.iter().zip(held) {
                if item.forgotten && !kept.forgotten {
                    *kept = kept.forgetting();
                }
            }
        }
    }
    Some(effective)
}

/// Whether two resolutions state the same pieces, minted payload aside.
///
/// Shape here is more than an operation document's, and more easily checked:
/// a `keep` is a reference and no text at all, so it must match exactly, and
/// an `insert` must mint the same number of items with the same terminators.
/// The items' text is what a redaction destroys and the only thing it may
/// differ in.
fn same_shape(left: &ResolutionDocument, right: &ResolutionDocument) -> bool {
    left.pieces.len() == right.pieces.len()
        && left
            .pieces
            .iter()
            .zip(&right.pieces)
            .all(|(mine, theirs)| match (mine, theirs) {
                (Piece::Keep { .. }, Piece::Keep { .. }) => mine == theirs,
                (Piece::Insert { items: mine }, Piece::Insert { items: theirs }) => {
                    mine.len() == theirs.len()
                        && mine
                            .iter()
                            .zip(theirs)
                            .all(|(a, b)| a.terminated == b.terminated)
                }
                _ => false,
            })
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

    /// Decision 0014 reaching this grammar: a `keep` carries a reference and
    /// no text, so what a resolution has of its own to destroy is exactly the
    /// items its `insert` pieces mint.
    #[test]
    fn a_forgetting_resolution_round_trips() {
        let bytes = format!(
            "historica\nforgets {DIGEST}\n\nkeep {DIGEST} 0 2\ninsert\n\\ forgotten\n+kept\n"
        )
        .into_bytes();
        let document = ResolutionDocument::parse(&bytes).expect("a forgetting resolution");
        assert_eq!(document.write(), bytes);
        assert_eq!(document.forgets, Some(DIGEST.parse().unwrap()));
        assert_eq!(document.result, None);
        assert!(is_resolution(&bytes));
        let Piece::Insert { items } = &document.pieces[1] else {
            panic!("an insert");
        };
        assert!(items[0].forgotten && items[0].text.is_empty());
        assert!(!items[1].forgotten);
        // The marker is one item, so the names a `keep` quotes do not move.
        assert_eq!(document.minted(), 2);
    }

    /// Decision 0031's rule, and 0014's reason for it: the file a forgetting
    /// resolution assembles is the destroyed state, and a digest of it would
    /// confirm a guess at what was destroyed.
    #[test]
    fn a_forgetting_resolution_may_not_state_a_result() {
        let bytes = format!("historica\nforgets {DIGEST}\nresult {RESULT}\n\nkeep {DIGEST} 0 1\n")
            .into_bytes();
        assert!(matches!(
            ResolutionDocument::parse(&bytes)
                .expect_err("a result beside a forgets")
                .kind,
            ParseErrorKind::ResultOfForgetting
        ));
        // And an ordinary resolution still must state one.
        let bare = b"historica\n\nkeep 0 1\n";
        assert!(ResolutionDocument::parse(bare).is_err());
    }

    /// The union rule, word for word decision 0014's: an item is forgotten if
    /// any held forgetting resolution forgets it, so two replicas that redact
    /// differently converge whichever order they meet in.
    #[test]
    fn redactions_union_whichever_order_they_arrive_in() {
        let bytes =
            format!("historica\nresult {RESULT}\n\ninsert\n+one\n+two\n+three\n").into_bytes();
        let held = ResolutionDocument::parse(&bytes).expect("a resolution");
        let forgetting = |which: &[usize]| {
            let mut document = held.clone();
            document.forgets = Some(held.id());
            document.result = None;
            let Piece::Insert { items } = &mut document.pieces[0] else {
                panic!("an insert");
            };
            for at in which {
                items[*at] = items[*at].forgetting();
            }
            document
        };
        let (first, second) = (forgetting(&[1]), forgetting(&[2]));
        let one_way = stand_in(Some(&held), &[&first, &second]).expect("a stand-in");
        let other_way = stand_in(Some(&held), &[&second, &first]).expect("a stand-in");
        assert_eq!(one_way, other_way);
        let Piece::Insert { items } = &one_way.pieces[0] else {
            panic!("an insert");
        };
        assert!(!items[0].forgotten && items[1].forgotten && items[2].forgotten);
        // With the original destroyed, the first stand-in is the shape and
        // the rest union into it — so the pieces agree, and the headers are
        // the ones a stand-in carries rather than the ones a base did.
        let destroyed = stand_in(None, &[&first, &second]).expect("a stand-in");
        assert_eq!(destroyed.pieces, one_way.pieces);
        assert_eq!(destroyed.forgets, Some(held.id()));
        assert_eq!(destroyed.result, None);
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
