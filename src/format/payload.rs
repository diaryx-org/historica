//! The forgetting document that stands in for a payload of bytes.
//!
//! Specified by `docs/decisions/0066-forgetting-a-payload.md`, and shaped by
//! decision 0017, which wrote it out before anything could parse it:
//!
//! ```text
//! historica
//! forgets e10f37c2a3b7e4d1c5f9082a6b4d3e1f7c8a9b0d2e3f4a5b6c7d8e9f0a1b2c3d
//! length 2418573
//! ```
//!
//! Decision 0014 destroys payload and preserves shape. A file of lines has a
//! shape worth a whole grammar — positions, counts, terminators, and a marker
//! per destroyed item — because every one of those numbers is what replay and
//! merge read. A file of bytes has none of them: decision 0017 gives it no
//! items, no grammar, and no operation chain, so all the shape it has is how
//! much of it there was. That is the whole document, and its brevity is the
//! decision rather than an omission.
//!
//! It is a document like any other: it opens with the preamble, it is stored
//! under the digest of its own bytes, and it is named by nothing — a
//! revision's `bytes` line still names the payload whose bytes were
//! destroyed, and a reader that cannot find that payload looks for a document
//! that says it `forgets` it.

use std::fmt;

use crate::core::RevisionId;

use super::operations::{carriage_return, number};
use super::{
    Lines, PREAMBLE, ParseError, ParseErrorKind, check_byte_order_mark, check_preamble, digest,
};

/// One forgetting document for a payload: what stood here, and how much of it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ForgottenPayload {
    /// The payload whose bytes were destroyed.
    pub forgets: RevisionId,
    /// How many bytes it held.
    ///
    /// Shape, which decision 0014 keeps: a file's length is already visible
    /// in what its revision says about it, and destroying it would buy
    /// nothing a person could rely on. What it buys instead is an answer —
    /// `check`, `update`, and `cat` can say how much was destroyed rather
    /// than only that something was.
    pub length: usize,
}

impl ForgottenPayload {
    /// Parse one forgetting document for a payload.
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
    /// `write(parse(bytes)) == bytes` for every input `parse` accepts. There
    /// is nothing here to sort and nothing optional, so two replicas that
    /// forget one payload write one file, byte for byte, and the store holds
    /// their redaction once.
    pub fn write(&self) -> Vec<u8> {
        format!(
            "{PREAMBLE}\nforgets {}\nlength {}\n",
            self.forgets, self.length
        )
        .into_bytes()
    }

    /// The digest that names this document in a store.
    pub fn id(&self) -> RevisionId {
        digest(&self.write())
    }
}

impl fmt::Display for ForgottenPayload {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&String::from_utf8_lossy(&self.write()))
    }
}

/// Whether these bytes spell a forgotten payload rather than either of the
/// document grammars that state operations.
///
/// The `length` header is what says so, and it is a header no other document
/// carries. Looking for it is cheap and decides which strict parser the bytes
/// are held to — the same dispatch decision 0032 made for a resolution, and
/// for the same reason: one directory, one suffix, and the file itself saying
/// which grammar it is written in.
pub fn is_forgotten_payload(bytes: &[u8]) -> bool {
    let Ok(text) = std::str::from_utf8(bytes) else {
        return false;
    };
    let mut lines = text.lines();
    if lines.next() != Some(PREAMBLE) {
        return false;
    }
    lines
        .take_while(|line| !line.is_empty())
        .any(|line| line.starts_with("length "))
}

struct Parser<'a> {
    lines: Lines<'a>,
}

impl Parser<'_> {
    fn run(mut self) -> Result<ForgottenPayload, ParseError> {
        let Some((line, terminated)) = self.lines.next() else {
            return Err(ParseError::new(1, ParseErrorKind::Empty));
        };
        carriage_return(line, 1)?;
        check_preamble(line, terminated)?;

        let mut forgets: Option<RevisionId> = None;
        let mut length: Option<usize> = None;
        while let Some((line, terminated)) = self.lines.next() {
            let at = self.lines.line;
            if !terminated {
                return Err(ParseError::new(at, ParseErrorKind::UnterminatedLine));
            }
            carriage_return(line, at)?;
            // The blank line every other document in `operations/` carries,
            // separating headers from a body. There is no body here, so
            // there is nothing for it to separate.
            if line.is_empty() {
                return Err(ParseError::new(
                    at,
                    ParseErrorKind::ForgottenPayloadWithBody,
                ));
            }
            let (key, value) = match line.split_once(' ') {
                Some((key, value)) => (key, value),
                None => (line, ""),
            };
            if value.is_empty() {
                return Err(ParseError::new(at, ParseErrorKind::EmptyValue));
            }
            match key {
                "forgets" => {
                    if forgets.is_some() {
                        return Err(ParseError::new(
                            at,
                            ParseErrorKind::RepeatedHeader {
                                key: key.to_owned(),
                            },
                        ));
                    }
                    if length.is_some() {
                        return Err(ParseError::new(
                            at,
                            ParseErrorKind::KeysOutOfOrder {
                                key: key.to_owned(),
                                after: "length".to_owned(),
                            },
                        ));
                    }
                    forgets = Some(value.parse().map_err(|_| {
                        ParseError::new(
                            at,
                            ParseErrorKind::MalformedDigest {
                                key: "forgets",
                                found: value.to_owned(),
                            },
                        )
                    })?);
                }
                "length" => {
                    if length.is_some() {
                        return Err(ParseError::new(
                            at,
                            ParseErrorKind::RepeatedHeader {
                                key: key.to_owned(),
                            },
                        ));
                    }
                    length = Some(number(value, at)?);
                }
                // Decision 0031's rule, arriving where there is even less to
                // state: the bytes are gone, so the only digest this document
                // could carry is the one a person destroyed them to withhold.
                "result" => return Err(ParseError::new(at, ParseErrorKind::ResultOfForgetting)),
                other => {
                    return Err(ParseError::new(
                        at,
                        ParseErrorKind::UnknownHeader {
                            key: other.to_owned(),
                        },
                    ));
                }
            }
        }
        let at = self.lines.line;
        let Some(forgets) = forgets else {
            return Err(ParseError::new(
                at,
                ParseErrorKind::MissingHeader { key: "forgets" },
            ));
        };
        let Some(length) = length else {
            return Err(ParseError::new(
                at,
                ParseErrorKind::MissingHeader { key: "length" },
            ));
        };
        Ok(ForgottenPayload { forgets, length })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn digest_of(text: &str) -> RevisionId {
        digest(text.as_bytes())
    }

    #[test]
    fn a_forgotten_payload_round_trips() {
        let document = ForgottenPayload {
            forgets: digest_of("a photograph"),
            length: 2_418_573,
        };
        let bytes = document.write();
        assert_eq!(
            ForgottenPayload::parse(&bytes).expect("a document"),
            document
        );
        assert!(is_forgotten_payload(&bytes));
        assert_eq!(
            String::from_utf8(bytes).expect("text"),
            format!(
                "historica\nforgets {}\nlength 2418573\n",
                digest_of("a photograph")
            )
        );
    }

    #[test]
    fn an_empty_payload_has_a_length_and_is_still_one() {
        let document = ForgottenPayload {
            forgets: digest_of(""),
            length: 0,
        };
        assert_eq!(
            ForgottenPayload::parse(&document.write()).expect("a document"),
            document
        );
    }

    #[test]
    fn the_two_headers_are_both_required_and_in_order() {
        let forgets = digest_of("a photograph");
        for (text, expected) in [
            (
                "historica\nlength 4\n".to_owned(),
                ParseErrorKind::MissingHeader { key: "forgets" },
            ),
            (
                format!("historica\nlength 4\nforgets {forgets}\n"),
                ParseErrorKind::KeysOutOfOrder {
                    key: "forgets".to_owned(),
                    after: "length".to_owned(),
                },
            ),
            (
                format!("historica\nforgets {forgets}\nlength 04\n"),
                ParseErrorKind::MalformedNumber {
                    found: "04".to_owned(),
                },
            ),
            (
                format!("historica\nforgets {forgets}\nlength 4\n\ninsert 0\n+a\n"),
                ParseErrorKind::ForgottenPayloadWithBody,
            ),
            (
                format!("historica\nforgets {forgets}\nlength 4\nresult {forgets}\n"),
                ParseErrorKind::ResultOfForgetting,
            ),
        ] {
            let error = ForgottenPayload::parse(text.as_bytes())
                .map(|document| format!("{document:?}"))
                .expect_err(&format!("`{text}` should not parse"));
            assert_eq!(error.kind, expected, "`{text}` failed for the wrong reason");
        }
    }
}
