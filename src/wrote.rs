//! What a command wrote, as a statement of where to look.
//!
//! Decision 0074. A writing command run with `--fields` prints one of these
//! instead of the sentences 0021 wrote for a person: a `historica-wrote-1`
//! header, then a line per thing the store now holds or no longer holds.
//!
//! ```text
//! historica-wrote-1
//! revision <digest>
//! name <bookmark>
//! unname <bookmark>
//! gone <digest>
//! ```
//!
//! Every line is a pointer rather than a report — *where to look*, never what
//! the thing says. `revision` names a document now in `revisions/`, `name` a
//! bookmark now in `names/`, `unname` one that was removed, and `gone` a digest
//! something destroyed. Nothing a document states is restated here, because the
//! document is the authority and is one read away.
//!
//! That makes the whole of this output derivable from the store, with one
//! exception which is the reason it exists: a statement with no lines under its
//! header says *nothing was written*, and a store nobody wrote to looks exactly
//! like a store that did not change.
//!
//! The writer and the parser are here, together, and the `historica` binary
//! calls them rather than holding its own. Decision 0053: a tool beside this
//! one gets what it needs from the API, rather than writing a second
//! implementation of a grammar we own — and a parser inside the command-line
//! front end is a parser they could not link.

use std::collections::BTreeSet;
use std::collections::btree_set;
use std::fmt;
use std::io;
use std::str::FromStr;

use crate::core::RevisionId;

/// The header a statement of what a command wrote begins with.
///
/// Numbered, for the reason 0064 numbers the reading half's: a document is
/// permanent and a store's grammar is a promise, and this is neither. A reader
/// that meets a header it does not know discards the statement whole rather
/// than guessing at the lines under it.
pub const HEADER: &str = "historica-wrote-1";

/// One pointer into the store.
///
/// Deliberately not `#[non_exhaustive]`. The vocabulary is closed by decision
/// 0074 — a fifth kind is `historica-wrote-2`, which is a different header and
/// would be a different type — so a caller that matches every kind here has
/// matched every kind there will ever be under this header, and should be told
/// so by the compiler rather than made to write an arm it can never reach.
///
/// The order these are declared in is the order they are printed in: it is what
/// [`Ord`] derives, and [`Statement`] keeps its lines in a set ordered by it.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Line {
    /// A revision document that was written and is now in `revisions/`.
    Revision(RevisionId),
    /// A bookmark that was written or moved and is now in `names/`.
    Name(String),
    /// A bookmark that was removed, per decision 0073.
    Unname(String),
    /// A digest something destroyed, which is `prune` and `forget`'s half.
    Gone(RevisionId),
}

impl Line {
    /// The word this line begins with.
    pub fn kind(&self) -> &'static str {
        match self {
            Self::Revision(_) => "revision",
            Self::Name(_) => "name",
            Self::Unname(_) => "unname",
            Self::Gone(_) => "gone",
        }
    }
}

impl fmt::Display for Line {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // Digests spelled whole, never abbreviated: an abbreviation is a fact
        // about what else the store holds today (decision 0001), so a caller
        // that wrote one down would find it ambiguous after a fetch, through no
        // change to the revision it named.
        match self {
            Self::Revision(id) | Self::Gone(id) => write!(f, "{} {id}", self.kind()),
            Self::Name(name) | Self::Unname(name) => write!(f, "{} {name}", self.kind()),
        }
    }
}

/// Everything one command wrote, in the order decision 0074 states.
///
/// Kind first, in the order [`Line`] declares them, and within a kind digests
/// ascending and bookmark names in byte order. Sorted rather than written in
/// the order the command happened to write in, so that two replicas doing the
/// same work print the same bytes — the standard `carry` already holds for the
/// documents themselves.
///
/// A set, so the same pointer stated twice is stated once. Nothing a writing
/// command does can name one thing twice, and a statement that did would be
/// claiming the same fact about the store two times over.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Statement {
    lines: BTreeSet<Line>,
}

impl Statement {
    /// A statement of nothing, which is a header and no lines.
    pub fn new() -> Self {
        Self::default()
    }

    /// Add a line, returning whether it was not already there.
    pub fn push(&mut self, line: Line) -> bool {
        self.lines.insert(line)
    }

    /// A revision document now in `revisions/`.
    pub fn revision(&mut self, id: RevisionId) -> &mut Self {
        self.push(Line::Revision(id));
        self
    }

    /// A bookmark now in `names/`.
    pub fn name(&mut self, name: impl Into<String>) -> &mut Self {
        self.push(Line::Name(name.into()));
        self
    }

    /// A bookmark that was removed.
    pub fn unname(&mut self, name: impl Into<String>) -> &mut Self {
        self.push(Line::Unname(name.into()));
        self
    }

    /// A digest something destroyed.
    pub fn gone(&mut self, id: RevisionId) -> &mut Self {
        self.push(Line::Gone(id));
        self
    }

    /// Whether the command wrote nothing.
    ///
    /// Not an error and not silence: an empty statement is this format's
    /// well-formed statement of nothing, and it is the one fact here a caller
    /// cannot recover by reading the store.
    pub fn is_empty(&self) -> bool {
        self.lines.is_empty()
    }

    /// How many lines it has.
    pub fn len(&self) -> usize {
        self.lines.len()
    }

    /// The lines, in the order they are printed.
    pub fn lines(&self) -> btree_set::Iter<'_, Line> {
        self.lines.iter()
    }

    /// Print the statement, header and all.
    pub fn write(&self, out: &mut impl io::Write) -> io::Result<()> {
        writeln!(out, "{HEADER}")?;
        for line in &self.lines {
            writeln!(out, "{line}")?;
        }
        Ok(())
    }
}

impl fmt::Display for Statement {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "{HEADER}")?;
        for line in &self.lines {
            writeln!(f, "{line}")?;
        }
        Ok(())
    }
}

impl Extend<Line> for Statement {
    fn extend<I: IntoIterator<Item = Line>>(&mut self, lines: I) {
        self.lines.extend(lines);
    }
}

impl FromIterator<Line> for Statement {
    fn from_iter<I: IntoIterator<Item = Line>>(lines: I) -> Self {
        Self {
            lines: lines.into_iter().collect(),
        }
    }
}

/// Why a statement could not be read.
///
/// Every one of these discards the statement whole rather than the line that
/// caused it. A caller reacting to a write it only partly understood would be
/// acting on a claim nobody made.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum ParseError {
    /// The first line was not [`HEADER`].
    ///
    /// `found` is `None` where there was no first line at all, which is what
    /// an empty input is: a statement of nothing still has its header.
    Header {
        /// What stood where the header should have been.
        found: Option<String>,
    },
    /// A line began with a word this vocabulary does not have.
    UnknownKind {
        /// Which line, counting the header as line 1.
        line: usize,
        /// The word it began with.
        kind: String,
    },
    /// There was a blank line between the header and the end.
    ///
    /// A statement is its header and its lines and has no separators in it, so
    /// a blank one is a sign the input is two statements, or a fragment of one.
    Blank {
        /// Which line, counting the header as line 1.
        line: usize,
    },
    /// A line had a kind and nothing after it.
    Empty {
        /// Which line, counting the header as line 1.
        line: usize,
    },
    /// A `revision` or `gone` line did not carry a whole digest.
    Digest {
        /// Which line, counting the header as line 1.
        line: usize,
    },
    /// A `name` or `unname` line carried something no bookmark could be.
    ///
    /// Only what the grammar itself can see — a leading or trailing space,
    /// which decision 0071 forbids in a name. Whether the store holds a
    /// bookmark by that name is the store's question, asked by looking.
    Name {
        /// Which line, counting the header as line 1.
        line: usize,
    },
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Header { found: Some(found) } => {
                write!(f, "this begins `{found}` rather than `{HEADER}`")
            }
            Self::Header { found: None } => {
                write!(
                    f,
                    "this is empty, and even a statement of nothing has `{HEADER}`"
                )
            }
            Self::UnknownKind { line, kind } => {
                write!(f, "line {line}: `{kind}` is not a kind `{HEADER}` has")
            }
            Self::Blank { line } => {
                write!(
                    f,
                    "line {line}: blank, and a statement has no blank lines in it"
                )
            }
            Self::Empty { line } => write!(f, "line {line}: a kind, and nothing after it"),
            Self::Digest { line } => {
                write!(
                    f,
                    "line {line}: a digest is 64 lowercase hex characters, spelled whole"
                )
            }
            Self::Name { line } => {
                write!(
                    f,
                    "line {line}: a bookmark has no leading or trailing space"
                )
            }
        }
    }
}

impl std::error::Error for ParseError {}

impl FromStr for Statement {
    type Err = ParseError;

    /// Read a statement, header and all.
    ///
    /// Liberal in one direction only: lines out of the stated order are
    /// accepted and come back in it, and the same line twice comes back once,
    /// because the statement is a set of claims rather than a narrative. Every
    /// other departure from the grammar discards the whole.
    fn from_str(text: &str) -> Result<Self, Self::Err> {
        let mut lines = text.lines();
        match lines.next() {
            Some(HEADER) => {}
            Some(found) => {
                return Err(ParseError::Header {
                    found: Some(found.to_owned()),
                });
            }
            None => return Err(ParseError::Header { found: None }),
        }

        let mut statement = Self::new();
        for (offset, text) in lines.enumerate() {
            // The header is line 1, so the first line under it is line 2.
            let line = offset + 2;
            if text.is_empty() {
                return Err(ParseError::Blank { line });
            }
            // Split once, which is the rule that lets a bookmark hold a space:
            // decision 0071 makes a name a path forbidding only a leading or
            // trailing one, and 0018's ban on control characters is what stops
            // it holding the newline that ends the line it is written on.
            let (kind, rest) = text.split_once(' ').unwrap_or((text, ""));
            if rest.is_empty() {
                return Err(match kind {
                    "revision" | "name" | "unname" | "gone" => ParseError::Empty { line },
                    kind => ParseError::UnknownKind {
                        line,
                        kind: kind.to_owned(),
                    },
                });
            }
            let digest = |value: &str| value.parse().map_err(|_| ParseError::Digest { line });
            let name = |value: &str| {
                if value.trim() == value {
                    Ok(value.to_owned())
                } else {
                    Err(ParseError::Name { line })
                }
            };
            statement.push(match kind {
                "revision" => Line::Revision(digest(rest)?),
                "gone" => Line::Gone(digest(rest)?),
                "name" => Line::Name(name(rest)?),
                "unname" => Line::Unname(name(rest)?),
                kind => {
                    return Err(ParseError::UnknownKind {
                        line,
                        kind: kind.to_owned(),
                    });
                }
            });
        }
        Ok(statement)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Two whole digests, distinguishable and in a known order.
    const ONE: &str = "0000000000000000000000000000000000000000000000000000000000000001";
    const TWO: &str = "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff02";

    fn id(hex: &str) -> RevisionId {
        hex.parse().expect("a whole digest")
    }

    fn parse(text: &str) -> Result<Statement, ParseError> {
        text.parse()
    }

    /// Decision 0074's most useful line: a store nobody wrote to and a store
    /// that did not change look identical, so this is the one fact here that
    /// reading the store cannot recover.
    #[test]
    fn nothing_written_is_a_header_and_no_lines() {
        let statement = Statement::new();
        assert!(statement.is_empty());
        assert_eq!(statement.to_string(), "historica-wrote-1\n");
        assert_eq!(parse("historica-wrote-1\n"), Ok(Statement::new()));
    }

    /// Kind first in the order the vocabulary lists them, then digests
    /// ascending and names in byte order — whatever order they arrived in.
    #[test]
    fn the_lines_come_out_in_the_stated_order() {
        let mut statement = Statement::new();
        statement
            .gone(id(TWO))
            .unname(id(ONE).to_string())
            .name("zebra")
            .name("alpha")
            .revision(id(TWO))
            .revision(id(ONE));

        let lines: Vec<String> = statement.lines().map(ToString::to_string).collect();
        assert_eq!(
            lines,
            vec![
                format!("revision {ONE}"),
                format!("revision {TWO}"),
                "name alpha".to_owned(),
                "name zebra".to_owned(),
                format!("unname {ONE}"),
                format!("gone {TWO}"),
            ]
        );
    }

    /// A set: the same pointer stated twice is one claim about the store.
    #[test]
    fn the_same_line_twice_is_one_line() {
        let mut statement = Statement::new();
        assert!(statement.push(Line::Revision(id(ONE))));
        assert!(!statement.push(Line::Revision(id(ONE))));
        assert_eq!(statement.len(), 1);

        // And a `gone` for the same digest is a different claim, not a repeat.
        assert!(statement.push(Line::Gone(id(ONE))));
        assert_eq!(statement.len(), 2);
    }

    /// The rule that makes 0071's names sayable: split once, and the rest of
    /// the line is the bookmark whole.
    #[test]
    fn a_bookmark_may_hold_a_space() {
        let mut statement = Statement::new();
        statement.name("feature/two words").unname("one more name");

        let text = statement.to_string();
        assert!(text.contains("name feature/two words\n"), "{text}");
        assert_eq!(parse(&text), Ok(statement));
    }

    /// Every statement this writes is one it reads back unchanged, which is
    /// what makes the corpus comparison a comparison rather than a rendering.
    #[test]
    fn what_it_writes_it_reads() {
        let mut statement = Statement::new();
        statement
            .revision(id(ONE))
            .revision(id(TWO))
            .name("main")
            .name("feature/a b")
            .unname("old")
            .gone(id(TWO));

        let mut out = Vec::new();
        statement.write(&mut out).expect("a vector never fails");
        assert_eq!(
            String::from_utf8(out).expect("ascii and names"),
            statement.to_string()
        );
        assert_eq!(parse(&statement.to_string()), Ok(statement));
    }

    /// Out of order in, in order out: the statement is a set of claims rather
    /// than a narrative, so nothing is lost by normalising it.
    #[test]
    fn a_statement_out_of_order_comes_back_in_it() {
        let text = format!("historica-wrote-1\ngone {TWO}\nname b\nname a\nrevision {ONE}\n");
        let statement = parse(&text).expect("well formed, if unsorted");
        assert_eq!(
            statement.to_string(),
            format!("historica-wrote-1\nrevision {ONE}\nname a\nname b\ngone {TWO}\n")
        );
    }

    /// A reader that meets something it does not understand discards the
    /// statement whole, rather than acting on the part it recognised.
    #[test]
    fn anything_ungrammatical_discards_the_whole() {
        assert_eq!(
            parse(""),
            Err(ParseError::Header { found: None }),
            "even a statement of nothing has its header"
        );
        assert_eq!(
            parse("historica-wrote-2\n"),
            Err(ParseError::Header {
                found: Some("historica-wrote-2".to_owned())
            })
        );
        assert_eq!(
            parse(&format!("historica-wrote-1\nrevision {ONE}\nskip *.log\n")),
            Err(ParseError::UnknownKind {
                line: 3,
                kind: "skip".to_owned()
            }),
            "0074 defers `skip` to a second header rather than adding a kind"
        );
        assert_eq!(
            parse("historica-wrote-1\nrevision\n"),
            Err(ParseError::Empty { line: 2 })
        );
        assert_eq!(
            parse("historica-wrote-1\nname \n"),
            Err(ParseError::Empty { line: 2 })
        );
        assert_eq!(
            parse("historica-wrote-1\n\nname a\n"),
            Err(ParseError::Blank { line: 2 })
        );
    }

    /// Spelled whole, because an abbreviation is a fact about what else the
    /// store holds today rather than about the revision it names.
    #[test]
    fn a_digest_is_never_short_and_never_shouted() {
        for spelling in [
            "0000000",
            &TWO.to_uppercase(),
            &format!("{ONE}0"),
            "not-hex",
        ] {
            assert_eq!(
                parse(&format!("historica-wrote-1\nrevision {spelling}\n")),
                Err(ParseError::Digest { line: 2 }),
                "{spelling}"
            );
        }
    }

    /// What the grammar itself can see. Whether the store holds a bookmark by
    /// this name is the store's question, asked by looking.
    #[test]
    fn a_name_the_grammar_can_refuse_is_refused() {
        assert_eq!(
            parse("historica-wrote-1\nname  padded\n"),
            Err(ParseError::Name { line: 2 })
        );
        assert_eq!(
            parse("historica-wrote-1\nname trailing \n"),
            Err(ParseError::Name { line: 2 })
        );
    }
}
