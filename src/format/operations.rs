//! The readable operation document: what one revision did to one file.
//!
//! Specified by `docs/decisions/0007-content-and-merge.md`. A revision does not
//! record what a file *is*; it records what it *did* to it, as a list of
//! operations against the state at that revision's parents:
//!
//! ```text
//! historica-v0
//!
//! delete 3 1
//! -Nothing here chooses a document syntax yet.
//! insert 4
//! +Model causality before content: immutable revisions, explicit parents, and a
//! +history that merges by union.
//! ```
//!
//! The preamble and the blank line are decision 0004's, for its reasons: the
//! file says how to hash itself, and can be identified by content rather than by
//! the extension it happens to carry. Nothing else a revision holds appears
//! here, because the revision that names this document already states it.
//!
//! Positions are zero-based indices **into the parent state**, never into the
//! document being built, which is what lets a person check an operation by eye
//! against one fixed file. Items are lines, terminator included; the terminator
//! is the document's own newline unless [`NO_NEWLINE`] says the item is the
//! file's last and carries none.
//!
//! Reading is as strict as [`super::RevisionDocument`]'s and for the same
//! reason: operations are sorted, non-overlapping, and never state one fact
//! twice, so exactly one byte sequence parses per set of facts and the digest
//! can cover the file's bytes.

use std::fmt;

use crate::core::RevisionId;

use super::{
    Lines, PREAMBLE, ParseError, ParseErrorKind, check_byte_order_mark, check_preamble, digest,
};

/// The line that says the item above it is the file's last and unterminated.
pub const NO_NEWLINE: &str = "\\ no newline";

/// One item of a file: a line, and whether it ends with a newline.
///
/// The terminator is not stored — it is the operation document's own newline —
/// so an item that lacks one is spelled by the [`NO_NEWLINE`] marker instead.
/// An item's text may hold a carriage return, because a CRLF document is a
/// thing people have and this is content rather than the format's own line.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Item {
    /// The line's bytes, terminator excluded.
    pub text: String,
    /// Whether the line ends with a newline. False only for a file's last line.
    pub terminated: bool,
}

impl Item {
    /// An ordinary line, ending with a newline.
    pub fn line(text: impl Into<String>) -> Self {
        Self {
            text: text.into(),
            terminated: true,
        }
    }

    /// A file's last line, ending without a newline.
    pub fn unterminated(text: impl Into<String>) -> Self {
        Self {
            text: text.into(),
            terminated: false,
        }
    }

    /// The bytes this item contributes to the file, terminator included.
    pub fn bytes(&self) -> Vec<u8> {
        let mut out = self.text.clone().into_bytes();
        if self.terminated {
            out.push(b'\n');
        }
        out
    }
}

/// Which of the two operations this is.
///
/// The order of these variants is the order they are written in at one
/// position: decision 0007 spells a replacement the way every diff spells it,
/// minus lines above plus lines.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum OperationKind {
    /// Remove items from the parent state.
    Delete,
    /// Add items to the parent state.
    Insert,
}

impl OperationKind {
    /// The keyword this operation's line opens with.
    pub const fn keyword(self) -> &'static str {
        match self {
            OperationKind::Delete => "delete",
            OperationKind::Insert => "insert",
        }
    }

    /// The single byte each of this operation's content lines opens with.
    pub const fn prefix(self) -> char {
        match self {
            OperationKind::Delete => '-',
            OperationKind::Insert => '+',
        }
    }
}

/// One operation, and the items it removed or added.
///
/// A delete carries the removed items as well as their count. That is
/// redundant — they are recoverable from the parent — and it is the point:
/// it makes the document readable alone, and it lets a replayer catch a
/// document that disagrees with the parent it claims to edit.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Operation {
    /// Whether this removes or adds.
    pub kind: OperationKind,
    /// The zero-based position in the parent state.
    pub at: usize,
    /// The items removed, or the items added. Never empty.
    pub items: Vec<Item>,
}

impl Operation {
    /// Remove `items` from the parent state, beginning at `at`.
    pub fn delete(at: usize, items: impl IntoIterator<Item = Item>) -> Self {
        Self {
            kind: OperationKind::Delete,
            at,
            items: items.into_iter().collect(),
        }
    }

    /// Add `items` to the parent state, before position `at`.
    pub fn insert(at: usize, items: impl IntoIterator<Item = Item>) -> Self {
        Self {
            kind: OperationKind::Insert,
            at,
            items: items.into_iter().collect(),
        }
    }

    /// One past the last parent position this operation covers.
    ///
    /// An insert covers nothing: it names a gap between two parent items rather
    /// than the items themselves.
    pub fn end(&self) -> usize {
        match self.kind {
            OperationKind::Delete => self.at.saturating_add(self.items.len()),
            OperationKind::Insert => self.at,
        }
    }
}

/// One operation document: everything one revision did to one file.
///
/// Operations are held in the order they are written, which is the order they
/// are read in: ascending by position, delete before insert at one position.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OperationDocument {
    /// What the revision did, in position order. Never empty.
    pub operations: Vec<Operation>,
}

impl OperationDocument {
    /// Parse one operation document from the bytes of an `.ops` file.
    pub fn parse(bytes: &[u8]) -> Result<Self, ParseError> {
        check_byte_order_mark(bytes)?;
        let text =
            std::str::from_utf8(bytes).map_err(|_| ParseError::new(0, ParseErrorKind::NotUtf8))?;
        Parser {
            lines: Lines::new(text),
            markers: Vec::new(),
        }
        .run()
    }

    /// The exact bytes of this document.
    ///
    /// `write(parse(bytes)) == bytes` for every input `parse` accepts. Writing
    /// sorts, so two replicas that record one edit write one file whatever
    /// order they assembled it in.
    pub fn write(&self) -> Vec<u8> {
        let mut order: Vec<&Operation> = self.operations.iter().collect();
        order.sort_by_key(|operation| (operation.at, operation.kind));

        let mut out = String::new();
        out.push_str(PREAMBLE);
        out.push_str("\n\n");
        for operation in order {
            match operation.kind {
                OperationKind::Delete => {
                    out.push_str(&format!(
                        "delete {} {}\n",
                        operation.at,
                        operation.items.len()
                    ));
                }
                OperationKind::Insert => out.push_str(&format!("insert {}\n", operation.at)),
            }
            for item in &operation.items {
                out.push(operation.kind.prefix());
                out.push_str(&item.text);
                out.push('\n');
                if !item.terminated {
                    out.push_str(NO_NEWLINE);
                    out.push('\n');
                }
            }
        }
        out.into_bytes()
    }

    /// The digest that names this document in a store.
    ///
    /// A [`RevisionId`] is the store's name for a digest, and decision 0003
    /// identifies every document in it the same way: the SHA-256 of its bytes,
    /// which is what `shasum -a 256` prints.
    pub fn id(&self) -> RevisionId {
        digest(&self.write())
    }
}

impl fmt::Display for OperationDocument {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&String::from_utf8_lossy(&self.write()))
    }
}

/// Where one `\ no newline` marker was, so a misplaced one can name its line.
struct Marker {
    operation: usize,
    item: usize,
    line: usize,
    prefix: char,
}

struct Parser<'a> {
    lines: Lines<'a>,
    markers: Vec<Marker>,
}

impl Parser<'_> {
    fn run(mut self) -> Result<OperationDocument, ParseError> {
        let Some((line, terminated)) = self.lines.next() else {
            return Err(ParseError::new(1, ParseErrorKind::Empty));
        };
        carriage_return(line, 1)?;
        check_preamble(line, terminated)?;

        // The blank line is mandatory though no header precedes it: both
        // documents in the format open the same way, so a person learns one
        // shape and a parser reads a preamble the same way in both.
        match self.lines.next() {
            Some(("", _)) => {}
            _ => {
                return Err(ParseError::new(
                    self.lines.line,
                    ParseErrorKind::MissingSeparator,
                ));
            }
        }

        let operations = self.operations()?;
        if operations.is_empty() {
            return Err(ParseError::new(
                self.lines.line,
                ParseErrorKind::NoOperations,
            ));
        }
        self.check_markers(&operations)?;
        Ok(OperationDocument { operations })
    }

    fn operations(&mut self) -> Result<Vec<Operation>, ParseError> {
        let mut operations: Vec<Operation> = Vec::new();
        while let Some((line, terminated)) = self.lines.next() {
            let at = self.lines.line;
            if !terminated {
                return Err(ParseError::new(at, ParseErrorKind::UnterminatedLine));
            }
            let operation = self.operation(line, at, operations.len())?;
            ordered(operations.last(), &operation, at)?;
            operations.push(operation);
        }
        Ok(operations)
    }

    /// One operation line and the content lines that belong to it.
    fn operation(&mut self, line: &str, at: usize, index: usize) -> Result<Operation, ParseError> {
        let (keyword, rest) = match line.split_once(' ') {
            Some((keyword, rest)) => (keyword, rest),
            None => (line, ""),
        };
        match keyword {
            "delete" => {
                carriage_return(line, at)?;
                let fields = rest
                    .split_once(' ')
                    .filter(|(_, count)| !count.contains(' '));
                let Some((position, count)) = fields else {
                    return Err(malformed(OperationKind::Delete, at));
                };
                let position = number(position, at)?;
                let count = number(count, at)?;
                if count == 0 {
                    return Err(ParseError::new(at, ParseErrorKind::EmptyDelete));
                }
                let items = self.items(OperationKind::Delete, Some(count), index)?;
                Ok(Operation::delete(position, items))
            }
            "insert" => {
                carriage_return(line, at)?;
                if rest.is_empty() || rest.contains(' ') {
                    return Err(malformed(OperationKind::Insert, at));
                }
                let position = number(rest, at)?;
                let items = self.items(OperationKind::Insert, None, index)?;
                if items.is_empty() {
                    return Err(ParseError::new(at, ParseErrorKind::EmptyInsert));
                }
                Ok(Operation::insert(position, items))
            }
            _ if line.starts_with('-') || line.starts_with('+') => Err(ParseError::new(
                at,
                ParseErrorKind::ContentWithoutOperation {
                    prefix: line.chars().next().expect("a prefix byte"),
                },
            )),
            _ if line == NO_NEWLINE => {
                Err(ParseError::new(at, ParseErrorKind::NoNewlineWithoutItem))
            }
            _ => {
                carriage_return(line, at)?;
                Err(ParseError::new(
                    at,
                    ParseErrorKind::UnknownOperation {
                        found: line.to_owned(),
                    },
                ))
            }
        }
    }

    /// The content lines under one operation.
    ///
    /// A delete reads exactly the number of items it stated; an insert reads
    /// until a line that is not its own, because its count is the lines
    /// themselves. Exactly one byte is stripped from each and nothing else is
    /// trimmed, unescaped, or normalised.
    fn items(
        &mut self,
        kind: OperationKind,
        expected: Option<usize>,
        operation: usize,
    ) -> Result<Vec<Item>, ParseError> {
        let prefix = kind.prefix();
        let mut items: Vec<Item> = Vec::new();
        while expected != Some(items.len()) {
            let mark = self.lines.mark();
            let Some((line, terminated)) = self.lines.next() else {
                break;
            };
            // A marker where an item was expected describes the operation
            // line, or another marker, and neither is an item.
            if line == NO_NEWLINE {
                return Err(ParseError::new(
                    self.lines.line,
                    ParseErrorKind::NoNewlineWithoutItem,
                ));
            }
            if !line.starts_with(prefix) {
                self.lines.reset(mark);
                break;
            }
            if !terminated {
                return Err(ParseError::new(
                    self.lines.line,
                    ParseErrorKind::UnterminatedLine,
                ));
            }
            items.push(Item::line(&line[prefix.len_utf8()..]));
            self.marker(kind, operation, items.len() - 1, &mut items)?;
        }
        if let Some(expected) = expected
            && items.len() != expected
        {
            return Err(ParseError::new(
                self.lines.line,
                ParseErrorKind::DeleteCountDisagrees {
                    stated: expected,
                    found: items.len(),
                },
            ));
        }
        Ok(items)
    }

    /// A `\ no newline` line, if the item just read is followed by one.
    fn marker(
        &mut self,
        kind: OperationKind,
        operation: usize,
        item: usize,
        items: &mut [Item],
    ) -> Result<(), ParseError> {
        let mark = self.lines.mark();
        let Some((line, terminated)) = self.lines.next() else {
            return Ok(());
        };
        if line != NO_NEWLINE {
            self.lines.reset(mark);
            return Ok(());
        }
        if !terminated {
            return Err(ParseError::new(
                self.lines.line,
                ParseErrorKind::UnterminatedLine,
            ));
        }
        items[item].terminated = false;
        self.markers.push(Marker {
            operation,
            item,
            line: self.lines.line,
            prefix: kind.prefix(),
        });
        Ok(())
    }

    /// A marker marks the file's last line, so items of its kind cannot follow.
    fn check_markers(&self, operations: &[Operation]) -> Result<(), ParseError> {
        for marker in &self.markers {
            let operation = &operations[marker.operation];
            let last_item = marker.item + 1 == operation.items.len();
            let last_of_its_kind = !operations[marker.operation + 1..]
                .iter()
                .any(|later| later.kind == operation.kind);
            if !(last_item && last_of_its_kind) {
                return Err(ParseError::new(
                    marker.line,
                    ParseErrorKind::NoNewlineNotLast {
                        prefix: marker.prefix,
                    },
                ));
            }
        }
        Ok(())
    }
}

/// Hold one operation against the one before it.
///
/// Positions ascend and regions never overlap, which is a total order, which is
/// a canonical order: decision 0004's "exactly one byte sequence per set of
/// facts" survives contact with content only because of this.
fn ordered(previous: Option<&Operation>, next: &Operation, at: usize) -> Result<(), ParseError> {
    use OperationKind::{Delete, Insert};

    let Some(previous) = previous else {
        return Ok(());
    };
    if next.at < previous.at {
        return Err(ParseError::new(
            at,
            ParseErrorKind::OperationsOutOfOrder {
                position: next.at,
                after: previous.at,
            },
        ));
    }
    if next.at == previous.at {
        let kind = match (previous.kind, next.kind) {
            // The canonical replacement, and the only tie there is.
            (Delete, Insert) => return Ok(()),
            (Delete, Delete) => ParseErrorKind::OverlappingOperations { position: next.at },
            (Insert, Delete) => ParseErrorKind::DeleteAfterInsert { position: next.at },
            (Insert, Insert) => ParseErrorKind::InsertsAtOnePosition { position: next.at },
        };
        return Err(ParseError::new(at, kind));
    }
    if previous.kind == Delete {
        if next.at < previous.end() {
            return Err(ParseError::new(
                at,
                ParseErrorKind::OverlappingOperations { position: next.at },
            ));
        }
        // Two deletes that meet remove one run, which is one fact.
        if next.at == previous.end() && next.kind == Delete {
            return Err(ParseError::new(
                at,
                ParseErrorKind::AdjacentDeletes {
                    at: previous.at,
                    total: previous.items.len() + next.items.len(),
                },
            ));
        }
    }
    Ok(())
}

/// An operation line with the wrong number of fields.
fn malformed(kind: OperationKind, at: usize) -> ParseError {
    ParseError::new(
        at,
        ParseErrorKind::MalformedOperation {
            keyword: kind.keyword(),
        },
    )
}

/// A position or a count: decimal digits, no sign, and no leading zero.
///
/// A second spelling of one number would be a second spelling of one document.
fn number(field: &str, at: usize) -> Result<usize, ParseError> {
    let canonical = !field.is_empty()
        && field.bytes().all(|byte| byte.is_ascii_digit())
        && (field.len() == 1 || !field.starts_with('0'));
    if !canonical {
        return Err(ParseError::new(
            at,
            ParseErrorKind::MalformedNumber {
                found: field.to_owned(),
            },
        ));
    }
    field.parse().map_err(|_| {
        ParseError::new(
            at,
            ParseErrorKind::MalformedNumber {
                found: field.to_owned(),
            },
        )
    })
}

/// A carriage return in the format's own line, which content lines may hold.
fn carriage_return(line: &str, at: usize) -> Result<(), ParseError> {
    if line.contains('\r') {
        return Err(ParseError::new(
            at,
            ParseErrorKind::CarriageReturnInOperation,
        ));
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Assemble a file from the lines below the separator.
    fn file(lines: &[&str]) -> Vec<u8> {
        let mut out = format!("{PREAMBLE}\n\n");
        for line in lines {
            out.push_str(line);
            out.push('\n');
        }
        out.into_bytes()
    }

    fn accept(lines: &[&str]) -> OperationDocument {
        OperationDocument::parse(&file(lines)).expect("should parse")
    }

    fn refuse(lines: &[&str]) -> ParseErrorKind {
        OperationDocument::parse(&file(lines))
            .expect_err("should be refused")
            .kind
    }

    #[test]
    fn a_files_first_version_is_one_insert_of_every_line() {
        let document = accept(&["insert 0", "+one", "+two"]);
        assert_eq!(
            document.operations,
            vec![Operation::insert(0, [Item::line("one"), Item::line("two")])]
        );
        assert_eq!(document.write(), file(&["insert 0", "+one", "+two"]));
    }

    #[test]
    fn a_replacement_is_minus_lines_above_plus_lines() {
        let document = accept(&["delete 3 1", "-old", "insert 3", "+new"]);
        assert_eq!(document.operations.len(), 2);
        assert_eq!(document.operations[0].kind, OperationKind::Delete);
        assert_eq!(document.operations[1].kind, OperationKind::Insert);

        // The same facts in the other order are the same document, so the
        // writer puts them back into the one order that parses.
        let reversed = OperationDocument {
            operations: document.operations.iter().rev().cloned().collect(),
        };
        assert_eq!(reversed.write(), document.write());
        assert_eq!(reversed.id(), document.id());
    }

    #[test]
    fn an_operation_line_states_its_position_exactly_once_and_plainly() {
        assert_eq!(
            refuse(&["delete 3", "-old"]),
            ParseErrorKind::MalformedOperation { keyword: "delete" }
        );
        assert_eq!(
            refuse(&["insert 3 1", "+new"]),
            ParseErrorKind::MalformedOperation { keyword: "insert" }
        );
        assert_eq!(
            refuse(&["insert", "+new"]),
            ParseErrorKind::MalformedOperation { keyword: "insert" }
        );
        // A leading zero is a second spelling of one number.
        assert_eq!(
            refuse(&["insert 03", "+new"]),
            ParseErrorKind::MalformedNumber {
                found: "03".to_owned()
            }
        );
        assert_eq!(
            refuse(&["insert -1", "+new"]),
            ParseErrorKind::MalformedNumber {
                found: "-1".to_owned()
            }
        );
    }

    #[test]
    fn an_operation_carries_at_least_one_item_and_says_how_many() {
        assert_eq!(refuse(&["delete 3 0"]), ParseErrorKind::EmptyDelete);
        assert_eq!(refuse(&["insert 3"]), ParseErrorKind::EmptyInsert);
        assert_eq!(
            refuse(&["delete 3 2", "-old"]),
            ParseErrorKind::DeleteCountDisagrees {
                stated: 2,
                found: 1
            }
        );
        assert_eq!(
            refuse(&["delete 3 1", "-old", "-older"]),
            ParseErrorKind::ContentWithoutOperation { prefix: '-' }
        );
    }

    #[test]
    fn operations_ascend_and_never_describe_one_region_twice() {
        accept(&["delete 0 2", "-a", "-b", "insert 5", "+c"]);

        assert_eq!(
            refuse(&["insert 5", "+c", "delete 0 1", "-a"]),
            ParseErrorKind::OperationsOutOfOrder {
                position: 0,
                after: 5
            }
        );
        assert_eq!(
            refuse(&["delete 0 3", "-a", "-b", "-c", "delete 2 1", "-c"]),
            ParseErrorKind::OverlappingOperations { position: 2 }
        );
        // An insert inside a deleted run names a gap that is being removed.
        assert_eq!(
            refuse(&["delete 0 3", "-a", "-b", "-c", "insert 1", "+d"]),
            ParseErrorKind::OverlappingOperations { position: 1 }
        );
        // Two deletes that meet remove one run.
        assert_eq!(
            refuse(&["delete 0 2", "-a", "-b", "delete 2 1", "-c"]),
            ParseErrorKind::AdjacentDeletes { at: 0, total: 3 }
        );
    }

    #[test]
    fn at_one_position_delete_comes_before_insert() {
        accept(&["delete 4 1", "-old", "insert 4", "+new"]);
        assert_eq!(
            refuse(&["insert 4", "+new", "delete 4 1", "-old"]),
            ParseErrorKind::DeleteAfterInsert { position: 4 }
        );
        assert_eq!(
            refuse(&["insert 4", "+one", "insert 4", "+two"]),
            ParseErrorKind::InsertsAtOnePosition { position: 4 }
        );
    }

    #[test]
    fn an_insert_may_follow_the_run_a_delete_removed() {
        // Distinct from `insert 0`: the position it anchors to is different,
        // and a concurrent edit can tell the two apart.
        let document = accept(&["delete 0 2", "-a", "-b", "insert 2", "+c"]);
        assert_eq!(document.operations[1].at, 2);
    }

    #[test]
    fn the_last_line_may_lack_a_terminator_and_says_so_once() {
        let document = accept(&[
            "delete 9 1",
            "-old last",
            NO_NEWLINE,
            "insert 9",
            "+new last",
        ]);
        assert!(!document.operations[0].items[0].terminated);
        assert!(document.operations[1].items[0].terminated);
        assert_eq!(
            document.write(),
            file(&[
                "delete 9 1",
                "-old last",
                NO_NEWLINE,
                "insert 9",
                "+new last"
            ])
        );

        // Both sides may be unterminated: a last line replaced by another.
        accept(&[
            "delete 9 1",
            "-old last",
            NO_NEWLINE,
            "insert 9",
            "+new last",
            NO_NEWLINE,
        ]);
    }

    #[test]
    fn a_no_newline_marker_describes_the_last_item_of_its_kind() {
        assert_eq!(
            refuse(&["insert 0", "+a", NO_NEWLINE, "+b"]),
            ParseErrorKind::NoNewlineNotLast { prefix: '+' }
        );
        assert_eq!(
            refuse(&["delete 0 1", "-a", NO_NEWLINE, "delete 4 1", "-b"]),
            ParseErrorKind::NoNewlineNotLast { prefix: '-' }
        );
        assert_eq!(
            refuse(&["insert 0", NO_NEWLINE, "+a"]),
            ParseErrorKind::NoNewlineWithoutItem
        );
    }

    #[test]
    fn an_item_is_one_prefix_byte_and_then_bytes_that_are_never_touched() {
        let document = accept(&["insert 0", "+  padded  ", "+\ttab", "+", "+insert 4"]);
        let items = &document.operations[0].items;
        assert_eq!(items[0].text, "  padded  ");
        assert_eq!(items[1].text, "\ttab");
        // An empty line in the file is an item with no bytes but a terminator.
        assert_eq!(items[2].text, "");
        assert_eq!(items[2].bytes(), b"\n");
        // A line that reads like an operation is content, not an operation.
        assert_eq!(items[3].text, "insert 4");
        assert_eq!(
            document.write(),
            file(&["insert 0", "+  padded  ", "+\ttab", "+", "+insert 4"])
        );
    }

    #[test]
    fn a_carriage_return_is_content_in_an_item_and_a_fault_anywhere_else() {
        // A CRLF file's lines carry their CR into the item's bytes.
        let document = accept(&["insert 0", "+one\r", "+two\r"]);
        assert_eq!(document.operations[0].items[0].bytes(), b"one\r\n");

        assert_eq!(
            refuse(&["insert 0\r", "+one"]),
            ParseErrorKind::CarriageReturnInOperation
        );
        assert_eq!(
            refuse(&["insert 0", "+one", "\\ no newline\r"]),
            ParseErrorKind::CarriageReturnInOperation
        );
    }

    #[test]
    fn the_document_is_a_preamble_a_blank_line_and_at_least_one_operation() {
        assert_eq!(
            OperationDocument::parse(b"").expect_err("empty").kind,
            ParseErrorKind::Empty
        );
        assert_eq!(
            OperationDocument::parse(b"historica-v0\ninsert 0\n+a\n")
                .expect_err("no separator")
                .kind,
            ParseErrorKind::MissingSeparator
        );
        assert_eq!(
            OperationDocument::parse(b"historica-v0\n")
                .expect_err("nothing after the preamble")
                .kind,
            ParseErrorKind::MissingSeparator
        );
        // A revision that changes nothing about a file names no document.
        assert_eq!(
            OperationDocument::parse(b"historica-v0\n\n")
                .expect_err("no operations")
                .kind,
            ParseErrorKind::NoOperations
        );
        assert_eq!(
            OperationDocument::parse(b"historica-v1\n\ninsert 0\n+a\n")
                .expect_err("a later version")
                .kind,
            ParseErrorKind::UnknownVersion {
                found: "1".to_owned()
            }
        );
        assert_eq!(
            OperationDocument::parse(b"insert 0\n+a\n")
                .expect_err("no preamble")
                .kind,
            ParseErrorKind::MissingPreamble
        );
        // Every line the parser reads ends with a newline.
        assert_eq!(
            OperationDocument::parse(b"historica-v0\n\ninsert 0\n+a")
                .expect_err("unterminated")
                .kind,
            ParseErrorKind::UnterminatedLine
        );
    }

    #[test]
    fn a_line_that_is_neither_operation_nor_content_is_refused_by_name() {
        assert_eq!(
            refuse(&["replace 3 1", "-old", "+new"]),
            ParseErrorKind::UnknownOperation {
                found: "replace 3 1".to_owned()
            }
        );
        assert_eq!(
            refuse(&["+orphan"]),
            ParseErrorKind::ContentWithoutOperation { prefix: '+' }
        );
        assert_eq!(
            refuse(&["\\ nonewline"]),
            ParseErrorKind::UnknownOperation {
                found: "\\ nonewline".to_owned()
            }
        );
    }

    #[test]
    fn the_id_is_the_digest_of_the_file() {
        let document = accept(&["insert 0", "+one"]);
        assert_eq!(document.id(), digest(&document.write()));
    }
}
