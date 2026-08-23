//! Materialising a file by replaying what was done to it.
//!
//! Decision 0007 makes the operation document authoritative and the file a
//! cache: a revision records what it *did*, so the file at a revision is what
//! you get by replaying every operation from the root.
//!
//! This module does the linear case, which the decision says is free:
//!
//! > When no two operations in the region are concurrent — one person, one
//! > device, or any history that has already been merged — the internal
//! > structure is never built and replay is application.
//!
//! [`State::apply`] is that application. Merging concurrent branches through
//! Eg-walker is not here yet, and neither is the tree that would say which
//! documents belong to which file, so a caller supplies the chain itself.
//!
//! Replay is also where the redundancy in an operation document earns its
//! keep. A `delete` records the items it removed as well as their count, so a
//! document that disagrees with the parent it claims to edit is caught here
//! rather than absorbed into a merge — decision 0007 calls that an error and
//! means it, because it is the store contradicting itself.

use std::collections::BTreeMap;
use std::fmt;

use crate::format::{Item, Operation, OperationDocument, OperationKind, Version, digest};

/// The operation document a `text` payload is exactly equivalent to.
///
/// Decision 0017: a created file's items are its lines, inserted at 0, and
/// they take the names that document would have given them — `(R, 0)` through
/// `(R, n-1)` — so nothing downstream of here can tell which spelling a
/// creation used. `None` for an empty payload, which is a file created with no
/// content and names no payload at all.
pub fn creation(text: &str) -> Option<OperationDocument> {
    let items = State::from_text(text).items;
    if items.is_empty() {
        return None;
    }
    Some(OperationDocument {
        // A payload's lines are never forgotten — forgetting one destroys
        // the payload and leaves a stand-in — so this is version 1's
        // vocabulary and claims no more. The synthesised version is not
        // raised by the result below, because this document is never
        // written: it is the equivalence 0017 states, held in memory.
        version: Version::V1,
        forgets: None,
        // Decision 0031: a creation's result is the payload itself — 0017
        // already named the file's content by digest, and this makes the
        // synthesised document verifiable on the same terms as a written one.
        result: Some(digest(text.as_bytes())),
        operations: vec![Operation::insert(0, items)],
    })
}

/// One file, as a list of items.
///
/// Items are lines, terminator included, because decision 0007 makes the item
/// a line. A state is derived and disposable: every one of them is replayable
/// from the operations that produced it, which is what lets `cache/` be
/// genuinely deletable rather than nominally so.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct State {
    items: Vec<Item>,
}

impl State {
    /// The state a root revision edits: a file that does not exist yet.
    pub fn empty() -> Self {
        Self::default()
    }

    /// Split a file into items, which is the reverse of [`State::text`].
    ///
    /// A file whose last line carries no terminator produces a last item that
    /// says so, which is the fact `\ no newline` records in a document.
    pub fn from_text(text: &str) -> Self {
        let mut items = Vec::new();
        let mut rest = text;
        while !rest.is_empty() {
            match rest.find('\n') {
                Some(index) => {
                    items.push(Item::line(&rest[..index]));
                    rest = &rest[index + 1..];
                }
                None => {
                    items.push(Item::unterminated(rest));
                    break;
                }
            }
        }
        Self { items }
    }

    /// The file's bytes.
    ///
    /// A forgotten item shows the `\ forgotten` marker, per decision 0014:
    /// the file has it where a run of lines used to be, and nothing else in
    /// the history moves.
    pub fn text(&self) -> String {
        let mut out = String::new();
        for item in &self.items {
            out.push_str(item.shown());
            if item.terminated {
                out.push('\n');
            }
        }
        out
    }

    /// The items, in file order.
    pub fn items(&self) -> &[Item] {
        &self.items
    }

    /// A file assembled from items that came from somewhere else.
    ///
    /// [`crate::merge`] produces items rather than text, because a merge is a
    /// statement about which items survived rather than about bytes.
    pub fn from_items(items: impl IntoIterator<Item = Item>) -> Self {
        Self {
            items: items.into_iter().collect(),
        }
    }

    /// How many items the file has.
    pub fn len(&self) -> usize {
        self.items.len()
    }

    /// Whether the file has no items, which is how a file that does not exist
    /// yet is spelled.
    pub fn is_empty(&self) -> bool {
        self.items.is_empty()
    }

    /// The state after one revision's operations, given the state at its parent.
    ///
    /// Positions are indices into `self` rather than into the file being built,
    /// which is what lets a person check a document against one fixed state.
    /// Turning them into the sequential form is this function's arithmetic, and
    /// is why `insert 4` after `delete 3 1` puts its items past the removed run
    /// while `insert 3` would put them before it.
    ///
    /// `document` is expected to be one the parser would accept. Operations out
    /// of order are applied to the same result, because every position is
    /// stated against `self` and none of them move.
    pub fn apply(&self, document: &OperationDocument) -> Result<Self, ReplayError> {
        let length = self.items.len();
        let mut deleted = vec![false; length];
        let mut inserted: BTreeMap<usize, Vec<Item>> = BTreeMap::new();

        for operation in &document.operations {
            match operation.kind {
                OperationKind::Delete => {
                    let end = operation.at.saturating_add(operation.items.len());
                    if end > length {
                        return Err(ReplayError::OutOfRange {
                            position: end,
                            length,
                        });
                    }
                    for (offset, recorded) in operation.items.iter().enumerate() {
                        let position = operation.at + offset;
                        agrees(position, recorded, &self.items[position])?;
                        deleted[position] = true;
                    }
                }
                OperationKind::Insert => {
                    if operation.at > length {
                        return Err(ReplayError::OutOfRange {
                            position: operation.at,
                            length,
                        });
                    }
                    inserted
                        .entry(operation.at)
                        .or_default()
                        .extend(operation.items.iter().cloned());
                }
            }
        }

        let mut items = Vec::with_capacity(length);
        for (position, item) in self.items.iter().enumerate() {
            if let Some(new) = inserted.remove(&position) {
                items.extend(new);
            }
            if !deleted[position] {
                items.push(item.clone());
            }
        }
        // An insert at the end names the gap past the last item, which the
        // walk above never reaches.
        if let Some(new) = inserted.remove(&length) {
            items.extend(new);
        }

        // Only a file's last line may lack a terminator. Appending past one is
        // the ordinary way to break that, and the fix is to rewrite that line.
        if let Some(position) = items
            .iter()
            .take(items.len().saturating_sub(1))
            .position(|item| !item.terminated)
        {
            return Err(ReplayError::UnterminatedItemNotLast { position });
        }

        let produced = Self { items };

        // Decision 0031: a document states the digest of the file it
        // produces, and a replay is held to it — the checkpoint a hand
        // replayer has, an implementation must not be spared. Verification
        // stops where forgetting begins, because a state showing markers has
        // bytes the recorder never hashed: 0014's structure-not-content
        // sentence, collecting one more thing.
        if let Some(stated) = &document.result
            && !produced.items.iter().any(|item| item.forgotten)
        {
            let found = digest(produced.text().as_bytes());
            if found != *stated {
                return Err(ReplayError::ResultDisagrees {
                    stated: *stated,
                    found,
                });
            }
        }

        Ok(produced)
    }
}

/// Replay a linear chain of documents from the root.
///
/// Every document is applied to the state the one before it produced, so the
/// chain must be one revision's ancestry in order, oldest first. A caller that
/// needs to name the document a failure came from should call [`State::apply`]
/// itself; this returns only what went wrong.
pub fn replay<'a>(
    documents: impl IntoIterator<Item = &'a OperationDocument>,
) -> Result<State, ReplayError> {
    let mut state = State::empty();
    for document in documents {
        state = state.apply(document)?;
    }
    Ok(state)
}

/// Hold a recorded item against the one the parent actually has.
///
/// A forgotten item on either side matches, per decision 0014: the
/// redundancy the text paid for is exactly what was destroyed. The
/// terminator is still held, because that is shape.
fn agrees(position: usize, recorded: &Item, found: &Item) -> Result<(), ReplayError> {
    if recorded.terminated != found.terminated {
        return Err(ReplayError::TerminatorDisagrees {
            position,
            recorded: recorded.terminated,
        });
    }
    if !recorded.matches(found) {
        return Err(ReplayError::ItemDisagrees {
            position,
            recorded: recorded.text.clone(),
            found: found.text.clone(),
        });
    }
    Ok(())
}

/// Why a document could not be replayed against the state it names.
///
/// None of these mean the algorithm failed. They mean the store contradicts
/// itself: a document was applied to a state it was not written against, and
/// the redundancy decision 0007 kept on purpose is what noticed.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum ReplayError {
    /// An operation names a position the parent state does not have.
    OutOfRange {
        /// The position named.
        position: usize,
        /// How many items the parent has.
        length: usize,
    },
    /// A recorded item's text is not the text the parent holds there.
    ItemDisagrees {
        /// Where the two disagree.
        position: usize,
        /// What the document recorded.
        recorded: String,
        /// What the parent holds.
        found: String,
    },
    /// A recorded item's terminator is not the parent's.
    TerminatorDisagrees {
        /// Where the two disagree.
        position: usize,
        /// Whether the document recorded a terminated item.
        recorded: bool,
    },
    /// The result would hold an unterminated item that is not its last.
    UnterminatedItemNotLast {
        /// Where that item ended up.
        position: usize,
    },
    /// The document's stated result is not what replaying it produces.
    ///
    /// Decision 0031: one of the two is wrong — the document, the parent it
    /// was applied to, or the replayer — and refusing is friendlier than
    /// carrying the disagreement forward.
    ResultDisagrees {
        /// The digest the document states.
        stated: crate::core::RevisionId,
        /// The digest of what replaying actually produced.
        found: crate::core::RevisionId,
    },
}

impl fmt::Display for ReplayError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ReplayError::OutOfRange { position, length } => write!(
                f,
                "this operation names position {position} of a parent that has {length} items; \
                 the document was written against a different state, so check that its \
                 revision's parents are the ones it was recorded from"
            ),
            ReplayError::ItemDisagrees {
                position,
                recorded,
                found,
            } => write!(
                f,
                "the document deletes `{recorded}` at position {position}, where the parent \
                 holds `{found}`; one of the two is corrupt, and the parent's digest says which"
            ),
            ReplayError::TerminatorDisagrees { position, recorded } => {
                if *recorded {
                    write!(
                        f,
                        "the parent's item at position {position} ends without a newline and \
                         this document deletes it as though it had one; \
                         add `\\ no newline` under that line"
                    )
                } else {
                    write!(
                        f,
                        "`\\ no newline` says the item at position {position} is the file's last \
                         and unterminated, and the parent's ends with a newline; \
                         delete the marker"
                    )
                }
            }
            ReplayError::UnterminatedItemNotLast { position } => write!(
                f,
                "only a file's last line may end without a newline, and item {position} of the \
                 result does not end with one; delete that line and add it back with a \
                 terminator, in the revision that puts items after it"
            ),
            ReplayError::ResultDisagrees { stated, found } => write!(
                f,
                "this document says it produces {stated} and replaying it produces {found}; \
                 the document, its parent, or the replayer is wrong, and `shasum -a 256` on \
                 the replayed file is how to see which"
            ),
        }
    }
}

impl std::error::Error for ReplayError {}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::format::{Operation, PREAMBLE};

    fn document(lines: &[&str]) -> OperationDocument {
        let mut text = format!("{PREAMBLE}\n\n");
        for line in lines {
            text.push_str(line);
            text.push('\n');
        }
        OperationDocument::parse(text.as_bytes()).expect("a document the parser accepts")
    }

    fn apply(text: &str, lines: &[&str]) -> String {
        State::from_text(text)
            .apply(&document(lines))
            .expect("should replay")
            .text()
    }

    fn refuse(text: &str, lines: &[&str]) -> ReplayError {
        State::from_text(text)
            .apply(&document(lines))
            .expect_err("should be refused")
    }

    #[test]
    fn a_file_and_its_items_are_the_same_thing_read_two_ways() {
        for text in ["", "one\n", "one\ntwo\n", "one\ntwo", "\n", "\n\n"] {
            assert_eq!(State::from_text(text).text(), text, "{text:?}");
        }
        assert!(State::from_text("").is_empty());
        assert_eq!(State::from_text("one\ntwo").len(), 2);
        // A file whose last line has no terminator says so in its last item.
        assert!(!State::from_text("one\ntwo").items()[1].terminated);
        assert!(State::from_text("one\ntwo\n").items()[1].terminated);
    }

    #[test]
    fn a_root_revision_replays_against_a_file_that_does_not_exist_yet() {
        let state = State::empty()
            .apply(&document(&["insert 0", "+one", "+two"]))
            .expect("a first version");
        assert_eq!(state.text(), "one\ntwo\n");
    }

    #[test]
    fn positions_are_stated_against_the_parent_and_never_move() {
        // Two operations far apart: the second is not shifted by the first,
        // which is the property that lets a person check them by eye.
        assert_eq!(
            apply(
                "one\ntwo\nthree\nfour\n",
                &["delete 0 1", "-one", "insert 3", "+inserted"]
            ),
            "two\nthree\ninserted\nfour\n"
        );
        // The same document written the other way round is the same document.
        assert_eq!(
            apply(
                "one\ntwo\nthree\nfour\n",
                &["insert 0", "+inserted", "delete 3 1", "-four"]
            ),
            "inserted\none\ntwo\nthree\n"
        );
    }

    #[test]
    fn a_replacement_puts_its_items_where_the_insert_says() {
        // Decision 0007's example spells a replacement with the insert past
        // the removed run; at the run's start it is a different operation,
        // and here that difference is visible.
        assert_eq!(
            apply("a\nb\nc\n", &["delete 1 1", "-b", "insert 2", "+new"]),
            "a\nnew\nc\n"
        );
        assert_eq!(
            apply("a\nb\nc\n", &["delete 1 1", "-b", "insert 1", "+new"]),
            "a\nnew\nc\n"
        );
        // They differ where something else sits between the two positions.
        assert_eq!(
            apply("a\nb\nc\n", &["delete 1 1", "-b", "insert 3", "+new"]),
            "a\nc\nnew\n"
        );
    }

    #[test]
    fn a_document_that_disagrees_with_its_parent_is_caught_here() {
        // The check decision 0007 bought with a deleted line's redundancy.
        assert_eq!(
            refuse("one\ntwo\n", &["delete 0 1", "-uno"]),
            ReplayError::ItemDisagrees {
                position: 0,
                recorded: "uno".to_owned(),
                found: "one".to_owned(),
            }
        );
        assert_eq!(
            refuse("one\ntwo\n", &["delete 2 1", "-three"]),
            ReplayError::OutOfRange {
                position: 3,
                length: 2,
            }
        );
        assert_eq!(
            refuse("one\n", &["insert 4", "+late"]),
            ReplayError::OutOfRange {
                position: 4,
                length: 1,
            }
        );
    }

    #[test]
    fn a_terminator_is_part_of_what_a_deleted_item_claims() {
        // The parent's last line has one and the document says it does not.
        assert_eq!(
            refuse("one\ntwo\n", &["delete 1 1", "-two", "\\ no newline"]),
            ReplayError::TerminatorDisagrees {
                position: 1,
                recorded: false,
            }
        );
        // And the other way round.
        assert_eq!(
            refuse("one\ntwo", &["delete 1 1", "-two"]),
            ReplayError::TerminatorDisagrees {
                position: 1,
                recorded: true,
            }
        );
        // Replacing an unterminated last line with another one.
        assert_eq!(
            apply(
                "one\ntwo",
                &[
                    "delete 1 1",
                    "-two",
                    "\\ no newline",
                    "insert 2",
                    "+deux",
                    "\\ no newline"
                ]
            ),
            "one\ndeux"
        );
    }

    #[test]
    fn appending_past_an_unterminated_last_line_is_refused() {
        // Decision 0007's third open question, in the linear case: the item is
        // asserting two things at once, and the way out is to rewrite the line.
        assert_eq!(
            refuse("one\ntwo", &["insert 2", "+three"]),
            ReplayError::UnterminatedItemNotLast { position: 1 }
        );
        assert_eq!(
            apply(
                "one\ntwo",
                &[
                    "delete 1 1",
                    "-two",
                    "\\ no newline",
                    "insert 2",
                    "+two",
                    "+three"
                ]
            ),
            "one\ntwo\nthree\n"
        );
    }

    #[test]
    fn a_chain_replays_from_the_root() {
        let chain = [
            document(&["insert 0", "+one", "+two"]),
            document(&["insert 2", "+three"]),
            document(&["delete 0 1", "-one"]),
        ];
        assert_eq!(replay(&chain).expect("a chain").text(), "two\nthree\n");
        assert_eq!(replay([]).expect("nothing"), State::empty());
    }

    #[test]
    fn deleting_everything_leaves_a_file_that_does_not_exist_yet() {
        let state = State::from_text("one\ntwo\n")
            .apply(&document(&["delete 0 2", "-one", "-two"]))
            .expect("should replay");
        assert!(state.is_empty());
        assert_eq!(state.text(), "");
    }

    #[test]
    fn an_operation_document_is_the_authority_and_the_file_is_the_cache() {
        // Replaying the same chain twice produces the same bytes, which is the
        // whole claim `cache/` rests on.
        let chain = [
            document(&["insert 0", "+first", "+second"]),
            document(&["delete 1 1", "-second", "insert 2", "+edited"]),
        ];
        let once = replay(&chain).expect("a chain");
        let again = replay(&chain).expect("a chain");
        assert_eq!(once, again);
        assert_eq!(once.text(), "first\nedited\n");

        // And the items round-trip through the file they materialise.
        assert_eq!(State::from_text(&once.text()), once);
    }

    #[test]
    fn operations_may_not_be_ordered_and_still_land_in_one_place() {
        // Positions are stated against a fixed parent, so a document assembled
        // out of order replays to what its canonical spelling replays to.
        let canonical = document(&["delete 0 1", "-a", "insert 3", "+z"]);
        let scrambled = OperationDocument {
            version: Version::CURRENT,
            forgets: None,
            result: None,
            operations: canonical.operations.iter().rev().cloned().collect(),
        };
        let parent = State::from_text("a\nb\nc\n");
        assert_eq!(
            parent.apply(&canonical).expect("canonical"),
            parent.apply(&scrambled).expect("scrambled")
        );
        assert_eq!(
            scrambled.operations,
            vec![
                Operation::insert(3, [Item::line("z")]),
                Operation::delete(0, [Item::line("a")]),
            ]
        );
    }

    #[test]
    fn a_result_that_lies_is_refused() {
        // Decision 0031: the document, its parent, or the replayer is wrong,
        // and carrying the disagreement forward would compound it silently.
        let honest = OperationDocument::parse(
            b"historica-v3\n\
              result c3f9c8c283a2b1f2f1896f27a01cbe3cddc0c9d93f752e4639035a0f5b36f6e8\n\
              \ninsert 0\n+one\n+two\n",
        )
        .expect("a document");
        assert_eq!(
            State::empty().apply(&honest).expect("a replay").text(),
            "one\ntwo\n"
        );

        let mut lying = honest.clone();
        lying.result = Some(digest(b"something else entirely"));
        assert!(matches!(
            State::empty().apply(&lying),
            Err(ReplayError::ResultDisagrees { .. })
        ));
    }

    #[test]
    fn a_state_showing_a_marker_is_not_held_to_a_result() {
        // Decision 0031 under decision 0014: the bytes that would hash are
        // marker bytes, not the bytes the recorder hashed, so structure is
        // provable and content is not.
        let parent = State::from_items([Item::line("kept"), Item::forgotten()]);
        let document = OperationDocument::parse(
            b"historica-v3\n\
              result c3f9c8c283a2b1f2f1896f27a01cbe3cddc0c9d93f752e4639035a0f5b36f6e8\n\
              \ninsert 0\n+new\n",
        )
        .expect("a document");
        // The result is for a state this replay cannot produce, and that is
        // not an error: verification is suspended where forgetting reaches.
        let replayed = parent.apply(&document).expect("a replay");
        assert!(replayed.items().iter().any(|item| item.forgotten));
    }
}
