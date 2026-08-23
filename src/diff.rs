//! Recording operations from an edited file.
//!
//! Specified by `docs/decisions/0009-diff.md`, which is the writing half of
//! decision 0007: [`crate::replay`] turns operations into a file, and this
//! turns a file back into the operations that would produce it.
//!
//! The decomposition this chooses is recorded once and never recomputed, so it
//! is not a rendering detail — every operation here is a permanent event that
//! all later merges are computed against. That is why the objective is a
//! decomposition that merges well rather than a minimal edit script, and it is
//! what the two configuration choices are for:
//!
//! - **Histogram**, which records the fewest operations of the algorithms
//!   measured in `examples/matchers.rs`, and so gives a concurrent edit the
//!   fewest places to interleave. The margin is small and 0009 says so.
//! - **No deadline, ever.** `similar`'s algorithms fall back to a simpler
//!   script when one expires, which would make what gets written down a
//!   function of how fast the machine was.
//!
//! Everything after the matching is Historica's: runs are maximal, a
//! replacement is anchored at the removed run's start, and the result obeys the
//! format's rules whatever the matcher hands over.

use similar::{Algorithm, DiffOp, capture_diff_slices};

use crate::core::RevisionId;
use crate::format::{Operation, OperationDocument, Piece, ResolutionDocument, Version, digest};
use crate::replay::State;

/// The matcher this tool records with.
///
/// Changing it changes what future revisions write down and rewrites nothing,
/// which is the same property decision 0007 noticed about merge rules.
const ALGORITHM: Algorithm = Algorithm::Histogram;

/// What one revision did, given the file at its parent and the file now.
///
/// `None` means the two are the same file: a revision that changes nothing
/// about a file names no operation document, because an absent fact is an
/// absent line.
///
/// The result always parses, and applying it to `parent` reproduces `child`
/// exactly. Those two properties are the whole contract — the particular
/// decomposition is this tool's judgement, and another tool's may differ
/// without either being wrong.
pub fn diff(parent: &State, child: &State) -> Option<OperationDocument> {
    let old = parent.items();
    let new = child.items();

    let mut deletes: Vec<Operation> = Vec::new();
    let mut inserts: Vec<Operation> = Vec::new();
    let mut delete = |at: usize, len: usize| {
        if len > 0 {
            deletes.push(Operation::delete(at, old[at..at + len].iter().cloned()));
        }
    };
    let mut insert = |at: usize, from: usize, len: usize| {
        if len > 0 {
            inserts.push(Operation::insert(at, new[from..from + len].iter().cloned()));
        }
    };

    for operation in capture_diff_slices(ALGORITHM, old, new) {
        match operation {
            DiffOp::Equal { .. } => {}
            DiffOp::Delete {
                old_index, old_len, ..
            } => delete(old_index, old_len),
            DiffOp::Insert {
                old_index,
                new_index,
                new_len,
            } => insert(old_index, new_index, new_len),
            // A replacement is minus lines above plus lines: both halves are
            // anchored at the removed run's start, which is also the only
            // position `similar` names for either of them.
            DiffOp::Replace {
                old_index,
                old_len,
                new_index,
                new_len,
            } => {
                delete(old_index, old_len);
                insert(old_index, new_index, new_len);
            }
        }
    }

    let operations = canonical(deletes, inserts);
    if operations.is_empty() {
        return None;
    }
    let mut document = OperationDocument {
        version: Version::V1,
        forgets: None,
        // Decision 0031: the document states the digest of the file it
        // produces, which is the file this diff was handed — the checkpoint
        // a hand replay is held to.
        result: Some(digest(child.text().as_bytes())),
        operations,
    };
    // Stating a result is version 3's vocabulary, so every document this
    // writes claims it; a document claims the lowest version that expresses
    // it, and `needs` is what knows.
    document.version = document.needs();
    Some(document)
}

/// The resolution a merge states, given what the walk proposed and what the
/// folder holds.
///
/// Decision 0032's writing half. The proposal is the event-graph merge's
/// answer — the tool's draft, which a person then edits — and `after` is what
/// they left. Aligning the two says which of the proposed items survived, and
/// a surviving item is *named* rather than restated: that is the decision's
/// load-bearing choice, because a restated line would be a new item and the
/// first merge reaching across this one would meet the same text twice.
///
/// `None` where the alignment leaves nothing at all. The grammar has no
/// spelling for a file with no pieces, and neither does the operation
/// document's: an empty file is one nothing can state.
pub fn resolve(
    proposed: &State,
    references: &[(RevisionId, usize)],
    after: &State,
) -> Option<ResolutionDocument> {
    let old = proposed.items();
    let new = after.items();

    // Which proposed items survive, and what the person wrote between them.
    // Positions are into `old`, which is what the matcher counts in.
    let mut dropped = vec![false; old.len()];
    let mut written: Vec<(usize, usize, usize)> = Vec::new();
    let mut drop = |at: usize, len: usize| {
        for gone in &mut dropped[at..at + len] {
            *gone = true;
        }
    };
    for operation in capture_diff_slices(ALGORITHM, old, new) {
        match operation {
            DiffOp::Equal { .. } => {}
            DiffOp::Delete {
                old_index, old_len, ..
            } => drop(old_index, old_len),
            DiffOp::Insert {
                old_index,
                new_index,
                new_len,
            } => written.push((old_index, new_index, new_len)),
            DiffOp::Replace {
                old_index,
                old_len,
                new_index,
                new_len,
            } => {
                drop(old_index, old_len);
                written.push((old_index, new_index, new_len));
            }
        }
    }

    let mut pieces: Vec<Piece> = Vec::new();
    // Pieces are maximal: a `keep` that continues the one before it is the
    // same run, and two inserts that meet are one insert. Exactly one byte
    // sequence parses per resolution, and this is where that is arranged.
    let push_keep = |pieces: &mut Vec<Piece>, document: RevisionId, at: usize| {
        if let Some(Piece::Keep {
            document: same,
            first,
            count,
        }) = pieces.last_mut()
            && *same == document
            && *first + *count == at
        {
            *count += 1;
            return;
        }
        pieces.push(Piece::Keep {
            document,
            first: at,
            count: 1,
        });
    };
    let push_insert = |pieces: &mut Vec<Piece>, items: &[crate::format::Item]| {
        if items.is_empty() {
            return;
        }
        if let Some(Piece::Insert { items: run }) = pieces.last_mut() {
            run.extend(items.iter().cloned());
            return;
        }
        pieces.push(Piece::Insert {
            items: items.to_vec(),
        });
    };

    let at_position = |pieces: &mut Vec<Piece>, position: usize| {
        for (_, from, len) in written.iter().filter(|(at, _, _)| *at == position) {
            push_insert(pieces, &new[*from..*from + *len]);
        }
    };
    for position in 0..old.len() {
        at_position(&mut pieces, position);
        if !dropped[position] {
            let (document, ordinal) = references[position];
            push_keep(&mut pieces, document, ordinal);
        }
    }
    // What the person wrote past the last proposed item.
    at_position(&mut pieces, old.len());

    if pieces.is_empty() {
        return None;
    }
    Some(ResolutionDocument {
        // `keep` and `result` are both version 3's vocabulary, so a
        // resolution never claims anything lower.
        version: Version::V3,
        // Decision 0031, which 0032 is what landed first for: the digest a
        // hand-assembled resolution is checked against.
        result: digest(after.text().as_bytes()),
        pieces,
    })
}

/// Put the operations into the one spelling the format has for them.
///
/// The matcher is not held to Historica's rules, so this holds it to them:
/// deletes that meet are one run, inserts at one position are one insert, and
/// an insert inside a removed run is moved to the run's start, which is where
/// this tool anchors a replacement anyway. Runs come out maximal, which is what
/// keeps a concurrent edit from interleaving inside one of them.
fn canonical(mut deletes: Vec<Operation>, mut inserts: Vec<Operation>) -> Vec<Operation> {
    deletes.sort_by_key(|operation| operation.at);
    let mut runs: Vec<Operation> = Vec::new();
    for operation in deletes {
        match runs.last_mut() {
            Some(last) if last.end() == operation.at => last.items.extend(operation.items),
            _ => runs.push(operation),
        }
    }

    for operation in &mut inserts {
        if let Some(run) = runs
            .iter()
            .find(|run| run.at < operation.at && operation.at < run.end())
        {
            operation.at = run.at;
        }
    }
    inserts.sort_by_key(|operation| operation.at);
    let mut added: Vec<Operation> = Vec::new();
    for operation in inserts {
        match added.last_mut() {
            Some(last) if last.at == operation.at => last.items.extend(operation.items),
            _ => added.push(operation),
        }
    }

    let mut operations = runs;
    operations.extend(added);
    operations.sort_by_key(|operation| (operation.at, operation.kind));
    operations
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A proposed merge whose items come from two documents, alternating by
    /// the `from` mask, and the resolution recording `after` against it.
    fn resolved(proposed: &str, from: &[u8], after: &str) -> Option<ResolutionDocument> {
        let mut names = [0u8; 32];
        names[0] = 1;
        let left = crate::core::RevisionId::from_bytes(names);
        names[0] = 2;
        let right = crate::core::RevisionId::from_bytes(names);

        // Each document's ordinals count only its own items, which is what
        // "in document order" means.
        let (mut mine, mut theirs) = (0, 0);
        let references: Vec<(RevisionId, usize)> = from
            .iter()
            .map(|side| {
                if *side == 0 {
                    mine += 1;
                    (left, mine - 1)
                } else {
                    theirs += 1;
                    (right, theirs - 1)
                }
            })
            .collect();

        let proposed = State::from_text(proposed);
        assert_eq!(proposed.len(), references.len(), "one name per item");
        let after = State::from_text(after);
        let resolution = resolve(&proposed, &references, &after);

        // Every resolution this produces parses, and assembles to the file it
        // was recorded from. Nothing below is worth reading if these two fail.
        if let Some(document) = &resolution {
            let bytes = document.write();
            ResolutionDocument::parse(&bytes)
                .unwrap_or_else(|error| panic!("should parse: {error}\n{document}"));
            let held = |name: &RevisionId| {
                let side = if *name == left { 0 } else { 1 };
                proposed
                    .items()
                    .iter()
                    .zip(from)
                    .filter(|(_, which)| **which == side)
                    .map(|(item, _)| item.clone())
                    .collect::<Vec<_>>()
            };
            let (mine, theirs) = (held(&left), held(&right));
            let assembled = crate::replay::assemble(document, |name| {
                Some(if *name == left { &mine } else { &theirs })
            })
            .expect("should assemble");
            assert_eq!(assembled.text(), after.text());
        } else {
            assert!(after.is_empty(), "only an empty file states nothing");
        }
        resolution
    }

    /// Decision 0032: a surviving line is named, never restated, because a
    /// restated line would be a new item and the next merge across this one
    /// would meet the same text twice.
    #[test]
    fn a_clean_merge_still_states_its_file_and_restates_nothing() {
        let resolution = resolved("a\nb\nc\n", &[0, 1, 0], "a\nb\nc\n").expect("a resolution");
        assert_eq!(
            resolution.pieces.len(),
            3,
            "three runs, because the items alternate between two documents"
        );
        assert_eq!(resolution.minted(), 0, "nothing is restated");
    }

    #[test]
    fn what_the_person_wrote_is_minted_and_the_rest_is_kept() {
        let resolution =
            resolved("a\nMINE\nTHEIRS\nz\n", &[0, 0, 1, 0], "a\nBOTH\nz\n").expect("a resolution");
        assert_eq!(resolution.minted(), 1);
        // A run split by a removal is two keeps, and they are not adjacent:
        // item 1 of the left document went.
        assert_eq!(
            resolution.pieces,
            vec![
                Piece::Keep {
                    document: resolution_document(1),
                    first: 0,
                    count: 1
                },
                Piece::Insert {
                    items: vec![crate::format::Item::line("BOTH")]
                },
                Piece::Keep {
                    document: resolution_document(1),
                    first: 2,
                    count: 1
                },
            ]
        );
    }

    #[test]
    fn runs_are_maximal_so_one_byte_sequence_spells_each_resolution() {
        // Four consecutive items of one document are one `keep`, and two
        // lines written in one place are one `insert`.
        let resolution = resolved("a\nb\nc\nd\n", &[0, 0, 0, 0], "a\nb\nc\nd\none\ntwo\n")
            .expect("a resolution");
        assert_eq!(resolution.pieces.len(), 2);
        assert!(matches!(resolution.pieces[0], Piece::Keep { count: 4, .. }));
        assert_eq!(resolution.minted(), 2);
    }

    #[test]
    fn a_file_resolved_to_nothing_has_no_spelling() {
        // The grammar has no resolution with no pieces, exactly as it has no
        // operation document with no operations.
        assert!(resolved("a\nb\n", &[0, 0], "").is_none());
    }

    fn resolution_document(byte: u8) -> RevisionId {
        let mut bytes = [0u8; 32];
        bytes[0] = byte;
        RevisionId::from_bytes(bytes)
    }

    fn record(parent: &str, child: &str) -> Option<OperationDocument> {
        let parent = State::from_text(parent);
        let child = State::from_text(child);
        let document = diff(&parent, &child);

        // Every document this produces parses, and replays to the file it was
        // recorded from. Nothing below is worth reading if these two fail.
        if let Some(document) = &document {
            let bytes = document.write();
            OperationDocument::parse(&bytes)
                .unwrap_or_else(|error| panic!("should parse: {error}\n{}", document));
            assert_eq!(
                parent.apply(document).expect("should replay").text(),
                child.text()
            );
        } else {
            assert_eq!(parent, child);
        }
        document
    }

    fn text(parent: &str, child: &str) -> String {
        let document = record(parent, child).expect("a document");
        String::from_utf8(document.write()).expect("UTF-8")
    }

    #[test]
    fn a_delete_quoting_a_forgotten_item_claims_the_version_that_spells_it() {
        // The one case an ordinary recording needs version 2: the parent
        // holds an item whose text was destroyed, and the delete quotes what
        // is left of it — the marker. Everything else claims version 1.
        use crate::format::Item;
        let parent = State::from_items([Item::line("kept"), Item::forgotten()]);
        let child = State::from_text("kept\n");
        let document = diff(&parent, &child).expect("a document");
        // The marker is version 2's vocabulary; the result the document also
        // states is version 3's, and a document claims the highest it needs.
        assert_eq!(document.version, Version::V3);
        let bytes = document.write();
        assert!(
            String::from_utf8(bytes.clone())
                .expect("UTF-8")
                .contains("\\ forgotten")
        );
        OperationDocument::parse(&bytes).expect("should parse");
        assert_eq!(
            parent.apply(&document).expect("should replay").text(),
            "kept\n"
        );
    }

    #[test]
    fn a_file_that_did_not_change_names_no_document() {
        assert!(record("one\ntwo\n", "one\ntwo\n").is_none());
        assert!(record("", "").is_none());
    }

    #[test]
    fn a_files_first_version_is_one_insert_of_every_line() {
        assert_eq!(
            text("", "one\ntwo\n"),
            format!(
                "historica-v3\nresult {}\n\ninsert 0\n+one\n+two\n",
                digest(b"one\ntwo\n")
            )
        );
    }

    #[test]
    fn a_replacement_is_anchored_at_the_removed_runs_start() {
        // Decision 0009 settling what 0007 spelled two ways.
        assert_eq!(
            text("a\nb\nc\n", "a\nB\nc\n"),
            format!(
                "historica-v3\nresult {}\n\ndelete 1 1\n-b\ninsert 1\n+B\n",
                digest(b"a\nB\nc\n")
            )
        );
    }

    #[test]
    fn runs_are_maximal() {
        // Three consecutive lines removed are one operation, not three: a
        // concurrent edit has one place to interleave rather than three.
        let document = record("a\nb\nc\nd\n", "a\n").expect("a document");
        assert_eq!(document.operations.len(), 1);
        assert_eq!(document.operations[0].items.len(), 3);

        let document = record("a\n", "a\nb\nc\nd\n").expect("a document");
        assert_eq!(document.operations.len(), 1);
        assert_eq!(document.operations[0].items.len(), 3);
    }

    #[test]
    fn a_line_between_two_rewritten_paragraphs_survives_them() {
        // A known cost, pinned so that it stays known. The blank line appears
        // once on each side, which makes it the best anchor in the file by
        // every matcher's reckoning, so all of them keep it — this is a cost of
        // decision 0007's line granularity and not of the algorithm behind it.
        // What survives is an item with an identity, in the middle of text its
        // author replaced, that a concurrent edit can anchor to.
        assert_eq!(
            text(
                "first paragraph\n\nsecond paragraph\n",
                "entirely new prose\n\nand more of it\n",
            ),
            format!(
                "historica-v3\nresult {}\n\n\
                 delete 0 1\n-first paragraph\ninsert 0\n+entirely new prose\n\
                 delete 2 1\n-second paragraph\ninsert 2\n+and more of it\n",
                digest(b"entirely new prose\n\nand more of it\n")
            )
        );
    }

    #[test]
    fn a_final_newline_needs_no_special_case() {
        // The terminator is part of the item, so a file that gains one differs
        // in that item and is recorded as a rewrite of the last line.
        assert_eq!(
            text("one\ntwo", "one\ntwo\n"),
            format!(
                "historica-v3\nresult {}\n\ndelete 1 1\n-two\n\\ no newline\ninsert 1\n+two\n",
                digest(b"one\ntwo\n")
            )
        );
        assert_eq!(
            text("one\ntwo\n", "one\ntwo"),
            format!(
                "historica-v3\nresult {}\n\ndelete 1 1\n-two\ninsert 1\n+two\n\\ no newline\n",
                digest(b"one\ntwo")
            )
        );
        // Appending past an unterminated last line rewrites it, which is what
        // replay demands and what decision 0007's third question asked about.
        assert_eq!(
            text("one\ntwo", "one\ntwo\nthree\n"),
            format!(
                "historica-v3\nresult {}\n\ndelete 1 1\n-two\n\\ no newline\ninsert 1\n+two\n+three\n",
                digest(b"one\ntwo\nthree\n")
            )
        );
    }

    #[test]
    fn a_carriage_return_is_content_and_survives_a_recording() {
        assert_eq!(
            text("a\r\nb\r\n", "a\r\nB\r\n"),
            format!(
                "historica-v3\nresult {}\n\ndelete 1 1\n-b\r\ninsert 1\n+B\r\n",
                digest(b"a\r\nB\r\n")
            )
        );
    }

    /// A deterministic generator, because a property test that cannot be
    /// replayed is a bug report nobody can act on.
    struct Rng(u64);

    impl Rng {
        fn next(&mut self) -> u64 {
            // xorshift64*, which is enough randomness to shuffle short lists.
            let mut x = self.0;
            x ^= x >> 12;
            x ^= x << 25;
            x ^= x >> 27;
            self.0 = x;
            x.wrapping_mul(0x2545_f491_4f6c_dd1d)
        }

        fn below(&mut self, bound: usize) -> usize {
            (self.next() % bound as u64) as usize
        }

        /// A file built from a small alphabet, so that repeated and blank lines
        /// are common rather than rare.
        fn file(&mut self, lines: usize) -> String {
            const ALPHABET: [&str; 6] = ["", "one", "two", "three", "one", "  "];
            let mut out = String::new();
            for _ in 0..self.below(lines) {
                out.push_str(ALPHABET[self.below(ALPHABET.len())]);
                out.push('\n');
            }
            // Sometimes the last line has no terminator.
            if self.below(4) == 0 && !out.is_empty() {
                out.pop();
            }
            out
        }
    }

    #[test]
    fn any_pair_of_files_records_a_document_that_replays_to_the_second() {
        // The acceptance test decision 0009 asks for: the round trip is exact,
        // the output parses, and identical files produce nothing.
        let mut rng = Rng(0x5eed_1e55);
        for _ in 0..2_000 {
            let parent = rng.file(9);
            let child = rng.file(9);
            record(&parent, &child);
        }
    }
}
