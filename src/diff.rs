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

use crate::format::{Operation, OperationDocument};
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
    Some(OperationDocument { operations })
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
    fn a_file_that_did_not_change_names_no_document() {
        assert!(record("one\ntwo\n", "one\ntwo\n").is_none());
        assert!(record("", "").is_none());
    }

    #[test]
    fn a_files_first_version_is_one_insert_of_every_line() {
        assert_eq!(
            text("", "one\ntwo\n"),
            "historica-v0\n\ninsert 0\n+one\n+two\n"
        );
    }

    #[test]
    fn a_replacement_is_anchored_at_the_removed_runs_start() {
        // Decision 0009 settling what 0007 spelled two ways.
        assert_eq!(
            text("a\nb\nc\n", "a\nB\nc\n"),
            "historica-v0\n\ndelete 1 1\n-b\ninsert 1\n+B\n"
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
            "historica-v0\n\n\
             delete 0 1\n-first paragraph\ninsert 0\n+entirely new prose\n\
             delete 2 1\n-second paragraph\ninsert 2\n+and more of it\n"
        );
    }

    #[test]
    fn a_final_newline_needs_no_special_case() {
        // The terminator is part of the item, so a file that gains one differs
        // in that item and is recorded as a rewrite of the last line.
        assert_eq!(
            text("one\ntwo", "one\ntwo\n"),
            "historica-v0\n\ndelete 1 1\n-two\n\\ no newline\ninsert 1\n+two\n"
        );
        assert_eq!(
            text("one\ntwo\n", "one\ntwo"),
            "historica-v0\n\ndelete 1 1\n-two\ninsert 1\n+two\n\\ no newline\n"
        );
        // Appending past an unterminated last line rewrites it, which is what
        // replay demands and what decision 0007's third question asked about.
        assert_eq!(
            text("one\ntwo", "one\ntwo\nthree\n"),
            "historica-v0\n\ndelete 1 1\n-two\n\\ no newline\ninsert 1\n+two\n+three\n"
        );
    }

    #[test]
    fn a_carriage_return_is_content_and_survives_a_recording() {
        assert_eq!(
            text("a\r\nb\r\n", "a\r\nB\r\n"),
            "historica-v0\n\ndelete 1 1\n-b\r\ninsert 1\n+B\r\n"
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
