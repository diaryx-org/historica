//! The Fugue paper's own executions, as test vectors.
//!
//! Decision 0007 adopts the insertion ordering of Fugue (Weidner and
//! Kleppmann, *The Art of the Fugue: Minimizing Interleaving in Collaborative
//! Text Editing*, arXiv:2305.00583). `tests/conformance.rs` holds two
//! implementations of that rule to each other, which is a strong check on the
//! two agreeing and no check at all on either matching the paper — the defect
//! recorded in 0007 was exactly a specification line both had transcribed the
//! same wrong way.
//!
//! These are the other kind of test: executions taken from the paper, with the
//! answer the paper states. Nothing here consults `historica`'s reading of
//! Fugue; the expected orders below come from the paper's own figures and its
//! Definition 4, and historica either produces them or does not.
//!
//! The paper's lists are of characters and historica's are of lines. Nothing
//! in Fugue depends on what an element holds, so an element here is a line
//! whose text is the paper's character.

use historica::core::RevisionId;
use historica::diff::diff;
use historica::format::{OperationDocument, digest};
use historica::merge::{Event, merge};
use historica::replay::State;

/// One revision of a hand-built history.
struct Written {
    revision: RevisionId,
    parents: Vec<RevisionId>,
    document: OperationDocument,
}

/// The name a revision is known by, as an identity.
///
/// Element identity in historica is `(revision, index)`, so a revision's
/// digest is what breaks a tie between two elements written at one place —
/// the paper's "lexicographic order of their IDs". Naming revisions here lets
/// a test state which identity is meant to be the larger one, rather than
/// hoping.
fn revision(name: &str) -> RevisionId {
    digest(name.as_bytes())
}

/// One revision, as the diff between the file its author saw and the file
/// they left.
fn written(name: &str, parents: &[&str], before: &str, after: &str) -> Written {
    Written {
        revision: revision(name),
        parents: parents.iter().copied().map(revision).collect(),
        document: diff(&State::from_text(before), &State::from_text(after))
            .unwrap_or_else(|| panic!("{name} changes something")),
    }
}

/// The file a set of revisions merges to.
fn merged(history: &[&Written]) -> String {
    merge(history.iter().map(|written| {
        Event::operations(
            written.revision,
            written.parents.clone(),
            digest(&written.document.write()),
            &written.document,
        )
    }))
    .expect("a history that merges")
    .state
    .text()
}

/// The paper's list, written the way its figures write it.
fn spelled(text: &str) -> String {
    text.lines().collect()
}

/// The execution of Figure 6, which both Fugue and FugueMax must satisfy.
///
/// > Starting from an empty list, three replicas concurrently insert A, B,
/// > and C. Replica 3 receives all three elements and puts them in some
/// > order; without loss of generality, it is A ≺ B ≺ C. Replica 1 receives A
/// > and C, then inserts X in between those elements to obtain AXC. Finally,
/// > Replica 1 receives B.
///
/// The paper's answer is `AXBC`, and it is forced: forward non-interleaving
/// requires `AX` to be consecutive, and the strong list specification
/// requires every replica to agree with Replica 3 that A ≺ B ≺ C.
///
/// Historica's files begin somewhere, so the three concurrent insertions
/// follow a shared first line rather than an empty file. That changes their
/// left origin from the list's start to that line and changes nothing else:
/// they remain three elements written concurrently at one position, ordered
/// against each other by identity alone.
#[test]
fn figure_6_puts_a_concurrent_insertion_beside_the_element_it_followed() {
    let (a, b, c) = concurrently_written();

    let root = written("the shared first line", &[], "", "L\n");
    let first = written(a, &["the shared first line"], "L\n", "L\nA\n");
    let second = written(b, &["the shared first line"], "L\n", "L\nB\n");
    let third = written(c, &["the shared first line"], "L\n", "L\nC\n");

    // Replica 3 receives all three and puts them in some order. The paper
    // takes A ≺ B ≺ C without loss of generality; here that is arranged by
    // which name has which digest, and asserted rather than assumed.
    assert_eq!(
        spelled(&merged(&[&root, &first, &second, &third])),
        "LABC",
        "the three concurrent elements are meant to be in the order A, B, C"
    );

    // Replica 1 has A and C, and writes X between them.
    let between = written(
        "the element written between A and C",
        &[a, c],
        "L\nA\nC\n",
        "L\nA\nX\nC\n",
    );
    assert_eq!(
        spelled(&merged(&[&root, &first, &third, &between])),
        "LAXC",
        "the state Replica 1 wrote X into"
    );

    // Finally, Replica 1 receives B.
    assert_eq!(
        spelled(&merged(&[&root, &first, &second, &third, &between])),
        "LAXBC",
        "Figure 6 of the Fugue paper"
    );
}

/// The execution of Figure 7, which separates Fugue from FugueMax.
///
/// Figure 6 again, with Replica 2 concurrently receiving A and B and writing
/// Y between *those*. Both X and Y are then right children of A with
/// different right origins — C and B — which is the only shape in which the
/// paper's two algorithms disagree:
///
/// > It turns out that in executions like Figure 7, Fugue might not satisfy
/// > maximal non-interleaving. Indeed, the previous paragraph explained that
/// > maximal non-interleaving implies X ≺ Y. But in the Fugue tree (Figure
/// > 8's left side), X and Y are same-side siblings, hence traversed in the
/// > lexicographic order of their IDs. This order might be Y ≺ X.
///
/// So the paper gives two answers, and which one an implementation produces
/// says which algorithm it implements:
///
/// - **FugueMax** orders right-side siblings by the reverse order of their
///   right origins, giving `AXYBC` — the only order satisfying the paper's
///   Definition 4.
/// - **Fugue** orders them by identity, giving `AXYBC` or `AYXBC` depending
///   on which identity is larger.
///
/// The names below are chosen so that X is the larger identity, which is the
/// case where the two answers differ. Historica produces `AYXBC`: it
/// implements Fugue, which the paper proves forward non-interleaving, and not
/// FugueMax, which the paper proves maximally non-interleaving.
#[test]
fn figure_7_shows_historica_implements_fugue_and_not_fuguemax() {
    let (a, b, c) = concurrently_written();

    // Two more identities, ordered against each other on purpose: the element
    // written between A and C is the larger, so that ordering the two by
    // identity puts the other one first. With them the other way round, Fugue
    // and FugueMax agree and this execution proves nothing.
    let mut pair = ["a hand at one keyboard", "a hand at another"];
    pair.sort_by_key(|name| revision(name));
    let (nearer, further) = (pair[0], pair[1]);
    assert!(
        revision(further) > revision(nearer),
        "X is meant to be the larger identity"
    );

    let root = written("the shared first line", &[], "", "L\n");
    let first = written(a, &["the shared first line"], "L\n", "L\nA\n");
    let second = written(b, &["the shared first line"], "L\n", "L\nB\n");
    let third = written(c, &["the shared first line"], "L\n", "L\nC\n");

    // Replica 1 has A and C, and writes X between them: right origin C.
    let x = written(further, &[a, c], "L\nA\nC\n", "L\nA\nX\nC\n");
    // Replica 2 has A and B, and writes Y between them: right origin B.
    let y = written(nearer, &[a, b], "L\nA\nB\n", "L\nA\nY\nB\n");

    assert_eq!(
        spelled(&merged(&[&root, &first, &third, &x])),
        "LAXC",
        "the state Replica 1 wrote X into"
    );
    assert_eq!(
        spelled(&merged(&[&root, &first, &second, &y])),
        "LAYB",
        "the state Replica 2 wrote Y into"
    );

    let whole = merged(&[&root, &first, &second, &third, &x, &y]);

    // What the paper's Definition 4 requires, and what historica does. The
    // difference is one transposition, and it is not a convergence defect:
    // every replica reads `AYXBC`, and Y and B are left un-consecutive where
    // FugueMax would have kept them together.
    assert_ne!(
        spelled(&whole),
        "LAXYBC",
        "historica is not expected to satisfy maximal non-interleaving — if it \
         now does, decision 0007 and this test both need rewriting"
    );
    assert_eq!(
        spelled(&whole),
        "LAYXBC",
        "Figure 7 of the Fugue paper, answered by Fugue's identity order"
    );
}

/// Three identities in ascending order, to stand for the paper's A ≺ B ≺ C.
///
/// The paper takes that order without loss of generality; historica's order
/// is by digest, so the labels are assigned to names rather than the other
/// way round. Sorted rather than hard-coded, so that a change to what a
/// revision is named by cannot quietly leave the execution meaning something
/// else.
fn concurrently_written() -> (&'static str, &'static str, &'static str) {
    let mut names = [
        "one hand at an empty file",
        "another hand at an empty file",
        "a third hand at an empty file",
    ];
    names.sort_by_key(|name| revision(name));
    (names[0], names[1], names[2])
}
