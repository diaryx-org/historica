//! Which events each event had seen.
//!
//! Two of this crate's merges — [`crate::merge`] over one file's items and
//! [`crate::tree`] over the file set — decide the same thing before they
//! decide anything else: whether one revision was in another's causal past.
//! Both walk a whole ancestry to answer it, both throw the answer away at the
//! end, and both used to keep it as a set per revision. This is that structure,
//! once, so the two cannot pay different prices for one question.
//!
//! The question is asked O(events × items) times in a merge, so it has to be
//! O(1). What changes is how much has to be stored to answer it.
//!
//! A history with no fork in it needs almost nothing: the causal order is
//! total, so an event's past is everything before it, and a position in that
//! order answers by comparison. That is the ordinary case — one person, one
//! device, or any history whose merges are all behind it — and it costs one
//! `usize` per event.
//!
//! A history with concurrency in it has no such shortcut and pays a bit per
//! pair. That is quadratic in the number of events, which is the honest cost
//! of an ancestry question over a DAG; what it is not is quadratic in
//! *allocations*, which is what a set per event was.

/// Which events each event had seen, in whichever form the graph allows.
pub(crate) enum Ancestry {
    /// One chain: `position[e]` is where `e` sits in the single causal order,
    /// and `o` is in `e`'s past exactly when it sits no later.
    Chain {
        /// Where each event sits in the causal order.
        position: Vec<usize>,
    },
    /// A DAG: one row of bits per event, a set bit meaning "in this event's
    /// causal past, itself included".
    Matrix {
        /// Words per row: `ceil(events / 64)`.
        words: usize,
        /// `events * words` words, row `e` starting at `e * words`.
        bits: Vec<u64>,
    },
}

impl Ancestry {
    /// Work out what each event had seen, from a causal order and the parents.
    ///
    /// `order` must place every event after all of its parents; both it and
    /// `parents` are indexed by event. A caller that has already refused a
    /// cycle has that.
    pub(crate) fn new(order: &[usize], parents: &[Vec<usize>]) -> Self {
        // A chain is the shape a history has until somebody works offline, and
        // recognising it is what keeps the ordinary case off the matrix. Every
        // event after the first standing on exactly the one before it is the
        // whole test: a second root, a fork, or a join all fail it.
        let chain = order.iter().enumerate().all(|(at, event)| match at {
            0 => parents[*event].is_empty(),
            _ => parents[*event] == [order[at - 1]],
        });
        if chain {
            let mut position = vec![0; parents.len()];
            for (at, event) in order.iter().enumerate() {
                position[*event] = at;
            }
            return Ancestry::Chain { position };
        }

        let words = parents.len().div_ceil(64);
        let mut bits = vec![0u64; parents.len() * words];
        for event in order {
            for parent in &parents[*event] {
                union_row(&mut bits, words, *event, *parent);
            }
            bits[event * words + event / 64] |= 1 << (event % 64);
        }
        Ancestry::Matrix { words, bits }
    }

    /// Whether `other` is in `event`'s causal past, `event` itself included.
    ///
    /// The view an insertion is placed against: an element written earlier by
    /// this same revision is one its author can see, because they wrote it.
    pub(crate) fn knows(&self, event: usize, other: usize) -> bool {
        match self {
            Ancestry::Chain { position } => position[other] <= position[event],
            Ancestry::Matrix { words, bits } => {
                bits[event * words + other / 64] & (1 << (other % 64)) != 0
            }
        }
    }

    /// Whether `other` is strictly in `event`'s past.
    ///
    /// The view an operation's positions are counted into: what the author had
    /// before they started, which is their parents' state and nothing of their
    /// own.
    pub(crate) fn saw(&self, event: usize, other: usize) -> bool {
        other != event && self.knows(event, other)
    }
}

/// `row[into] |= row[from]`, for two rows of one matrix.
fn union_row(bits: &mut [u64], words: usize, into: usize, from: usize) {
    debug_assert_ne!(into, from, "an event cannot be its own parent");
    // Split at the later row's start, so the two are provably disjoint slices
    // and one can be read while the other is written.
    if into < from {
        let (earlier, later) = bits.split_at_mut(from * words);
        let (target, source) = (&mut earlier[into * words..][..words], &later[..words]);
        for (target, source) in target.iter_mut().zip(source) {
            *target |= *source;
        }
    } else {
        let (earlier, later) = bits.split_at_mut(into * words);
        let (target, source) = (&mut later[..words], &earlier[from * words..][..words]);
        for (target, source) in target.iter_mut().zip(source) {
            *target |= *source;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A chain, stored as one, answering the same questions as the matrix
    /// would. The representation is an optimisation and nothing else.
    #[test]
    fn a_chain_and_a_matrix_answer_alike() {
        let parents = vec![vec![], vec![0], vec![1], vec![2]];
        let order = vec![0, 1, 2, 3];
        let chain = Ancestry::new(&order, &parents);
        assert!(matches!(chain, Ancestry::Chain { .. }));

        // The same graph, forced onto the matrix by a fork nobody reads.
        let forked = vec![vec![], vec![0], vec![1], vec![2], vec![0]];
        let matrix = Ancestry::new(&[0, 1, 2, 3, 4], &forked);
        assert!(matches!(matrix, Ancestry::Matrix { .. }));

        for event in 0..4 {
            for other in 0..4 {
                assert_eq!(
                    chain.knows(event, other),
                    matrix.knows(event, other),
                    "{event} and {other} are answered differently"
                );
                assert_eq!(chain.knows(event, other), other <= event);
            }
        }
    }

    /// A fork: neither side is in the other's past, and the join holds both.
    #[test]
    fn a_fork_is_concurrent_and_a_join_sees_everything() {
        //   0 ── 1 ─┐
        //     └─ 2 ─┴─ 3
        let parents = vec![vec![], vec![0], vec![0], vec![1, 2]];
        let ancestry = Ancestry::new(&[0, 1, 2, 3], &parents);
        assert!(matches!(ancestry, Ancestry::Matrix { .. }));

        assert!(!ancestry.knows(1, 2));
        assert!(!ancestry.knows(2, 1));
        assert!(ancestry.knows(1, 0));
        assert!(ancestry.knows(2, 0));
        for other in 0..4 {
            assert!(ancestry.knows(3, other), "the join has not seen {other}");
        }
        assert!(ancestry.saw(3, 0));
        assert!(!ancestry.saw(3, 3), "an event is not strictly its own past");
        assert!(ancestry.knows(3, 3), "an event knows itself");
    }

    /// More events than one word holds, so a row spans several.
    #[test]
    fn a_row_spans_as_many_words_as_it_needs() {
        let count = 130;
        let mut parents: Vec<Vec<usize>> = vec![vec![]];
        for event in 1..count {
            parents.push(vec![event - 1]);
        }
        // A second root forces the matrix without changing anyone's ancestry.
        parents.push(vec![]);
        let order: Vec<usize> = (0..=count).collect();
        let ancestry = Ancestry::new(&order, &parents);
        assert!(matches!(ancestry, Ancestry::Matrix { .. }));

        for other in 0..count {
            assert!(ancestry.knows(count - 1, other), "lost {other}");
        }
        assert!(!ancestry.knows(count - 1, count));
        assert!(!ancestry.knows(0, 1));
    }
}
