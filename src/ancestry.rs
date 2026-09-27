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

#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
pub(crate) mod proof;

/// Which events each event had seen, in whichever form the graph allows.
#[cfg_attr(verus_keep_ghost, verus_verify)]
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
        /// How many events there are, and rows. Read only by the proof,
        /// which only Verus compiles.
        #[allow(dead_code)]
        events: usize,
        /// Words per row: `ceil(events / 64)`.
        words: usize,
        /// `events * words` words, row `e` starting at `e * words`.
        bits: Vec<u64>,
    },
}

#[cfg_attr(verus_keep_ghost, cfg_eval, verus_verify)]
impl Ancestry {
    /// Work out what each event had seen, from a causal order and the parents.
    ///
    /// `order` must place every event after all of its parents; both it and
    /// `parents` are indexed by event. A caller that has already refused a
    /// cycle has that.
    ///
    /// Proved (decision 0076): for any two events, what this answers is
    /// exactly whether a walk down parent edges leads from one to the other —
    /// which, over such an order, is a partial order.
    #[cfg_attr(verus_keep_ghost, verifier::loop_isolation(false))]
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires
            proof::causal(proof::parents_of(parents@), order@),
            // The matrix has to be addressable: `events * ceil(events / 64)`
            // words.
            parents@.len() + 63 <= usize::MAX,
            parents@.len() * ((parents@.len() + 63) / 64) <= usize::MAX,
            forall|e: int, k: int| 0 <= e < parents@.len() && 0 <= k < parents@[e]@.len()
                ==> (#[trigger] parents@[e]@[k] as int) < parents@.len(),
        ensures
            r.holds(),
            r.events() == parents@.len(),
            forall|e: int, o: int| 0 <= e < parents@.len() && 0 <= o < parents@.len()
                ==> (#[trigger] r.knows_spec(e, o) <==> proof::reaches(proof::parents_of(parents@), e, o)),
    ))]
    pub(crate) fn new(order: &[usize], parents: &[Vec<usize>]) -> Self {
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost graph = proof::parents_of(parents@);
            let ghost n = parents@.len() as int;
        }
        // A chain is the shape a history has until somebody works offline, and
        // recognising it is what keeps the ordinary case off the matrix. Every
        // event after the first standing on exactly the one before it is the
        // whole test: a second root, a fork, or a join all fail it.
        if chained(order, parents) {
            let mut position = vec![0; parents.len()];
            let mut at: usize = 0;
            #[cfg_attr(verus_keep_ghost, verus_spec(
                invariant
                    at <= order@.len(),
                    order@.len() == parents@.len(),
                    position@.len() == parents@.len(),
                    proof::causal(graph, order@),
                    forall|j: int| 0 <= j < at ==> position@[#[trigger] order@[j] as int] as int == j,
                decreases order@.len() - at,
            ))]
            while at < order.len() {
                position[order[at]] = at;
                #[cfg(verus_keep_ghost)]
                proof! {
                    assert forall|j: int| 0 <= j <= at implies position@[#[trigger] order@[j] as int] as int == j by {
                        if j < at {
                            assert(order@[j] != order@[at as int]);
                        }
                    }
                }
                at += 1;
            }
            let chain = Ancestry::Chain { position };
            #[cfg(verus_keep_ghost)]
            proof! {
                assert forall|e: int, o: int| 0 <= e < n && 0 <= o < n
                    implies (#[trigger] chain.knows_spec(e, o) <==> proof::reaches(graph, e, o)) by {
                    proof::lemma_place(graph, order@, e);
                    proof::lemma_place(graph, order@, o);
                    let (i, j) = (proof::place(order@, e), proof::place(order@, o));
                    proof::lemma_chain_reaches(graph, order@, i, j);
                }
            }
            return chain;
        }

        // `div_ceil`, spelled out: the prover has no specification for it.
        #[allow(clippy::manual_div_ceil)]
        let words = (parents.len() + 63) / 64;
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(n <= 64 * (words as int)) by (nonlinear_arith) requires words == (n + 63) / 64, 0 <= n;
        }
        let mut bits = vec![0u64; parents.len() * words];
        #[cfg(verus_keep_ghost)]
        proof! {
            assert forall|e: int, w: int| 0 <= e < n && proof::place(order@, e) >= 0 && 0 <= w < words
                implies #[trigger] bits@[e * words + w] == 0u64 by {
                lemma_row_inside(n, words as int, e);
            }
        }
        let mut k: usize = 0;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant
                k <= order@.len(),
                order@.len() == parents@.len(),
                proof::causal(graph, order@),
                words == (n + 63) / 64,
                n <= 64 * (words as int),
                bits@.len() == n * words,
                bits@.len() <= usize::MAX,
                forall|j: int, o: int| 0 <= j < k && 0 <= o < n ==>
                    (#[trigger] row_bit(bits@, words as int, order@[j] as int, o)
                        <==> proof::reaches(graph, order@[j] as int, o)),
                forall|e: int, w: int| 0 <= e < n && proof::place(order@, e) >= k && 0 <= w < words
                    ==> #[trigger] bits@[e * words + w] == 0u64,
            decreases order@.len() - k,
        ))]
        while k < order.len() {
            let event = order[k];
            #[cfg(verus_keep_ghost)]
            proof_decl! {
                proof::lemma_place(graph, order@, event as int);
                let ghost before = bits@;
            }
            #[cfg(verus_keep_ghost)]
            proof! {
                assert forall|w: int| 0 <= w < words implies #[trigger] bits@[event * words + w] == 0u64 by {}
                assert forall|m: int| 0 <= m < parents@[event as int]@.len()
                    implies (#[trigger] parents@[event as int]@[m] as int) < n && parents@[event as int]@[m] != event by {
                    let i = proof::place(order@, event as int);
                    assert(graph[order@[i] as int][m] == parents@[event as int]@[m]);
                    let q = choose|q: int| 0 <= q < i && order@[q] == #[trigger] graph[order@[i] as int][m];
                    assert(order@[q] != order@[i]);
                }
            }
            #[cfg(verus_keep_ghost)]
            proof_with!(Ghost(n));
            self::row(&mut bits, words, event, &parents[event]);
            #[cfg(verus_keep_ghost)]
            proof! { self::lemma_row_done(graph, order@, before, bits@, words as int, k as int); }
            k += 1;
        }
        let matrix = Ancestry::Matrix {
            events: parents.len(),
            words,
            bits,
        };
        #[cfg(verus_keep_ghost)]
        proof! {
            assert forall|e: int, o: int| 0 <= e < n && 0 <= o < n
                implies (#[trigger] matrix.knows_spec(e, o) <==> proof::reaches(graph, e, o)) by {
                proof::lemma_place(graph, order@, e);
                let j = proof::place(order@, e);
                assert(row_bit(bits@, words as int, order@[j] as int, o) <==> proof::reaches(graph, order@[j] as int, o));
            }
            assert(n <= 64 * (words as int));
        }
        matrix
    }
}

/// Whether `order` is one chain: the first event has no parents, and every
/// other stands on exactly the one before it.
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verifier::loop_isolation(false))]
#[cfg_attr(verus_keep_ghost, verus_spec(r =>
    requires
        proof::causal(proof::parents_of(parents@), order@),
    ensures
        r == proof::chained(proof::parents_of(parents@), order@),
))]
fn chained(order: &[usize], parents: &[Vec<usize>]) -> bool {
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost graph = proof::parents_of(parents@); }
    let mut at: usize = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            at <= order@.len(),
            proof::causal(graph, order@),
            graph == proof::parents_of(parents@),
            at > 0 ==> graph[order@[0] as int].len() == 0,
            forall|i: int| 0 < i < at ==> #[trigger] graph[order@[i] as int] == seq![order@[i - 1]],
        decreases order@.len() - at,
    ))]
    while at < order.len() {
        let of = &parents[order[at]];
        #[cfg(verus_keep_ghost)]
        proof! { assert(graph[order@[at as int] as int] == of@); }
        let stands = if at == 0 {
            of.is_empty()
        } else {
            of.len() == 1 && of[0] == order[at - 1]
        };
        if !stands {
            #[cfg(verus_keep_ghost)]
            proof! {
                if at > 0 {
                    if graph[order@[at as int] as int] == seq![order@[at - 1]] {
                        assert(of@.len() == 1 && of@[0] == order@[at - 1]);
                    }
                }
            }
            return false;
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            if at > 0 {
                assert(of@ =~= seq![order@[at - 1]]);
            }
        }
        at += 1;
    }
    true
}

/// Row `event`: every row it stands on, unioned, and itself.
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verifier::loop_isolation(false))]
#[cfg_attr(verus_keep_ghost, verus_spec(
    with Ghost(n): Ghost<int>
    requires
        old(bits)@.len() == n * words,
        old(bits)@.len() <= usize::MAX,
        0 <= event < n,
        n <= 64 * words,
        forall|m: int| 0 <= m < of@.len() ==> (#[trigger] of@[m] as int) < n && of@[m] != event,
        forall|w: int| 0 <= w < words ==> #[trigger] old(bits)@[event * words + w] == 0u64,
    ensures
        final(bits)@.len() == old(bits)@.len(),
        forall|o: int| 0 <= o < n ==> (#[trigger] row_bit(final(bits)@, words as int, event as int, o)
            <==> (o == event || exists|m: int| 0 <= m < of@.len()
                && row_bit(old(bits)@, words as int, of@[m] as int, o))),
        forall|i: int| 0 <= i < old(bits)@.len() && !(event * words <= i < event * words + words)
            ==> #[trigger] final(bits)@[i] == old(bits)@[i],
))]
fn row(bits: &mut [u64], words: usize, event: usize, of: &[usize]) {
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost start = bits@;
        lemma_row_inside(n, words as int, event as int);
        assert forall|o: int| 0 <= o < n implies !(#[trigger] row_bit(start, words as int, event as int, o)) by {
            lemma_word(n, words as int, o);
            assert(start[event * words + o / 64] == 0u64);
            lemma_bit_zero((o % 64) as u64);
        }
    }
    let mut m: usize = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            m <= of@.len(),
            bits@.len() == start.len(),
            forall|o: int| 0 <= o < n ==> (#[trigger] row_bit(bits@, words as int, event as int, o)
                <==> exists|m2: int| 0 <= m2 < m && row_bit(start, words as int, of@[m2] as int, o)),
            forall|i: int| 0 <= i < start.len() && !(event * words <= i < event * words + words)
                ==> #[trigger] bits@[i] == start[i],
        decreases of@.len() - m,
    ))]
    while m < of.len() {
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost before = bits@;
            let ghost from = of@[m as int] as int;
            lemma_row_inside(n, words as int, from);
        }
        union_row(bits, words, event, of[m]);
        #[cfg(verus_keep_ghost)]
        proof! {
            assert forall|o: int| 0 <= o < n implies (#[trigger] row_bit(bits@, words as int, event as int, o)
                <==> exists|m2: int| 0 <= m2 < m + 1 && row_bit(start, words as int, of@[m2] as int, o)) by {
                let w = o / 64;
                lemma_word(n, words as int, o);
                lemma_bit_or(before[event * words + w], before[from * words + w], (o % 64) as u64);
                lemma_rows_apart(words as int, from, w, event as int);
                lemma_row_inside(n, words as int, from);
                assert(before[from * words + w] == start[from * words + w]);
                assert(bits@[event * words + w] == before[event * words + w] | before[from * words + w]);
                let now = row_bit(bits@, words as int, event as int, o);
                assert(now <==> (row_bit(before, words as int, event as int, o) || row_bit(start, words as int, from, o)));
                if exists|m2: int| 0 <= m2 < m + 1 && row_bit(start, words as int, of@[m2] as int, o) {
                    let m2 = choose|m2: int| 0 <= m2 < m + 1 && row_bit(start, words as int, of@[m2] as int, o);
                    if m2 < m {
                        assert(row_bit(before, words as int, event as int, o));
                    }
                }
                if now {
                    if row_bit(before, words as int, event as int, o) {
                        let m2 = choose|m2: int| 0 <= m2 < m && row_bit(start, words as int, of@[m2] as int, o);
                        assert(0 <= m2 < m + 1);
                    } else {
                        assert(row_bit(start, words as int, of@[m as int] as int, o));
                    }
                }
            }
            assert forall|i: int| 0 <= i < start.len() && !(event * words <= i < event * words + words)
                implies #[trigger] bits@[i] == start[i] by {
                assert(bits@[i] == before[i]);
            }
        }
        m += 1;
    }
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost before = bits@;
        lemma_word(n, words as int, event as int);
    }
    bits[event * words + event / 64] |= 1 << (event % 64);
    #[cfg(verus_keep_ghost)]
    proof! {
        assert forall|o: int| 0 <= o < n implies (#[trigger] row_bit(bits@, words as int, event as int, o)
            <==> (o == event || exists|m2: int| 0 <= m2 < of@.len()
                && row_bit(start, words as int, of@[m2] as int, o))) by {
            let w = o / 64;
            lemma_word(n, words as int, o);
            let at = event * words + w;
            if w == event / 64 {
                assert(bits@[at] == before[at] | (1u64 << (event % 64) as u64));
                lemma_bit_one(before[at], (event % 64) as u64, (o % 64) as u64);
                assert(o == event <==> o % 64 == event % 64);
            } else {
                assert(o != event);
                lemma_rows_apart_word(words as int, event as int, w, (event / 64) as int);
                assert(bits@[at] == before[at]);
            }
            assert(row_bit(before, words as int, event as int, o) <==> exists|m2: int| 0 <= m2 < of@.len()
                && row_bit(start, words as int, of@[m2] as int, o));
        }
    }
}

/// `row[into] |= row[from]`, for two rows of one matrix.
///
/// Word by word, by index: `into` is never `from`, because an event is
/// never its own parent in a causal order.
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verifier::loop_isolation(false))]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires
        into != from,
        into * words + words <= old(bits)@.len(),
        from * words + words <= old(bits)@.len(),
        old(bits)@.len() <= usize::MAX,
    ensures
        final(bits)@.len() == old(bits)@.len(),
        forall|w: int| 0 <= w < words ==> #[trigger] final(bits)@[into * words + w]
            == old(bits)@[into * words + w] | old(bits)@[from * words + w],
        forall|i: int| 0 <= i < old(bits)@.len() && !(into * words <= i < into * words + words)
            ==> #[trigger] final(bits)@[i] == old(bits)@[i],
))]
fn union_row(bits: &mut [u64], words: usize, into: usize, from: usize) {
    let mut w: usize = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            w <= words,
            into != from,
            into * words + words <= old(bits)@.len(),
            from * words + words <= old(bits)@.len(),
            bits@.len() == old(bits)@.len(),
            forall|v: int| 0 <= v < w ==> #[trigger] bits@[into * words + v]
                == old(bits)@[into * words + v] | old(bits)@[from * words + v],
            forall|i: int| 0 <= i < old(bits)@.len() && !(into * words <= i < into * words + w)
                ==> #[trigger] bits@[i] == old(bits)@[i],
        decreases words - w,
    ))]
    while w < words {
        #[cfg(verus_keep_ghost)]
        proof! { lemma_rows_apart(words as int, from as int, w as int, into as int); }
        let source = bits[from * words + w];
        bits[into * words + w] |= source;
        w += 1;
    }
}

#[cfg_attr(verus_keep_ghost, cfg_eval, verus_verify)]
impl Ancestry {
    /// Whether `other` is in `event`'s causal past, `event` itself included.
    ///
    /// The view an insertion is placed against: an element written earlier by
    /// this same revision is one its author can see, because they wrote it.
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires
            self.holds(),
            event < self.events(),
            other < self.events(),
        ensures
            r == self.knows_spec(event as int, other as int),
    ))]
    pub(crate) fn knows(&self, event: usize, other: usize) -> bool {
        match self {
            Ancestry::Chain { position } => position[other] <= position[event],
            Ancestry::Matrix { words, bits, .. } => {
                #[cfg(verus_keep_ghost)]
                proof! {
                    let (n, w) = (self.events() as int, *words as int);
                    assert(event * w + w <= n * w) by (nonlinear_arith)
                        requires event < n, 0 <= w;
                    assert(other / 64 < w) by (nonlinear_arith)
                        requires 0 <= other < n, n <= 64 * w;
                    assert(event * w <= n * w) by (nonlinear_arith)
                        requires event < n, 0 <= w;
                }
                bits[event * words + other / 64] & (1 << (other % 64)) != 0
            }
        }
    }

    /// Whether `other` is strictly in `event`'s past.
    ///
    /// The view an operation's positions are counted into: what the author had
    /// before they started, which is their parents' state and nothing of their
    /// own.
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires
            self.holds(),
            event < self.events(),
            other < self.events(),
        ensures
            r == (other != event && self.knows_spec(event as int, other as int)),
    ))]
    pub(crate) fn saw(&self, event: usize, other: usize) -> bool {
        other != event && self.knows(event, other)
    }
}

#[cfg(verus_keep_ghost)]
verus! {

/// Whether bit `o` of row `e` is set.
spec fn row_bit(bits: Seq<u64>, words: int, e: int, o: int) -> bool {
    bits[e * words + o / 64] & (1u64 << (o % 64) as u64) != 0
}

proof fn lemma_bit_or(a: u64, b: u64, i: u64)
    requires i < 64
    ensures ((a | b) & (1u64 << i)) != 0 <==> ((a & (1u64 << i)) != 0 || (b & (1u64 << i)) != 0)
{
    assert(((a | b) & (1u64 << i)) != 0 <==> ((a & (1u64 << i)) != 0 || (b & (1u64 << i)) != 0)) by (bit_vector)
        requires i < 64;
}

proof fn lemma_bit_one(a: u64, i: u64, j: u64)
    requires i < 64, j < 64
    ensures ((a | (1u64 << i)) & (1u64 << j)) != 0 <==> ((a & (1u64 << j)) != 0 || i == j)
{
    assert(((a | (1u64 << i)) & (1u64 << j)) != 0 <==> ((a & (1u64 << j)) != 0 || i == j)) by (bit_vector)
        requires i < 64, j < 64;
}

proof fn lemma_bit_zero(i: u64)
    requires i < 64
    ensures (0u64 & (1u64 << i)) == 0
{
    assert((0u64 & (1u64 << i)) == 0) by (bit_vector)
        requires i < 64;
}

/// Row `e` of a matrix of `n` rows lies inside it.
proof fn lemma_row_inside(n: int, words: int, e: int)
    requires 0 <= e < n, 0 <= words
    ensures e * words + words <= n * words, 0 <= e * words
{
    assert(e * words + words <= n * words) by (nonlinear_arith) requires 0 <= e < n, 0 <= words;
    assert(0 <= e * words) by (nonlinear_arith) requires 0 <= e, 0 <= words;
}

/// Bit `o` of any row is in one of its words.
proof fn lemma_word(n: int, words: int, o: int)
    requires 0 <= o < n, n <= 64 * words
    ensures 0 <= o / 64 < words, 0 <= o % 64 < 64
{
    assert(o / 64 < words) by (nonlinear_arith) requires 0 <= o < n, n <= 64 * words;
}

/// Two rows share no word.
proof fn lemma_rows_apart(words: int, a: int, w: int, b: int)
    requires a != b, 0 <= a, 0 <= b, 0 <= w < words
    ensures !(b * words <= a * words + w < b * words + words),
{
    assert(!(b * words <= a * words + w < b * words + words)) by (nonlinear_arith)
        requires a != b, 0 <= a, 0 <= b, 0 <= w < words;
}

/// Two words of one row are different words.
proof fn lemma_rows_apart_word(words: int, e: int, v: int, w: int)
    requires v != w
    ensures e * words + v != e * words + w
{
}

/// One more event's row is done: the rows before it still say what their
/// events reach, and so does this one, and the rows after are still empty.
proof fn lemma_row_done(graph: Seq<Seq<usize>>, order: Seq<usize>, before: Seq<u64>, after: Seq<u64>, words: int, k: int)
    requires
        proof::causal(graph, order),
        0 <= k < order.len(),
        words == (graph.len() + 63) / 64,
        graph.len() <= usize::MAX,
        before.len() == graph.len() * words,
        after.len() == before.len(),
        forall|j: int, o: int| 0 <= j < k && 0 <= o < graph.len() ==>
            (#[trigger] row_bit(before, words, order[j] as int, o) <==> proof::reaches(graph, order[j] as int, o)),
        forall|o: int| 0 <= o < graph.len() ==> (#[trigger] row_bit(after, words, order[k] as int, o)
            <==> (o == order[k] as int || exists|m: int| 0 <= m < graph[order[k] as int].len()
                && row_bit(before, words, graph[order[k] as int][m] as int, o))),
        forall|i: int| 0 <= i < before.len() && !(order[k] * words <= i < order[k] * words + words)
            ==> #[trigger] after[i] == before[i],
        forall|e: int, w: int| 0 <= e < graph.len() && proof::place(order, e) >= k && 0 <= w < words
            ==> #[trigger] before[e * words + w] == 0u64,
    ensures
        forall|j: int, o: int| 0 <= j < k + 1 && 0 <= o < graph.len() ==>
            (#[trigger] row_bit(after, words, order[j] as int, o) <==> proof::reaches(graph, order[j] as int, o)),
        forall|e: int, w: int| 0 <= e < graph.len() && proof::place(order, e) >= k + 1 && 0 <= w < words
            ==> #[trigger] after[e * words + w] == 0u64,
{
    let n = graph.len() as int;
    let event = order[k] as int;
    assert(n <= 64 * words) by (nonlinear_arith) requires words == (n + 63) / 64, 0 <= n;
    proof::lemma_place(graph, order, event);
    assert forall|j: int, o: int| 0 <= j < k + 1 && 0 <= o < n implies
        (#[trigger] row_bit(after, words, order[j] as int, o) <==> proof::reaches(graph, order[j] as int, o)) by {
        lemma_word(n, words, o);
        if j < k {
            let e = order[j] as int;
            assert(order[j] != order[k]);
            lemma_rows_apart(words, e, o / 64, event);
            lemma_row_inside(n, words, e);
            assert(after[e * words + o / 64] == before[e * words + o / 64]);
            assert(row_bit(before, words, e, o) <==> proof::reaches(graph, e, o));
        } else {
            assert(order[j] == order[k]);
            assert(proof::place(order, event) == k);
            let bit = row_bit(after, words, event, o);
            assert(bit <==> (o == event || exists|m: int| 0 <= m < graph[event].len()
                && row_bit(before, words, graph[event][m] as int, o)));
            if proof::reaches(graph, event, o) && o != event {
                proof::lemma_reaches_split(graph, event, o);
                let p = choose|p: int| 0 <= p < n && #[trigger] graph[event].contains(p as usize)
                    && proof::reaches(graph, p, o);
                let m = choose|m: int| 0 <= m < graph[event].len() && graph[event][m] == p as usize;
                assert(graph[order[k] as int][m] == p as usize);
                let q = choose|q: int| 0 <= q < k && order[q] == #[trigger] graph[order[k] as int][m];
                assert(order[q] as int == p);
                assert(row_bit(before, words, order[q] as int, o) <==> proof::reaches(graph, order[q] as int, o));
                assert(row_bit(before, words, graph[event][m] as int, o));
                assert(bit);
            }
            if o == event {
                proof::lemma_reaches_self(graph, event);
            }
            if bit && o != event {
                let m = choose|m: int| 0 <= m < graph[event].len() && row_bit(before, words, graph[event][m] as int, o);
                let p = graph[event][m] as int;
                assert(graph[order[k] as int][m] == p as usize);
                let q = choose|q: int| 0 <= q < k && order[q] == #[trigger] graph[order[k] as int][m];
                assert(order[q] as int == p);
                assert(row_bit(before, words, order[q] as int, o) <==> proof::reaches(graph, order[q] as int, o));
                assert(graph[event].contains(p as usize));
                proof::lemma_reaches_step(graph, event, p, o);
            }
        }
    }
    assert forall|e: int, w: int| 0 <= e < n && proof::place(order, e) >= k + 1 && 0 <= w < words
        implies #[trigger] after[e * words + w] == 0u64 by {
        proof::lemma_place(graph, order, e);
        assert(e != event);
        lemma_rows_apart(words, e, w, event);
        lemma_row_inside(n, words, e);
    }
}

impl Ancestry {
    /// How many events this answers for.
    pub(crate) closed spec fn events(&self) -> nat {
        match self {
            Ancestry::Chain { position } => position@.len(),
            Ancestry::Matrix { events, .. } => *events as nat,
        }
    }

    /// The shape `new` builds: a position per event, or a row of words per
    /// event with a bit per event in it.
    pub(crate) closed spec fn holds(&self) -> bool {
        match self {
            Ancestry::Chain { .. } => true,
            Ancestry::Matrix { events, words, bits } => {
                &&& bits@.len() == *events as int * *words as int
                &&& bits@.len() <= usize::MAX
                &&& *events as int <= 64 * *words as int
            },
        }
    }

    /// Whether `other` is in `event`'s causal past, `event` itself included,
    /// as this answers it.
    pub(crate) closed spec fn knows_spec(&self, event: int, other: int) -> bool {
        match self {
            Ancestry::Chain { position } => position@[other] <= position@[event],
            Ancestry::Matrix { words, bits, .. } =>
                bits@[event * *words as int + other / 64] & (1u64 << (other % 64) as u64) != 0,
        }
    }
}

} // verus!

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
