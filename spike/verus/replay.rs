//! A Verus port of `crate::replay::State::applied`, with its contract stated.
//!
//! This is a spike, not the crate: it asks whether the linear replay step can
//! be *proven* to do what `replay.rs`'s rustdoc says it does. The code is the
//! same two-pass shape — count deletions and insertions against the parent,
//! then walk the parent once — with two deliberate differences:
//!
//! - `inserted` is a `Vec<Vec<Item>>` of length `len + 1` rather than a
//!   `BTreeMap<usize, Vec<Item>>`. Same map, one index per gap; Verus's
//!   specification of `BTreeMap` is thin and the map was never the point.
//! - The digest a document states (decision 0031) is held against an
//!   uninterpreted `digest` function. SHA-256 is below the line: what is
//!   proven is that the check is *made* whenever the crate makes it.
//!
//! The specification is written first and never mentions the implementation:
//! `deleted_at` and `inserts_at` read the document, `result` assembles the
//! file from them, and `applied` is held to `result`.

use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// The data, as `crate::format` has it.
// ---------------------------------------------------------------------------

/// One line of a file, terminator excluded. Mirrors `format::Item`.
pub struct Item {
    pub text: Vec<u8>,
    pub terminated: bool,
    pub forgotten: bool,
}

/// The mathematical item: what `Item` is once its bytes are a sequence.
pub struct ItemS {
    pub text: Seq<u8>,
    pub terminated: bool,
    pub forgotten: bool,
}

impl View for Item {
    type V = ItemS;
    open spec fn view(&self) -> ItemS {
        ItemS { text: self.text@, terminated: self.terminated, forgotten: self.forgotten }
    }
}

impl DeepView for Item {
    type V = ItemS;
    open spec fn deep_view(&self) -> ItemS { self@ }
}

impl Item {
    /// `format::Item::matches`, with its meaning stated: equality up to
    /// forgetting, as decision 0014 has it.
    pub fn matches(&self, found: &Item) -> (r: bool)
        ensures r == matches_s(self@, found@)
    {
        self.terminated == found.terminated
            && (self.forgotten || found.forgotten || bytes_equal(&self.text, &found.text))
    }

    pub fn clone(&self) -> (r: Item)
        ensures r@ == self@
    {
        Item { text: clone_bytes(&self.text), terminated: self.terminated, forgotten: self.forgotten }
    }
}

pub open spec fn matches_s(recorded: ItemS, found: ItemS) -> bool {
    recorded.terminated == found.terminated
        && (recorded.forgotten || found.forgotten || recorded.text == found.text)
}

fn bytes_equal(a: &Vec<u8>, b: &Vec<u8>) -> (r: bool)
    ensures r == (a@ == b@)
{
    if a.len() != b.len() {
        return false;
    }
    let mut i: usize = 0;
    while i < a.len()
        invariant i <= a.len(), a.len() == b.len(), forall|j: int| 0 <= j < i ==> a@[j] == b@[j]
        decreases a.len() - i
    {
        if a[i] != b[i] {
            return false;
        }
        i += 1;
    }
    assert(a@ =~= b@);
    true
}

fn clone_bytes(a: &Vec<u8>) -> (r: Vec<u8>)
    ensures r@ == a@
{
    let mut out: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant i <= a.len(), out@ == a@.take(i as int)
        decreases a.len() - i
    {
        out.push(a[i]);
        assert(out@ =~= a@.take(i as int + 1));
        i += 1;
    }
    assert(out@ =~= a@);
    out
}

pub enum OperationKind { Delete, Insert }

/// Mirrors `format::Operation`.
pub struct Operation {
    pub kind: OperationKind,
    pub at: usize,
    pub items: Vec<Item>,
}

pub struct OperationS {
    pub delete: bool,
    pub at: int,
    pub items: Seq<ItemS>,
}

impl View for Operation {
    type V = OperationS;
    open spec fn view(&self) -> OperationS {
        OperationS { delete: self.kind is Delete, at: self.at as int, items: self.items.deep_view() }
    }
}

impl DeepView for Operation {
    type V = OperationS;
    open spec fn deep_view(&self) -> OperationS { self@ }
}

/// Mirrors `format::OperationDocument`, minus `forgets`, which replay does
/// not read.
pub struct OperationDocument {
    pub result: Option<u64>,
    pub operations: Vec<Operation>,
}

/// Decision 0031's digest, uninterpreted. Below the line.
pub uninterp spec fn digest_s(items: Seq<ItemS>) -> u64;

#[verifier::external_body]
pub fn digest(items: &Vec<Item>) -> (r: u64)
    ensures r == digest_s(items.deep_view())
{
    unimplemented!()
}

// ---------------------------------------------------------------------------
// The specification: what a document says, read off the document.
// ---------------------------------------------------------------------------

/// Whether some `delete` in `ops` covers parent position `p`.
pub open spec fn deleted_at(ops: Seq<OperationS>, p: int) -> bool {
    exists|k: int| 0 <= k < ops.len() && ops[k].delete && ops[k].at <= p < ops[k].at + ops[k].items.len()
}

/// The items every `insert` at parent position `p` contributes, in document
/// order.
pub open spec fn inserts_at(ops: Seq<OperationS>, p: int) -> Seq<ItemS>
    decreases ops.len()
{
    if ops.len() == 0 {
        Seq::empty()
    } else {
        let last = ops[ops.len() - 1];
        let before = inserts_at(ops.drop_last(), p);
        if !last.delete && last.at == p { before + last.items } else { before }
    }
}

/// The file after the document, for parent positions `0..n`: at each gap
/// the inserts there, then the parent's item unless it was deleted.
pub open spec fn result_to(parent: Seq<ItemS>, ops: Seq<OperationS>, n: int) -> Seq<ItemS>
    decreases n
{
    if n <= 0 {
        Seq::empty()
    } else {
        let before = result_to(parent, ops, n - 1);
        let gap = before + inserts_at(ops, n - 1);
        if deleted_at(ops, n - 1) { gap } else { gap.push(parent[n - 1]) }
    }
}

/// The whole file: every parent position, then the gap past the last item.
pub open spec fn result(parent: Seq<ItemS>, ops: Seq<OperationS>) -> Seq<ItemS> {
    result_to(parent, ops, parent.len() as int) + inserts_at(ops, parent.len() as int)
}

/// Only a file's last line may lack a terminator.
pub open spec fn well_terminated(items: Seq<ItemS>) -> bool {
    forall|i: int| 0 <= i < items.len() - 1 ==> items[i].terminated
}

pub open spec fn any_forgotten(items: Seq<ItemS>) -> bool {
    exists|i: int| 0 <= i < items.len() && items[i].forgotten
}

/// A delete that names a position the parent does not have.
pub open spec fn some_delete_out_of_range(parent: Seq<ItemS>, ops: Seq<OperationS>) -> bool {
    exists|k: int| 0 <= k < ops.len() && ops[k].delete && ops[k].at + ops[k].items.len() > parent.len()
}

/// An insert that names a gap the parent does not have.
pub open spec fn some_insert_out_of_range(parent: Seq<ItemS>, ops: Seq<OperationS>) -> bool {
    exists|k: int| 0 <= k < ops.len() && !ops[k].delete && ops[k].at > parent.len()
}

/// A delete whose recorded item is not what the parent holds there.
pub open spec fn some_disagreement(parent: Seq<ItemS>, ops: Seq<OperationS>) -> bool {
    exists|k: int, o: int| 0 <= k < ops.len() && ops[k].delete
        && 0 <= o < ops[k].items.len()
        && ops[k].at + o < parent.len()
        && !matches_s(ops[k].items[o], parent[ops[k].at + o])
}

// ---------------------------------------------------------------------------
// The implementation, held to the specification.
// ---------------------------------------------------------------------------

pub enum ReplayError {
    OutOfRange { position: usize, length: usize },
    ItemDisagrees { position: usize },
    TerminatorDisagrees { position: usize, recorded: bool },
    UnterminatedItemNotLast { position: usize },
    ResultDisagrees { stated: u64, found: u64 },
}

pub struct State {
    pub items: Vec<Item>,
}

/// `replay::agrees`: hold a recorded item against the parent's.
fn agrees(position: usize, recorded: &Item, found: &Item) -> (r: Result<(), ReplayError>)
    ensures
        r is Ok <==> matches_s(recorded@, found@),
        r is Err ==> (r->Err_0 is ItemDisagrees || r->Err_0 is TerminatorDisagrees),
{
    if recorded.terminated != found.terminated {
        return Err(ReplayError::TerminatorDisagrees { position, recorded: recorded.terminated });
    }
    if !recorded.matches(found) {
        return Err(ReplayError::ItemDisagrees { position });
    }
    Ok(())
}

impl State {
    /// `replay::State::applied`. The contract is the module doc's claims,
    /// written down:
    ///
    /// - `Ok` produces exactly `result(parent, ops)`, which is stated
    ///   position-by-position against the parent and so does not depend on
    ///   the order of operations at *distinct* positions;
    /// - every `Err` is a real contradiction between document and parent.
    #[verifier::loop_isolation(false)]
    pub fn applied(self, document: &OperationDocument) -> (r: Result<State, ReplayError>)
        ensures
            r is Ok ==> {
                let out = r->Ok_0.items.deep_view();
                &&& out == result(self.items.deep_view(), document.operations.deep_view())
                &&& well_terminated(out)
                &&& (document.result is Some && !any_forgotten(out)
                        ==> digest_s(out) == document.result->Some_0)
            },
            r is Err ==> match r->Err_0 {
                ReplayError::OutOfRange { .. } =>
                    some_delete_out_of_range(self.items.deep_view(), document.operations.deep_view())
                    || some_insert_out_of_range(self.items.deep_view(), document.operations.deep_view()),
                ReplayError::ItemDisagrees { .. } | ReplayError::TerminatorDisagrees { .. } =>
                    some_disagreement(self.items.deep_view(), document.operations.deep_view()),
                ReplayError::UnterminatedItemNotLast { .. } =>
                    !well_terminated(result(self.items.deep_view(), document.operations.deep_view())),
                ReplayError::ResultDisagrees { stated, found } =>
                    document.result == Some(stated)
                    && found == digest_s(result(self.items.deep_view(), document.operations.deep_view()))
                    && stated != found,
            },
    {
        let ghost parent = self.items.deep_view();
        let ghost ops = document.operations.deep_view();
        let length = self.items.len();

        // Pass one: what the document says about each parent position.
        let mut deleted: Vec<bool> = Vec::new();
        let mut inserted: Vec<Vec<Item>> = Vec::new();
        let mut p: usize = 0;
        while p < length
            invariant
                p <= length,
                deleted.len() == p,
                inserted.len() == p,
                forall|q: int| 0 <= q < p ==> !deleted@[q],
                forall|q: int| 0 <= q < p ==> #[trigger] inserted@[q].deep_view() =~= Seq::<ItemS>::empty(),
            decreases length - p
        {
            deleted.push(false);
            inserted.push(Vec::new());
            p += 1;
        }
        inserted.push(Vec::new());

        let mut k: usize = 0;
        while k < document.operations.len()
            invariant
                k <= document.operations.len(),
                ops == document.operations.deep_view(),
                ops.len() == document.operations.len(),
                parent == self.items.deep_view(),
                length == parent.len(),
                deleted.len() == length,
                inserted.len() == length + 1,
                forall|q: int| 0 <= q < length ==> #[trigger] deleted@[q] == deleted_at(ops.take(k as int), q),
                forall|q: int| 0 <= q <= length ==> #[trigger] inserted@[q].deep_view() == inserts_at(ops.take(k as int), q),
                // Nothing seen so far was out of range or disagreed.
                forall|j: int| 0 <= j < k && ops[j].delete ==> ops[j].at + ops[j].items.len() <= length,
                forall|j: int| 0 <= j < k && !ops[j].delete ==> ops[j].at <= length,
                forall|j: int, o: int| 0 <= j < k && ops[j].delete && 0 <= o < ops[j].items.len()
                    ==> matches_s(ops[j].items[o], parent[ops[j].at + o]),
            decreases document.operations.len() - k
        {
            let operation = &document.operations[k];
            assert(ops[k as int] == operation@);
            let ghost prefix = ops.take(k as int);
            let ghost next = ops.take(k as int + 1);
            assert(next.drop_last() =~= prefix);
            assert(next[next.len() - 1] == ops[k as int]);

            match operation.kind {
                OperationKind::Delete => {
                    let count = operation.items.len();
                    // `saturating_add` in the crate; spelled out here.
                    let end = if count > usize::MAX - operation.at { usize::MAX } else { operation.at + count };
                    if end > length {
                        assert(some_delete_out_of_range(parent, ops)) by {
                            assert(ops[k as int].delete && ops[k as int].at + ops[k as int].items.len() > parent.len());
                        }
                        return Err(ReplayError::OutOfRange { position: end, length });
                    }
                    let mut o: usize = 0;
                    while o < count
                        invariant
                            o <= count,
                            count == operation.items.len(),
                            operation.at + count <= length,
                            ops == document.operations.deep_view(),
                            ops[k as int] == operation@,
                            parent == self.items.deep_view(),
                            length == parent.len(),
                            deleted.len() == length,
                            inserted.len() == length + 1,
                            forall|q: int| 0 <= q < length ==> #[trigger] deleted@[q] ==
                                (deleted_at(prefix, q) || (operation.at <= q < operation.at + o)),
                            forall|q: int| 0 <= q <= length ==> #[trigger] inserted@[q].deep_view() == inserts_at(prefix, q),
                            forall|j: int| 0 <= j < o ==> matches_s(operation@.items[j], parent[operation.at + j]),
                        decreases count - o
                    {
                        let position = operation.at + o;
                        match agrees(position, &operation.items[o], &self.items[position]) {
                            Ok(()) => {}
                            Err(e) => {
                                assert(some_disagreement(parent, ops)) by {
                                    let kk = k as int;
                                    let oo = o as int;
                                    assert(ops[kk].items[oo] == operation.items@[oo]@);
                                    assert(parent[ops[kk].at + oo] == self.items@[position as int]@);
                                    assert(0 <= kk < ops.len() && ops[kk].delete && 0 <= oo < ops[kk].items.len()
                                        && ops[kk].at + oo < parent.len()
                                        && !matches_s(ops[kk].items[oo], parent[ops[kk].at + oo]));
                                }
                                return Err(e);
                            }
                        }
                        deleted.set(position, true);
                        o += 1;
                    }
                    assert forall|q: int| 0 <= q < length implies #[trigger] deleted@[q] == deleted_at(next, q) by {
                        if deleted_at(prefix, q) {
                            let j = choose|j: int| 0 <= j < prefix.len() && prefix[j].delete && prefix[j].at <= q < prefix[j].at + prefix[j].items.len();
                            assert(next[j] == prefix[j]);
                        }
                        if deleted_at(next, q) {
                            let j = choose|j: int| 0 <= j < next.len() && next[j].delete && next[j].at <= q < next[j].at + next[j].items.len();
                            if j < prefix.len() { assert(prefix[j] == next[j]); }
                        }
                    }
                    assert forall|q: int| 0 <= q <= length implies #[trigger] inserted@[q].deep_view() == inserts_at(next, q) by {
                        assert(inserts_at(next, q) == inserts_at(prefix, q));
                    }
                }
                OperationKind::Insert => {
                    if operation.at > length {
                        assert(some_insert_out_of_range(parent, ops)) by {
                            assert(!ops[k as int].delete && ops[k as int].at > parent.len());
                        }
                        return Err(ReplayError::OutOfRange { position: operation.at, length });
                    }
                    let at = operation.at;
                    let mut run: Vec<Item> = inserted.remove(at);
                    let ghost before = run.deep_view();
                    let mut o: usize = 0;
                    while o < operation.items.len()
                        invariant
                            o <= operation.items.len(),
                            ops[k as int] == operation@,
                            run.deep_view() =~= before + operation.items.deep_view().take(o as int),
                        decreases operation.items.len() - o
                    {
                        let ghost run_before = run.deep_view();
                        let item = operation.items[o].clone();
                        assert(item@ == operation.items.deep_view()[o as int]);
                        run.push(item);
                        assert(run.deep_view() =~= run_before.push(item@));
                        assert(run.deep_view() =~= before + operation.items.deep_view().take(o as int + 1));
                        o += 1;
                    }
                    assert(run.deep_view() =~= before + operation.items.deep_view());
                    inserted.insert(at, run);
                    assert forall|q: int| 0 <= q <= length implies #[trigger] inserted@[q].deep_view() == inserts_at(next, q) by {
                        if q == at as int {
                            assert(inserts_at(next, q) == inserts_at(prefix, q) + ops[k as int].items);
                        } else {
                            assert(inserts_at(next, q) == inserts_at(prefix, q));
                        }
                    }
                    assert forall|q: int| 0 <= q < length implies #[trigger] deleted@[q] == deleted_at(next, q) by {
                        if deleted_at(prefix, q) {
                            let j = choose|j: int| 0 <= j < prefix.len() && prefix[j].delete && prefix[j].at <= q < prefix[j].at + prefix[j].items.len();
                            assert(next[j] == prefix[j]);
                        }
                        if deleted_at(next, q) {
                            let j = choose|j: int| 0 <= j < next.len() && next[j].delete && next[j].at <= q < next[j].at + next[j].items.len();
                            if j < prefix.len() { assert(prefix[j] == next[j]); }
                        }
                    }
                }
            }
            k += 1;
        }
        assert(ops.take(ops.len() as int) =~= ops);

        // Pass two: walk the parent once.
        let mut items: Vec<Item> = Vec::new();
        let mut source = self.items;
        let mut p: usize = 0;
        while p < length
            invariant
                p <= length,
                length == parent.len(),
                source.deep_view() == parent,
                deleted.len() == length,
                inserted.len() == length + 1,
                forall|q: int| 0 <= q < length ==> #[trigger] deleted@[q] == deleted_at(ops, q),
                forall|q: int| p <= q <= length ==> #[trigger] inserted@[q].deep_view() == inserts_at(ops, q),
                items.deep_view() == result_to(parent, ops, p as int),
            decreases length - p
        {
            let run: Vec<Item> = inserted.remove(p);
            inserted.insert(p, Vec::new());
            let ghost gap_before = items.deep_view();
            let mut o: usize = 0;
            while o < run.len()
                invariant
                    o <= run.len(),
                    run.deep_view() == inserts_at(ops, p as int),
                    items.deep_view() =~= gap_before + run.deep_view().take(o as int),
                decreases run.len() - o
            {
                let ghost items_before = items.deep_view();
                let item = run[o].clone();
                assert(item@ == run.deep_view()[o as int]);
                items.push(item);
                assert(items.deep_view() =~= items_before.push(item@));
                assert(items.deep_view() =~= gap_before + run.deep_view().take(o as int + 1));
                o += 1;
            }
            assert(items.deep_view() =~= gap_before + inserts_at(ops, p as int));
            if !deleted[p] {
                let ghost items_before = items.deep_view();
                let item = source[p].clone();
                assert(item@ == parent[p as int]);
                items.push(item);
                assert(items.deep_view() =~= items_before.push(item@));
            }
            assert(items.deep_view() =~= result_to(parent, ops, p as int + 1));
            p += 1;
        }
        // The gap past the last item.
        let tail: Vec<Item> = inserted.remove(length);
        let ghost tail_before = items.deep_view();
        let mut t: usize = 0;
        while t < tail.len()
            invariant
                t <= tail.len(),
                tail.deep_view() == inserts_at(ops, length as int),
                items.deep_view() =~= tail_before + tail.deep_view().take(t as int),
            decreases tail.len() - t
        {
            let ghost items_before = items.deep_view();
            let item = tail[t].clone();
            assert(item@ == tail.deep_view()[t as int]);
            items.push(item);
            assert(items.deep_view() =~= items_before.push(item@));
            assert(items.deep_view() =~= tail_before + tail.deep_view().take(t as int + 1));
            t += 1;
        }
        assert(items.deep_view() =~= result(parent, ops));

        // Only a file's last line may lack a terminator.
        let mut i: usize = 0;
        let mut forgotten = false;
        while i < items.len()
            invariant
                i <= items.len(),
                items.deep_view() == result(parent, ops),
                forall|j: int| 0 <= j < i && j < items.len() - 1 ==> items.deep_view()[j].terminated,
                forgotten ==> any_forgotten(items.deep_view()),
                !forgotten ==> forall|j: int| 0 <= j < i ==> !items.deep_view()[j].forgotten,
            decreases items.len() - i
        {
            if i + 1 < items.len() && !items[i].terminated {
                assert(!well_terminated(items.deep_view())) by {
                    assert(!items.deep_view()[i as int].terminated);
                }
                return Err(ReplayError::UnterminatedItemNotLast { position: i });
            }
            if items[i].forgotten {
                assert(any_forgotten(items.deep_view())) by {
                    assert(items.deep_view()[i as int].forgotten);
                }
                forgotten = true;
            }
            i += 1;
        }

        // Decision 0031: held to the digest the document states, unless a
        // forgotten item means the recorder never hashed these bytes.
        if let Some(stated) = document.result {
            if !forgotten {
                let found = digest(&items);
                if found != stated {
                    return Err(ReplayError::ResultDisagrees { stated, found });
                }
            }
        }

        Ok(State { items })
    }
}

// ---------------------------------------------------------------------------
// Theorems about the specification itself.
// ---------------------------------------------------------------------------

/// What the parser guarantees and `applied` relies on: no two inserts name
/// one position (`ParseErrorKind::InsertsAtOnePosition`).
pub open spec fn distinct_inserts(ops: Seq<OperationS>) -> bool {
    forall|i: int, j: int| 0 <= i < ops.len() && 0 <= j < ops.len() && i != j
        && !ops[i].delete && !ops[j].delete ==> ops[i].at != ops[j].at
}

/// Two documents that state the same facts, in any order.
pub open spec fn same_facts(a: Seq<OperationS>, b: Seq<OperationS>) -> bool {
    forall|x: OperationS| a.contains(x) <==> b.contains(x)
}

/// Under `distinct_inserts`, what is inserted at `p` is the one insert
/// there, or nothing — the document's order does not enter.
proof fn lemma_inserts_at_unique(ops: Seq<OperationS>, p: int)
    requires distinct_inserts(ops)
    ensures
        (exists|k: int| 0 <= k < ops.len() && !ops[k].delete && ops[k].at == p)
            ==> inserts_at(ops, p) == ops[choose|k: int| 0 <= k < ops.len() && !ops[k].delete && ops[k].at == p].items,
        !(exists|k: int| 0 <= k < ops.len() && !ops[k].delete && ops[k].at == p)
            ==> inserts_at(ops, p) == Seq::<ItemS>::empty(),
    decreases ops.len()
{
    if ops.len() == 0 {
    } else {
        let rest = ops.drop_last();
        let last = ops[ops.len() - 1];
        assert(distinct_inserts(rest)) by {
            assert forall|i: int, j: int| 0 <= i < rest.len() && 0 <= j < rest.len() && i != j
                && !rest[i].delete && !rest[j].delete implies rest[i].at != rest[j].at by {
                assert(rest[i] == ops[i] && rest[j] == ops[j]);
            }
        }
        lemma_inserts_at_unique(rest, p);
        if !last.delete && last.at == p {
            // The last one is the insert at p, so no earlier one is.
            assert(!(exists|k: int| 0 <= k < rest.len() && !rest[k].delete && rest[k].at == p)) by {
                if exists|k: int| 0 <= k < rest.len() && !rest[k].delete && rest[k].at == p {
                    let k = choose|k: int| 0 <= k < rest.len() && !rest[k].delete && rest[k].at == p;
                    assert(ops[k] == rest[k]);
                    assert(ops[k].at != ops[ops.len() - 1].at);
                }
            }
            assert(inserts_at(ops, p) == last.items);
            let k = choose|k: int| 0 <= k < ops.len() && !ops[k].delete && ops[k].at == p;
            assert(k == ops.len() - 1) by {
                if k < ops.len() - 1 { assert(ops[k].at != ops[ops.len() - 1].at); }
            }
        } else {
            assert(inserts_at(ops, p) == inserts_at(rest, p));
            if exists|k: int| 0 <= k < ops.len() && !ops[k].delete && ops[k].at == p {
                let k = choose|k: int| 0 <= k < ops.len() && !ops[k].delete && ops[k].at == p;
                assert(k < rest.len());
                assert(rest[k] == ops[k]);
                let k2 = choose|k: int| 0 <= k < rest.len() && !rest[k].delete && rest[k].at == p;
                assert(ops[k2] == rest[k2]);
                if k != k2 { assert(ops[k].at != ops[k2].at); }
            } else {
                if exists|k: int| 0 <= k < rest.len() && !rest[k].delete && rest[k].at == p {
                    let k = choose|k: int| 0 <= k < rest.len() && !rest[k].delete && rest[k].at == p;
                    assert(ops[k] == rest[k]);
                }
            }
        }
    }
}

proof fn lemma_same_facts_same_gaps(a: Seq<OperationS>, b: Seq<OperationS>, p: int)
    requires distinct_inserts(a), distinct_inserts(b), same_facts(a, b)
    ensures deleted_at(a, p) == deleted_at(b, p), inserts_at(a, p) == inserts_at(b, p)
{
    // deleted_at is an existential over the facts.
    if deleted_at(a, p) {
        let k = choose|k: int| 0 <= k < a.len() && a[k].delete && a[k].at <= p < a[k].at + a[k].items.len();
        assert(b.contains(a[k]));
        let j = choose|j: int| 0 <= j < b.len() && b[j] == a[k];
        assert(deleted_at(b, p));
    }
    if deleted_at(b, p) {
        let k = choose|k: int| 0 <= k < b.len() && b[k].delete && b[k].at <= p < b[k].at + b[k].items.len();
        assert(a.contains(b[k]));
        let j = choose|j: int| 0 <= j < a.len() && a[j] == b[k];
        assert(deleted_at(a, p));
    }
    // inserts_at is the one insert at p, on either side.
    lemma_inserts_at_unique(a, p);
    lemma_inserts_at_unique(b, p);
    if exists|k: int| 0 <= k < a.len() && !a[k].delete && a[k].at == p {
        let ka = choose|k: int| 0 <= k < a.len() && !a[k].delete && a[k].at == p;
        assert(b.contains(a[ka]));
        let jb = choose|j: int| 0 <= j < b.len() && b[j] == a[ka];
        let kb = choose|k: int| 0 <= k < b.len() && !b[k].delete && b[k].at == p;
        if jb != kb { assert(b[jb].at != b[kb].at); }
        assert(inserts_at(a, p) == a[ka].items);
        assert(inserts_at(b, p) == b[kb].items);
    } else {
        if exists|k: int| 0 <= k < b.len() && !b[k].delete && b[k].at == p {
            let kb = choose|k: int| 0 <= k < b.len() && !b[k].delete && b[k].at == p;
            assert(a.contains(b[kb]));
            let ja = choose|j: int| 0 <= j < a.len() && a[j] == b[kb];
            assert(false);
        }
    }
}

proof fn lemma_result_to_same(parent: Seq<ItemS>, a: Seq<OperationS>, b: Seq<OperationS>, n: int)
    requires distinct_inserts(a), distinct_inserts(b), same_facts(a, b)
    ensures result_to(parent, a, n) == result_to(parent, b, n)
    decreases n
{
    if n > 0 {
        lemma_result_to_same(parent, a, b, n - 1);
        lemma_same_facts_same_gaps(a, b, n - 1);
    }
}

/// The module doc's claim, as a theorem: a document the parser accepts
/// replays to the same file however its operations are ordered, because
/// every position is stated against the parent and none of them move.
pub proof fn theorem_order_independent(parent: Seq<ItemS>, a: Seq<OperationS>, b: Seq<OperationS>)
    requires distinct_inserts(a), distinct_inserts(b), same_facts(a, b)
    ensures result(parent, a) == result(parent, b)
{
    lemma_result_to_same(parent, a, b, parent.len() as int);
    lemma_same_facts_same_gaps(a, b, parent.len() as int);
}

// ---------------------------------------------------------------------------
// The specification on concrete files, so it is not vacuous.
// ---------------------------------------------------------------------------

spec fn line(c: u8) -> ItemS { ItemS { text: seq![c], terminated: true, forgotten: false } }
spec fn del(at: int, items: Seq<ItemS>) -> OperationS { OperationS { delete: true, at, items } }
spec fn ins(at: int, items: Seq<ItemS>) -> OperationS { OperationS { delete: false, at, items } }

/// A replacement: `delete 1 [b]; insert 1 [x]` on `a b c` is `a x c`.
proof fn example_replacement() {
    let (a, b, c, x) = (line(b'a'), line(b'b'), line(b'c'), line(b'x'));
    let parent = seq![a, b, c];
    let ops = seq![del(1, seq![b]), ins(1, seq![x])];
    reveal_with_fuel(result_to, 4);
    reveal_with_fuel(inserts_at, 3);
    assert(ops.drop_last() =~= seq![del(1, seq![b])]);
    assert(ops.drop_last().drop_last() =~= Seq::<OperationS>::empty());
    assert(deleted_at(ops, 1)) by { assert(ops[0].delete && ops[0].at <= 1 < ops[0].at + ops[0].items.len()); }
    assert(!deleted_at(ops, 0)) by {
        if deleted_at(ops, 0) {
            let k = choose|k: int| 0 <= k < ops.len() && ops[k].delete && ops[k].at <= 0 < ops[k].at + ops[k].items.len();
            assert(k == 0 || k == 1);
        }
    }
    assert(!deleted_at(ops, 2)) by {
        if deleted_at(ops, 2) {
            let k = choose|k: int| 0 <= k < ops.len() && ops[k].delete && ops[k].at <= 2 < ops[k].at + ops[k].items.len();
            assert(k == 0 || k == 1);
        }
    }
    assert(inserts_at(ops, 0) =~= Seq::<ItemS>::empty());
    assert(inserts_at(ops, 1) =~= seq![x]);
    assert(inserts_at(ops, 2) =~= Seq::<ItemS>::empty());
    assert(inserts_at(ops, 3) =~= Seq::<ItemS>::empty());
    assert(result_to(parent, ops, 1) =~= seq![a]);
    assert(result_to(parent, ops, 2) =~= seq![a, x]);
    assert(result_to(parent, ops, 3) =~= seq![a, x, c]);
    assert(result(parent, ops) =~= seq![a, x, c]);
}

/// The rustdoc's `insert 4` after `delete 3 1` versus `insert 3`: in a
/// linear replay both produce the same bytes. They differ only in which
/// side of the removed run the new items sit on, which is a fact a merge
/// can see and a file cannot.
proof fn example_insert_beside_a_deletion() {
    let (a, b, c, d, e, x) = (line(b'a'), line(b'b'), line(b'c'), line(b'd'), line(b'e'), line(b'x'));
    let parent = seq![a, b, c, d, e];
    let past = seq![del(3, seq![d]), ins(4, seq![x])];
    let before = seq![del(3, seq![d]), ins(3, seq![x])];
    reveal_with_fuel(result_to, 6);
    reveal_with_fuel(inserts_at, 3);
    assert(past.drop_last() =~= seq![del(3, seq![d])]);
    assert(before.drop_last() =~= seq![del(3, seq![d])]);
    assert(past.drop_last().drop_last() =~= Seq::<OperationS>::empty());
    assert forall|p: int| 0 <= p < 5 implies deleted_at(past, p) == (p == 3) && deleted_at(before, p) == (p == 3) by {
        if deleted_at(past, p) {
            let k = choose|k: int| 0 <= k < past.len() && past[k].delete && past[k].at <= p < past[k].at + past[k].items.len();
            assert(k == 0 || k == 1);
        }
        if deleted_at(before, p) {
            let k = choose|k: int| 0 <= k < before.len() && before[k].delete && before[k].at <= p < before[k].at + before[k].items.len();
            assert(k == 0 || k == 1);
        }
        if p == 3 {
            assert(past[0].delete && past[0].at <= 3 < past[0].at + past[0].items.len());
            assert(before[0].delete && before[0].at <= 3 < before[0].at + before[0].items.len());
        }
    }
    assert forall|p: int| 0 <= p <= 5 implies inserts_at(past, p) =~= (if p == 4 { seq![x] } else { Seq::<ItemS>::empty() })
        && inserts_at(before, p) =~= (if p == 3 { seq![x] } else { Seq::<ItemS>::empty() }) by {}
    assert(result_to(parent, past, 1) =~= seq![a]);
    assert(result_to(parent, past, 2) =~= seq![a, b]);
    assert(result_to(parent, past, 3) =~= seq![a, b, c]);
    assert(result_to(parent, past, 4) =~= seq![a, b, c]);
    assert(result_to(parent, past, 5) =~= seq![a, b, c, x, e]);
    assert(result(parent, past) =~= seq![a, b, c, x, e]);
    assert(result_to(parent, before, 1) =~= seq![a]);
    assert(result_to(parent, before, 2) =~= seq![a, b]);
    assert(result_to(parent, before, 3) =~= seq![a, b, c]);
    assert(result_to(parent, before, 4) =~= seq![a, b, c, x]);
    assert(result_to(parent, before, 5) =~= seq![a, b, c, x, e]);
    assert(result(parent, before) =~= seq![a, b, c, x, e]);
}

fn main() {}

} // verus!
