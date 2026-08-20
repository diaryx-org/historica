//! Pure causal-history primitives.
//!
//! A [`History`] is a grow-only collection of immutable [`Revision`] values.
//! Replicas merge by set union. No timestamp participates in identity or
//! causality.
//!
//! Every revision carries two identities, for the reasons recorded in
//! `docs/decisions/0001-identity.md`:
//!
//! - a [`RevisionId`], derived from the revision's canonical readable bytes,
//!   answering *are these the same bytes?*;
//! - a [`ChangeId`], assigned once and copied forward through every rewrite,
//!   answering *are these the same piece of work?*.

use std::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::str::FromStr;

/// Bytes in a [`RevisionId`] digest.
pub const REVISION_ID_LEN: usize = 32;

/// Bytes in a [`ChangeId`].
///
/// 96 bits. A change ID is assigned rather than derived, so only accidental
/// collision matters, and 96 bits keeps that negligible past any plausible
/// bulk import while costing eight fewer characters on every revision's second
/// line than a 128-bit name would.
pub const CHANGE_ID_LEN: usize = 12;

/// Reversed hexadecimal: nibble `0` is `z` and nibble `15` is `k`.
///
/// [`ChangeId`] is spelled in this alphabet so that no change ID can be
/// mistaken for a digest and no digest for a change ID.
const REVERSE_HEX: [u8; 16] = *b"zyxwvutsrqponmlk";

/// The identity of one immutable revision: a digest of its canonical bytes.
///
/// The core cannot yet compute a digest, because canonical bytes are not yet
/// specified, so it accepts an ID as given and keeps it opaque. Bare lowercase
/// hex is a provisional spelling; whether the readable form carries an
/// algorithm label belongs to the format decision.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct RevisionId([u8; REVISION_ID_LEN]);

impl RevisionId {
    /// Wrap a digest computed elsewhere.
    pub const fn from_bytes(bytes: [u8; REVISION_ID_LEN]) -> Self {
        Self(bytes)
    }

    /// The raw digest.
    pub const fn as_bytes(&self) -> &[u8; REVISION_ID_LEN] {
        &self.0
    }

    /// The leading `chars` characters of the readable spelling.
    ///
    /// Digest prefixes change whenever content changes, so they are for reading
    /// rather than remembering. A [`ChangeId`] prefix is the stable one.
    pub fn abbreviate(&self, chars: usize) -> String {
        self.to_string().chars().take(chars).collect()
    }
}

impl fmt::Display for RevisionId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for byte in &self.0 {
            write!(f, "{byte:02x}")?;
        }
        Ok(())
    }
}

impl fmt::Debug for RevisionId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "RevisionId({})", self.abbreviate(12))
    }
}

impl FromStr for RevisionId {
    type Err = InvalidRevisionId;

    fn from_str(value: &str) -> Result<Self, Self::Err> {
        let value = value.as_bytes();
        if value.len() != REVISION_ID_LEN * 2 {
            return Err(InvalidRevisionId);
        }

        let mut bytes = [0u8; REVISION_ID_LEN];
        for (slot, pair) in bytes.iter_mut().zip(value.chunks_exact(2)) {
            let high = hex_nibble(pair[0]).ok_or(InvalidRevisionId)?;
            let low = hex_nibble(pair[1]).ok_or(InvalidRevisionId)?;
            *slot = (high << 4) | low;
        }
        Ok(Self(bytes))
    }
}

fn hex_nibble(character: u8) -> Option<u8> {
    match character {
        b'0'..=b'9' => Some(character - b'0'),
        b'a'..=b'f' => Some(character - b'a' + 10),
        _ => None,
    }
}

/// The stable identity of one piece of work, unchanged by rewriting it.
///
/// Amending, describing, or rebasing produces a new [`Revision`] of the same
/// change. A change ID is assigned rather than derived, so nothing about it can
/// be verified: it must never be a security boundary.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct ChangeId([u8; CHANGE_ID_LEN]);

impl Ord for ChangeId {
    fn cmp(&self, other: &Self) -> Ordering {
        spelled_order(&self.0, &other.0)
    }
}

impl PartialOrd for ChangeId {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl ChangeId {
    /// Wrap bytes minted elsewhere.
    ///
    /// Minting needs a cryptographic random source and belongs to the layer
    /// that creates revisions rather than to this pure core.
    pub const fn from_bytes(bytes: [u8; CHANGE_ID_LEN]) -> Self {
        Self(bytes)
    }

    /// The raw bytes.
    pub const fn as_bytes(&self) -> &[u8; CHANGE_ID_LEN] {
        &self.0
    }

    /// The leading `chars` characters of the readable spelling.
    ///
    /// This prefix survives rewriting, so it is the name a person can learn.
    pub fn abbreviate(&self, chars: usize) -> String {
        self.to_string().chars().take(chars).collect()
    }
}

impl fmt::Display for ChangeId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&spell(&self.0))
    }
}

impl fmt::Debug for ChangeId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "ChangeId({})", self.abbreviate(8))
    }
}

impl FromStr for ChangeId {
    type Err = InvalidChangeId;

    fn from_str(value: &str) -> Result<Self, Self::Err> {
        decipher(value).map(Self).ok_or(InvalidChangeId)
    }
}

/// Bytes in a [`FileId`], which is a [`ChangeId`]'s size for its reasons.
pub const FILE_ID_LEN: usize = CHANGE_ID_LEN;

/// The identity of one file, independent of where it sits.
///
/// Decision 0008: a path is a fact *about* a file rather than the file's name,
/// so that renaming one keeps the operations recorded against it. The
/// identifier is minted rather than derived for the reason 0001 gave about
/// change IDs — a derived identifier changes when the thing it derives from is
/// rewritten, and every later line naming it would then name nothing.
///
/// It is spelled exactly as a [`ChangeId`] is, in an alphabet no digest can be
/// mistaken for. Nothing in the causal core reads it; it is here because
/// identity is what this module is for.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct FileId([u8; FILE_ID_LEN]);

impl Ord for FileId {
    fn cmp(&self, other: &Self) -> Ordering {
        spelled_order(&self.0, &other.0)
    }
}

impl PartialOrd for FileId {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl FileId {
    /// Wrap bytes minted elsewhere.
    pub const fn from_bytes(bytes: [u8; FILE_ID_LEN]) -> Self {
        Self(bytes)
    }

    /// The raw bytes.
    pub const fn as_bytes(&self) -> &[u8; FILE_ID_LEN] {
        &self.0
    }

    /// The leading `chars` characters of the readable spelling.
    pub fn abbreviate(&self, chars: usize) -> String {
        self.to_string().chars().take(chars).collect()
    }
}

impl fmt::Display for FileId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&spell(&self.0))
    }
}

impl fmt::Debug for FileId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "FileId({})", self.abbreviate(8))
    }
}

impl FromStr for FileId {
    type Err = InvalidFileId;

    fn from_str(value: &str) -> Result<Self, Self::Err> {
        decipher(value).map(Self).ok_or(InvalidFileId)
    }
}

/// A file ID that was not the right length, or not in the right alphabet.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct InvalidFileId;

impl fmt::Display for InvalidFileId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "a file ID is {} characters from the alphabet `k` to `z`",
            FILE_ID_LEN * 2
        )
    }
}

impl std::error::Error for InvalidFileId {}

/// Order two assigned identifiers the way their spellings order.
///
/// [`REVERSE_HEX`] runs backwards — nibble 0 is `z` and nibble 15 is `k` — so
/// ordering by bytes would order two identifiers differently from the readable
/// file that records them, and a document sorted by one would be rejected by a
/// parser checking the other. The readable file is the authority here as
/// everywhere, so this compares as it reads: backwards through the bytes.
fn spelled_order(left: &[u8], right: &[u8]) -> Ordering {
    right.cmp(left)
}

/// The readable spelling of an assigned identifier.
fn spell(bytes: &[u8]) -> String {
    let mut out = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        out.push(REVERSE_HEX[usize::from(byte >> 4)] as char);
        out.push(REVERSE_HEX[usize::from(byte & 0x0f)] as char);
    }
    out
}

/// Read an assigned identifier of `N` bytes, or `None` if it is not one.
fn decipher<const N: usize>(value: &str) -> Option<[u8; N]> {
    let value = value.as_bytes();
    if value.len() != N * 2 {
        return None;
    }
    let mut bytes = [0u8; N];
    for (slot, pair) in bytes.iter_mut().zip(value.chunks_exact(2)) {
        *slot = (reverse_hex_nibble(pair[0])? << 4) | reverse_hex_nibble(pair[1])?;
    }
    Some(bytes)
}

fn reverse_hex_nibble(character: u8) -> Option<u8> {
    REVERSE_HEX
        .iter()
        .position(|candidate| *candidate == character)
        .map(|nibble| nibble as u8)
}

/// A revision ID is exactly [`REVISION_ID_LEN`] bytes of lowercase hex.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct InvalidRevisionId;

impl fmt::Display for InvalidRevisionId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "a revision ID is {} lowercase hex characters",
            REVISION_ID_LEN * 2
        )
    }
}

impl std::error::Error for InvalidRevisionId {}

/// A change ID is exactly [`CHANGE_ID_LEN`] bytes of reversed hex, `k` to `z`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct InvalidChangeId;

impl fmt::Display for InvalidChangeId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "a change ID is {} characters from the alphabet `k` to `z`",
            CHANGE_ID_LEN * 2
        )
    }
}

impl std::error::Error for InvalidChangeId {}

/// One immutable point in causal history: a single version of one change.
///
/// Payloads, trees, and patches are intentionally absent from this first
/// model. The core first establishes the convergence and causality rules they
/// will live inside.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Revision {
    /// The digest of this revision's canonical bytes.
    pub id: RevisionId,
    /// The piece of work this revision is one version of.
    pub change: ChangeId,
    /// Causal parents, named by revision so that the digest covers ancestry.
    pub parents: BTreeSet<RevisionId>,
    /// Revisions this one replaces, named by the successor that replaced them.
    ///
    /// Recording the edge on the successor keeps rewriting legible when a
    /// superseded revision is absent locally, which is ordinary rather than
    /// incomplete. Supersession may cross change IDs: that is what squashing
    /// one change into another does.
    pub supersedes: BTreeSet<RevisionId>,
    /// The human description of the work.
    pub message: String,
}

impl Revision {
    /// Construct a root revision of `change` with no parents and no predecessors.
    pub fn new(id: RevisionId, change: ChangeId, message: impl Into<String>) -> Self {
        Self {
            id,
            change,
            parents: BTreeSet::new(),
            supersedes: BTreeSet::new(),
            message: message.into(),
        }
    }

    /// Name this revision's causal parents.
    #[must_use]
    pub fn with_parents(mut self, parents: impl IntoIterator<Item = RevisionId>) -> Self {
        self.parents = parents.into_iter().collect();
        self
    }

    /// Name the revisions this one replaces.
    #[must_use]
    pub fn superseding(mut self, predecessors: impl IntoIterator<Item = RevisionId>) -> Self {
        self.supersedes = predecessors.into_iter().collect();
        self
    }
}

/// What one [`ChangeId`] currently means in one [`History`].
///
/// Only disagreeing bytes under a single [`RevisionId`] are corruption. Every
/// state here is legitimate, including divergence, which is unavoidable in a
/// tool that allows both rewriting and offline work.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ChangeState<'a> {
    /// No observed revision claims this change.
    Unknown,
    /// Exactly one revision of this change is current.
    Resolved(&'a Revision),
    /// Concurrent revisions of one change, none superseding the others.
    ///
    /// Two replicas amended the same change without seeing each other. A person
    /// has to choose; the core will not choose arbitrarily.
    Divergent(BTreeSet<RevisionId>),
    /// Every revision of this change was superseded by revisions of others.
    ///
    /// The work was squashed elsewhere or abandoned, so the change ID still
    /// names something real but has no current revision of its own.
    Abandoned,
}

/// A convergent collection of immutable revisions.
///
/// Two replicas merge by union. Receiving the same revision repeatedly is
/// idempotent. Receiving different content under the same [`RevisionId`] is
/// corruption and is rejected rather than resolved arbitrarily.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct History {
    revisions: BTreeMap<RevisionId, Revision>,
}

impl History {
    /// An empty history.
    pub fn new() -> Self {
        Self::default()
    }

    /// How many revisions have been observed.
    pub fn len(&self) -> usize {
        self.revisions.len()
    }

    /// Whether no revision has been observed.
    pub fn is_empty(&self) -> bool {
        self.revisions.is_empty()
    }

    /// Look up one revision by digest.
    pub fn get(&self, id: &RevisionId) -> Option<&Revision> {
        self.revisions.get(id)
    }

    /// Every observed revision, in a deterministic order.
    pub fn iter(&self) -> impl Iterator<Item = &Revision> {
        self.revisions.values()
    }

    /// Add one immutable revision.
    pub fn insert(&mut self, revision: Revision) -> Result<bool, RevisionIdCollision> {
        match self.revisions.get(&revision.id) {
            Some(existing) if existing == &revision => Ok(false),
            Some(_) => Err(RevisionIdCollision { id: revision.id }),
            None => {
                self.revisions.insert(revision.id, revision);
                Ok(true)
            }
        }
    }

    /// Merge everything observed by `other` into this replica.
    pub fn merge(&mut self, other: &Self) -> Result<usize, RevisionIdCollision> {
        // Validate first so a collision cannot leave a partial merge behind.
        for (id, incoming) in &other.revisions {
            if let Some(existing) = self.revisions.get(id)
                && existing != incoming
            {
                return Err(RevisionIdCollision { id: *id });
            }
        }

        let before = self.len();
        self.revisions.extend(other.revisions.clone());
        Ok(self.len() - before)
    }

    /// Revisions no observed revision names as a parent.
    ///
    /// This is a pure graph question, so superseded revisions can appear here.
    /// Filter with [`History::superseded`] to render only current work; whether
    /// a given view hides obsolete heads is a rendering policy, not a fact
    /// about the graph.
    ///
    /// Missing parents do not make a child a head: the child's declaration is
    /// still evidence that its named parent has a successor, even if transport
    /// has not delivered that parent yet.
    pub fn heads(&self) -> BTreeSet<RevisionId> {
        let parents = self
            .revisions
            .values()
            .flat_map(|revision| revision.parents.iter())
            .collect::<BTreeSet<_>>();

        self.revisions
            .keys()
            .filter(|id| !parents.contains(id))
            .copied()
            .collect()
    }

    /// Parent digests named by a revision but not yet present locally.
    ///
    /// Unlike a missing predecessor, a missing parent means history is
    /// incomplete and transport has more to deliver.
    pub fn missing_parents(&self) -> BTreeSet<RevisionId> {
        self.revisions
            .values()
            .flat_map(|revision| revision.parents.iter())
            .filter(|parent| !self.revisions.contains_key(*parent))
            .copied()
            .collect()
    }

    /// Revisions some observed revision has replaced.
    ///
    /// A superseded revision need not be present locally: the successor carries
    /// the evidence, so rewriting stays legible without the predecessor.
    pub fn superseded(&self) -> BTreeSet<RevisionId> {
        self.revisions
            .values()
            .flat_map(|revision| revision.supersedes.iter())
            .copied()
            .collect()
    }

    /// Every change ID some observed revision claims.
    pub fn changes(&self) -> BTreeSet<ChangeId> {
        self.revisions
            .values()
            .map(|revision| revision.change)
            .collect()
    }

    /// Every observed revision of one change, current or superseded.
    pub fn revisions_of(&self, change: &ChangeId) -> impl Iterator<Item = &Revision> {
        self.revisions
            .values()
            .filter(move |revision| &revision.change == change)
    }

    /// What this change ID currently means.
    ///
    /// Resolution is head discovery over supersession edges, the same rule
    /// [`History::heads`] applies to parent edges.
    pub fn change_state(&self, change: &ChangeId) -> ChangeState<'_> {
        let superseded = self.superseded();
        let mut current = self
            .revisions_of(change)
            .filter(|revision| !superseded.contains(&revision.id));

        match (current.next(), current.next()) {
            (None, _) if self.revisions_of(change).next().is_none() => ChangeState::Unknown,
            (None, _) => ChangeState::Abandoned,
            (Some(only), None) => ChangeState::Resolved(only),
            (Some(first), Some(second)) => ChangeState::Divergent(
                [first.id, second.id]
                    .into_iter()
                    .chain(current.map(|revision| revision.id))
                    .collect(),
            ),
        }
    }

    /// Changes with concurrent current revisions, and the revisions in conflict.
    ///
    /// A caller rendering history needs this to mark divergence rather than to
    /// silently show one of several answers.
    pub fn divergent_changes(&self) -> BTreeMap<ChangeId, BTreeSet<RevisionId>> {
        self.changes()
            .into_iter()
            .filter_map(|change| match self.change_state(&change) {
                ChangeState::Divergent(revisions) => Some((change, revisions)),
                _ => None,
            })
            .collect()
    }
}

/// Two revisions with disagreeing bytes claimed one [`RevisionId`].
///
/// A derived digest cannot disagree with its own content, so this is tampering
/// or a broken digest rather than a situation to resolve. It remains
/// load-bearing until the core can recompute a digest and verify it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RevisionIdCollision {
    /// The contested digest.
    pub id: RevisionId,
}

impl fmt::Display for RevisionIdCollision {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "different revisions claim the digest `{}`",
            self.id.abbreviate(12)
        )
    }
}

impl std::error::Error for RevisionIdCollision {}

#[cfg(test)]
mod tests {
    use super::*;

    /// Deterministic stand-in for identities the core cannot yet compute or
    /// mint, so that tests read as labels rather than as digests.
    fn spread<const N: usize>(label: &str) -> [u8; N] {
        let mut state = 0xcbf2_9ce4_8422_2325_u64;
        for byte in label.as_bytes() {
            state ^= u64::from(*byte);
            state = state.wrapping_mul(0x0000_0100_0000_01b3);
        }

        let mut bytes = [0u8; N];
        for slot in &mut bytes {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            *slot = (state >> 24) as u8;
        }
        bytes
    }

    fn rev(label: &str) -> RevisionId {
        RevisionId::from_bytes(spread(label))
    }

    fn chg(label: &str) -> ChangeId {
        ChangeId::from_bytes(spread(label))
    }

    /// One revision of its own change, named for readability.
    fn revision(label: &str, parents: &[&str]) -> Revision {
        Revision::new(rev(label), chg(label), label)
            .with_parents(parents.iter().map(|parent| rev(parent)))
    }

    #[test]
    fn concurrent_replicas_converge_by_union() {
        let root = revision("root", &[]);
        let mut left = History::new();
        let mut right = History::new();
        left.insert(root.clone()).unwrap();
        right.insert(root).unwrap();
        left.insert(revision("left", &["root"])).unwrap();
        right.insert(revision("right", &["root"])).unwrap();

        let left_before = left.clone();
        let right_before = right.clone();
        left.merge(&right_before).unwrap();
        right.merge(&left_before).unwrap();

        assert_eq!(left, right);
        assert_eq!(left.heads(), BTreeSet::from([rev("left"), rev("right")]));
    }

    #[test]
    fn a_merge_revision_joins_concurrent_heads() {
        let mut history = History::new();
        history.insert(revision("root", &[])).unwrap();
        history.insert(revision("left", &["root"])).unwrap();
        history.insert(revision("right", &["root"])).unwrap();
        history
            .insert(revision("merge", &["left", "right"]))
            .unwrap();

        assert_eq!(history.heads(), BTreeSet::from([rev("merge")]));
    }

    #[test]
    fn duplicate_delivery_is_idempotent() {
        let mut history = History::new();
        let root = revision("root", &[]);

        assert!(history.insert(root.clone()).unwrap());
        assert!(!history.insert(root).unwrap());
        assert_eq!(history.len(), 1);
    }

    #[test]
    fn disagreeing_bytes_under_one_digest_are_rejected_atomically() {
        let mut local = History::new();
        local.insert(revision("same", &[])).unwrap();

        let mut remote = History::new();
        remote
            .insert(Revision::new(rev("same"), chg("same"), "different message"))
            .unwrap();
        remote.insert(revision("other", &[])).unwrap();

        assert_eq!(
            local.merge(&remote),
            Err(RevisionIdCollision { id: rev("same") })
        );
        assert_eq!(local.len(), 1);
        assert!(local.get(&rev("other")).is_none());
    }

    #[test]
    fn incomplete_transport_names_missing_parents() {
        let mut history = History::new();
        history.insert(revision("child", &["absent"])).unwrap();

        assert_eq!(history.heads(), BTreeSet::from([rev("child")]));
        assert_eq!(history.missing_parents(), BTreeSet::from([rev("absent")]));
    }

    #[test]
    fn amending_keeps_the_change_id_and_resolves_to_the_successor() {
        let mut history = History::new();
        history
            .insert(Revision::new(rev("a1"), chg("work"), "teh fix"))
            .unwrap();
        history
            .insert(Revision::new(rev("a2"), chg("work"), "the fix").superseding([rev("a1")]))
            .unwrap();

        assert_eq!(history.revisions_of(&chg("work")).count(), 2);
        assert_eq!(
            history.change_state(&chg("work")),
            ChangeState::Resolved(history.get(&rev("a2")).unwrap())
        );
        assert!(history.divergent_changes().is_empty());
    }

    #[test]
    fn a_superseded_revision_need_not_be_present_locally() {
        let mut history = History::new();
        history
            .insert(Revision::new(rev("a2"), chg("work"), "the fix").superseding([rev("a1")]))
            .unwrap();

        assert!(history.get(&rev("a1")).is_none());
        assert!(history.missing_parents().is_empty());
        assert_eq!(
            history.change_state(&chg("work")),
            ChangeState::Resolved(history.get(&rev("a2")).unwrap())
        );
    }

    #[test]
    fn concurrent_amendments_of_one_change_diverge_without_being_corruption() {
        let mut history = History::new();
        history
            .insert(Revision::new(rev("a1"), chg("work"), "first try"))
            .unwrap();
        history
            .insert(Revision::new(rev("mine"), chg("work"), "my wording").superseding([rev("a1")]))
            .unwrap();
        history
            .insert(
                Revision::new(rev("yours"), chg("work"), "your wording").superseding([rev("a1")]),
            )
            .unwrap();

        let contested = BTreeSet::from([rev("mine"), rev("yours")]);
        assert_eq!(
            history.change_state(&chg("work")),
            ChangeState::Divergent(contested.clone())
        );
        assert_eq!(
            history.divergent_changes(),
            BTreeMap::from([(chg("work"), contested)])
        );
    }

    #[test]
    fn squashing_leaves_the_absorbed_change_with_no_current_revision() {
        let mut history = History::new();
        history
            .insert(Revision::new(rev("keep1"), chg("keep"), "the feature"))
            .unwrap();
        history
            .insert(Revision::new(rev("fixup1"), chg("fixup"), "oops").with_parents([rev("keep1")]))
            .unwrap();
        history
            .insert(
                Revision::new(rev("keep2"), chg("keep"), "the feature")
                    .superseding([rev("keep1"), rev("fixup1")]),
            )
            .unwrap();

        assert_eq!(
            history.change_state(&chg("keep")),
            ChangeState::Resolved(history.get(&rev("keep2")).unwrap())
        );
        assert_eq!(history.change_state(&chg("fixup")), ChangeState::Abandoned);
        assert_eq!(history.change_state(&chg("never")), ChangeState::Unknown);
    }

    #[test]
    fn rewriting_a_parent_replaces_descendant_revisions_but_not_their_change_ids() {
        let mut history = History::new();
        for revision in [
            Revision::new(rev("a1"), chg("a"), "first"),
            Revision::new(rev("b1"), chg("b"), "second").with_parents([rev("a1")]),
            Revision::new(rev("c1"), chg("c"), "third").with_parents([rev("b1")]),
        ] {
            history.insert(revision).unwrap();
        }

        // Amending `a` forces a new revision of every descendant, because a
        // parent edge names a digest.
        for revision in [
            Revision::new(rev("a2"), chg("a"), "first, reworded").superseding([rev("a1")]),
            Revision::new(rev("b2"), chg("b"), "second")
                .with_parents([rev("a2")])
                .superseding([rev("b1")]),
            Revision::new(rev("c2"), chg("c"), "third")
                .with_parents([rev("b2")])
                .superseding([rev("c1")]),
        ] {
            history.insert(revision).unwrap();
        }

        // The person's three changes are untouched; six objects exist beneath
        // them.
        for (change, current) in [("a", "a2"), ("b", "b2"), ("c", "c2")] {
            assert_eq!(
                history.change_state(&chg(change)),
                ChangeState::Resolved(history.get(&rev(current)).unwrap()),
                "change {change} should resolve to {current}"
            );
        }
        assert_eq!(history.len(), 6);

        // Head discovery is a pure graph question, so the obsolete tip is still
        // a head until a caller filters by supersession.
        let heads = history.heads();
        assert_eq!(heads, BTreeSet::from([rev("c1"), rev("c2")]));

        let superseded = history.superseded();
        let current_heads = heads
            .difference(&superseded)
            .copied()
            .collect::<BTreeSet<_>>();
        assert_eq!(current_heads, BTreeSet::from([rev("c2")]));
    }

    #[test]
    fn the_two_identities_are_spelled_in_disjoint_alphabets() {
        let revision_id = rev("a1").to_string();
        let change_id = chg("a").to_string();

        assert_eq!(revision_id.len(), REVISION_ID_LEN * 2);
        assert!(revision_id.bytes().all(|byte| hex_nibble(byte).is_some()));

        assert_eq!(change_id.len(), CHANGE_ID_LEN * 2);
        assert!(change_id.bytes().all(|byte| (b'k'..=b'z').contains(&byte)));

        assert_eq!(revision_id.parse(), Ok(rev("a1")));
        assert_eq!(change_id.parse(), Ok(chg("a")));

        // Neither spelling can be read as the other kind of name.
        assert_eq!(revision_id.parse::<ChangeId>(), Err(InvalidChangeId));
        assert_eq!(change_id.parse::<RevisionId>(), Err(InvalidRevisionId));
    }
}
