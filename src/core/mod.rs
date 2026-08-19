//! Pure causal-history primitives.
//!
//! A [`History`] is a grow-only collection of immutable [`Change`] values.
//! Replicas merge by set union. No timestamp participates in identity or
//! causality.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

/// The stable identity of one immutable change.
///
/// The core keeps this opaque. A later readable format will define how an ID is
/// derived and spelled.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ChangeId(String);

impl ChangeId {
    /// Construct an ID from its readable spelling.
    pub fn new(value: impl Into<String>) -> Result<Self, InvalidChangeId> {
        let value = value.into();
        if value.trim().is_empty() {
            return Err(InvalidChangeId);
        }
        Ok(Self(value))
    }

    /// The readable spelling of this ID.
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl fmt::Display for ChangeId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

/// An empty string is not an identity.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct InvalidChangeId;

impl fmt::Display for InvalidChangeId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("a change ID cannot be empty")
    }
}

impl std::error::Error for InvalidChangeId {}

/// One immutable point in causal history.
///
/// Payloads, trees, and patches are intentionally absent from this first
/// model. The core first establishes the convergence and causality rules they
/// will live inside.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Change {
    pub id: ChangeId,
    pub parents: BTreeSet<ChangeId>,
    pub message: String,
}

impl Change {
    /// Construct a change with an explicit set of causal parents.
    pub fn new(
        id: ChangeId,
        parents: impl IntoIterator<Item = ChangeId>,
        message: impl Into<String>,
    ) -> Self {
        Self {
            id,
            parents: parents.into_iter().collect(),
            message: message.into(),
        }
    }
}

/// A convergent collection of immutable changes.
///
/// Two replicas merge by union. Receiving the same change repeatedly is
/// idempotent. Receiving different content under the same ID is corruption or
/// an invalid ID scheme and is rejected rather than resolved arbitrarily.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct History {
    changes: BTreeMap<ChangeId, Change>,
}

impl History {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn len(&self) -> usize {
        self.changes.len()
    }

    pub fn is_empty(&self) -> bool {
        self.changes.is_empty()
    }

    pub fn get(&self, id: &ChangeId) -> Option<&Change> {
        self.changes.get(id)
    }

    pub fn iter(&self) -> impl Iterator<Item = &Change> {
        self.changes.values()
    }

    /// Add one immutable change.
    pub fn insert(&mut self, change: Change) -> Result<bool, IdCollision> {
        match self.changes.get(&change.id) {
            Some(existing) if existing == &change => Ok(false),
            Some(_) => Err(IdCollision {
                id: change.id.clone(),
            }),
            None => {
                self.changes.insert(change.id.clone(), change);
                Ok(true)
            }
        }
    }

    /// Merge everything observed by `other` into this replica.
    pub fn merge(&mut self, other: &Self) -> Result<usize, IdCollision> {
        // Validate first so a collision cannot leave a partial merge behind.
        for (id, incoming) in &other.changes {
            if let Some(existing) = self.changes.get(id)
                && existing != incoming
            {
                return Err(IdCollision { id: id.clone() });
            }
        }

        let before = self.len();
        self.changes.extend(other.changes.clone());
        Ok(self.len() - before)
    }

    /// Changes no observed change names as a parent.
    ///
    /// Missing parents do not make a child a head: the child's declaration is
    /// still evidence that its named parent has a successor, even if transport
    /// has not delivered that parent yet.
    pub fn heads(&self) -> BTreeSet<ChangeId> {
        let parents = self
            .changes
            .values()
            .flat_map(|change| change.parents.iter())
            .collect::<BTreeSet<_>>();

        self.changes
            .keys()
            .filter(|id| !parents.contains(id))
            .cloned()
            .collect()
    }

    /// Parent IDs named by a change but not yet present locally.
    pub fn missing_parents(&self) -> BTreeSet<ChangeId> {
        self.changes
            .values()
            .flat_map(|change| change.parents.iter())
            .filter(|parent| !self.changes.contains_key(*parent))
            .cloned()
            .collect()
    }
}

/// Two non-identical immutable changes claimed the same ID.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IdCollision {
    pub id: ChangeId,
}

impl fmt::Display for IdCollision {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "different changes claim the ID `{}`", self.id)
    }
}

impl std::error::Error for IdCollision {}

#[cfg(test)]
mod tests {
    use super::*;

    fn id(value: &str) -> ChangeId {
        ChangeId::new(value).unwrap()
    }

    fn change(value: &str, parents: &[&str]) -> Change {
        Change::new(id(value), parents.iter().map(|parent| id(parent)), value)
    }

    #[test]
    fn concurrent_replicas_converge_by_union() {
        let root = change("root", &[]);
        let mut left = History::new();
        let mut right = History::new();
        left.insert(root.clone()).unwrap();
        right.insert(root).unwrap();
        left.insert(change("left", &["root"])).unwrap();
        right.insert(change("right", &["root"])).unwrap();

        let left_before = left.clone();
        let right_before = right.clone();
        left.merge(&right_before).unwrap();
        right.merge(&left_before).unwrap();

        assert_eq!(left, right);
        assert_eq!(left.heads(), BTreeSet::from([id("left"), id("right")]));
    }

    #[test]
    fn a_merge_change_joins_concurrent_heads() {
        let mut history = History::new();
        history.insert(change("root", &[])).unwrap();
        history.insert(change("left", &["root"])).unwrap();
        history.insert(change("right", &["root"])).unwrap();
        history.insert(change("merge", &["left", "right"])).unwrap();

        assert_eq!(history.heads(), BTreeSet::from([id("merge")]));
    }

    #[test]
    fn duplicate_delivery_is_idempotent() {
        let mut history = History::new();
        let root = change("root", &[]);

        assert!(history.insert(root.clone()).unwrap());
        assert!(!history.insert(root).unwrap());
        assert_eq!(history.len(), 1);
    }

    #[test]
    fn conflicting_content_under_one_id_is_rejected_atomically() {
        let mut local = History::new();
        local.insert(change("same", &[])).unwrap();

        let mut remote = History::new();
        remote
            .insert(Change::new(id("same"), [], "different message"))
            .unwrap();
        remote.insert(change("other", &[])).unwrap();

        assert_eq!(local.merge(&remote), Err(IdCollision { id: id("same") }));
        assert_eq!(local.len(), 1);
        assert!(local.get(&id("other")).is_none());
    }

    #[test]
    fn incomplete_transport_names_missing_parents() {
        let mut history = History::new();
        history.insert(change("child", &["absent"])).unwrap();

        assert_eq!(history.heads(), BTreeSet::from([id("child")]));
        assert_eq!(history.missing_parents(), BTreeSet::from([id("absent")]));
    }
}
