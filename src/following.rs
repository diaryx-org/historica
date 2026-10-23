//! Which part of history a copy stands on.
//!
//! Decision 0086. A *tip* is a fact about the store: a current revision no
//! current revision stands on ([`History::tips`]). A *head* is a fact about
//! the copy: a tip of the part of history the copy follows. The store cannot
//! know which part that is, because it is a choice made by whoever holds the
//! copy, so the caller supplies a [`Following`] rule and nothing is stored.
//! Heads are derived from the store and the rule every time they are asked
//! for, which keeps decision 0030's sentence true: the folder as it stands,
//! the store as it stands, and no third thing that can disagree with either.
//!
//! A tip the rule does not follow is *held*. It is shown, and joins a head only
//! by being taken, `carry <held> --onto <head>`.

use std::collections::BTreeSet;
use std::fmt;

use crate::core::{History, RevisionId};
use crate::format::RevisionDocument;
use crate::fs::Filesystem;
use crate::store::Store;

/// An embedder's question of one revision: does this copy follow it?
pub type Accepts = dyn Fn(&RevisionId, &RevisionDocument) -> bool + Send + Sync;

/// A rule a copy follows, asked of one revision at a time.
///
/// Following a revision follows everything it stands on. The library makes
/// that true rather than trusting the rule to: the followed part of history is
/// the ancestry of every revision the rule accepts, so a rule that accepts a
/// revision standing on unaccepted work has accepted that work too.
///
/// A rule is not a permission. Held work is in the store, readable, and
/// travels on in every export. The rule decides only what this copy stands
/// on.
pub enum Following {
    /// Every revision. Every tip is a head, which is what a copy that has not
    /// said whose work it follows is given.
    Everything,
    /// Every revision one of these names wrote: its `revised-by`, or its
    /// `author` where it has none ([`writer`]).
    ///
    /// A name is a claim, not evidence (decision 0005). This rule keeps a
    /// person from sweeping in what they did not mean to, and protects them
    /// from no one who will type their name.
    Writers(BTreeSet<String>),
    /// An embedder's own rule: a signature checked against trusted keys, a
    /// maintainer's say-so, anything that can be asked of one document.
    Rule(Box<Accepts>),
}

impl fmt::Debug for Following {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Everything => f.write_str("Everything"),
            Self::Writers(names) => f.debug_tuple("Writers").field(names).finish(),
            Self::Rule(_) => f.write_str("Rule(..)"),
        }
    }
}

/// Who wrote these bytes: `revised-by`, or `author` where it is absent.
///
/// Not who began the change. A take is the taker's, and a contributor's
/// amendment of their own offer is the contributor's.
pub fn writer(document: &RevisionDocument) -> &str {
    document.revised_by.as_deref().unwrap_or(&document.author)
}

impl Following {
    /// Whether the rule itself accepts this one revision.
    ///
    /// A document that will not parse names no writer, so a rule that reads
    /// one does not accept it. [`Following::Everything`] never parses.
    fn accepts<F: Filesystem>(&self, store: &Store<F>, id: &RevisionId) -> bool {
        let read = || store.get(id).ok().flatten();
        match self {
            Self::Everything => true,
            Self::Writers(names) => read().is_some_and(|document| names.contains(writer(document))),
            Self::Rule(rule) => read().is_some_and(|document| rule(id, document)),
        }
    }

    /// The heads of this store under this rule, and the tips it holds.
    pub fn heads<F: Filesystem>(&self, store: &Store<F>) -> Heads {
        let history = store.history();
        let followed = self.followed(store, &history);
        Heads::derive(&history, followed)
    }

    /// The ancestry of every revision the rule accepts.
    ///
    /// Walked down from the childless, stopping at the first accepted revision
    /// on each path: everything beneath an accepted revision is followed
    /// without being asked about, so only revisions above every accepted one
    /// are read in full, and decision 0061's causal read stays the path the
    /// rest of the store takes.
    fn followed<F: Filesystem>(&self, store: &Store<F>, history: &History) -> BTreeSet<RevisionId> {
        if matches!(self, Self::Everything) {
            return history.iter().map(|revision| revision.id).collect();
        }
        let mut followed: BTreeSet<RevisionId> = BTreeSet::new();
        let mut asked: BTreeSet<RevisionId> = BTreeSet::new();
        let mut walking: Vec<RevisionId> = history.childless().into_iter().collect();
        while let Some(id) = walking.pop() {
            if followed.contains(&id) || !asked.insert(id) {
                continue;
            }
            let Some(revision) = history.get(&id) else {
                continue;
            };
            if self.accepts(store, &id) {
                follow_down(history, id, &mut followed);
            } else {
                walking.extend(revision.parents.iter().copied());
            }
        }
        followed
    }
}

/// Mark `from` and everything it stands on as followed.
fn follow_down(history: &History, from: RevisionId, followed: &mut BTreeSet<RevisionId>) {
    let mut stack = vec![from];
    while let Some(id) = stack.pop() {
        let Some(revision) = history.get(&id) else {
            continue;
        };
        if followed.insert(id) {
            stack.extend(revision.parents.iter().copied());
        }
    }
}

/// What a rule makes of a store: the heads it follows and the tips it holds.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Heads {
    /// Tips of the followed part of history: the lines this copy stands on.
    pub heads: BTreeSet<RevisionId>,
    /// Current revisions the rule does not follow and nothing current stands
    /// on: work waiting to be taken.
    pub held: BTreeSet<RevisionId>,
    followed: BTreeSet<RevisionId>,
}

impl Heads {
    /// Whether this copy follows `revision`.
    pub fn follows(&self, revision: &RevisionId) -> bool {
        self.followed.contains(revision)
    }

    /// [`Heads::derive`], for a test elsewhere in the crate that states what
    /// is followed rather than asking a rule.
    #[cfg(test)]
    pub(crate) fn derived(history: &History, followed: BTreeSet<RevisionId>) -> Self {
        Self::derive(history, followed)
    }

    /// Heads and held tips, given what is followed.
    ///
    /// A supersession counts only when the copy follows the revision that
    /// states it, so a held revision naming a followed one on `supersedes`
    /// leaves it current. Among held work, every supersession counts: no held
    /// revision is anybody's head, so nobody's line is hidden by it.
    fn derive(history: &History, followed: BTreeSet<RevisionId>) -> Self {
        let mut superseded: BTreeSet<RevisionId> = BTreeSet::new();
        for revision in history.iter() {
            let counts = followed.contains(&revision.id);
            for predecessor in &revision.supersedes {
                if counts || !followed.contains(predecessor) {
                    superseded.insert(*predecessor);
                }
            }
        }
        let current = |id: &RevisionId| !superseded.contains(id);

        // A head is a tip of what is followed, so a held revision standing on
        // it does not stop it being one. A held tip has no current child at
        // all, since a revision standing on it is held as well.
        let mut standing: BTreeSet<RevisionId> = BTreeSet::new();
        let mut standing_followed: BTreeSet<RevisionId> = BTreeSet::new();
        for revision in history.iter().filter(|revision| current(&revision.id)) {
            standing.extend(revision.parents.iter().copied());
            if followed.contains(&revision.id) {
                standing_followed.extend(revision.parents.iter().copied());
            }
        }

        let mut heads = BTreeSet::new();
        let mut held = BTreeSet::new();
        for revision in history.iter().filter(|revision| current(&revision.id)) {
            if followed.contains(&revision.id) {
                if !standing_followed.contains(&revision.id) {
                    heads.insert(revision.id);
                }
            } else if !standing.contains(&revision.id) {
                held.insert(revision.id);
            }
        }
        Self {
            heads,
            held,
            followed,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::{ChangeId, Revision};

    fn rev(label: &str) -> RevisionId {
        RevisionId::from_bytes(spread(label))
    }

    fn chg(label: &str) -> ChangeId {
        ChangeId::from_bytes(spread(label))
    }

    // The same labels-to-digests spreading `core`'s tests use.
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

    fn history(revisions: impl IntoIterator<Item = Revision>) -> History {
        let mut history = History::new();
        for revision in revisions {
            history.insert(revision).unwrap();
        }
        history
    }

    /// What the copy follows, given the revisions the rule accepts.
    fn following(history: &History, accepted: &[&str]) -> Heads {
        let mut followed = BTreeSet::new();
        for label in accepted {
            follow_down(history, rev(label), &mut followed);
        }
        Heads::derive(history, followed)
    }

    fn set(labels: &[&str]) -> BTreeSet<RevisionId> {
        labels.iter().map(|label| rev(label)).collect()
    }

    #[test]
    fn a_held_line_on_the_head_leaves_the_head_a_head() {
        let history = history([
            Revision::new(rev("h"), chg("h"), "h"),
            Revision::new(rev("s"), chg("s"), "s").with_parents([rev("h")]),
        ]);
        let heads = following(&history, &["h"]);
        assert_eq!(heads.heads, set(&["h"]));
        assert_eq!(heads.held, set(&["s"]));
    }

    #[test]
    fn a_partial_take_leaves_the_untaken_revisions_one_held_tip() {
        let history = history([
            Revision::new(rev("p"), chg("p"), "p"),
            Revision::new(rev("a"), chg("a"), "a").with_parents([rev("p")]),
            Revision::new(rev("b"), chg("b"), "b").with_parents([rev("a")]),
            Revision::new(rev("c"), chg("c"), "c").with_parents([rev("b")]),
            Revision::new(rev("c'"), chg("c"), "c")
                .with_parents([rev("p")])
                .superseding([rev("c")]),
        ]);
        let heads = following(&history, &["c'"]);
        assert_eq!(heads.heads, set(&["c'"]));
        assert_eq!(heads.held, set(&["b"]));
    }

    #[test]
    fn a_stranger_superseding_the_head_hides_nothing() {
        let history = history([
            Revision::new(rev("h"), chg("h"), "h"),
            Revision::new(rev("s"), chg("h"), "s").superseding([rev("h")]),
        ]);
        let heads = following(&history, &["h"]);
        assert_eq!(heads.heads, set(&["h"]));
        assert_eq!(heads.held, set(&["s"]));
    }

    #[test]
    fn an_amended_offer_shows_only_its_successor() {
        let history = history([
            Revision::new(rev("h"), chg("h"), "h"),
            Revision::new(rev("o1"), chg("o"), "o").with_parents([rev("h")]),
            Revision::new(rev("o2"), chg("o"), "o")
                .with_parents([rev("h")])
                .superseding([rev("o1")]),
        ]);
        let heads = following(&history, &["h"]);
        assert_eq!(heads.heads, set(&["h"]));
        assert_eq!(heads.held, set(&["o2"]));
    }

    #[test]
    fn following_a_revision_follows_what_it_stands_on() {
        let history = history([
            Revision::new(rev("a"), chg("a"), "a"),
            Revision::new(rev("b"), chg("b"), "b").with_parents([rev("a")]),
        ]);
        let heads = following(&history, &["b"]);
        assert!(heads.follows(&rev("a")));
        assert_eq!(heads.heads, set(&["b"]));
        assert!(heads.held.is_empty());
    }

    #[test]
    fn following_everything_makes_every_tip_a_head() {
        let history = history([
            Revision::new(rev("p"), chg("p"), "p"),
            Revision::new(rev("x"), chg("x"), "x").with_parents([rev("p")]),
            Revision::new(rev("y"), chg("y"), "y").with_parents([rev("p")]),
            Revision::new(rev("y'"), chg("y"), "y")
                .with_parents([rev("p")])
                .superseding([rev("y")]),
        ]);
        let everything = history.iter().map(|revision| revision.id).collect();
        let heads = Heads::derive(&history, everything);
        assert_eq!(heads.heads, history.tips());
        assert!(heads.held.is_empty());
    }
}
