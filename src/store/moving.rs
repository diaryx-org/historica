//! Which bookmarks a fetch moves.
//!
//! Decision 0088. A bookmark this copy holds and the publisher also states
//! moves to the publisher's reading when the move is forward along a line the
//! copy follows: the revision the copy's bookmark resolves to is in the
//! ancestry of the one the publisher's resolves to, and the copy follows the
//! publisher's. Otherwise it stays, and the fetch says which and why.
//!
//! The ancestry is walked once for every bookmark a fetch weighs, not once
//! per bookmark, so a publisher sharing one name per change set costs one
//! walk.

use std::collections::{BTreeMap, BTreeSet};

use crate::core::{ChangeState, History, RevisionId};
use crate::following::Heads;

use super::Name;

/// A bookmark a fetch moved to the publisher's reading.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct MovedName {
    /// The bookmark.
    pub name: String,
    /// What it named before the fetch.
    pub from: Name,
    /// What it names now, which is what the publisher's names.
    pub to: Name,
}

/// A bookmark the publisher reads differently, which this copy kept.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct KeptName {
    /// The bookmark.
    pub name: String,
    /// This copy's reading, which it still has.
    pub ours: Name,
    /// The publisher's reading.
    pub theirs: Name,
    /// Why the copy's reading stayed.
    pub because: Keeping,
}

/// Why a fetch did not move a bookmark.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[non_exhaustive]
pub enum Keeping {
    /// The copy's revision is not in the ancestry of the publisher's, so the
    /// copy has work of its own on the bookmark (decision 0062's case).
    NotForward,
    /// The copy does not follow the publisher's revision: it holds it as
    /// work waiting to be taken (decision 0086).
    NotFollowed,
    /// One of the two names a revision or a file, which has no line to be
    /// forward on.
    Pinned,
    /// One of the two changes has no single current revision here: it is
    /// divergent, abandoned, or claimed by no revision this store holds.
    Unresolved,
}

/// Weigh each bookmark the copy and the publisher both state, and say
/// what became of each, by name.
///
/// `readings` is the name, the copy's target and the publisher's target.
/// Two readings that agree are neither moved nor kept: there was nothing to
/// decide.
pub(super) fn decide(
    history: &History,
    heads: &Heads,
    readings: Vec<(String, Name, Name)>,
) -> (Vec<MovedName>, Vec<KeptName>) {
    let mut moved = Vec::new();
    let mut kept = Vec::new();
    let mut weighed: Vec<(String, Name, Name, RevisionId, RevisionId)> = Vec::new();
    let keep = |kept: &mut Vec<KeptName>, name: String, ours, theirs, because| {
        kept.push(KeptName {
            name,
            ours,
            theirs,
            because,
        });
    };
    for (name, ours, theirs) in readings {
        if ours == theirs {
            continue;
        }
        let (Name::Change(mine), Name::Change(publishers)) = (ours, theirs) else {
            keep(&mut kept, name, ours, theirs, Keeping::Pinned);
            continue;
        };
        let (Some(from), Some(to)) = (current(history, &mine), current(history, &publishers))
        else {
            keep(&mut kept, name, ours, theirs, Keeping::Unresolved);
            continue;
        };
        weighed.push((name, ours, theirs, from, to));
    }

    let pairs: Vec<(RevisionId, RevisionId)> = weighed
        .iter()
        .map(|(_, _, _, from, to)| (*from, *to))
        .collect();
    let forward = reaches(history, &pairs);
    for ((name, ours, theirs, _, to), forward) in weighed.into_iter().zip(forward) {
        if !forward {
            keep(&mut kept, name, ours, theirs, Keeping::NotForward);
        } else if !heads.follows(&to) {
            keep(&mut kept, name, ours, theirs, Keeping::NotFollowed);
        } else {
            moved.push(MovedName {
                name,
                from: ours,
                to: theirs,
            });
        }
    }
    moved.sort_by(|a, b| a.name.cmp(&b.name));
    kept.sort_by(|a, b| a.name.cmp(&b.name));
    (moved, kept)
}

/// The one current revision of a change, where it has one.
fn current(history: &History, change: &crate::core::ChangeId) -> Option<RevisionId> {
    match history.change_state(change) {
        ChangeState::Resolved(revision) => Some(revision.id),
        _ => None,
    }
}

/// For each `(from, to)`, whether `from` is a strict ancestor of `to`.
///
/// One walk for all of them. Each distinct `to` is a bit, every revision
/// carries the bits of the `to`s that stand on it, and a revision is walked
/// again only when it gains a bit, so the cost is the ancestry of the `to`s
/// times the number of them in words rather than in walks.
fn reaches(history: &History, pairs: &[(RevisionId, RevisionId)]) -> Vec<bool> {
    let sources: BTreeSet<RevisionId> = pairs.iter().map(|(_, to)| *to).collect();
    let index: BTreeMap<RevisionId, usize> = sources
        .iter()
        .enumerate()
        .map(|(at, id)| (*id, at))
        .collect();
    let words = sources.len().div_ceil(64);
    let mut bits: BTreeMap<RevisionId, Vec<u64>> = BTreeMap::new();
    let mut walking: Vec<RevisionId> = Vec::new();
    // A `to` does not reach itself: a source's own bit is given to its
    // parents, not to it.
    for (id, at) in &index {
        let Some(revision) = history.get(id) else {
            continue;
        };
        for parent in &revision.parents {
            if gain(&mut bits, *parent, words, |into| {
                into[at / 64] |= 1 << (at % 64)
            }) {
                walking.push(*parent);
            }
        }
    }
    while let Some(id) = walking.pop() {
        let Some(revision) = history.get(&id) else {
            continue;
        };
        let carried = bits.get(&id).cloned().unwrap_or_default();
        for parent in &revision.parents {
            let changed = gain(&mut bits, *parent, words, |into| {
                for (word, more) in into.iter_mut().zip(&carried) {
                    *word |= more;
                }
            });
            if changed {
                walking.push(*parent);
            }
        }
    }
    pairs
        .iter()
        .map(|(from, to)| {
            let at = index[to];
            bits.get(from)
                .is_some_and(|word| word[at / 64] & (1 << (at % 64)) != 0)
        })
        .collect()
}

/// Add bits to one revision's set, saying whether it gained any.
fn gain(
    bits: &mut BTreeMap<RevisionId, Vec<u64>>,
    id: RevisionId,
    words: usize,
    add: impl FnOnce(&mut Vec<u64>),
) -> bool {
    let set = bits.entry(id).or_insert_with(|| vec![0; words]);
    let before = set.clone();
    add(set);
    *set != before
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

    /// A line `a`–`b`–`c`, and `m` on `a` beside it.
    fn line() -> History {
        let mut history = History::new();
        for revision in [
            Revision::new(rev("a"), chg("a"), "a"),
            Revision::new(rev("b"), chg("b"), "b").with_parents([rev("a")]),
            Revision::new(rev("c"), chg("c"), "c").with_parents([rev("b")]),
            Revision::new(rev("m"), chg("m"), "m").with_parents([rev("a")]),
        ] {
            history.insert(revision).unwrap();
        }
        history
    }

    #[test]
    fn ancestry_is_strict_and_answered_for_every_pair_in_one_walk() {
        let history = line();
        let answers = reaches(
            &history,
            &[
                (rev("a"), rev("c")),
                (rev("b"), rev("c")),
                (rev("c"), rev("c")),
                (rev("m"), rev("c")),
                (rev("a"), rev("m")),
                (rev("b"), rev("m")),
            ],
        );
        assert_eq!(answers, [true, true, false, false, true, false]);
    }

    #[test]
    fn more_than_one_word_of_bookmarks_is_still_answered() {
        let mut history = History::new();
        history
            .insert(Revision::new(rev("root"), chg("root"), "root"))
            .unwrap();
        let mut pairs = Vec::new();
        for at in 0..130 {
            let label = format!("tip-{at}");
            history
                .insert(Revision::new(rev(&label), chg(&label), "tip").with_parents([rev("root")]))
                .unwrap();
            pairs.push((rev("root"), rev(&label)));
        }
        pairs.push((rev("tip-1"), rev("tip-129")));
        let answers = reaches(&history, &pairs);
        assert!(answers[..130].iter().all(|forward| *forward));
        assert!(!answers[130]);
    }

    #[test]
    fn a_bookmark_moves_forward_on_a_followed_line_and_says_why_it_stays_otherwise() {
        let history = line();
        let everything = crate::following::Heads::derived(
            &history,
            history.iter().map(|revision| revision.id).collect(),
        );
        let readings = vec![
            (
                "main".to_owned(),
                Name::Change(chg("b")),
                Name::Change(chg("c")),
            ),
            (
                "mine".to_owned(),
                Name::Change(chg("m")),
                Name::Change(chg("c")),
            ),
            (
                "same".to_owned(),
                Name::Change(chg("c")),
                Name::Change(chg("c")),
            ),
            (
                "tag".to_owned(),
                Name::Revision(rev("a")),
                Name::Change(chg("c")),
            ),
            (
                "lost".to_owned(),
                Name::Change(chg("nowhere")),
                Name::Change(chg("c")),
            ),
        ];
        let (moved, kept) = decide(&history, &everything, readings.clone());
        assert_eq!(
            moved,
            [MovedName {
                name: "main".to_owned(),
                from: Name::Change(chg("b")),
                to: Name::Change(chg("c")),
            }]
        );
        let reasons: Vec<(&str, Keeping)> = kept
            .iter()
            .map(|kept| (kept.name.as_str(), kept.because))
            .collect();
        assert_eq!(
            reasons,
            [
                ("lost", Keeping::Unresolved),
                ("mine", Keeping::NotForward),
                ("tag", Keeping::Pinned),
            ]
        );

        // Following only `b` and what it stands on: `c` is held, so `main`
        // is not moved onto it.
        let up_to_b = crate::following::Heads::derived(&history, [rev("a"), rev("b")].into());
        let (moved, kept) = decide(&history, &up_to_b, readings[..1].to_vec());
        assert!(moved.is_empty());
        assert_eq!(kept[0].because, Keeping::NotFollowed);
    }
}
