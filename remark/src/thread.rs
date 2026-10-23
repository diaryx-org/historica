//! A thread's state — *what the replies under a remark have made of it.*
//!
//! A thread is a root remark and the `replying` remarks under it. Any reply
//! may carry a `thread` status or labels (see [the annotation
//! module](crate::annotation#a-threads-state)), but not every writer's reply
//! counts:
//!
//! - the owner, or the root remark's writer, may close or reopen it, and the
//!   latest such reply wins;
//! - only the owner's replies label it.
//!
//! Who the owner is is not a fact any remark can state about itself, so the
//! caller says: [`fold`] takes a predicate over writers. On a forge it is
//! "a key the reader trusts for the repository", and the root's writer is
//! the key that signed the root.
//!
//! The fold is a pure function of the remarks. Anybody holding the same
//! remarks and trusting the same keys gets the same state, whatever order
//! the remarks arrived in. That is what lets an index of threads be
//! deleted and rebuilt from the chains.
//!
//! # The order
//!
//! "Latest" needs an order, and a remark does not carry a time this crate
//! can trust. So the caller gives each reply an order key, [`Post::when`]
//! — the time its revision was recorded, the time a claim vouched for it,
//! anything [`Ord`] the caller holds for every reply alike. Replies are taken
//! in that order. Where two keys are equal, the tie is broken by the writer,
//! then by what the reply changes ([`Status`] order, then the labels it
//! adds, then the labels it removes). Two replies equal in all of that make
//! the same change, so which of them goes first makes no difference.
//!
//! The tie-break makes the answer the same everywhere. It does not make it
//! the right answer: two replies at the same moment that disagree are a
//! disagreement, and the order only decides which of them shows.

use std::collections::BTreeSet;

use crate::annotation::{Annotation, Motivation, Status};

/// One remark in a thread, as the fold sees it: who wrote it, where it falls,
/// and what it says.
#[derive(Debug, Clone, Copy)]
pub struct Post<'a, T> {
    /// The writer, as the caller recognises writers — on a forge, the key
    /// that signed it. Compared with the root's writer and handed to the
    /// owner predicate, and with nothing else.
    pub writer: &'a str,
    /// Where the post falls in the thread. See the module note on the order.
    pub when: T,
    /// The remark itself.
    pub annotation: &'a Annotation,
}

/// A thread, folded: whether it is open, and its labels.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Thread {
    /// [`Status::Open`] until a reply that counts closes it.
    pub status: Status,
    /// The labels the owner's replies have left on it.
    pub labels: BTreeSet<String>,
}

impl Default for Thread {
    /// A thread nobody has replied to: open, with no labels.
    fn default() -> Self {
        Self {
            status: Status::Open,
            labels: BTreeSet::new(),
        }
    }
}

/// The state of the thread under a root remark written by `reporter`.
///
/// `replies` are the remarks under the root, in any order. A post whose
/// motivation is not `replying` changes nothing and is passed over; which
/// remarks belong to the thread is the caller's to gather, because a remark
/// does not know its own identity. `owner` says whether a writer's replies
/// count as the owner's.
///
/// A reply from the owner or from `reporter` sets the status. A reply from
/// the owner adds and removes labels. Anybody else's reply is part of the
/// discussion and changes nothing here. Replies are applied in the order the
/// module note defines, so the latest that counts wins.
pub fn fold<'a, T: Ord>(
    reporter: &str,
    replies: impl IntoIterator<Item = Post<'a, T>>,
    owner: impl Fn(&str) -> bool,
) -> Thread {
    let mut replies: Vec<Post<'a, T>> = replies
        .into_iter()
        .filter(|post| post.annotation.motivation == Motivation::Replying)
        .collect();
    replies.sort_by(|a, b| {
        a.when
            .cmp(&b.when)
            .then_with(|| a.writer.cmp(b.writer))
            .then_with(|| change(a.annotation).cmp(&change(b.annotation)))
    });

    let mut thread = Thread::default();
    for post in replies {
        let owns = owner(post.writer);
        if let Some(status) = post.annotation.thread
            && (owns || post.writer == reporter)
        {
            thread.status = status;
        }
        if owns {
            for label in &post.annotation.unlabel {
                thread.labels.remove(label);
            }
            thread.labels.extend(post.annotation.label.iter().cloned());
        }
    }
    thread
}

/// What a reply changes, as the last of the fold's tie-breaks.
fn change(annotation: &Annotation) -> (Option<Status>, &[String], &[String]) {
    (annotation.thread, &annotation.label, &annotation.unlabel)
}

#[cfg(test)]
mod tests {
    use super::*;

    const ROOT: &str = "ada/remarks/lake-question";
    const OWNER: &str = "owner-key";
    const REPORTER: &str = "ada-key";
    const STRANGER: &str = "eve-key";

    fn reply(status: Option<Status>, label: &[&str], unlabel: &[&str]) -> Annotation {
        let mut a = Annotation::new(ROOT, Motivation::Replying);
        a.thread = status;
        a.label = label.iter().map(|l| l.to_string()).collect();
        a.unlabel = unlabel.iter().map(|l| l.to_string()).collect();
        a.check().unwrap();
        a
    }

    fn post<'a>(writer: &'a str, when: u32, annotation: &'a Annotation) -> Post<'a, u32> {
        Post {
            writer,
            when,
            annotation,
        }
    }

    fn state(posts: Vec<Post<'_, u32>>) -> Thread {
        fold(REPORTER, posts, |writer| writer == OWNER)
    }

    fn labels(thread: &Thread) -> Vec<&str> {
        thread.labels.iter().map(String::as_str).collect()
    }

    #[test]
    fn a_thread_nobody_has_closed_is_open() {
        let talk = reply(None, &[], &[]);
        let thread = state(vec![post(STRANGER, 1, &talk)]);
        assert_eq!(thread, Thread::default());
    }

    #[test]
    fn the_owner_closes_it() {
        let close = reply(Some(Status::Closed), &[], &[]);
        assert_eq!(state(vec![post(OWNER, 1, &close)]).status, Status::Closed);
    }

    #[test]
    fn the_reporter_closes_their_own() {
        let close = reply(Some(Status::Closed), &[], &[]);
        assert_eq!(
            state(vec![post(REPORTER, 1, &close)]).status,
            Status::Closed
        );
    }

    #[test]
    fn a_strangers_close_changes_nothing() {
        let close = reply(Some(Status::Closed), &[], &[]);
        assert_eq!(state(vec![post(STRANGER, 1, &close)]).status, Status::Open);

        // Nor does a stranger reopen what the owner closed.
        let reopen = reply(Some(Status::Open), &[], &[]);
        let thread = state(vec![post(OWNER, 1, &close), post(STRANGER, 2, &reopen)]);
        assert_eq!(thread.status, Status::Closed);
    }

    /// The latest reply that counts wins, whoever of the two wrote it.
    #[test]
    fn a_reopen_after_a_close_reopens_it() {
        let close = reply(Some(Status::Closed), &[], &[]);
        let reopen = reply(Some(Status::Open), &[], &[]);
        let thread = state(vec![post(OWNER, 1, &close), post(REPORTER, 2, &reopen)]);
        assert_eq!(thread.status, Status::Open);
        let thread = state(vec![
            post(OWNER, 1, &close),
            post(REPORTER, 2, &reopen),
            post(OWNER, 3, &close),
        ]);
        assert_eq!(thread.status, Status::Closed);
    }

    /// Labels are the owner's alone; the reporter's are as ignored as a
    /// stranger's.
    #[test]
    fn only_the_owners_labels_count() {
        let bug = reply(None, &["bug", "triage"], &[]);
        let spam = reply(None, &["wontfix"], &["bug"]);
        let triaged = reply(None, &["confirmed"], &["triage"]);
        let thread = state(vec![
            post(OWNER, 1, &bug),
            post(STRANGER, 2, &spam),
            post(REPORTER, 3, &spam),
            post(OWNER, 4, &triaged),
        ]);
        assert_eq!(labels(&thread), vec!["bug", "confirmed"]);
    }

    /// A remark under the root that is not a reply is not a state change,
    /// even from the owner.
    #[test]
    fn only_a_reply_changes_the_thread() {
        let mut note = Annotation::new(ROOT, Motivation::Commenting);
        note.body = "closing thoughts".into();
        assert_eq!(state(vec![post(OWNER, 1, &note)]), Thread::default());
    }

    /// The same remarks, in every order they could arrive in, fold to one
    /// state — including the tie of two replies at the same moment.
    #[test]
    fn the_order_they_arrive_in_does_not_matter() {
        let close = reply(Some(Status::Closed), &["done"], &[]);
        let reopen = reply(Some(Status::Open), &[], &["done"]);
        let label = reply(None, &["docs"], &[]);
        let stranger = reply(Some(Status::Open), &["spam"], &[]);
        let posts = [
            post(OWNER, 1, &label),
            post(OWNER, 2, &close),
            post(REPORTER, 2, &reopen),
            post(OWNER, 2, &reopen),
            post(STRANGER, 3, &stranger),
        ];

        let first = state(posts.to_vec());
        let mut seen = Vec::new();
        permutations(&posts, &mut Vec::new(), &mut seen);
        assert_eq!(seen.len(), 120);
        for order in seen {
            assert_eq!(state(order), first);
        }
        // At the tie, the owner's two replies are ordered by what they
        // change — reopen (`open`) before close — and the owner sorts after
        // the reporter, so the owner's close is last.
        assert_eq!(first.status, Status::Closed);
        assert_eq!(labels(&first), vec!["docs", "done"]);
    }

    fn permutations<'a>(
        rest: &[Post<'a, u32>],
        taken: &mut Vec<Post<'a, u32>>,
        out: &mut Vec<Vec<Post<'a, u32>>>,
    ) {
        if rest.is_empty() {
            out.push(taken.clone());
            return;
        }
        for i in 0..rest.len() {
            let mut left = rest.to_vec();
            taken.push(left.remove(i));
            permutations(&left, taken, out);
            taken.pop();
        }
    }
}
