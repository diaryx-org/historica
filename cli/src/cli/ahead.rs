//! Asking ahead: what [`Source::prefetch`] is for, over a transport whose every
//! answer is a round trip.
//!
//! A fetch hands its source every small file of its plan before it asks for
//! any of them, and then asks for each in plan order. Over HTTP, asking in
//! that order one at a time is one round trip after another, and a first fetch
//! of a few hundred files spends a minute and a half waiting on the network
//! and none of it working. So the hint starts a few requests at once and keeps
//! what they answer, and [`get`](Source::get) hands a kept answer back where
//! there is one and asks as it always did where there is not.
//!
//! `get` stays the answer, as the trait says. A prefetch that failed, or was
//! never made, or was made for a plan the fetch has since left behind, changes
//! nothing but the time:
//!
//! - **A failure is not kept.** The fetch asks again when it gets there, and
//!   whatever it is told then is what it reports.
//! - **A missing file is kept**, as `Ok(None)`. It is an answer, not a failure,
//!   and decision 0048's reading of the manifest again still happens when the
//!   fetch reaches it.
//! - **A new hint drops the old one's answers.** The fetch hints again after
//!   reading the manifest again, and an answer from before that is an answer
//!   about what the publisher had then.
//!
//! The asking is a few threads and not an executor, because the client
//! underneath is blocking. How few is [`IN_FLIGHT`]: enough to hide the round
//! trips, and not so many that a static host takes it for something else.
//! What is held is bounded too, by [`HELD`]: past it, the asking waits for the
//! fetch to take some, so a plan larger than that is asked for in pieces, in
//! plan order.

use std::collections::{HashMap, HashSet, VecDeque};
use std::panic::{self, AssertUnwindSafe};
use std::sync::{Arc, Condvar, Mutex, MutexGuard, PoisonError};
use std::thread;

use historica::store::{Source, Unreachable};

/// Requests in flight at once, at most.
pub(super) const IN_FLIGHT: usize = 8;

/// Bytes of answers held for the fetch before the asking waits for it.
pub(super) const HELD: usize = 8 << 20;

/// What one request says: [`Source::get`]'s answer.
type Answer = Result<Option<Vec<u8>>, Unreachable>;

/// One request, made however the transport makes it.
type Ask = dyn Fn(&str) -> Answer + Send + Sync;

/// A source that asks ahead for what it is told it will be asked.
pub(super) struct Ahead {
    ask: Arc<Ask>,
    shared: Arc<Shared>,
    in_flight: usize,
}

struct Shared {
    state: Mutex<State>,
    /// Told whenever an answer lands, one is taken, or the hint changes.
    changed: Condvar,
    held_at_most: usize,
}

#[derive(Default)]
struct State {
    /// Which hint this is, counted, so an answer to an earlier one is not kept.
    hint: u64,
    /// Hinted and not yet asked for, in plan order.
    queued: VecDeque<String>,
    /// Being asked for now, each with the hint it was asked under.
    asking: HashMap<String, u64>,
    /// Answered, and not yet taken.
    kept: HashMap<String, Option<Vec<u8>>>,
    /// The bytes in `kept`.
    held: usize,
    /// Threads asking.
    workers: usize,
}

impl Shared {
    fn lock(&self) -> MutexGuard<'_, State> {
        // Nothing is left half-done under the lock, so a panic elsewhere
        // leaves the state as good as it was.
        self.state.lock().unwrap_or_else(PoisonError::into_inner)
    }

    fn wait<'a>(&self, state: MutexGuard<'a, State>) -> MutexGuard<'a, State> {
        self.changed
            .wait(state)
            .unwrap_or_else(PoisonError::into_inner)
    }
}

impl Ahead {
    /// Ask through `ask`, with at most `in_flight` requests ahead of the fetch
    /// and at most `held_at_most` bytes of their answers waiting for it.
    pub(super) fn new(
        ask: impl Fn(&str) -> Answer + Send + Sync + 'static,
        in_flight: usize,
        held_at_most: usize,
    ) -> Self {
        Self {
            ask: Arc::new(ask),
            shared: Arc::new(Shared {
                state: Mutex::new(State::default()),
                changed: Condvar::new(),
                held_at_most,
            }),
            in_flight,
        }
    }
}

impl Source for Ahead {
    fn get(&self, path: &str) -> Answer {
        let mut state = self.shared.lock();
        loop {
            if let Some(answer) = state.kept.remove(path) {
                state.held -= answer.as_ref().map_or(0, Vec::len);
                self.shared.changed.notify_all();
                return Ok(answer);
            }
            // Already on its way: waiting for it is never slower than asking
            // again behind it.
            if state.asking.get(path) != Some(&state.hint) {
                break;
            }
            state = self.shared.wait(state);
        }
        // Not asked for yet, so it is asked for here and not twice.
        if let Some(at) = state.queued.iter().position(|queued| queued == path) {
            state.queued.remove(at);
        }
        drop(state);
        (self.ask)(path)
    }

    fn prefetch(&self, paths: &[&str]) {
        let mut state = self.shared.lock();
        state.hint += 1;
        state.kept.clear();
        state.held = 0;
        let mut seen = HashSet::new();
        state.queued = paths
            .iter()
            .filter(|path| seen.insert(**path))
            .map(|path| (*path).to_owned())
            .collect();
        self.shared.changed.notify_all();
        let wanted = self.in_flight.min(state.queued.len());
        while state.workers < wanted {
            let ask = Arc::clone(&self.ask);
            let shared = Arc::clone(&self.shared);
            // A thread that cannot be started is a request the fetch makes
            // itself, in its turn.
            if thread::Builder::new()
                .name("historica-fetch".to_owned())
                .spawn(move || work(&*ask, &shared))
                .is_err()
            {
                break;
            }
            state.workers += 1;
        }
    }
}

impl Drop for Ahead {
    /// Nothing more is asked for, and a thread mid-request finishes it and
    /// goes.
    fn drop(&mut self) {
        let mut state = self.shared.lock();
        state.hint += 1;
        state.queued.clear();
        state.kept.clear();
        state.held = 0;
        self.shared.changed.notify_all();
    }
}

/// One thread's share of the asking: the next queued path, until none is left.
fn work(ask: &Ask, shared: &Shared) {
    let mut state = shared.lock();
    while let Some(path) = state.queued.front().cloned() {
        if state.held >= shared.held_at_most {
            state = shared.wait(state);
            continue;
        }
        state.queued.pop_front();
        let hint = state.hint;
        state.asking.insert(path.clone(), hint);
        drop(state);
        let answer = panic::catch_unwind(AssertUnwindSafe(|| ask(&path)))
            .unwrap_or_else(|_| Err(Unreachable::saying("the request panicked")));
        state = shared.lock();
        if state.asking.get(&path) == Some(&hint) {
            state.asking.remove(&path);
        }
        if let Ok(answer) = answer
            && state.hint == hint
        {
            state.held += answer.as_ref().map_or(0, Vec::len);
            state.kept.insert(path, answer);
        }
        shared.changed.notify_all();
    }
    state.workers -= 1;
}

#[cfg(test)]
mod tests {
    use std::sync::atomic::{AtomicUsize, Ordering};
    use std::sync::{Arc, Mutex};
    use std::thread;
    use std::time::Duration;

    use historica::store::{Source, Unreachable};

    use super::{Ahead, Answer};

    /// A transport that takes a while to answer and counts what it is asked.
    #[derive(Default)]
    struct Far {
        now: AtomicUsize,
        most: AtomicUsize,
        asked: Mutex<Vec<String>>,
    }

    impl Far {
        fn ask(&self, path: &str, answer: impl FnOnce(usize) -> Answer) -> Answer {
            let before = {
                let mut asked = self.asked.lock().unwrap();
                asked.push(path.to_owned());
                asked.iter().filter(|asked| *asked == path).count() - 1
            };
            let now = self.now.fetch_add(1, Ordering::SeqCst) + 1;
            self.most.fetch_max(now, Ordering::SeqCst);
            thread::sleep(Duration::from_millis(40));
            self.now.fetch_sub(1, Ordering::SeqCst);
            answer(before)
        }

        fn times_asked(&self, path: &str) -> usize {
            let asked = self.asked.lock().unwrap();
            asked.iter().filter(|asked| *asked == path).count()
        }

        fn asked(&self) -> usize {
            self.asked.lock().unwrap().len()
        }
    }

    /// A source over `far` whose every path holds its own name.
    fn naming(far: &Arc<Far>, in_flight: usize, held: usize) -> Ahead {
        let far = Arc::clone(far);
        Ahead::new(
            move |path| far.ask(path, |_| Ok(Some(path.as_bytes().to_vec()))),
            in_flight,
            held,
        )
    }

    fn paths(count: usize) -> Vec<String> {
        (0..count)
            .map(|n| format!("documents/{n:04}.txt"))
            .collect()
    }

    #[test]
    fn the_small_files_of_a_plan_are_asked_for_together() {
        let far = Arc::new(Far::default());
        let source = naming(&far, 4, usize::MAX);
        let plan = paths(16);
        source.prefetch(&plan.iter().map(String::as_str).collect::<Vec<_>>());
        for path in &plan {
            assert_eq!(source.get(path).unwrap().as_deref(), Some(path.as_bytes()));
        }
        let most = far.most.load(Ordering::SeqCst);
        assert!(most > 1, "one request at a time");
        assert!(most <= 4, "{most} requests at once, past the bound");
        for path in &plan {
            assert_eq!(far.times_asked(path), 1, "{path}");
        }
    }

    #[test]
    fn without_a_hint_each_path_is_asked_for_in_its_turn() {
        let far = Arc::new(Far::default());
        let source = naming(&far, 4, usize::MAX);
        for path in paths(3) {
            assert_eq!(source.get(&path).unwrap().as_deref(), Some(path.as_bytes()));
        }
        assert_eq!(far.most.load(Ordering::SeqCst), 1);
        assert_eq!(far.asked(), 3);
    }

    #[test]
    fn a_missing_file_is_kept_as_an_answer() {
        let far = Arc::new(Far::default());
        let source = {
            let far = Arc::clone(&far);
            Ahead::new(move |path| far.ask(path, |_| Ok(None)), 4, usize::MAX)
        };
        source.prefetch(&["gone.txt"]);
        thread::sleep(Duration::from_millis(100));
        assert_eq!(source.get("gone.txt").unwrap(), None);
        assert_eq!(far.times_asked("gone.txt"), 1);
    }

    #[test]
    fn a_failed_prefetch_is_asked_again() {
        let far = Arc::new(Far::default());
        let source = {
            let far = Arc::clone(&far);
            Ahead::new(
                move |path| {
                    far.ask(path, |before| match before {
                        0 => Err(Unreachable::saying("the connection went away")),
                        _ => Ok(Some(b"there".to_vec())),
                    })
                },
                4,
                usize::MAX,
            )
        };
        source.prefetch(&["flaky.txt"]);
        thread::sleep(Duration::from_millis(100));
        assert_eq!(
            source.get("flaky.txt").unwrap().as_deref(),
            Some(&b"there"[..])
        );
        assert_eq!(far.times_asked("flaky.txt"), 2);
    }

    #[test]
    fn a_new_hint_drops_what_the_old_one_kept() {
        let far = Arc::new(Far::default());
        let source = naming(&far, 4, usize::MAX);
        source.prefetch(&["a.txt"]);
        thread::sleep(Duration::from_millis(100));
        source.prefetch(&["b.txt"]);
        assert_eq!(source.get("a.txt").unwrap().as_deref(), Some(&b"a.txt"[..]));
        assert_eq!(far.times_asked("a.txt"), 2);
        assert_eq!(source.get("b.txt").unwrap().as_deref(), Some(&b"b.txt"[..]));
        assert_eq!(far.times_asked("b.txt"), 1);
    }

    #[test]
    fn a_large_plan_is_held_a_piece_at_a_time() {
        let far = Arc::new(Far::default());
        let plan = paths(32);
        // Room for two answers, and the two threads may each be one request
        // past it when it fills.
        let source = naming(&far, 2, 2 * plan[0].len());
        source.prefetch(&plan.iter().map(String::as_str).collect::<Vec<_>>());
        thread::sleep(Duration::from_millis(400));
        let asked = far.asked();
        assert!(asked <= 4, "{asked} asked for with room for two");
        for path in &plan {
            assert_eq!(source.get(path).unwrap().as_deref(), Some(path.as_bytes()));
        }
        assert_eq!(far.asked(), plan.len());
    }
}
