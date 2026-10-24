---
title: A fetch asks past its bound
part_of: '[Tasks](/docs/tasks/tasks.md)'
status: open
created: 2026-10-24
updated: 2026-10-24
description: Ahead counts only its own threads against IN_FLIGHT, so a get for a path no thread has taken yet asks beside them — nine requests at once where the trailer promises eight — and the test that holds it to the bound fails on main
---

# A fetch asks past its bound

`Ahead` (`cli/src/cli/ahead.rs`) is meant to have at most
[`IN_FLIGHT`](/cli/src/cli/ahead.rs) requests out at once: its doc says
"Requests in flight at once, at most", and `831165f`, which added it,
promises "up to eight requests in flight at once" in its
`Behavioural-change:` trailer. Only the threads `prefetch` starts count
against that bound. `get` asks on the caller's thread for any path that is
neither kept nor being asked for, taking it out of the queue first, and
nothing stops it doing that while every thread is busy.

The fetch calls `get` for the first path of its plan straight after
`prefetch` returns, usually before any thread has taken that path. The
threads then take the next `IN_FLIGHT` paths and the fetch asks for the
first one beside them, so `IN_FLIGHT + 1` requests are out at once: nine
from `historica fetch`. The same happens later whenever the fetch reaches a
path the threads have not taken yet.

`the_small_files_of_a_plan_are_asked_for_together` holds `Ahead` to the
bound and sees five requests against four. On a loaded machine the threads
usually win the race and it passes, which is why `831165f`'s pull request
was green. Run alone it nearly always fails, and it failed `CI / Test` on
`main` at `56567fc`.

## Repro

```console
$ cargo test -p historica-cli --bin historica --no-run
$ bin=$(ls -t target/debug/deps/historica-* | grep -v '\.d$' | head -1)
$ for i in $(seq 100); do $bin cli::ahead::tests::the_small_files_of_a_plan_are_asked_for_together >/dev/null 2>&1 || echo fail; done | wc -l
99
```

Each failure reads `5 requests at once, past the bound` at `ahead.rs:281`.

## Candidates

- **Count the fetch's request against the bound.** A `get` for a path still
  queued moves it to the front of the queue and waits for it as it waits
  for one being asked for, so that while threads are running only they
  ask. `get` asks for itself only for a path that was never hinted, or when
  no thread is running. One thing to check: the threads also stop while
  `HELD` bytes are unclaimed, so a `get` that waits must not wait behind
  answers that only it would take.
- **Make the bound mean "ahead of the fetch".** `Ahead::new` already says
  "at most `in_flight` requests ahead of the fetch". If that is the intent,
  `IN_FLIGHT`'s doc, the test (`most <= 5`) and the changelog entry that
  `831165f`'s trailer will produce all say `IN_FLIGHT + 1`, which is nine.

## Done when

The bound `IN_FLIGHT`'s doc and the changelog state is the one `Ahead`
keeps, the repro's loop prints `0`, and `CI / Test` is green on `main`.
