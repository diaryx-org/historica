---
title: Two git tests share one scratch directory
description: Both tests in `git/tests/run.rs` delete and remake `CARGO_TARGET_TMPDIR/run-cli` before running the binary in it, so under `cargo test`'s parallel threads one removes the other's working directory and its spawn fails — about one run in six
status: done
created: 2026-10-28
updated: 2026-10-30
part_of: '[Closed tasks](/docs/tasks/closed/closed.md)'
---

# Two git tests share one scratch directory

**Status.** Done, by `test(git): give each run test a scratch directory of
its own`, which takes the change below: `run` takes a name, and each test's
directory is `CARGO_TARGET_TMPDIR/run-cli-<name>`. The test binary, run 300
times with the default thread count, failed 11 times before and none after;
the repro's first loop prints `0`.

`run` in `git/tests/run.rs` gives every call the same directory,
`CARGO_TARGET_TMPDIR/run-cli`: it removes it, makes it again, and spawns
`historica-git write --wrote -` with it as the working directory. Its two
tests, `wrote_nothing_is_silent_and_succeeds_with_no_store_anywhere` and
`a_statement_this_build_does_not_read_is_refused_whole`, run on separate
threads under `cargo test`, which is how CI's `test` job runs them
(`cargo xtask test`, `cargo test --workspace`). When one removes the
directory between the other's `create_dir_all` and its spawn, the spawn
fails, because the working directory is gone.

## Repro

```console
$ for i in $(seq 30); do cargo test -q -p historica-git --test run 2>&1 | grep -q FAILED && echo failed; done | wc -l
5
$ for i in $(seq 30); do cargo test -q -p historica-git --test run -- --test-threads=1 2>&1 | grep -q FAILED && echo failed; done | wc -l
0
```

Measured on hbox (Linux, 8 threads) against `main` at d84a6f0. A failure
reads:

```text
thread 'a_statement_this_build_does_not_read_is_refused_whole' panicked at git/tests/run.rs:20:10:
the binary runs: Os { code: 2, kind: NotFound, message: "No such file or directory" }
```

Either test can be the one that fails. Nothing in historica-git itself is
wrong; it is the test's directory.

## The change

Give each test a directory of its own, as `tests/store.rs`,
`tests/sizes.rs` and the rest of the root crate's tests already do by
joining the test's name onto `CARGO_TARGET_TMPDIR`: `run` takes the test's
name, or the directory, as an argument.

## Done when

`cargo test -p historica-git --test run` passes 30 runs out of 30 with the
default thread count.
