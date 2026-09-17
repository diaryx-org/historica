---
title: Tasks
description: Deferred work in historica — one file each, every one with a done state
created: 2026-09-02
updated: 2026-09-16
contents:
  - "[The first capture is barrier-bound](first-capture-is-barrier-bound.md)"
  - "[A claim arriving needs no line](a-claim-arriving-needs-no-line.md)"
  - "[Saying what a command wrote](saying-what-a-command-wrote.md)"
  - "[The state at a revision without the walk](the-state-at-a-revision-without-the-walk.md)"
  - "[A capture pushes per file and barriers once](a-capture-pushes-per-file-and-barriers-once.md)"
part_of: '[historica](/README.md)'
---

# Tasks

Work this project has committed to and has not done yet, one document each. A
bug is a task with a repro; anything else is a task with a done state written
down, so that finishing it is a fact rather than an opinion.

`contents` above lists every task, open and closed: the index is the spine,
and what is open is a view of it (`dx tasks`). Closing a task is an edit, not
a delete: its `status` becomes `done` or `dropped`, it names the commit or
release that resolved it, and it keeps its place above while the file stays
where it is, findable by grep.

What does not belong here:

- **What shipped** is documented in [the CLI guide](../cli.md), the
  [decisions](../decisions), and the [changelog](../CHANGELOG.md) — never in a
  task.
- **A commitment to consumers** is the changelog's unreleased region or a
  `Behavioural-change:` trailer, not a task file.
- **An argument for a change** that might lose is a proposal, and would live in
  `docs/proposals/`. This repository has none yet.

`status` takes `open`, `in-progress`, `done`, or `dropped`, and nothing else,
so that a tool can read it across every repository in the org.
