---
title: cargo doc writes the CLI's pages over the library's
part_of: '[Tasks](/docs/tasks/tasks.md)'
status: open
description: The `historica` binary in historica-cli and the `historica` library both document to `target/doc/historica/`, so the Docs job's `cargo doc` mixes the two crates' pages, sometimes losing the library's, and passes
created: 2026-10-28
updated: 2026-10-28
---

# cargo doc writes the CLI's pages over the library's

## Repro

```sh
RUSTDOCFLAGS='-D warnings' cargo doc --workspace --all-features --no-deps   # the Docs job, at 51ef5ed
```

Cargo warns, and the job still passes, because `RUSTDOCFLAGS='-D warnings'`
covers rustdoc's warnings and not Cargo's:

```text
warning: output filename collision at target/doc/historica/index.html
  = note: the bin target `historica` in package `historica-cli` has the same
    output filename as the lib target `historica` in package `historica`
  = note: this is a known bug where multiple crates with the same name use the
    same path; see <https://github.com/rust-lang/cargo/issues/6313>
```

`cli/Cargo.toml` names its binary `historica`, so that the installed command
is `historica`, and rustdoc writes both crates into `target/doc/historica/`.
Which one wins depends on which rustdoc finishes last. Two runs from an empty
`target/doc` on hbox gave two answers:

- once the directory held only the binary's `fn.main.html` and `cli/`, and none
  of the library's modules (`store`, `record`, `merge`, `tree`, …);
- once it held the library's index and modules, with the binary's
  `fn.main.html` and `cli/` left among them.

docs.rs is not affected, since it documents each published crate on its own.
Someone reading the workspace's docs locally, or anything that publishes the
Docs job's output, may see no library.

## Candidates

- **`doc = false` on the `[[bin]]`.** Tried on a copy at 51ef5ed: the
  collision goes, and `target/doc/historica/` is the library's alone. The
  binary's `cli` module is then not documented at all, which loses nothing
  published (it is private to the binary) but does lose it locally.
- **Document the binary under another name**, with its modules moved into a
  library target of historica-cli's that the `historica` binary calls. The
  binary's docs then have a directory of their own.
- **Either way, make the Docs job fail on the warning**, so a second
  collision cannot come back unseen; for example by refusing any
  `output filename collision` in `cargo doc`'s output.

plates has the same collision, filed there as its own task.

## Done when

`cargo doc --workspace --all-features --no-deps` prints no collision warning,
`target/doc/historica/` holds only the library's pages, and the Docs job fails
if a collision comes back.
