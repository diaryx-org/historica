# 0068 — The package a caller pays for

0025 put the filesystem seam at the library's edge, and said what the front end
was:

> **The CLI is `std::fs` throughout**, deliberately. `src/cli/` and
> `src/main.rs` call it directly

0057 put the transport one seam further out and said the same thing about it:

> `src/cli/fetch.rs` is the binary's half and the only `#[cfg(feature =
> "http")]` outside the manifest

Both are true of the code and neither was true of the package. `disk` and
`http` were features of the one crate named `historica`, both on by default,
and default features are chosen by whoever depends on you. So a library
consumer who wrote `historica = "1.0"` and nothing else compiled nyquest and
linked WinRT, NSURLSession or libcurl — a platform HTTP stack, its TLS root
store and its proxy configuration — in order to build `src/cli/fetch.rs`, a
file they had no way to call, in a binary they were not installing.

The escape was one line, `default-features = false`, and it was there the whole
time. historica-sign found it. historica-git did not. That is the argument:
a seam a caller has to know about is not a seam, it is a footgun with a
comment above it.

## Why now and not later

Because default features are semver. Adding one is a minor release; removing
one, or removing a feature a caller may have named, is a major. A 1.0 that
ships `default = ["disk", "http"]` has promised both to everyone who depends on
it, and the correction stops being an edit and becomes a 2.0.

1.0 is also the last moment it is nearly free. The front end already talked to
the library the way an outside crate does — every file under `src/cli/` reads
`use historica::…` and not one reads `crate::`, which was 0025's discipline
followed further than it had to be. Moving it was `git mv` and a manifest.

## The decision

**Two packages, one repository.**

- **`historica`** is the library. One feature, `disk`, on by default, which is
  0025's `std::fs` implementation of `Filesystem` — genuinely library code, and
  what every short constructor resolves to. `http` does not exist here.
- **`historica-cli`** is the front end: `src/cli/`, `src/main.rs`, the eight
  test files that run the binary, and nyquest. Its feature `http` is 0057's
  transport, default-on. It depends on `historica` with `default-features =
  false, features = ["disk"]`, spelled out rather than inherited, so that a
  change to the library's defaults is a compile error here rather than a silent
  swap of the filesystem the program runs on.
- **The program is still called `historica`.** `[[bin]] name = "historica"` in
  a package called `historica-cli` is ordinary, and the name a person types has
  nothing to do with which package on crates.io holds it.

`disk` stays a library feature and stays default. It is one dependency,
`fs-transaction`, it is the implementation a caller almost always wants, and
0025's whole point is that the *library* can be built without it — moving it
out would be answering a different question than the one this decision asks.

## What it costs, and it is a real cost

`cargo install historica` stops installing anything. It is the line in the
README, it is in 0057, and it is what 0.1.0 and 0.2.0 taught anyone who tried
them. The replacement is `cargo install historica-cli`, cargo's message for the
old spelling says the package has no binaries, and nothing points from one to
the other.

Accepted, for the reason above: the cost is a sentence someone reads once, and
the thing it buys is a promise 1.0 cannot revise. A crates.io description and
the README are where the sentence goes.

## Consequences

- `cargo install historica-cli`, in `README.md` and in `cli/README.md`, which
  is the page crates.io renders for the new package.
- `categories` splits: `command-line-utilities` belonged to the binary and goes
  with it; the library keeps `development-tools` and `filesystem`.
- The `wasi` job builds `--package historica-cli --no-default-features` instead
  of the root package with `--features disk`. It is the same promise — a whole
  CLI with no transport compiled into it — asked of the package that now has
  the transport.
- `Sh::library_sources` stops filtering `src/cli/` and `src/main.rs` back out of
  `src/`, because `src/` is the library now. The `bare` job's grep gets
  stricter for free.
- The front end depends on the library by version as well as by path, and that
  literal `"1.0"` is a number `cargo xtask bump` does not rewrite. Inside 1.x it
  cannot go wrong, since `"1.0"` is a caret requirement. At the next major it
  can, and quietly — the front end would publish against a library a major
  behind the one beside it, and crates.io would serve exactly that. The
  `historica_requirement_tracks_the_workspace` test compares the majors, which
  costs nothing and fails on the one commit that can introduce it.
- Three tests reached `tests/corpus` and `tests/by-hand.sh` through
  `CARGO_MANIFEST_DIR`, which now names `cli/`. They reach one directory up.
  The corpus itself does not move: it is the library's, and the library's own
  tests read it.
- `jiff` and `similar` are declared in both manifests, at the same
  requirements, so cargo unifies them. The front end's uses are its own —
  parsing the moment a person types at `--since`, and the word-level
  decomposition inside a changed line that 0037 calls rendering.

## Rejected alternatives

**Leave the defaults alone and document `default-features = false`.** This is
what the situation already was, and historica-git is the evidence for how well
documentation works against a default. It also spends the 1.0 on the wrong
promise: the manifest would be saying `http` is part of what depending on
historica means, forever, when no line of the library reads it.

**Drop `http` from the defaults and keep one package.** `cargo install
historica` survives and library callers stop paying, which is most of the win
for none of the churn. What it leaves is a headline install command that
produces a binary whose `fetch` is missing — refusing by name, so 0021 is
satisfied, but a person who followed the README and hit that refusal has been
told nothing except that they installed the wrong thing. The reduced build
should be the one somebody asks for, not the one they get.

**Move `disk` out too.** `Disk` is an implementation of a library trait, used
by library code, wanted by library callers. It is not a front-end concern that
leaked; it is the answer 0025 gave.

## Deferred

**A `historica` package that installs the CLI.** Cargo has no way for one
package to hand `cargo install` off to another, and a stub binary that printed
"install historica-cli" would be a program that lies about what it is. If the
old spelling proves to be the thing everyone types, the answer is documentation
and the crates.io description, not code.

**Whether the front end should be published at all.** It is, because
`cargo install` is how a person tries this. But `historica-cli` on crates.io is
a second version number to move and a second set of release notes to mean
something, and 1.0 does not yet know whether anyone wants the CLI as a
dependency. Nothing here decides that; the packages simply share
`[workspace.package] version` and move together.
