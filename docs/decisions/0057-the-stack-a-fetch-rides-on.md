# 0057 — The stack a fetch rides on

0048 put the transport behind one method and stopped there:

> **The transport is the binary's, through a one-method source.** The library
> takes something that answers `get(path) -> bytes` and does the whole of the
> algorithm; the binary brings the TLS, the redirects and the proxy settings.

The seam is right and it names no implementation. `historica fetch` has to be
some particular program making some particular request, and which one is a
choice with consequences for every person who installs this: what certificate
roots a fetch trusts, who ships the fix when that stack has a hole in it, and
what a build for a target with no such stack at all is supposed to do.

Three candidates, and the first is the one to say no to out loud.

## Rejected: exec `curl`

Tempting, and 0048 all but invited it — "it keeps `curl` an honest
implementation of the trait". It is honest as an *implementation*; it is
dishonest as a *dependency*. What `historica fetch` would then trust is
whichever file called `curl` is first on `PATH`, chosen by an environment
variable, at the moment of the request, with the arguments we pass and whatever
`~/.curlrc` says. That is a program deciding, at run time, to hand a URL and
the shape of its store to something it has not identified and cannot verify —
and the one thing a fetch must get right is who it is talking to.

It is also the wrong shape twice over. `curl` is not on every machine this
runs on, and a missing one is discovered at the moment somebody is trying to
fetch rather than at the moment they installed. And decision 0034 already had
to be careful about what historica will and will not execute; spawning a
process named by the environment is not a place to relax that.

The narrower version — a vendored HTTP client in pure Rust, with a bundled root
store — is honest and costs a second copy of everything the operating system
already maintains: a TLS implementation, a certificate bundle that goes stale
between our releases, and the dependency tree of both. It is the ordinary
answer and it is not free.

## The decision

- **The binary links the platform's own HTTP stack, through
  [`nyquest`](https://github.com/bdbai/nyquest) and `nyquest-preset`.** WinRT on
  Windows, NSURLSession on Apple platforms, libcurl elsewhere — one interface,
  and underneath it the stack the machine already has. So a fetch rides the
  system's TLS roots, its proxy configuration, and its security update cadence,
  and none of those three is a thing this repository has to ship, refresh, or
  be late with. The blocking API, because the CLI is synchronous from `main`
  down and an executor would be the largest dependency in the tree by a wide
  margin.

- **The versions are pinned exactly.** `=0.4.0` for both, which is unusual here
  and deliberate: nyquest is early and says its API is subject to change, so a
  patch release is a thing to read before taking rather than to receive. Moving
  it is somebody typing a version number.

- **It is behind a feature called `http`, and `http` is in `default`.** So
  `cargo install historica` fetches out of the box and nobody has to know the
  feature exists, while `--no-default-features --features disk` builds every
  other command with no transport compiled in. `src/cli/fetch.rs` is the whole
  of what the feature adds, and the `fetch` line of the usage text is `#[cfg]`ed
  with it, because a usage text that named a command this binary does not have
  would be the one line in it that is not true.

- **The reason for the gate is a target, not a preference: wasi.** There is no
  WinRT, NSURLSession or libcurl under `wasm32-wasip1` or `wasip2`, and there is
  no sensible fallback to reach for either — a wasi guest gets its network from
  its host or not at all. So a build for wasi turns `http` off and the host
  brings its own transport through the library's `Source` trait, which is
  exactly what 0048 built that trait for and exactly what 0025 did for the
  filesystem one seam in. Both preview versions build the whole CLI today, and
  `cargo xtask wasi` is what keeps that true — the `bare` job's argument, made
  about the binary instead of the library.

- **Typing `fetch` in a build without it is answered, not fallen through.**
  "There is no `fetch` command" would be true of the binary and false of
  historica. The refusal says the transport is absent, points at the trait, and
  names what still works without one: `export`, an archive, and `receive`.

- **A declined `reserved` line is an observation.** 0056 deferred this by name —
  "whether that should be said out loud" — and the answer is 0006's split, which
  parts an error from an observation by whether anything is wrong. Nothing is:
  the publisher's historica reserves a directory this one has never heard of, or
  reserves it under a class that does not cross, and 0053 fixed the default at
  leave it behind precisely so that this is survivable. But silence is worse
  than either, because the recipient is the only party who could install the
  tool that would read those files, and nobody goes looking for what was never
  mentioned. So `fetch` prints one line per directory — how many files, and
  which directory — and takes everything else.

## What the transport does not decide

Two settings on the client are consequences of decisions already made, and are
worth stating because they look like tuning and are not.

**Caching is off.** 0048 answers a moved path by reading the manifest *again*,
and a transparent cache that served the same manifest twice would turn the one
recoverable failure into the one unrecoverable one. Everything else a fetch asks
for is named by the digest of its own bytes and asked for once, so there was
nothing for a cache to save.

**Cookies are off.** 0048 deferred authentication and everything that follows
from it; the premise is a public directory of files, and a fetch of one should
say nothing about who is asking.

**Paths are escaped and never rewritten.** 0016 lets a person file their history
under any name they like, and 0043's trailing-path convention exists because a
path may hold a space. So every byte of a manifest's path that is not
unreserved is percent-encoded and `/` alone survives, because it is the one
character in a path that is structure rather than content.

## Consequences

- `src/store/fetch.rs` is the library: the `Source` trait, the difference
  against this store's own contents, the ordered requests, the verification, and
  the bounded retry. It compiles with no features at all, and every test of it
  is against a directory on disk.
- `src/cli/fetch.rs` is the binary's half and the only `#[cfg(feature =
  "http")]` in the tree beside the usage line and the dispatch arm.
- `historica`'s default features now pull a native dependency: `objc2` and
  friends on Apple, `curl` on Linux, `windows` on Windows. A packager who does
  not want them builds `--no-default-features --features disk` and loses one
  command.
- `cargo xtask wasi` joins the job table, so the promise about wasi is checked
  on every push rather than remembered.
- The `Source` error is prose rather than a type. Nothing in the library reads
  it — the one distinction a fetch reasons about is absence, and absence is in
  the return type as `Ok(None)` — so what is left is a sentence for whoever
  typed the command, and inventing a vocabulary for it would make every
  implementation translate in and every caller translate back out for no
  decision either of them makes. This is where the seam differs from
  `Filesystem`, which trades in `std::io::Error` because it genuinely branches
  on two of its kinds.

## Deferred

1. **Authentication.** 0048 deferred it and nothing here changes that. A private
   host, credentials, or a fetch that is refused is a transport question, and
   the trait is where it would be answered — by a host that has an answer,
   rather than by a flag on this command.
2. **Anything but `GET`.** No conditional requests, no ranges, no
   `If-None-Match` on the manifest. A conditional manifest would be the one
   place a fetch could save a round trip, and it needs a story about what a
   cache did that the retry can survive; the current answer, one unconditional
   uncached read, is correct and costs one small file per pull.
3. **A second implementation shipped in the library.** A `Source` over a local
   directory is six lines, every test here writes one, and putting it in the
   library would make it `disk`-gated for the benefit of callers who have
   `std::fs` and can write it themselves.
