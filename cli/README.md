# historica-cli

The command line for [historica](https://crates.io/crates/historica), an
experiment in readable, convergent version control.

```console
cargo install historica-cli
```

The program it installs is called `historica`. What it does, and why, is in
[the repository's README](https://github.com/diaryx-org/historica#readme) and
in [`docs/cli.md`](https://github.com/diaryx-org/historica/blob/main/docs/cli.md);
this package is only the front end. Every answer a command prints is one the
library can be asked for directly — decision 0053 makes that the rule rather
than a coincidence — so a tool built on historica depends on the
[`historica`](https://docs.rs/historica) crate and not on this one.

## Features

`http` is on by default and is decision 0057's transport: the platform's own
HTTP stack — WinRT on Windows, NSURLSession on Apple, libcurl elsewhere —
which is what `historica fetch` rides on. Turn it off

```console
cargo install historica-cli --no-default-features
```

and every other command is unchanged; `fetch` refuses by name, and a store
still travels by `export`, an archive, and `receive`. That build is what the
`wasi` CI job holds open, for a host that brings its own transport through the
library's `Source` trait.

## Licence

MIT or Apache-2.0, at your option.
