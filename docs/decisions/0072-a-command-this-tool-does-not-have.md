# 0072 — A command this tool does not have

0053 settled what a side tool *is*: an ordinary crate depending on `historica`
at a semver range from crates.io, optionally owning one directory at the store
root whose travel class historica knows without reading a byte inside it. Two
tools exist on that footing — historica-git, which calls the published API, and
historica-minisign, which needs nothing from it at all — and neither wants
anything the decision did not give it.

What is left over is smaller than the thing 0053 refused, and 0053 refused it
anyway, in one bullet:

> **Subprocess dispatch is not a plugin mechanism here.** 0025 exists because
> the folder may be an iCloud document provider or an Android content URI,
> reached by an application that is not a shell and has no `PATH`. A mechanism
> built on spawning a process works on a desktop and nowhere else, which would
> make every embedding host a second-class one and quietly relocate this
> format's centre of gravity to the command line it was deliberately not built
> around.

Every word of that is right about a *plugin mechanism* — an arrangement in
which spawning a process is how a tool gets its capability, so that a host
which cannot spawn is a host which cannot extend. It says nothing about how a
person spells a command they already have installed. `historica git import` and
`historica-git import` run the same program with the same arguments, and an
embedding host with no command line is not the poorer for which of the two
somebody typed.

The distinction is the whole of this decision. Capability comes from the API,
which is where 0053 put it and where it stays. Spelling comes from `PATH`,
which the embedding host was never using.

## Why not a registry

The obvious prior art is nushell's `plugin add`, which authorises a binary and
files it in a registry the shell reads at startup. It is a good design for
nushell and a bad one here, and the reason is that nu needs something historica
does not: nu parses whole scripts before running them and is typed, so it must
know a plugin's command signatures at parse time. The registry is a signature
cache, and that is what earns the file, the protocol, and the `add` step.

Historica hands the remaining arguments to the other program verbatim and
learns nothing from it. There is no parse-time knowledge to cache, so a
registry here would be the costs of nu's design with none of its reason.

Two of those costs are worth naming, because they are the ones that would have
been paid quietly.

**It would be the first thing that changes what a command means.** 0011 keeps
nothing between commands, and the one configuration file this project has —
0010's identity, under the platform's configuration directory — states a fact
about a person that a revision would otherwise have to guess. A registry is a
different kind of file: two machines holding the same store would answer
differently to the same command line, and the difference would live somewhere
neither the store nor the arguments can show you.

**"Authorise" would be a promise this tool cannot keep.** A registry holds a
name or a path, and the binary behind either can be replaced afterwards by
anything that can write to it. Pinning a digest instead buys a real check and a
re-authorisation every time a tool legitimately upgrades, which is a workflow
nobody asked for. Nushell does not claim `plugin add` is a security boundary.
Neither should this, and the way not to claim it is not to build the thing that
looks like one. What actually guards the fall-through is the alphabet below: a
word from `argv` may name a program on `PATH` and may never name a position on
disk.

## Why not features of the command line

The other way to stop typing two words is to fold the tools into
`historica-cli` behind cargo features, and it is the more tempting one, because
it looks like it removes weight rather than adding a mechanism.

It does not, in either shape it can take.

**As optional dependencies on the published crates**, the boundary survives —
they would still be separate packages consumed by version — and the release
path acquires a three-stage lockstep. `historica-cli` 1.1 would need
historica-git published against `historica` 1.1, which needs `historica` 1.1
published first. That is the condition CLAUDE.md already records for
`fs-transaction`, arriving in the release path, which is the part of this
project that is already the most careful. Three repositories, three CI setups
and three release cuts would all remain.

**In-tree behind features**, two xtasks and two release cuts genuinely go away,
and what pays for them is 0053's guarantee. historica-git today *cannot* reach
a `pub(crate)`; its `Cargo.lock` resolves `historica` to
`registry+https://github.com/rust-lang/crates.io-index` with a checksum, so the
published surface is the only surface it has. 0053 promises that "a fact the
API does not expose is a change to historica, not a hole opened elsewhere", and
in-tree that promise stops being a compiler error and becomes a habit.

The second cost is worse and less obvious: those two tools are the only
evidence the plugin story works. One is written against the API and one needs
nothing from it, which is exactly the span 0053 claims is servable from
outside. Absorbed into this workspace, they stop being evidence of anything,
and the next person wanting a side tool has no worked example that the boundary
holds.

The duplication that prompted the idea is real and is somewhere else: the two
side repositories' xtasks are about four hundred lines each and differ by forty.
That is duplicated *tooling*, it is `dx`'s problem rather than this format's,
and fixing it there costs nothing argued here.

## The decision

- **A word the command table does not have is looked for on `PATH` as
  `historica-<word>`, and run with the remaining arguments as given.** Nothing
  is inserted, removed, or re-ordered. `historica git import a b` is
  `historica-git import a b`.

- **The word must be ASCII letters, digits, and interior hyphens, and anything
  else is simply not a command.** This is a positive rule rather than a
  blocklist because the word arrives straight from `argv`. `Command::new`
  resolves a name holding a separator as a *path*, without consulting `PATH` at
  all, so `historica ../thing` would otherwise be a way to run a file by
  position. A word outside the alphabet gets the same message as a word nobody
  installed, because from here they are the same fact.

- **`-C` becomes the child's working directory.** The side tool is handed the
  folder rather than told about a flag it has never heard of, and this is what
  `git -C` does too.

- **The child's exit code is this process's, and nothing on `PATH` is the
  ordinary "there is no `<word>` command" at exit 2.** A script wrapping
  `historica git` sees what wrapping `historica-git` would have shown it, and a
  typo still reads as a typo rather than as a failed spawn.

- **Nothing is registered, authorised, cached, or remembered.** No
  configuration file, no manifest, no protocol, no `add` step, no state of any
  kind. The whole mechanism is `PATH` and a naming convention, both of which a
  person can already read.

- **The tool's own name stays primary.** A side tool must work when invoked as
  `historica-git`, and nothing in it may depend on having been reached through
  here — it is given no argument saying so, and it is not told this happened.
  That is what keeps this a spelling: remove the fall-through and every tool
  still works, which is how they worked before it existed.

- **A built-in command wins, and a later one shadows a program silently.** The
  table is consulted first, so the day historica gains a `<word>` of its own,
  an installed `historica-<word>` stops being reachable that way. Git has this
  and it is the price of the convention; the mitigation available is saying so
  rather than pretending otherwise, and the tool's own name is the escape.

- **Behind a feature, on by default, off in the flag `http` is off in.** A wasi
  guest has no `PATH` and no process to spawn, and 0057's promise — that
  turning the default features off leaves a whole CLI rather than a broken one
  — has to keep holding. What turning it off costs is a spelling and no
  capability: the tools are reached by their own names, which is where they
  started.

- **0053 is unchanged, and this grants no capability.** A side tool still gets
  what it can do from the published Rust API, and what it may write in a store
  from 0053's reservation and its travel class. Nothing here lets a program do
  anything it could not do when a person ran it themselves.

- **`help` states the rule and does not list what is installed.** A listing
  would go stale between the printing and the typing, would be a second answer
  that can disagree with the first, and would make `help` the one command that
  reads the machine rather than the store.

## What this leaves open

**Discovery, which is the half this does not solve.** A person who has not
heard of historica-minisign will not hear of it from `historica help`, which
says the rule rather than the roster. If that turns out to be the real gap, the
answer is a command that lists what `PATH` holds — a question somebody asks —
rather than a registry, which is a state somebody maintains.

**Windows.** `Command::new` appends `.exe` there, so the convention should
carry, and nothing here has been run on it: CI is ubuntu and the test is
`cfg(unix)`. It is a promise about a naming convention rather than about a
platform, and the day somebody runs it on Windows is the day it is a promise
about that too.

**A child killed by a signal** is reported as killed rather than reproduced,
because this process cannot exit by a signal it did not receive. `exec` would
make the question not arise — the child would *be* the process — and it is
unix-only, so it would be a second code path for a case that only matters to a
caller inspecting `WTERMSIG`. One path was worth more than the fidelity.

## Rejected alternatives

**`historica plugin add`, a registry of authorised binaries.** Above, at
length: nu's design solving nu's parse-time problem, which this does not have;
the first state that changes what a command means; and an "authorise" that
names a file whose contents can change underneath it.

**Folding the side tools into `historica-cli` behind features.** Above: as
published dependencies it adds a release lockstep and removes no repository; in
tree it removes two xtasks and spends the compiler-enforced boundary that is
what 0053's promise is made of, along with the only external evidence that the
promise is keepable.

**`exec` rather than spawn and wait.** Correct on unix, absent on Windows, and
buying signal fidelity for a caller nobody has. See above.

**Listing installed tools in `help`.** A second answer, stale by construction,
and the one place this program would consult the machine rather than the store.

**Reserving the unclaimed subcommand namespace, or a prefix inside it.** 0053
gives a store directory out one at a time, when a tool exists that wants one,
because a reservation is a thing somebody argues for. A subcommand is cheaper
than a directory — it travels nowhere, it survives in nobody's copy, and a
collision costs a person one longer name — so it does not need the ceremony,
and giving names out in advance would be ceremony for something that has never
gone wrong.

**A protocol, so the tool could describe itself.** That is the registry with
extra steps: something has to ask, something has to remember the answer, and
the answer can be a lie. Everything a person needs is the tool's own `--help`,
which they can reach by the tool's own name.
