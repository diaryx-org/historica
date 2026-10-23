//! historica's tasks: the ones too big to be a command.
//!
//! CI itself is the `job` list in `.config/ship.figl`, run by `ship ci` here
//! and on the runners. A job that is a plain command is written there; one
//! that is real logic — `test`, `bare`, `wasi`, `proofs` — is a task here, and
//! its job runs `cargo xtask <task>`. Adding, renaming or reordering a job is
//! an edit to that file; changing what one of these four does is an edit here.
//!
//! Cutting a release does not live here. It is `ship`, configured by the same
//! `.config/ship.figl`.
//!
//! There are no dependencies on purpose. Four CI jobs build this crate before
//! they can start, so its build time is paid several times over per push.

mod bench;
mod proofs;
mod search;

use std::env;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode};

/// Anything that goes wrong here is a message for whoever is reading the log;
/// there is nothing for a CI runner to recover from.
type Result<T> = std::result::Result<T, String>;

// ---------------------------------------------------------------------------
// The CI tasks
// ---------------------------------------------------------------------------

/// The workspace test suite, with every seeded search pointed somewhere new.
///
/// `tests/conformance.rs` and `tests/simulation.rs` search randomly from a
/// seed, and each one's default is a constant: the same rounds every time,
/// which stop being a search the day they first pass. CI hands them a fresh
/// one, so every run looks somewhere it has not looked before. One seed for
/// both, since each draws its rounds from its own stream.
///
/// The seed is echoed with the command that used it — a rotated search is only
/// worth running if a red run can be made red again, and `Sh::run` prints the
/// environment alongside the command so the log reads as something to paste
/// back. The suites print it again in any failure, for the same reason.
/// `tests/strict.rs` needs no seed handed to it: bolero draws a fresh one per
/// run and prints it in a failure.
fn test(sh: &Sh) -> Result<()> {
    let seed = format!("0x{:016x}", rotating_seed());
    sh.cargo_with(
        &[
            ("HISTORICA_CONFORMANCE_SEED", seed.as_str()),
            ("HISTORICA_SIMULATION_SEED", seed.as_str()),
        ],
        &["test", "--workspace"],
    )
}

/// A seed nobody chose.
///
/// The clock, which is all this needs: the point is to look somewhere other
/// than last run, not to be unguessable. Mixed rather than used raw so that
/// two runs a moment apart do not search two nearly identical places.
pub(crate) fn rotating_seed() -> u64 {
    let now = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map_or(0, |since| since.as_nanos() as u64);
    let mut seed = now ^ 0x9e37_79b9_7f4a_7c15;
    seed ^= seed >> 30;
    seed = seed.wrapping_mul(0xbf58_476d_1ce4_e5b9);
    seed ^= seed >> 27;
    seed = seed.wrapping_mul(0x94d0_49bb_1331_11eb);
    seed ^ (seed >> 31)
}

/// Build the library with `disk` off, and grep for what must not be there.
///
/// Decision 0025 says the library reaches the folder through
/// `historica::fs::Filesystem` and never through `std::fs`. A default-features
/// build cannot tell: `std::fs` compiles everywhere the CLI does, so a call
/// that slipped back into `store` would pass every other job here.
///
/// The compile is the real check — with `disk` off there is no `Disk` and no
/// `std::fs` in the library at all — and the grep is what turns a slip into a
/// message that says which line, rather than an error about a missing feature.
fn bare(sh: &Sh) -> Result<()> {
    sh.cargo(&[
        "clippy",
        "--lib",
        "--no-default-features",
        "--",
        "-D",
        "warnings",
    ])?;

    let mut offending = Vec::new();
    for file in sh.library_sources()? {
        // `src/fs.rs` is the one place `std::fs` belongs, behind `disk`.
        if file.ends_with("/src/fs.rs") {
            continue;
        }
        let text = std::fs::read_to_string(&file).map_err(|error| format!("{file}: {error}"))?;
        for (at, line) in text.lines().enumerate() {
            // A comment naming `std::fs` is a comment explaining why this file
            // does not call it, which is the opposite of the fault.
            let code = line.trim();
            if code.starts_with("//") {
                continue;
            }
            if code.contains("std::fs") {
                offending.push(format!("  {file}:{}: {code}", at + 1));
            }
        }
    }
    if !offending.is_empty() {
        return Err(format!(
            "the library reaches `std::fs` directly, which decision 0025 says it \
             must not — go through `historica::fs::Filesystem`:\n{}",
            offending.join("\n")
        ));
    }
    println!("the library builds without `disk` and names `std::fs` nowhere");
    Ok(())
}

/// Every target that has no HTTP stack under it, built without the one that
/// assumes there is.
///
/// Decision 0057 puts the transport behind `http`, a feature of the
/// `historica-cli` package and on by default there, and the promise that comes
/// with it is that turning it off leaves a whole CLI rather than a broken one.
/// `bare` holds the *library* to compiling where `std::fs` does not work; this
/// holds the *binary* to compiling where a socket does not exist — a wasi
/// guest, whose host brings its own transport through the library's `Source`
/// trait.
///
/// A build rather than a test run: there is no wasi runtime here to run one
/// in, and what is being promised is that it compiles.
/// Both preview versions, because the promise was made about both and they are
/// separate targets with separate standard libraries.
fn wasi(sh: &Sh) -> Result<()> {
    for target in ["wasm32-wasip1", "wasm32-wasip2"] {
        // Idempotent: rustup reports an already-installed target and returns 0.
        sh.run("rustup", &["target", "add", target])
            .map_err(|e| format!("{e}\n\nthe wasi job needs rustup on PATH to install {target}"))?;
        sh.cargo(&[
            "build",
            "--package",
            "historica-cli",
            "--target",
            target,
            "--no-default-features",
        ])?;
    }
    println!("the whole CLI builds for wasi with no transport compiled into it");
    Ok(())
}

// ---------------------------------------------------------------------------
// Driving the tasks
// ---------------------------------------------------------------------------

fn main() -> ExitCode {
    // Called by cargo as the compiler wrapper the `proofs` job sets up, not by
    // a person — and before `env::args`, which would refuse a path cargo
    // passed that is not UTF-8.
    if let Some(verus) = env::var_os(proofs::WRAPPER) {
        return proofs::wrap(verus);
    }

    let args: Vec<String> = env::args().skip(1).collect();
    let sh = Sh::new();

    let outcome = match args.iter().map(String::as_str).collect::<Vec<_>>()[..] {
        [] | ["-h" | "--help" | "help"] => {
            print!("{}", usage());
            return ExitCode::SUCCESS;
        }
        ["bench", ref rest @ ..] => bench::bench(&sh, rest),
        ["soak", ref rest @ ..] => search::soak(&sh, rest),
        ["fuzz", ref rest @ ..] => search::fuzz(&sh, rest),
        ["test"] => test(&sh),
        ["bare"] => bare(&sh),
        ["wasi"] => wasi(&sh),
        ["proofs"] => proofs::proofs(&sh),
        // These moved to ship rather than being retired, and a muscle-memory
        // `cargo xtask ci` or `cargo xtask release` should say where they went.
        [
            command @ ("ci" | "ci-matrix" | "fmt" | "clippy" | "doc" | "msrv"),
            ..,
        ] => Err(format!(
            "CI moved out of xtask: `cargo xtask {command}` is now a job in \
             .config/ship.figl.\n`ship ci` runs every job, `ship ci <id>` one, and \
             `ship ci --list` names them.\n\n{}",
            usage()
        )),
        [
            command @ ("version" | "bump" | "changelog" | "release" | "release-notes"
            | "github-release"),
            ..,
        ] => {
            let moved = match command {
                "release" => "ship <patch|minor|major|x.y.z>",
                "release-notes" => "ship notes",
                "github-release" => "ship github",
                "version" => "ship version",
                "bump" => "ship bump",
                _ => "ship changelog",
            };
            Err(format!(
                "releasing moved out of xtask: `cargo xtask {command}` is now \
                 `{moved}`,\nconfigured in .config/ship.figl.\n\n{}",
                usage()
            ))
        }
        [id] => Err(format!("unknown task `{id}`\n\n{}", usage())),
        [id, ..] => Err(format!("`{id}` takes no arguments\n\n{}", usage())),
    };

    match outcome {
        Ok(()) => ExitCode::SUCCESS,
        Err(message) => {
            eprintln!("\nxtask: {message}");
            ExitCode::FAILURE
        }
    }
}

fn usage() -> String {
    let mut out = String::from(
        "historica's tasks.\n\n\
         usage: cargo xtask <task>\n\nCI jobs that are programs (`ship ci <id>` runs the job):\n\n",
    );
    for (task, about) in [
        (
            "test",
            "the workspace test suite, every seeded search given a fresh seed",
        ),
        (
            "bare",
            "the library without `disk`, which must not reach std::fs",
        ),
        (
            "wasi",
            "build the whole CLI for wasi, where no HTTP stack exists",
        ),
        (
            "proofs",
            "Verus over the library, fetching the pinned release once",
        ),
    ] {
        out.push_str(&format!("  {task:<20}{about}\n"));
    }
    out.push_str("\nnot CI:\n\n");
    // Measuring is not CI: see `bench` for why a timing must not fail a build.
    out.push_str(&format!(
        "  {:<20}{}\n",
        "bench [<shape>]", "time the reading commands on a store built to order"
    ));
    // Nor is searching for longer than a build should take.
    out.push_str(&format!(
        "  {:<20}{}\n",
        "soak [rounds=<n>]", "the simulation and the parser targets, run for longer"
    ));
    out.push_str(&format!(
        "  {:<20}{}\n",
        "fuzz [<target>]", "one parser target under libFuzzer (nightly, cargo-bolero)"
    ));
    out.push_str(
        "\nCI:         ship ci [<job>]   (the jobs are in .config/ship.figl)\n\
         releasing:  ship <command>    (see `ship help`)\n",
    );
    out
}

// ---------------------------------------------------------------------------
// The workspace
// ---------------------------------------------------------------------------
//
// This came across from `release.rs` when releasing left xtask. Its only
// remaining caller is a CI test: a member asking for a version of
// `historica` that is not the one beside it would publish against the wrong
// library, and nothing else catches that.

#[cfg(test)]
/// The version `historica = { version = "…", … }` asks for, from the line that
/// asks for it — and `None` from every other line. Shared with the test in
/// `main.rs` that checks the committed manifests agree.
fn requirement(line: &str) -> Option<&str> {
    line.trim_start()
        .strip_prefix("historica = {")?
        .split("version = \"")
        .nth(1)?
        .split('"')
        .next()
}

// ---------------------------------------------------------------------------
// Running things
// ---------------------------------------------------------------------------

/// A shell rooted at the workspace, so a job never has to think about where it
/// was invoked from.
struct Sh {
    root: PathBuf,
    /// Cargo tells its subprocesses which cargo it is; prefer that over
    /// whichever one happens to be first on PATH.
    cargo: String,
}

impl Sh {
    fn new() -> Self {
        let root = Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .expect("xtask/ always has a parent")
            .to_path_buf();
        let cargo = env::var("CARGO").unwrap_or_else(|_| "cargo".into());
        Sh { root, cargo }
    }

    fn cargo(&self, args: &[&str]) -> Result<()> {
        let cargo = self.cargo.clone();
        self.run(&cargo, args)
    }

    /// The same, with environment the job wants the command to see.
    fn cargo_with(&self, environment: &[(&str, &str)], args: &[&str]) -> Result<()> {
        let cargo = self.cargo.clone();
        self.run_with(environment, &cargo, args)
    }

    /// Run a command at the workspace root, echoing it first so a CI log reads
    /// as a transcript of commands anyone can paste back.
    fn run(&self, program: &str, args: &[&str]) -> Result<()> {
        self.run_with(&[], program, args)
    }

    /// The same, with environment — echoed in front of the command, since a
    /// transcript that leaves out what the command was told is not one.
    fn run_with(&self, environment: &[(&str, &str)], program: &str, args: &[&str]) -> Result<()> {
        let shown = if program == self.cargo {
            "cargo"
        } else {
            program
        };
        let prefix: String = environment
            .iter()
            .map(|(name, value)| format!("{name}={value} "))
            .collect();
        println!("\x1b[2m$ {prefix}{} {}\x1b[0m", shown, args.join(" "));

        let status = Command::new(program)
            .args(args)
            .envs(environment.iter().copied())
            .current_dir(&self.root)
            .status()
            .map_err(|e| format!("could not run `{shown}`: {e}"))?;

        if status.success() {
            Ok(())
        } else {
            Err(format!(
                "`{prefix}{shown} {}` failed ({status})",
                args.join(" ")
            ))
        }
    }

    /// Read a workspace file, by its path from the root. Test-only since
    /// releasing moved out: the tests read the manifests, and no job touches a
    /// file directly.
    #[cfg(test)]
    fn read(&self, path: &str) -> Result<String> {
        let path = self.root.join(path);
        std::fs::read_to_string(&path)
            .map_err(|e| format!("could not read {}: {e}", path.display()))
    }

    /// Every `.rs` file of the library, which is every `.rs` file under `src/`.
    ///
    /// It was not always: the command-line front end lived at `src/cli/` and
    /// `src/main.rs` and had to be filtered back out, because a CLI is
    /// `std::fs` on purpose. It is the `historica-cli` package now, so the
    /// directory this walks holds nothing the `bare` job should excuse.
    fn library_sources(&self) -> Result<Vec<String>> {
        fn walk(directory: &Path, into: &mut Vec<String>) -> Result<()> {
            let entries = std::fs::read_dir(directory)
                .map_err(|e| format!("could not read {}: {e}", directory.display()))?;
            for entry in entries {
                let path = entry
                    .map_err(|e| format!("could not read {}: {e}", directory.display()))?
                    .path();
                if path.is_dir() {
                    walk(&path, into)?;
                } else if path.extension().is_some_and(|e| e == "rs") {
                    into.push(path.to_string_lossy().replace('\\', "/"));
                }
            }
            Ok(())
        }
        let mut found = Vec::new();
        walk(&self.root.join("src"), &mut found)?;
        found.sort();
        Ok(found)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// `ship bump` rewrites one line — `[workspace.package] version` —
    /// and every member inherits it. The requirements do not inherit: the
    /// front end and the crates built on the library (`git`, `minisign`,
    /// `remark`) depend on it by version as well as by path, because that is
    /// what publishing needs, and each is a literal in its own manifest.
    ///
    /// The two are compared in full rather than by major, which is what this
    /// once did. By major it cannot catch the case that actually bites: a
    /// pre-release. `"1.0"` is a caret requirement, a caret requirement does not
    /// match `1.0.0-rc.1`, and the majors agree the whole time — so `cargo
    /// publish -p historica-cli` would go asking crates.io for a `1.0.x` that
    /// the pre-release deliberately is not. Comparing the whole string costs
    /// nothing and fails on the commit that introduces the drift rather than at
    /// the publish.
    #[test]
    fn historica_requirement_tracks_the_workspace() {
        let sh = Sh::new();

        let theirs = sh
            .read("Cargo.toml")
            .unwrap()
            .lines()
            .find_map(|line| {
                Some(
                    line.strip_prefix("version = \"")?
                        .split('"')
                        .next()?
                        .to_owned(),
                )
            })
            .expect("`version` in [workspace.package]");

        for manifest in [
            "cli/Cargo.toml",
            "git/Cargo.toml",
            "minisign/Cargo.toml",
            "remark/Cargo.toml",
        ] {
            let ours = sh
                .read(manifest)
                .unwrap()
                .lines()
                .find_map(|line| Some(requirement(line)?.to_owned()))
                .unwrap_or_else(|| {
                    panic!("a `historica = {{ version = \"…\" }}` requirement in {manifest}")
                });

            assert_eq!(
                ours, theirs,
                "{manifest} asks for historica {ours} while the workspace is {theirs} — \
                 the crate would publish against a library that is not the one beside it",
            );
        }
    }
}
