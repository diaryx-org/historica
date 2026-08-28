//! historica's CI, as one program.
//!
//! Every job the CI workflow runs is one entry in [`JOBS`] and one
//! `cargo xtask <id>` invocation. The workflow itself holds no build knowledge:
//! it asks `cargo xtask ci-matrix` what the jobs are, then runs each one by id.
//! Adding, renaming, reordering, or retiring a job is an edit to this file and
//! nothing else — the YAML does not change.
//!
//! Locally, `cargo xtask ci` runs the same jobs in the same order against the
//! same commands, so a green run here is a green run there.
//!
//! Cutting a release does not live here. It is `dx <command>`, the shared
//! tooling configured by `.config/release.toml` — the same tool
//! prov, twig, leaf, flower, and the other historica repos all cut releases
//! with, because five copies of one program is five places for it to drift.
//!
//! There are no dependencies on purpose. Every CI job builds this crate before
//! it can start, so its build time is paid several times over per push.

mod bench;

use std::env;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode};

/// Anything that goes wrong here is a message for whoever is reading the log;
/// there is nothing for a CI runner to recover from.
type Result<T> = std::result::Result<T, String>;

/// One CI job: what to call it, what the runner must install for it, and the
/// work itself.
struct Job {
    /// `cargo xtask <id>`, and the key the workflow dispatches on.
    id: &'static str,
    /// The name GitHub shows in the checks list. Renaming it renames the
    /// required status check, so branch protection has to be updated to match.
    name: &'static str,
    /// rustup components the job needs, comma-joined for
    /// `dtolnay/rust-toolchain`. Empty means the default toolchain is enough.
    components: &'static str,
    /// Does this job *compile* the crate? If so, restoring the cargo cache is
    /// worth its cost. `fmt` is the one job that only ever parses.
    builds: bool,
    /// One line of explanation, printed by `cargo xtask` with no arguments.
    about: &'static str,
    run: fn(&Sh) -> Result<()>,
}

/// The whole of CI, in the order `cargo xtask ci` runs it: cheapest and most
/// likely to fail first.
const JOBS: &[Job] = &[
    Job {
        id: "fmt",
        name: "Format",
        components: "rustfmt",
        builds: false,
        about: "rustfmt, in check mode",
        run: fmt,
    },
    Job {
        id: "clippy",
        name: "Clippy",
        components: "clippy",
        builds: true,
        about: "clippy over every target, warnings denied",
        run: clippy,
    },
    Job {
        id: "doc",
        name: "Doc",
        components: "",
        builds: true,
        about: "rustdoc over every feature, warnings denied",
        run: doc,
    },
    Job {
        id: "test",
        name: "Test",
        components: "",
        builds: true,
        about: "the workspace test suite",
        run: test,
    },
    Job {
        id: "bare",
        name: "Bare",
        components: "clippy",
        builds: true,
        about: "the library without `disk`, which must not reach std::fs",
        run: bare,
    },
    Job {
        id: "wasi",
        name: "Wasi",
        components: "",
        builds: true,
        about: "build the whole CLI for wasi, where no HTTP stack exists",
        run: wasi,
    },
    Job {
        id: "msrv",
        name: "MSRV",
        components: "",
        builds: true,
        about: "build on the minimum supported Rust version",
        run: msrv,
    },
];

// ---------------------------------------------------------------------------
// The jobs
// ---------------------------------------------------------------------------

fn fmt(sh: &Sh) -> Result<()> {
    sh.cargo(&["fmt", "--all", "--check"])
}

/// Warnings are errors in CI, so they are errors here too — a lint that only
/// fires on the runner is a lint found too late.
fn clippy(sh: &Sh) -> Result<()> {
    sh.cargo(&[
        "clippy",
        "--workspace",
        "--all-targets",
        "--",
        "-D",
        "warnings",
    ])
}

/// rustdoc, held to the same standard as the compiler.
///
/// `documentation` in `Cargo.toml` points at docs.rs, so the pages rustdoc
/// generates here are the ones a person deciding whether to use historica
/// reads. Nothing else in CI looks at them: a `[`Thing`]` naming an item that
/// was renamed last week still compiles, still passes clippy, and renders as
/// plain text on the page — which is how five of them accumulated before 1.0.
///
/// `-D warnings` is what turns that into a failure, and it catches the three
/// kinds worth catching: a link to an item that no longer exists, a link from
/// public documentation into a private item nobody following it can reach, and
/// a `[label](target)` whose two halves say the same thing.
///
/// `--all-features` because a feature-gated item is documented only in a build
/// that has it, and `--no-deps` because a dependency's documentation is its
/// author's problem.
fn doc(sh: &Sh) -> Result<()> {
    sh.cargo_with(
        &[("RUSTDOCFLAGS", "-D warnings")],
        &["doc", "--workspace", "--all-features", "--no-deps"],
    )
}

/// The workspace test suite, with the conformance suite pointed somewhere new.
///
/// `tests/conformance.rs` searches randomly from a seed, and its default is a
/// constant: a hundred and fifty cases that are the same hundred and fifty
/// every time, which stop being a search the day they first pass. CI hands it
/// a fresh one, so every run looks somewhere it has not looked before.
///
/// The seed is echoed with the command that used it — a rotated search is only
/// worth running if a red run can be made red again, and `Sh::run` prints the
/// environment alongside the command so the log reads as something to paste
/// back. The suite prints it again in any failure, for the same reason.
fn test(sh: &Sh) -> Result<()> {
    let seed = format!("0x{:016x}", rotating_seed());
    sh.cargo_with(
        &[("HISTORICA_CONFORMANCE_SEED", seed.as_str())],
        &["test", "--workspace"],
    )
}

/// A seed nobody chose.
///
/// The clock, which is all this needs: the point is to look somewhere other
/// than last run, not to be unguessable. Mixed rather than used raw so that
/// two runs a moment apart do not search two nearly identical places.
fn rotating_seed() -> u64 {
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
/// A build rather than a test run, for `msrv`'s reason: there is no wasi
/// runtime here to run one in, and what is being promised is that it compiles.
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

/// Build on the crate's declared minimum supported Rust version. A build, not a
/// test run: MSRV is a promise about who can *compile* historica, and the
/// dev-dependencies and test tooling need not hold to it.
///
/// The version is read from `workspace.package.rust-version`, so the pin can
/// never drift from the declared floor — bump it in Cargo.toml and this follows.
fn msrv(sh: &Sh) -> Result<()> {
    let version = sh.workspace_rust_version()?;
    println!("MSRV from Cargo.toml: {version}");
    // Idempotent: rustup reports an already-installed toolchain and returns 0.
    sh.run(
        "rustup",
        &[
            "toolchain",
            "install",
            &version,
            "--profile",
            "minimal",
            "--no-self-update",
        ],
    )
    .map_err(|e| format!("{e}\n\nthe MSRV job needs rustup on PATH to pin Rust {version}"))?;
    // `rustup run`, not `cargo +{version}`: the `+toolchain` shorthand is a
    // rustup-proxy feature, and $CARGO may well point past the proxy at a real
    // toolchain binary that does not understand it.
    sh.run(
        "rustup",
        &["run", &version, "cargo", "build", "--workspace"],
    )
}

// ---------------------------------------------------------------------------
// Driving them
// ---------------------------------------------------------------------------

fn main() -> ExitCode {
    let args: Vec<String> = env::args().skip(1).collect();
    let sh = Sh::new();

    let outcome = match args.iter().map(String::as_str).collect::<Vec<_>>()[..] {
        [] | ["-h" | "--help" | "help"] => {
            print!("{}", usage());
            return ExitCode::SUCCESS;
        }
        ["bench", ref rest @ ..] => bench::bench(&sh, rest),
        ["ci"] => ci(&sh),
        ["ci-matrix"] => {
            println!("{}", ci_matrix());
            Ok(())
        }
        // These moved to the shared tool rather than being retired, and a
        // muscle-memory `cargo xtask release` should say where they went.
        [
            command @ ("version" | "bump" | "changelog" | "release" | "release-notes"),
            ..,
        ] => Err(format!(
            "releasing moved out of xtask: `cargo xtask {command}` is now \
                 `dx {command}`,\nthe shared tooling this repo configures in \
                 .config/release.toml.\n\n{}",
            usage()
        )),
        [id] => match JOBS.iter().find(|job| job.id == id) {
            Some(job) => (job.run)(&sh),
            None => Err(format!("unknown job `{id}`\n\n{}", usage())),
        },
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

/// Every job, in order — what CI does, on one machine. Stops at the first
/// failure, on the theory that a red build is worth reading before the next one
/// buries it.
fn ci(sh: &Sh) -> Result<()> {
    for job in JOBS {
        println!("\n\x1b[1m━━ {} ━━\x1b[0m", job.name);
        (job.run)(sh)?;
    }
    println!("\n\x1b[32mall {} jobs passed\x1b[0m", JOBS.len());
    Ok(())
}

/// The job table as a single line of JSON, for the workflow's `strategy.matrix`.
///
/// Hand-rolled rather than serde-derived: the crate has no dependencies, and
/// every value here is a `&'static str` literal from [`JOBS`] with nothing in it
/// that JSON would need escaped. A job name with a quote or a backslash in it
/// would produce invalid JSON, and `cargo xtask ci-matrix` in the test below is
/// what would notice.
fn ci_matrix() -> String {
    let entries: Vec<String> = JOBS
        .iter()
        .map(|job| {
            format!(
                r#"{{"id":"{}","name":"{}","components":"{}","builds":{}}}"#,
                job.id, job.name, job.components, job.builds
            )
        })
        .collect();
    format!("[{}]", entries.join(","))
}

fn usage() -> String {
    let mut out = String::from(
        "historica's CI, and its releases. Each job below is exactly what the CI \
         workflow runs.\n\n\
         usage: cargo xtask <command>\n\njobs:\n\n",
    );
    for job in JOBS {
        out.push_str(&format!("  {:<20}{}\n", job.id, job.about));
    }
    out.push_str(&format!("  {:<20}{}\n", "ci", "every job above, in order"));
    out.push_str(&format!(
        "  {:<20}{}\n",
        "ci-matrix", "the job table as JSON, for the workflow matrix"
    ));
    // Measuring is not CI either: see `bench` for why a timing must not fail
    // a build.
    out.push_str(&format!(
        "  {:<20}{}\n",
        "bench [<shape>]", "time the reading commands on a store built to order"
    ));
    // Releasing is not CI and is not here: it is one shared tool across the
    // org, so that the changelog contract has one implementation rather than
    // five that agree until they don't.
    out.push_str("\nreleasing:  dx <command>   (the shared tooling; see .config/release.toml)\n");
    out
}

// ---------------------------------------------------------------------------
// The workspace
// ---------------------------------------------------------------------------
//
// This came across from `release.rs` when releasing moved to the shared tooling.
// Its only remaining caller is a CI test: `cli/` asking for a version of
// `historica` that is not the one beside it would publish a front end against
// the wrong library, and nothing else catches that.

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

    /// `workspace.package.rust-version`, the single source of truth for the MSRV.
    fn workspace_rust_version(&self) -> Result<String> {
        let manifest = self.root.join("Cargo.toml");
        let text = std::fs::read_to_string(&manifest)
            .map_err(|e| format!("could not read {}: {e}", manifest.display()))?;
        text.lines()
            .find_map(|line| {
                let line = line.trim();
                // `rust-version.workspace = true` in `[package]` is the
                // inheriting side of this value, not the value itself.
                let rest = line.strip_prefix("rust-version")?;
                rest.split('"').nth(1)
            })
            .map(str::to_owned)
            .ok_or_else(|| format!("no `rust-version` in {}", manifest.display()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The workflow's `fromJSON` is the only thing that parses `ci-matrix`, and
    /// it fails at a point where the fix costs a push. Check the shape here
    /// instead: one object per job, every field present, nothing needing an
    /// escape.
    #[test]
    fn ci_matrix_is_well_formed_json() {
        let json = ci_matrix();
        assert!(json.starts_with('[') && json.ends_with(']'));
        assert_eq!(json.matches("\"id\":").count(), JOBS.len());
        assert_eq!(json.lines().count(), 1, "the workflow reads it as one line");

        for job in JOBS {
            for field in [job.id, job.name, job.components] {
                assert!(
                    !field.contains(['"', '\\']),
                    "`{field}` would need JSON escaping, which ci_matrix does not do",
                );
            }
            assert!(json.contains(&format!("\"id\":\"{}\"", job.id)));
        }
    }

    /// `ci` and `ci-matrix` are handled before the table is consulted, so a job
    /// by either name would be unreachable.
    #[test]
    fn job_ids_are_distinct_and_dispatchable() {
        let mut ids: Vec<&str> = JOBS.iter().map(|job| job.id).collect();
        let count = ids.len();
        ids.sort_unstable();
        ids.dedup();
        assert_eq!(ids.len(), count, "duplicate job id");
        assert!(!ids.contains(&"ci") && !ids.contains(&"ci-matrix"));
    }

    /// `dx bump` rewrites one line — `[workspace.package] version` —
    /// and every member inherits it. One requirement does not inherit: the
    /// front end depends on the library by version as well as by path, because
    /// that is what publishing needs, and a literal in `cli/Cargo.toml` is a
    /// number only `set_requirement` rewrites.
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

        let ours = sh
            .read("cli/Cargo.toml")
            .unwrap()
            .lines()
            .find_map(|line| Some(requirement(line)?.to_owned()))
            .expect("a `historica = { version = \"…\" }` requirement in cli/Cargo.toml");

        assert_eq!(
            ours, theirs,
            "cli/Cargo.toml asks for historica {ours} while the workspace is {theirs} — \
             the front end would publish against a library that is not the one beside it",
        );
    }

    /// The MSRV job reads this; if the parse breaks, the job silently pins the
    /// wrong compiler or fails far from the cause. `[package]` inherits the
    /// value with `rust-version.workspace = true`, which is a line the parse has
    /// to walk past rather than read.
    #[test]
    fn msrv_is_readable_from_the_manifest() {
        let version = Sh::new().workspace_rust_version().unwrap();
        assert!(
            version.split('.').all(|part| part.parse::<u32>().is_ok()),
            "`{version}` does not look like a Rust version",
        );
    }
}
