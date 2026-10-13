//! `cargo xtask soak` and `cargo xtask fuzz`: the searches, run for longer.
//!
//! Not CI jobs. `tests/strict.rs` and `tests/simulation.rs` already run in
//! `test`, for a second and eight rounds, from a seed `test` rotates — which
//! is what keeps CI looking somewhere new without making it slow. These run
//! the same searches for as long as somebody is willing to wait, which is
//! a judgement about one machine's afternoon rather than about a build, so
//! they live beside the jobs for `bench`'s reason.
//!
//! `soak` needs nothing installed: it is the same two test files in release,
//! told to go on longer. `fuzz` is coverage-guided — libFuzzer, through
//! `cargo-bolero` — and so needs a nightly toolchain and that tool. It runs
//! one strict target, because coverage guidance is a search of one program's
//! branches and splitting it across targets halves it each time.

use crate::{Result, Sh, rotating_seed};

/// The searches `test` runs in a moment, run until told to stop.
///
/// `rounds=<n>` simulated rounds (default 400) and `seconds=<n>` per parser
/// target (default 60). The seed is drawn as `test` draws one, and echoed so
/// a failure can be run again; `HISTORICA_SIMULATION_STRICT=1` in the
/// environment reports the open tasks' signatures as failures too.
pub fn soak(sh: &Sh, arguments: &[&str]) -> Result<()> {
    let mut rounds = String::from("400");
    let mut seconds = String::from("60");
    for argument in arguments {
        match argument.split_once('=') {
            Some(("rounds", value)) if value.parse::<u64>().is_ok() => rounds = value.to_owned(),
            Some(("seconds", value)) if value.parse::<u64>().is_ok() => seconds = value.to_owned(),
            _ => {
                return Err(format!(
                    "`soak` takes `rounds=<n>` and `seconds=<n>`, and `{argument}` is neither"
                ));
            }
        }
    }
    let seed = format!("0x{:016x}", rotating_seed());
    sh.cargo_with(
        &[
            ("HISTORICA_SIMULATION_SEED", seed.as_str()),
            ("HISTORICA_SIMULATION_ROUNDS", rounds.as_str()),
        ],
        &["test", "--release", "--test", "simulation"],
    )?;
    let milliseconds = format!("{}000", seconds);
    // The parser targets in `tests/strict.rs`, and the ones inside the cache
    // modules, which are among the library's own unit tests — the rest of
    // which take no notice of bolero's clock and run as they always do.
    sh.cargo_with(
        &[("BOLERO_RANDOM_TEST_TIME_MS", milliseconds.as_str())],
        &["test", "--release", "--test", "strict", "--lib"],
    )
}

/// One strict target under libFuzzer, for `seconds=<n>` (default 300).
///
/// `cargo xtask fuzz` with no target lists them. What libFuzzer learns, and
/// any crash, lands in `tests/__fuzz__/`, which git ignores: the corpus in
/// `tests/corpus/` is hand-written, and a crash worth keeping becomes a test
/// or a task the way every other finding does. Until it is cleared,
/// `cargo test` replays everything there too.
pub fn fuzz(sh: &Sh, arguments: &[&str]) -> Result<()> {
    let mut target: Option<&str> = None;
    let mut seconds = String::from("300");
    for argument in arguments {
        match argument.split_once('=') {
            Some(("seconds", value)) if value.parse::<u64>().is_ok() => seconds = value.to_owned(),
            None if target.is_none() => target = Some(argument),
            _ => {
                return Err(format!(
                    "`fuzz` takes a target and `seconds=<n>`, and `{argument}` is neither"
                ));
            }
        }
    }
    let Some(target) = target else {
        return sh.cargo(&["test", "--test", "strict", "--", "--list"]);
    };
    // The proxy's `+nightly`, through rustup rather than `$CARGO`, for the
    // reason `msrv` gives: `$CARGO` may be a real toolchain's cargo, which
    // does not understand it.
    sh.run(
        "rustup",
        &[
            "toolchain",
            "install",
            "nightly",
            "--profile",
            "minimal",
            "--no-self-update",
        ],
    )
    .map_err(|e| format!("{e}\n\n`fuzz` needs rustup on PATH to install nightly"))?;
    let time = format!("{seconds}s");
    sh.run(
        "rustup",
        &[
            "run",
            "nightly",
            "cargo",
            "bolero",
            "test",
            target,
            "--package",
            "historica",
            "-T",
            &time,
        ],
    )
    .map_err(|e| {
        format!(
            "{e}\n\n`fuzz` needs cargo-bolero: `cargo install cargo-bolero --no-default-features`"
        )
    })
}
