//! A command this tool does not have.
//!
//! Decision 0072: when the match in [`super::run`] falls through, the word a
//! person typed may still be a command — one belonging to a program beside
//! this one, named `historica-<word>` and found on `PATH`. Dispatching to it
//! is a spelling and nothing else: `historica git import` runs the same
//! program `historica-git import` runs, with the same arguments, and every
//! answer it gives is its own.
//!
//! What this is not is decision 0053's plugin mechanism, which is unchanged: a
//! side tool is an ordinary crate against the published API, and nothing here
//! lets it do anything it could not do when invoked by its own name. Nothing
//! is registered, nothing is authorised, nothing is remembered, and no
//! protocol is spoken. That is why this can exist at all — 0053 refuses
//! subprocess dispatch as a *plugin* mechanism, because an embedding host that
//! has no `PATH` would be second-class in it, and a host that has no command
//! line loses nothing by a command line's spelling.

use std::path::Path;
use std::process::Command;

use super::Failure;

/// The prefix a side tool's program carries. `historica-git` holds `git`.
const PREFIX: &str = "historica-";

/// Whether a word may be looked for on `PATH` at all.
///
/// A command name reaches this function straight from `argv`, so the rule has
/// to be a positive one. `Command::new` resolves a name holding a separator as
/// a *path* rather than through `PATH`, which would make `historica ../thing` a
/// way to run a file by position — so the alphabet is ASCII letters, digits,
/// and interior hyphens, and everything else is a command this tool does not
/// have rather than a program to go looking for.
fn dispatchable(command: &str) -> bool {
    !command.is_empty()
        && !command.starts_with('-')
        && !command.ends_with('-')
        && command
            .chars()
            .all(|c| c.is_ascii_alphanumeric() || c == '-')
}

/// Run `historica-<command>` if `PATH` has one, reporting the ordinary "no such
/// command" if it does not.
///
/// `base` becomes the child's working directory, which is what makes `-C` mean
/// the same thing on this side of the boundary as on the other: the side tool
/// is given the folder rather than told about a flag it has never heard of.
pub fn dispatch(command: &str, base: &Path, rest: Vec<String>) -> Result<u8, Failure> {
    let missing = || Failure::usage(format!("there is no `{command}` command"));
    if !dispatchable(command) {
        return Err(missing());
    }

    let program = format!("{PREFIX}{command}");
    let status = match Command::new(&program)
        .args(&rest)
        .current_dir(base)
        .status()
    {
        Ok(status) => status,
        // The one error worth telling apart: nothing on `PATH` answers to that
        // name, which is the plain typo and deserves the plain message.
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => return Err(missing()),
        Err(error) => return Err(Failure::error(format!("{program}: {error}"))),
    };

    match status.code() {
        // A child's code is this process's code, so that a script wrapping
        // `historica git` sees what wrapping `historica-git` would have shown
        // it. Anything a `u8` cannot hold is not a code a shell can report.
        Some(code) => Ok(u8::try_from(code).unwrap_or(1)),
        None => Err(Failure::error(format!("{program} was killed"))),
    }
}
