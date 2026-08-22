//! `arrange`, as a person reads it.
//!
//! The arranging itself is [`historica::store`]'s — decision 0025's first open
//! question, answered: readability is the offering, so the command that makes
//! a folder readable belongs where a host can call it too. What is left here
//! is the report, which is a front end's whole job.
//!
//! `--dry-run` asks for the plan and prints it. Without it the plan is carried
//! out and what is printed is what happened, which is the same pairing `prune`
//! has.

use std::io::{self, Write as _};
use std::path::Path;

use historica::store::{Arrangement, Filed, Store, Tally};

use super::Failure;

/// Rename every document to its arranged name.
pub fn arrange(root: &Path, dry_run: bool) -> Result<u8, Failure> {
    // Opening first means a store that does not parse is refused before
    // anything is renamed, and refused in the parser's own words.
    let mut store = Store::open(root)?;
    let done = if dry_run {
        store.arrangement()
    } else {
        store.arrange()
    }
    .map_err(Failure::error)?;

    // What this says is a running commentary on what has been done; a reader
    // who walks away must not stop a rename half-done, so write errors are
    // ignored here rather than raised.
    let mut out = io::stdout().lock();
    for filed in [Filed::Revision, Filed::Operation] {
        report(&mut out, root, &done, filed, dry_run);
    }
    Ok(0)
}

/// One directory's worth of the report.
fn report(
    out: &mut io::StdoutLock<'static>,
    root: &Path,
    done: &Arrangement,
    filed: Filed,
    dry_run: bool,
) {
    let directory = filed.directory();
    let kind = match filed {
        Filed::Revision => "revision",
        Filed::Operation => "document",
    };

    for rename in done.renames.iter().filter(|rename| rename.filed == filed) {
        let _ = writeln!(
            out,
            "{} {}  ->  {}",
            if dry_run { "would rename" } else { "renamed" },
            shown(&rename.from, directory),
            shown(&rename.to, directory)
        );
    }
    for left in done.occupied.iter().filter(|left| left.filed == filed) {
        let _ = writeln!(
            out,
            "left {}: {} already holds this {kind}",
            shown(&left.path, directory),
            shown(&left.holder, directory)
        );
    }
    // The whole path, as it always has been: a person running this from
    // somewhere else in the repository is told which folder was tidied.
    let within = root.join(directory);
    let _ = writeln!(out, "{}", line(done.tally(filed), &within, dry_run));
}

/// The line printed after a directory is done.
fn line(tally: Tally, directory: &Path, dry_run: bool) -> String {
    let mut line = format!(
        "{}: {} {}, {} already arranged",
        directory.display(),
        tally.renamed,
        if dry_run { "to rename" } else { "renamed" },
        tally.already
    );
    if tally.occupied > 0 {
        line.push_str(&format!(", {} left as duplicates", tally.occupied));
    }
    if tally.unnamed > 0 {
        line.push_str(&format!(", {} named by no revision", tally.unnamed));
    }
    line
}

/// A store path as the directory being arranged sees it.
///
/// Relative to that directory, not just the filename: nesting means two
/// documents can share a name and differ by the directory, and a commentary
/// that printed only the name would report the same rename twice.
fn shown(path: &Path, directory: &str) -> String {
    path.strip_prefix(directory)
        .unwrap_or(path)
        .to_string_lossy()
        .into_owned()
}
