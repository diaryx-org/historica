//! `revert`: one revision's work, taken back out of the folder.
//!
//! Decision 0090. The library's [`historica::revert::plan`] decides what the
//! folder holds with the revision undone, and [`historica::update::apply`]
//! writes it under the guards an update keeps. What lives here is which head
//! to stand on, which lines to print, and the `record` command that writes
//! the undoing down — printed rather than run, so a person can look at the
//! folder with `status` and `diff` before the history says anything.

use std::io::Write as _;
use std::path::PathBuf;

use historica::core::RevisionId;
use historica::revert::{RevertError, plan};
use historica::update::apply;

use super::{Failure, printing, target};

/// `revert <target> [-n|--dry-run]` — take one revision's work back out of
/// the folder, keeping everything recorded since.
pub fn revert(root: PathBuf, arguments: Vec<String>) -> Result<u8, Failure> {
    let mut spelling: Option<String> = None;
    let mut dry_run = false;
    for argument in arguments {
        match argument.as_str() {
            "-n" | "--dry-run" => dry_run = true,
            other if other.starts_with('-') => {
                return Err(Failure::usage(format!(
                    "`{other}` is not a `revert` option"
                )));
            }
            _ if spelling.is_none() => spelling = Some(argument),
            extra => {
                return Err(Failure::usage(format!(
                    "`revert` takes one target, and `{extra}` is a second"
                )));
            }
        }
    }
    let Some(spelling) = spelling else {
        return Err(Failure::usage(
            "`revert` takes the revision whose work to take back",
        ));
    };

    let mut store = super::cache::open(&root)?;
    let repository = root
        .parent()
        .ok_or_else(|| Failure::error("this store has no repository around it"))?
        .to_path_buf();

    let target = target::resolve(&store, &spelling)?;
    // The undoing is recorded on the head the folder holds, so it is that
    // head or a refusal naming the choice — as `record` would refuse it.
    let found = target::following(&store)?.heads(&store);
    let heads = found.heads;
    let head = match heads.len() {
        0 if found.held.is_empty() => {
            return Err(Failure::error("nothing is recorded here yet"));
        }
        0 => return Err(target::followed_nothing(&store, &found.held)),
        1 => heads.into_iter().next().expect("one head"),
        several => {
            return Err(Failure::error(format!(
                "this store has {several} heads, so there is no one line of work to \
                 undo this on; merge them first:\n{}",
                target::described_with_held(&store, &heads, &found.held)
            )));
        }
    };

    // Decision 0089: the content the three readings need is fetched from the
    // copy first, and without it nothing is written.
    let (parents, message) = {
        let document = store
            .get(&target)
            .map_err(Failure::error)?
            .ok_or_else(|| Failure::error(format!("this store holds no revision {spelling}")))?;
        (
            document
                .parents
                .iter()
                .copied()
                .collect::<Vec<RevisionId>>(),
            document.message.clone(),
        )
    };
    let mut sides = parents;
    sides.push(target);
    sides.push(head);
    super::elsewhere::held_whole(&mut store, &sides, None)?;

    let working = super::cache::working(&repository, &store).map_err(Failure::error)?;
    let reversal = plan(&store, &working, &target, &head).map_err(|error| match error {
        RevertError::NotBehind { .. } => Failure::error(format!(
            "{} is not behind the head the folder holds, so there is none of its \
             work here to take back",
            target::spelled(&store, &target)
        )),
        other => Failure::error(other),
    })?;

    let undoing = target::spelled(&store, &target);
    if reversal.is_settled() {
        return printing(|out| {
            for (path, because) in &reversal.left {
                writeln!(out, "left {path} alone: {because}")?;
            }
            writeln!(
                out,
                "nothing of {undoing} is left to undo: the head already holds what came before it"
            )
        });
    }

    let command = recording(&reversal.paths, &reversal.moves, &message, &target);
    if dry_run {
        return printing(|out| {
            for (fact, path) in &reversal.facts {
                writeln!(out, "{fact:<7} {path}")?;
            }
            for (path, because) in &reversal.left {
                writeln!(out, "left {path} alone: {because}")?;
            }
            writeln!(out, "undoing {undoing} would be recorded with:")?;
            writeln!(out, "  {command}")
        });
    }

    let applied = apply(&store, &working, &repository, &reversal.update).map_err(Failure::error)?;

    printing(|out| {
        for path in &applied.wrote {
            writeln!(out, "{:<7} {path}", "wrote")?;
        }
        for path in &applied.removed {
            writeln!(out, "{:<7} {path}", "removed")?;
        }
        for (path, mode) in &applied.set {
            writeln!(out, "{:<7} {path}  ({mode})", "mode")?;
        }
        for (path, target) in &applied.linked {
            writeln!(out, "{:<7} {path}  ({target})", "linked")?;
        }
        for (path, because) in reversal.left.iter().chain(&applied.left) {
            writeln!(out, "left {path} alone: {because}")?;
        }
        if applied.left.is_empty() && applied.folded.is_empty() {
            writeln!(
                out,
                "the folder holds the head with {undoing} undone; look with \
                 `historica diff`, then record it with:"
            )?;
            writeln!(out, "  {command}")?;
        }
        Ok(())
    })?;

    if !applied.folded.is_empty() {
        return Err(Failure::error(format!(
            "this folder folds paths the tree holds apart, and cannot represent it:{}",
            applied
                .folded
                .iter()
                .map(|path| format!("\n  {path}"))
                .collect::<String>()
        )));
    }
    if !applied.left.is_empty() {
        return Err(Failure::error(
            "the folder changed while undoing; some of it was left alone, above. \
             `historica update` puts the head back, and then revert again",
        ));
    }
    Ok(0)
}

/// The `record` that writes the undoing down.
///
/// Narrowed to the paths the undoing touched, which is decision 0039: a
/// person's unrecorded work elsewhere in the folder is not compared with
/// anything, so it is not swept into a revision that says it undid something
/// else. Every rename put back is stated, since the folder cannot show one,
/// and the message names what was undone by its own first line and its digest,
/// so `log` reads as what happened and `show` finds the revision undone.
fn recording(
    paths: &[String],
    moves: &[(String, String)],
    message: &str,
    target: &RevisionId,
) -> String {
    let mut command = String::from("historica record");
    for path in paths {
        command.push(' ');
        command.push_str(&quoted(path));
    }
    for (from, to) in moves {
        command.push_str(" --move ");
        command.push_str(&quoted(&format!("{from}={to}")));
    }
    let summary = message.lines().next().unwrap_or_default().trim();
    command.push_str(" -m ");
    command.push_str(&quoted(&format!(
        "Undo \"{summary}\" ({})",
        target.abbreviate(12)
    )));
    command
}

/// One argument, spelled so a POSIX shell hands it back unchanged.
fn quoted(argument: &str) -> String {
    let plain = !argument.is_empty()
        && argument
            .chars()
            .all(|c| c.is_ascii_alphanumeric() || "-_./=:@+,".contains(c));
    if plain {
        argument.to_owned()
    } else {
        format!("'{}'", argument.replace('\'', r"'\''"))
    }
}
