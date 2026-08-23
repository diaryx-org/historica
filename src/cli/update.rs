//! `update`: the folder catches up to a head.
//!
//! Decision 0030. The library's [`historica::update`] pair decides everything;
//! what lives here is which lines to print, in which order, and the
//! `--dry-run` flag that chooses between planning and doing.

use std::io::Write as _;
use std::path::PathBuf;

use historica::store::Store;
use historica::update::{UpdateError, apply, plan};
use historica::working::Working;

use super::{Failure, printing, target};

/// `update [<target>] [-n|--dry-run]` — make the folder hold a head.
pub fn update(root: PathBuf, arguments: Vec<String>) -> Result<u8, Failure> {
    let mut spelling: Option<String> = None;
    let mut dry_run = false;
    for argument in arguments {
        match argument.as_str() {
            "-n" | "--dry-run" => dry_run = true,
            other if other.starts_with('-') => {
                return Err(Failure::usage(format!(
                    "`{other}` is not an `update` option"
                )));
            }
            _ if spelling.is_none() => spelling = Some(argument),
            extra => {
                return Err(Failure::usage(format!(
                    "`update` takes one target, and `{extra}` is a second"
                )));
            }
        }
    }

    let store = Store::open(&root)?;
    let repository = root
        .parent()
        .ok_or_else(|| Failure::error("this store has no repository around it"))?
        .to_path_buf();

    let target = match &spelling {
        Some(spelling) => target::resolve(&store, spelling)?,
        None => {
            let heads = target::current_heads(&store);
            match heads.len() {
                0 => return Err(Failure::error("nothing is recorded here yet")),
                1 => heads.into_iter().next().expect("one head"),
                several => {
                    return Err(Failure::error(format!(
                        "this store has {several} heads, so nothing here is `the` latest; \
                         name the one the folder should hold:{}",
                        target::listed(heads.iter().map(|head| target::spelled(&store, head)))
                    )));
                }
            }
        }
    };

    let working = Working::read(&repository, store.skipped()).map_err(Failure::error)?;

    let update = plan(&store, &working, &repository, &target).map_err(|error| match error {
        UpdateError::NotAHead { target, heads } => Failure::error(format!(
            "{} is not a head, and the folder only ever holds one; \
             reading the past is `show` and `cat`, and going back is `abandon`. the heads:{}",
            target::spelled(&store, &target),
            target::listed(heads.iter().map(|head| target::spelled(&store, head)))
        )),
        other => Failure::error(other),
    })?;

    if dry_run {
        return printing(|out| {
            for write in &update.writes {
                writeln!(out, "{:<7} {}", "write", write.path)?;
            }
            for remove in &update.removes {
                writeln!(out, "{:<7} {}", "remove", remove.path)?;
            }
            for (path, because) in &update.leaves {
                writeln!(out, "left {path} alone: {because}")?;
            }
            if update.is_settled() {
                writeln!(
                    out,
                    "the folder already holds {}",
                    target::spelled(&store, &target)
                )?;
            }
            Ok(())
        });
    }

    if update.is_settled() {
        return printing(|out| {
            for (path, because) in &update.leaves {
                writeln!(out, "left {path} alone: {because}")?;
            }
            writeln!(
                out,
                "the folder already holds {}",
                target::spelled(&store, &target)
            )
        });
    }

    let applied = apply(&working, &repository, &update).map_err(Failure::error)?;

    let code = printing(|out| {
        for path in &applied.wrote {
            writeln!(out, "{:<7} {}", "wrote", path)?;
        }
        for path in &applied.removed {
            writeln!(out, "{:<7} {}", "removed", path)?;
        }
        for (path, because) in update.leaves.iter().chain(&applied.left) {
            writeln!(out, "left {path} alone: {because}")?;
        }
        if applied.folded.is_empty() && applied.left.is_empty() {
            writeln!(out, "the folder holds {}", target::spelled(&store, &target))?;
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
            "the folder changed while updating; some of it was left alone, above. \
             update again when it is still",
        ));
    }
    Ok(code)
}
