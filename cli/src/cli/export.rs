//! `export`: the copy a person takes away.
//!
//! Decision 0042. The library builds the directory; what lives here is which
//! lines to print, which target the default is, and the `--dry-run` flag that
//! chooses between planning and doing — decision 0006's division, and the
//! shape `receive` already has on the other side of the same journey.
//!
//! `--files-only` is the same command with the store left out: the folder
//! the target has, laid out at `<dir>` and nothing beneath it. What it is
//! for is looking at a revision rather than working on one, and what it
//! costs is the ancestry — the three-hundredth revision of a
//! six-hundred-revision store exports 14 MB, of which 13 is `history/`.

use std::io::Write as _;
use std::path::{Path, PathBuf};

use historica::fs::Disk;
use historica::store::{STORE_DIR, Store};

use super::{Failure, printing, target};

/// `export <dir> [<target>] [--files-only] [-n|--dry-run]` — a copy at `<dir>`.
pub fn export(base: &Path, root: PathBuf, arguments: Vec<String>) -> Result<u8, Failure> {
    let mut dry_run = false;
    let mut files_only = false;
    let mut rest: Vec<String> = Vec::new();
    for argument in arguments {
        match argument.as_str() {
            "-n" | "--dry-run" => dry_run = true,
            "--files-only" => files_only = true,
            other if other.starts_with('-') => {
                return Err(Failure::usage(format!(
                    "`{other}` is not an argument `export` takes"
                )));
            }
            other => rest.push(other.to_owned()),
        }
    }

    let mut rest = rest.into_iter();
    let directory = rest
        .next()
        .ok_or_else(|| Failure::usage("`export` wants a directory to write the copy into"))?;
    let spelling = rest.next();
    if let Some(extra) = rest.next() {
        return Err(Failure::usage(format!(
            "`export` takes a directory and one target, and `{extra}` is a third argument"
        )));
    }

    let store = Store::open(&root)?;
    // Decision 0042: the default is the head, and divergence refuses with the
    // heads described — which is what `head` already means everywhere else a
    // target is typed, so this is that answer rather than a second one.
    let target = target::resolve(&store, spelling.as_deref().unwrap_or("head"))?;
    let into = base.join(&directory);

    if files_only {
        return folder_only(&store, &into, &target, dry_run);
    }

    if dry_run {
        let plan = store
            .export_plan_onto(&Disk, &into, &target)
            .map_err(Failure::error)?;
        // Decision 0052: the counts are what this run writes, which is the
        // whole set for a fresh copy and the difference for one being updated
        // — the same numbers the real thing reports, from the same plan.
        let writes = plan.writes();
        return printing(|out| {
            writeln!(out, "would export {} revisions", writes.revisions)?;
            writeln!(out, "would export {} operation documents", writes.documents)?;
            writeln!(out, "would export {} payloads", writes.payloads)?;
            if writes.forgetting != 0 {
                writeln!(
                    out,
                    "would export {} forgetting documents",
                    writes.forgetting
                )?;
            }
            // Decision 0051 puts both counts on the same footing as the
            // rest: a copy that quietly dropped rules is what it fixes, so
            // the withheld count is printed even where it is the only one.
            if !plan.rules().is_empty() || plan.withheld() != 0 {
                writeln!(out, "would export {} rules", plan.rules().len())?;
            }
            if plan.withheld() != 0 {
                writeln!(out, "would hold back {} private rules", plan.withheld())?;
            }
            // Decision 0062, on the same footing and for the same reason, and
            // in three lines rather than two: a name held back because
            // somebody asked and a name held back because the copy does not
            // reach it are different facts, and only the first is a decision.
            if !plan.names().is_empty() || plan.withheld_names() != 0 {
                writeln!(out, "would export {} bookmarks", plan.names().len())?;
            }
            if plan.withheld_names() != 0 {
                writeln!(
                    out,
                    "would hold back {} private bookmarks",
                    plan.withheld_names()
                )?;
            }
            if plan.beyond_names() != 0 {
                writeln!(
                    out,
                    "would leave {} bookmarks pointing past this target",
                    plan.beyond_names()
                )?;
            }
            // Decision 0053: said as what it is — files historica does not
            // read, carried because the directory they sit in says they
            // travel — since naming the tool is exactly what transport does
            // not do.
            if !plan.reserved().is_empty() {
                writeln!(
                    out,
                    "would carry {} files another tool wrote",
                    plan.reserved().len()
                )?;
            }
            // Decision 0052: withdrawal is the point rather than a tidy-up, so
            // it is said file by file, where `prune` and `forget` say what
            // they destroy. The paths are the copy's, not this store's.
            for file in plan.withdraws() {
                writeln!(out, "would withdraw {STORE_DIR}/{}", file.display())?;
            }
            if !plan.destroys().is_empty() {
                writeln!(
                    out,
                    "would destroy {} forgotten originals",
                    plan.destroys().len()
                )?;
            }
            for path in plan.paths() {
                writeln!(out, "{:<7} {path}", "write")?;
            }
            writeln!(
                out,
                "would {} of {} at {}",
                match plan.updating() {
                    true => "update the copy",
                    false => "make a copy",
                },
                target::spelled(&store, &target),
                into.display()
            )
        });
    }

    let exported = store
        .export_onto(Disk, &into, &target)
        .map_err(Failure::error)?;
    let where_it_is = exported
        .root
        .canonicalize()
        .unwrap_or_else(|_| exported.root.clone());

    printing(|out| {
        writeln!(out, "exported {} revisions", exported.revisions)?;
        writeln!(out, "exported {} operation documents", exported.documents)?;
        writeln!(out, "exported {} payloads", exported.payloads)?;
        if exported.forgetting != 0 {
            writeln!(out, "exported {} forgetting documents", exported.forgetting)?;
        }
        if exported.rules != 0 || exported.withheld != 0 {
            writeln!(out, "exported {} rules", exported.rules)?;
        }
        if exported.withheld != 0 {
            writeln!(out, "held back {} private rules", exported.withheld)?;
        }
        if exported.names != 0 || exported.withheld_names != 0 {
            writeln!(out, "exported {} bookmarks", exported.names)?;
        }
        if exported.withheld_names != 0 {
            writeln!(
                out,
                "held back {} private bookmarks",
                exported.withheld_names
            )?;
        }
        if exported.beyond_names != 0 {
            writeln!(
                out,
                "left {} bookmarks pointing past this target",
                exported.beyond_names
            )?;
        }
        if exported.reserved != 0 {
            writeln!(
                out,
                "carried {} files another tool wrote",
                exported.reserved
            )?;
        }
        // Decision 0052: what left the copy, said as plainly as what arrived.
        // `--dry-run` names the files; this says how many, because the lines
        // under it are already a list of files.
        if exported.withdrawn != 0 {
            writeln!(out, "withdrew {} files", exported.withdrawn)?;
        }
        if exported.destroyed != 0 {
            writeln!(out, "destroyed {} forgotten originals", exported.destroyed)?;
        }
        for path in &exported.files {
            writeln!(out, "{:<7} {path}", "wrote")?;
        }
        writeln!(
            out,
            "{} of {} at {}",
            match exported.updated {
                true => "updated the copy",
                false => "made a copy",
            },
            target::spelled(&store, &target),
            where_it_is.display()
        )
    })
}

/// `export <dir> [<target>] --files-only` — the folder, and nothing under it.
///
/// The printing is `update`'s rather than `export`'s, because what this writes
/// is what `update` writes: a folder, file by file, with the links and the
/// modes said out loud for decisions 0040 and 0034's reason. What it is not is
/// said on the last line, since a directory that looks like a repository and
/// is not one is the one thing a person could take away from this wrongly.
fn folder_only(
    store: &Store,
    into: &Path,
    target: &historica::core::RevisionId,
    dry_run: bool,
) -> Result<u8, Failure> {
    if dry_run {
        let update = store
            .export_files_plan_onto(Disk, into, target)
            .map_err(Failure::error)?;
        return printing(|out| {
            for write in &update.writes {
                writeln!(out, "{:<7} {}", "write", write.path)?;
            }
            for chmod in &update.modes {
                writeln!(out, "{:<7} {}  ({})", "mode", chmod.path, chmod.mode)?;
            }
            for link in &update.links {
                writeln!(out, "{:<7} {}  ({})", "link", link.path, link.target)?;
            }
            writeln!(
                out,
                "would write the folder {} has at {}, and no history beside it",
                target::spelled(store, target),
                into.display()
            )
        });
    }

    let wrote = store
        .export_files_onto(Disk, into, target)
        .map_err(Failure::error)?;
    let where_it_is = wrote
        .root
        .canonicalize()
        .unwrap_or_else(|_| wrote.root.clone());

    let code = printing(|out| {
        for path in &wrote.files {
            writeln!(out, "{:<7} {path}", "wrote")?;
        }
        for (path, mode) in &wrote.modes {
            writeln!(out, "{:<7} {path}  ({mode})", "mode")?;
        }
        for (path, points) in &wrote.links {
            writeln!(out, "{:<7} {path}  ({points})", "linked")?;
        }
        for (path, because) in &wrote.left {
            writeln!(out, "left {path} alone: {because}")?;
        }
        writeln!(
            out,
            "the folder {} has, at {}, and no history beside it",
            target::spelled(store, target),
            where_it_is.display()
        )
    })?;

    // Decision 0027, and `update`'s wording for it.
    if !wrote.folded.is_empty() {
        return Err(Failure::error(format!(
            "this folder folds paths the tree holds apart, and cannot represent it:{}",
            wrote
                .folded
                .iter()
                .map(|path| format!("\n  {path}"))
                .collect::<String>()
        )));
    }
    // Into a directory that held nothing, anything left alone means somebody
    // else was writing there while this ran — which is a fault rather than the
    // note it is for `update`, where a folder holding work is the ordinary
    // case.
    if !wrote.left.is_empty() {
        return Err(Failure::error(
            "something wrote into that directory while the folder was being laid out; \
             some of it was left alone, above. export into an empty directory",
        ));
    }
    Ok(code)
}
