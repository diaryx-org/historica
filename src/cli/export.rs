//! `export`: the copy a person takes away.
//!
//! Decision 0042. The library builds the directory; what lives here is which
//! lines to print, which target the default is, and the `--dry-run` flag that
//! chooses between planning and doing — decision 0006's division, and the
//! shape `receive` already has on the other side of the same journey.

use std::io::Write as _;
use std::path::{Path, PathBuf};

use historica::fs::Disk;
use historica::store::Store;

use super::{Failure, printing, target};

/// `export <dir> [<target>] [-n|--dry-run]` — a fresh repository at `<dir>`.
pub fn export(base: &Path, root: PathBuf, arguments: Vec<String>) -> Result<u8, Failure> {
    let mut dry_run = false;
    let mut rest: Vec<String> = Vec::new();
    for argument in arguments {
        match argument.as_str() {
            "-n" | "--dry-run" => dry_run = true,
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

    if dry_run {
        let plan = store.export_plan(&target).map_err(Failure::error)?;
        return printing(|out| {
            writeln!(out, "would export {} revisions", plan.revisions().len())?;
            writeln!(
                out,
                "would export {} operation documents",
                plan.documents().len()
            )?;
            writeln!(out, "would export {} payloads", plan.payloads().len())?;
            if !plan.forgetting().is_empty() {
                writeln!(
                    out,
                    "would export {} forgetting documents",
                    plan.forgetting().len()
                )?;
            }
            for path in plan.paths() {
                writeln!(out, "{:<7} {path}", "write")?;
            }
            writeln!(
                out,
                "would make a copy of {} at {}, stating {}",
                target::spelled(&store, &target),
                into.display(),
                plan.version()
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
        for path in &exported.files {
            writeln!(out, "{:<7} {path}", "wrote")?;
        }
        writeln!(
            out,
            "made a copy of {} at {}, stating {}",
            target::spelled(&store, &target),
            where_it_is.display(),
            exported.version
        )
    })
}
