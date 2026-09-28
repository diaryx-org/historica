//! `offer`: the manifest, printed or kept.
//!
//! Decision 0048 builds the listing and decision 0052 says where it is written
//! from. What lives here is the two things the library cannot know: which
//! directory a person meant, and that its own name is the prefix every path
//! takes. Without `--into` the whole of standard output is the manifest, so
//! that `historica offer store > offer.txt` is the publish, and a line of
//! commentary would be a line in somebody's manifest. With it, decision 0080's
//! paged manifest is kept at the file named, and what is printed is what the
//! run did to it.

use std::io::Write as _;
use std::path::Path;

use historica::store::{HEADER_FILE, STORE_DIR};

use super::{Failure, printing};

/// `offer <dir>` — the transferable files of a published copy.
pub fn offer(base: &Path, arguments: Vec<String>) -> Result<u8, Failure> {
    let mut rest: Vec<String> = Vec::new();
    let mut into: Option<String> = None;
    let mut arguments = arguments.into_iter();
    while let Some(argument) = arguments.next() {
        match argument.as_str() {
            "--into" => {
                into = Some(arguments.next().ok_or_else(|| {
                    Failure::usage("`--into` wants the manifest's file, beside the copy")
                })?);
            }
            other if other.starts_with('-') => {
                return Err(Failure::usage(format!(
                    "`{other}` is not an argument `offer` takes"
                )));
            }
            other => rest.push(other.to_owned()),
        }
    }

    let mut rest = rest.into_iter();
    let directory = rest.next().ok_or_else(|| {
        Failure::usage(
            "`offer` wants the directory of the published copy: the one \
             `export` wrote, with the manifest going beside it",
        )
    })?;
    if let Some(extra) = rest.next() {
        return Err(Failure::usage(format!(
            "`offer` takes one directory, and `{extra}` is a second"
        )));
    }

    // The repository, never the store under it. Decision 0052 anchors a
    // manifest's paths at the directory it sits beside, so which of the two a
    // person meant is the difference between `store/history/…` and
    // `history/history/…` — a thing to be exact about rather than to guess at,
    // which is why this does not take the latitude `check` takes.
    let copy = base.join(&directory);
    let root = copy.join(STORE_DIR);
    if !root.join(HEADER_FILE).is_file() {
        return Err(Failure::error(format!(
            "{} holds no `{STORE_DIR}/{HEADER_FILE}`, so there is nothing to \
             offer; `offer` is pointed at the published copy — the directory \
             `export` wrote — rather than at the store inside it",
            copy.display()
        )));
    }
    let store = super::cache::open(&root)?;

    // The directory's own name, which is the prefix a fetcher resolves against
    // the manifest beside it. Canonical, so that `historica offer .` writes the
    // name the directory has rather than the punctuation that found it.
    let settled = copy.canonicalize().unwrap_or_else(|_| copy.clone());
    let prefix = settled
        .file_name()
        .map(|name| name.to_string_lossy().into_owned())
        .unwrap_or_default();

    let Some(into) = into else {
        let offer = store.offer(&prefix).map_err(Failure::error)?;
        return printing(|out| write!(out, "{offer}"));
    };

    // Beside the copy, or the paths in it resolve against the wrong
    // directory: decision 0052 anchors them at the manifest's own.
    let manifest = base.join(&into);
    let beside = manifest
        .parent()
        .and_then(|parent| parent.canonicalize().ok());
    if beside.as_deref() != settled.parent() {
        return Err(Failure::error(format!(
            "{} is not beside {}: a manifest's paths start with the copy's \
             name and resolve against the manifest's own directory, so the \
             manifest sits in the directory the copy is in",
            manifest.display(),
            copy.display()
        )));
    }
    let published = store
        .publish_offer(&prefix, &manifest)
        .map_err(Failure::error)?;
    printing(|out| {
        match (published.page, published.base) {
            (None, _) => writeln!(out, "nothing changed")?,
            (Some(page), true) => writeln!(
                out,
                "wrote a base, {}, listing the whole copy",
                page.abbreviate(12)
            )?,
            (Some(page), false) => writeln!(
                out,
                "wrote page {}, the {} after the base",
                page.abbreviate(12),
                ordinal(published.pages - 1)
            )?,
        }
        if published.removed > 0 {
            writeln!(
                out,
                "removed {} page{} the manifest no longer names",
                published.removed,
                if published.removed == 1 { "" } else { "s" }
            )?;
        }
        Ok(())
    })
}

/// A count said as a position: `1st`, `2nd`, `3rd`, `11th`.
fn ordinal(count: usize) -> String {
    let suffix = match (count % 10, count % 100) {
        (_, 11..=13) => "th",
        (1, _) => "st",
        (2, _) => "nd",
        (3, _) => "rd",
        _ => "th",
    };
    format!("{count}{suffix}")
}
