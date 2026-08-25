//! `offer`: the manifest, printed.
//!
//! Decision 0048 builds the listing and decision 0052 says where it is written
//! from. What lives here is the two things the library cannot know: which
//! directory a person meant, and that its own name is the prefix every path
//! takes. Nothing else — the whole of standard output is the manifest, so that
//! `historica offer store > offer.txt` is the publish, and a line of commentary
//! here would be a line in somebody's manifest.

use std::io::Write as _;
use std::path::Path;

use historica::store::{HEADER_FILE, STORE_DIR, Store};

use super::{Failure, printing};

/// `offer <dir>` — the transferable files of a published copy.
pub fn offer(base: &Path, arguments: Vec<String>) -> Result<u8, Failure> {
    let mut rest: Vec<String> = Vec::new();
    for argument in arguments {
        match argument.as_str() {
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
    let store = Store::open(&root)?;

    // The directory's own name, which is the prefix a fetcher resolves against
    // the manifest beside it. Canonical, so that `historica offer .` writes the
    // name the directory has rather than the punctuation that found it.
    let settled = copy.canonicalize().unwrap_or_else(|_| copy.clone());
    let prefix = settled
        .file_name()
        .map(|name| name.to_string_lossy().into_owned())
        .unwrap_or_default();

    let offer = store.offer(&prefix).map_err(Failure::error)?;
    printing(|out| write!(out, "{offer}"))
}
