//! Content held elsewhere, fetched when a command needs it.
//!
//! Decision 0089. A copy that took the history without the content holds
//! every revision and not every file's text. A command that reads a file asks
//! the store which content it lacks, fetches that from the copy this store
//! last fetched from, and goes on; where it cannot reach the copy it refuses,
//! naming the files and the `fetch` that brings them, and never answers from
//! part of a file.
//!
//! The copy is remembered in the host's cache beside the store's other
//! caches (decision 0078), so deleting the cache costs the next such command
//! a refusal and nothing else. A command never fetches from a copy the
//! person did not fetch from first.

use historica::core::RevisionId;
use historica::store::{Store, TextElsewhere};
use historica::working::Working;

use super::{Failure, cache};

/// The file in a store's cache directory that names the copy it last fetched
/// from.
const SOURCE: &str = "source.txt";

/// Remember `url` as the copy this store last fetched from. A failure is
/// ignored, as every failure to keep a cache is: the cost is a refusal later.
pub fn remember_source(store: &Store, url: &str) {
    if let Some(cache) = store.cache_directory() {
        let _ = std::fs::create_dir_all(cache);
        let _ = std::fs::write(cache.join(SOURCE), format!("{url}\n"));
    }
}

/// The copy this store last fetched from, where the cache still says.
pub fn remembered_source(store: &Store) -> Option<String> {
    let text = std::fs::read_to_string(store.cache_directory()?.join(SOURCE)).ok()?;
    let url = text.trim();
    (!url.is_empty()).then(|| url.to_owned())
}

/// Hold whole every file of lines at `revisions`, narrowed to `paths`,
/// fetching what this store lacks, or refuse.
pub fn held_whole(
    store: &mut Store,
    revisions: &[RevisionId],
    paths: Option<&[String]>,
) -> Result<(), Failure> {
    let elsewhere = store
        .text_elsewhere(revisions, paths)
        .map_err(Failure::error)?;
    take(store, &elsewhere)
}

/// Hold whole every file of lines at `parents` that the folder holds,
/// narrowed to `paths`, so that
/// `record` and `status` can diff it. A file the folder lacks is left where
/// it is: the survey reads it as held elsewhere, not as deleted.
pub fn folder_held_whole(
    store: &mut Store,
    working: &Working,
    parents: &[RevisionId],
    paths: Option<&[String]>,
) -> Result<(), Failure> {
    let mut elsewhere = store
        .text_elsewhere(parents, paths)
        .map_err(Failure::error)?;
    elsewhere.files.retain(|path, _| working.holds(path));
    take(store, &elsewhere)
}

/// Fetch what `elsewhere` lacks from the remembered copy, then open the store
/// again so nothing read before the fetch is believed after it.
fn take(store: &mut Store, elsewhere: &TextElsewhere) -> Result<(), Failure> {
    if elsewhere.is_empty() {
        return Ok(());
    }
    let paths: Vec<&str> = elsewhere.paths().collect();
    let Some(url) = remembered_source(store) else {
        return Err(Failure::error(format!(
            "{} held elsewhere: this copy took the history without that \
             content, and does not remember the copy it came from; \
             `historica fetch <url> {}` brings it:{}",
            files(&paths),
            paths.join(" "),
            listed(&paths)
        )));
    };
    let digests: Vec<RevisionId> = elsewhere.digests().into_iter().collect();
    fetched(store, &url, &digests).map_err(|because| {
        let because = because.trim_end_matches('.');
        Failure::error(format!(
            "{} held elsewhere, and the copy at {url} could not be asked for \
             it: {because}. no part of a file is read without all of it, so \
             nothing was done; `historica fetch {url} {}` brings it once the \
             copy can be reached:{}",
            files(&paths),
            paths.join(" "),
            listed(&paths)
        ))
    })?;
    let root = store.root().to_path_buf();
    *store = cache::open(&root)?;
    Ok(())
}

#[cfg(feature = "http")]
fn fetched(store: &mut Store, url: &str, digests: &[RevisionId]) -> Result<(), String> {
    super::fetch::content(store, url, digests)
}

/// A build without a transport fetches nothing, so it says so.
#[cfg(not(feature = "http"))]
fn fetched(_: &mut Store, _: &str, _: &[RevisionId]) -> Result<(), String> {
    Err("this historica was built without `fetch`".to_owned())
}

fn files(paths: &[&str]) -> String {
    match paths {
        [one] => format!("the content of `{one}` is"),
        several => format!("the content of {} files is", several.len()),
    }
}

fn listed(paths: &[&str]) -> String {
    paths.iter().map(|path| format!("\n  {path}")).collect()
}
