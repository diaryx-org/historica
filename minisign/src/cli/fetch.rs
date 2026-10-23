//! `fetch` and `token`: reading a copy a server keeps to its members.
//!
//! `fetch` is `historica fetch`, said again with a key. The library does the
//! whole of the algorithm through a `Source`, as historica's decision 0048
//! built it to, so what differs is the source: [`SignedSource`] signs each
//! request with this device's key. Everything else — the arguments, the
//! refusals, every line of what is printed — is historica's own command, so
//! that `historica minisign fetch <url>` (decision 0072's spelling) reads as
//! the command it stands in for.
//!
//! `token` is the half `git clone` needs, since git cannot sign a request: a
//! short-lived token from the hub, as JSON.

use std::collections::{BTreeMap, BTreeSet};
use std::env;
use std::path::{Path, PathBuf};

use historica::core::RevisionId;
use historica::format;
use historica::store::{Fetching, Store};
use historica::tree::Kind;
use historica::wrote::{Line, Statement};

use historica_minisign::http::{SignedSource, request_token};
use historica_minisign::verify;

use super::{Failure, printing, secret_key, value};

/// `fetch <url> [--join-unrelated] [--no-bytes] [--fields] [<path>...]`.
pub fn fetch(base: &Path, arguments: &[String]) -> Result<u8, Failure> {
    let mut asked = Fetching::default();
    let mut fields = false;
    let mut url: Option<String> = None;
    let mut paths: Vec<String> = Vec::new();
    let mut key_path: Option<PathBuf> = None;
    let mut password_file: Option<PathBuf> = None;
    let mut rest = arguments.iter();
    while let Some(argument) = rest.next() {
        match argument.as_str() {
            "--join-unrelated" => asked = asked.joining_unrelated(true),
            "--no-bytes" => asked = asked.leaving_bytes(true),
            "--fields" => fields = true,
            "--key" => key_path = Some(PathBuf::from(value(&mut rest, "--key")?)),
            "--password-file" => {
                password_file = Some(PathBuf::from(value(&mut rest, "--password-file")?));
            }
            other if other.starts_with('-') => {
                return Err(Failure::usage(format!(
                    "`{other}` is not an argument `fetch` takes"
                )));
            }
            other if url.is_none() => url = Some(other.to_owned()),
            other => paths.push(path(other)?),
        }
    }
    let url = url.ok_or_else(|| {
        Failure::usage(
            "`fetch` wants the URL of a manifest: the `offer.txt` a publisher \
             wrote beside the copy `export` made",
        )
    })?;
    let (root, manifest) = addressed(&url)?;
    if !paths.is_empty() && asked != Fetching::default() {
        return Err(Failure::usage(
            "`fetch <url> <path>...` takes the files of bytes named and \
             nothing else, so it has no use for `--no-bytes` or \
             `--join-unrelated`",
        ));
    }

    let mut store = open_caching(base)?;
    let secret = secret_key(key_path, password_file.as_deref())?;
    let source = SignedSource::at(&root, secret).map_err(Failure::error)?;

    // The files somebody named, and nothing else: the history is already
    // here, and what is missing is the bytes of these.
    if !paths.is_empty() {
        let named = files_of_bytes(&store, &paths)?;
        // Historica's decision 0014: bytes somebody forgot are not fetched
        // back, and the person who named them is told so rather than shown a
        // zero.
        let mut forgotten = Vec::new();
        let mut wanted = Vec::new();
        for (path, payload) in &named {
            if store.holds_payload(payload).map_err(Failure::error)? {
                continue;
            }
            if store.held_elsewhere(payload).map_err(Failure::error)? {
                wanted.push(*payload);
            } else {
                forgotten.push(path);
            }
        }
        let fetched = store
            .fetch_payloads(&source, &manifest, &wanted)
            .map_err(Failure::error)?;
        if fields {
            return printing(|mut out| Statement::new().write(&mut out));
        }
        return printing(|out| {
            for path in &forgotten {
                writeln!(
                    out,
                    "left {path} alone: its bytes were forgotten here, and are not fetched back"
                )?;
            }
            writeln!(out, "fetched {} payloads", fetched.payloads)?;
            if fetched.payloads != 0 {
                writeln!(
                    out,
                    "the folder is untouched; `historica update` writes them into it"
                )?;
            }
            Ok(())
        });
    }

    let fetched = store
        .fetch_with(&source, &manifest, asked)
        .map_err(Failure::error)?;

    if fields {
        let mut statement = Statement::new();
        statement.extend(fetched.revisions.iter().map(|id| Line::Revision(*id)));
        statement.extend(fetched.names.iter().map(|name| Line::Name(name.clone())));
        return printing(|mut out| statement.write(&mut out));
    }

    printing(|out| {
        writeln!(out, "fetched {} revisions", fetched.revisions.len())?;
        writeln!(out, "fetched {} content documents", fetched.documents)?;
        writeln!(out, "fetched {} payloads", fetched.payloads)?;
        if fetched.rules != 0 {
            writeln!(out, "fetched {} rules", fetched.rules)?;
        }
        if fetched.reserved != 0 {
            writeln!(out, "fetched {} files another tool wrote", fetched.reserved)?;
        }
        if !fetched.names.is_empty() {
            writeln!(out, "fetched {} bookmarks", fetched.names.len())?;
        }
        if fetched.kept != 0 {
            writeln!(
                out,
                "kept this copy's own reading of {} bookmarks the publisher \
                 also states",
                fetched.kept
            )?;
        }
        if fetched.destroyed != 0 {
            writeln!(out, "destroyed {} forgotten originals", fetched.destroyed)?;
        }
        if fetched.left != 0 {
            writeln!(
                out,
                "left {} payloads with the copy, each the bytes of a file at some \
                 revision; `fetch <url> <path>` takes a file's, and `fetch <url>` \
                 takes them all",
                fetched.left
            )?;
        }
        for declined in &fetched.declined {
            writeln!(
                out,
                "declined {} files of `{}/`, which this historica does not \
                 carry across a boundary",
                declined.files, declined.directory
            )?;
        }
        if fetched.refetches != 0 {
            writeln!(
                out,
                "read the manifest {} times: the copy was being rewritten while \
                 it was being read",
                fetched.refetches + 1
            )?;
        }
        if !fetched.revisions.is_empty() {
            writeln!(
                out,
                "the folder is untouched; `historica update` is its catch-up"
            )?;
        }
        Ok(())
    })
}

/// `token <hub>` — a short-lived token for this key, as JSON.
pub fn token(arguments: &[String]) -> Result<u8, Failure> {
    let mut hub: Option<String> = None;
    let mut key_path: Option<PathBuf> = None;
    let mut password_file: Option<PathBuf> = None;
    let mut rest = arguments.iter();
    while let Some(argument) = rest.next() {
        match argument.as_str() {
            "--key" => key_path = Some(PathBuf::from(value(&mut rest, "--key")?)),
            "--password-file" => {
                password_file = Some(PathBuf::from(value(&mut rest, "--password-file")?));
            }
            other if other.starts_with('-') => {
                return Err(Failure::usage(format!(
                    "`{other}` is not an option to token"
                )));
            }
            other if hub.is_none() => hub = Some(other.to_owned()),
            other => {
                return Err(Failure::usage(format!("`{other}`: token asks one hub")));
            }
        }
    }
    let hub = hub.ok_or_else(|| {
        Failure::usage("`token` wants the hub's URL, as `https://hub.example.org`")
    })?;
    let secret = secret_key(key_path, password_file.as_deref())?;
    let token = request_token(&hub, &secret).map_err(Failure::error)?;
    printing(|out| writeln!(out, "{}", token.to_json()))
}

/// The store containing `base`, opened with its caches where historica's own
/// command line keeps them.
///
/// A fetch remembers the pages of a paged manifest it has applied, and the
/// payloads it left with the copy, in the store's cache (historica's decision
/// 0078 gives caches to the host). Finding the same directory historica-cli
/// finds means `historica fetch` and this command share that memory, so
/// neither reads again what the other already took. The order is
/// historica-cli's, less its `--cache-dir` flag, which is that tool's.
fn open_caching(base: &Path) -> Result<Store, Failure> {
    let store = Store::discover(base)?;
    let root = store.root().to_path_buf();
    match cache_for(&root) {
        Some(cache) => Store::open_caching(&root, cache).map_err(Failure::from),
        None => Ok(store),
    }
}

fn cache_for(root: &Path) -> Option<PathBuf> {
    let given = |name: &str| {
        env::var_os(name)
            .filter(|value| !value.is_empty())
            .map(PathBuf::from)
    };
    let platform = if cfg!(target_os = "macos") {
        "Library/Caches/historica"
    } else {
        ".cache/historica"
    };
    let base = given("HISTORICA_CACHE_DIR")
        .or_else(|| {
            given("XDG_CACHE_HOME")
                .filter(|path| path.is_absolute())
                .map(|path| path.join("historica"))
        })
        .or_else(|| given("HOME").map(|home| home.join(platform)))?;
    let base = match base.is_absolute() {
        true => base,
        false => env::current_dir().ok()?.join(base),
    };
    let root = root.canonicalize().unwrap_or_else(|_| root.to_path_buf());
    let named = format::digest(root.as_os_str().as_encoded_bytes()).to_string();
    Some(base.join(&named[..16]))
}

/// One path argument, spelled as historica's `record` spells one.
fn path(argument: &str) -> Result<String, Failure> {
    let path = format::nfc(argument.trim_end_matches('/')).into_owned();
    if path.is_empty() {
        return Err(Failure::usage(
            "`fetch` takes the files to act on, and an empty path names nothing",
        ));
    }
    Ok(path)
}

/// The files of bytes the current heads hold at or beneath each path, with
/// the payload each names, as historica's own `fetch` finds them.
fn files_of_bytes(
    store: &Store,
    paths: &[String],
) -> Result<BTreeSet<(String, RevisionId)>, Failure> {
    let mut held: BTreeMap<String, Vec<(Kind, Option<RevisionId>)>> = BTreeMap::new();
    for head in verify::current_heads(store) {
        for (_, entry) in store.tree(&head).map_err(Failure::error)?.entries() {
            held.entry(entry.path.clone())
                .or_default()
                .push((entry.kind, entry.payload));
        }
    }
    let mut found = BTreeSet::new();
    for named in paths {
        let beneath = format!("{named}/");
        let exact = held.get_key_value(named.as_str()).into_iter();
        let under = held
            .range(beneath.clone()..)
            .take_while(|(path, _)| path.starts_with(&beneath));
        let mut any = false;
        let mut bytes = false;
        for (path, entries) in exact.chain(under) {
            any = true;
            for (kind, payload) in entries {
                match (kind, payload) {
                    (Kind::Whole, Some(payload)) => {
                        bytes = true;
                        found.insert((path.clone(), *payload));
                    }
                    _ if path == named => {
                        return Err(Failure::error(format!(
                            "`{named}` is not a file of bytes with one content, and \
                             only such a file is ever held elsewhere"
                        )));
                    }
                    _ => {}
                }
            }
        }
        if !any {
            return Err(Failure::error(format!(
                "`{named}` names no file the heads hold"
            )));
        }
        if !bytes {
            return Err(Failure::error(format!(
                "`{named}` holds no file of bytes, and only such a file is ever \
                 held elsewhere"
            )));
        }
    }
    Ok(found)
}

/// The directory a manifest sits in, and the manifest's own name in it, as
/// historica's own `fetch` splits a URL (decision 0052).
pub(super) fn addressed(url: &str) -> Result<(String, String), Failure> {
    let scheme = url.find("://").map(|at| at + 3).ok_or_else(|| {
        Failure::usage(format!(
            "`{url}` is not a URL; `fetch` wants one, and a directory on this \
             machine is `receive`'s to read"
        ))
    })?;
    if !["http://", "https://"]
        .iter()
        .any(|spoken| url[..scheme].eq_ignore_ascii_case(spoken))
    {
        return Err(Failure::usage(format!(
            "`{url}` is not an HTTP URL; `fetch` speaks HTTP, and a directory \
             on this machine is `receive`'s to read"
        )));
    }
    if let Some(at) = url.find(['?', '#']) {
        return Err(Failure::usage(format!(
            "`{}` cannot be part of a manifest's URL: the paths in a manifest \
             resolve against the directory it sits in, so there is nowhere for \
             it to go",
            &url[at..at + 1]
        )));
    }
    let Some(at) = url[scheme..].rfind('/').map(|at| at + scheme) else {
        return Err(Failure::usage(format!(
            "`{url}` names a host and no manifest; `fetch` wants the URL of \
             the `offer.txt` itself, since every path in it resolves against \
             the directory it sits in"
        )));
    };
    let manifest = &url[at + 1..];
    if manifest.is_empty() {
        return Err(Failure::usage(format!(
            "`{url}` names a directory; `fetch` wants the URL of the manifest \
             in it, conventionally `offer.txt`"
        )));
    }
    Ok((url[..=at].to_owned(), manifest.to_owned()))
}

#[cfg(test)]
mod tests {
    use super::addressed;

    #[test]
    fn a_manifests_url_parts_into_its_directory_and_its_name() {
        assert_eq!(
            addressed("https://example.org/pub/offer.txt").expect("a manifest URL"),
            (
                "https://example.org/pub/".to_owned(),
                "offer.txt".to_owned()
            )
        );
        for refused in [
            "example.org/offer.txt",
            "https://example.org",
            "https://example.org/pub/",
            "https://example.org/offer.txt?v=2",
            "file:///srv/pub/offer.txt",
        ] {
            assert!(addressed(refused).is_err(), "`{refused}` was accepted");
        }
    }
}
