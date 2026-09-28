//! `fetch`: the transport, which decision 0048 says is the binary's.
//!
//! The library does the whole of the algorithm — the listing, the difference,
//! the order, the verification — through a [`Source`] that answers one
//! question, `get(path)`. What lives here is the answer to that question over
//! HTTP, and the two things the library declines to know: which URL a person
//! meant, and how a path becomes one.
//!
//! Decision 0057 argues the stack. In one sentence: linking the platform's own
//! HTTP — WinRT, NSURLSession, libcurl — puts a fetch on the TLS roots, the
//! proxy configuration and the security updates the machine already maintains,
//! where shelling out to `curl` would put it on whatever binary of that name
//! happens to be first on `PATH`.
//!
//! It is behind a feature, and this module is the whole of what the feature
//! adds. A build without it is a CLI without a `fetch` — which is what a
//! `wasm32-wasip1` build is, since a wasi guest has no such stack under it and
//! a host that wants one implements the library's trait instead.

use std::collections::{BTreeMap, BTreeSet};
use std::io::Write as _;
use std::path::Path;
use std::time::Duration;

use historica::core::RevisionId;
use historica::format;
use historica::store::{Fetching, Source, Store, Unreachable};
use historica::tree::Kind;
use historica::update;
use historica::wrote::{Line, Statement};

use super::{Failure, locate, printing, render, target};

/// `fetch <url> [--join-unrelated] [--no-bytes] [<path>...]` — take what a
/// published copy has and this store lacks.
pub fn fetch(base: &Path, arguments: Vec<String>) -> Result<u8, Failure> {
    let mut asked = Fetching::default();
    let mut fields = false;
    let mut url: Option<String> = None;
    let mut paths: Vec<String> = Vec::new();
    for argument in arguments {
        match argument.as_str() {
            "--join-unrelated" => asked = asked.joining_unrelated(true),
            "--no-bytes" => asked = asked.leaving_bytes(true),
            "--fields" => fields = true,
            other if other.starts_with('-') => {
                return Err(Failure::usage(format!(
                    "`{other}` is not an argument `fetch` takes"
                )));
            }
            other if url.is_none() => url = Some(other.to_owned()),
            other => paths.push(path(other, "fetch")?),
        }
    }
    let url = url.ok_or_else(|| {
        Failure::usage(
            "`fetch` wants the URL of a manifest: the `offer.txt` a publisher \
             wrote beside the copy `export` made",
        )
    })?;
    let (root, manifest) = addressed(&url)?;

    let mut store = super::cache::open(&locate(base)?)?;
    let source = Web::at(&root)?;

    // The files somebody named, and nothing else: the history is already
    // here, and what is missing is the bytes of these.
    if !paths.is_empty() {
        if asked != Fetching::default() {
            return Err(Failure::usage(
                "`fetch <url> <path>...` takes the files of bytes named and \
                 nothing else, so it has no use for `--no-bytes` or \
                 `--join-unrelated`",
            ));
        }
        let named = files_of_bytes(&store, &paths)?;
        // Decision 0014: bytes somebody forgot are not fetched back, and the
        // person who named them is told so rather than shown a zero.
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
            return printing(|out| render::wrote(out, &Statement::new()));
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
        return printing(|out| render::wrote(out, &statement));
    }

    printing(|out| {
        writeln!(out, "fetched {} revisions", fetched.revisions.len())?;
        writeln!(out, "fetched {} content documents", fetched.documents)?;
        writeln!(out, "fetched {} payloads", fetched.payloads)?;
        if fetched.rules != 0 {
            writeln!(out, "fetched {} rules", fetched.rules)?;
        }
        // Decision 0053: a class, not a tool, so this says what these files are
        // rather than whose they are.
        if fetched.reserved != 0 {
            writeln!(out, "fetched {} files another tool wrote", fetched.reserved)?;
        }
        if !fetched.names.is_empty() {
            writeln!(out, "fetched {} bookmarks", fetched.names.len())?;
        }
        // Decision 0062: a bookmark this store already has is one it keeps,
        // and saying so is what keeps a person from reading an unmoved `main`
        // as a fetch that failed to notice.
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
        // The proposal *Bytes held elsewhere*: said every time, since a fetch
        // without `--no-bytes` is what takes them.
        if fetched.left != 0 {
            writeln!(
                out,
                "left {} payloads with the copy, each the bytes of a file at some \
                 revision; `fetch <url> <path>` takes a file's, and `fetch <url>` \
                 takes them all",
                fetched.left
            )?;
        }
        // Decision 0057: an observation. The recipient is the only party who
        // can install the tool that would read these, so a silent decline
        // would be a thing nobody could go looking for.
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
        // Decision 0030, said where the person is: a fetch adds history and
        // stops, and the folder catching up is a separate thing to type.
        if !fetched.revisions.is_empty() {
            writeln!(
                out,
                "the folder is untouched; `historica update` is its catch-up"
            )?;
        }
        Ok(())
    })
}

/// `evict <url> <path>...` — let go of the bytes of files a published copy
/// also holds.
///
/// The proposal *Bytes held elsewhere*. The store's copy of each file goes
/// first and the folder's second, so an interruption leaves the folder
/// holding bytes the head names, which `record` reads as unchanged and
/// running `evict` again finishes.
pub fn evict(base: &Path, arguments: Vec<String>) -> Result<u8, Failure> {
    let mut dry_run = false;
    let mut url: Option<String> = None;
    let mut paths: Vec<String> = Vec::new();
    for argument in arguments {
        match argument.as_str() {
            "-n" | "--dry-run" => dry_run = true,
            other if other.starts_with('-') => {
                return Err(Failure::usage(format!(
                    "`{other}` is not an argument `evict` takes"
                )));
            }
            other if url.is_none() => url = Some(other.to_owned()),
            other => paths.push(path(other, "evict")?),
        }
    }
    let url = url.ok_or_else(|| {
        Failure::usage(
            "`evict` wants the URL of the manifest of a copy that holds the \
             bytes, and then the files to let go of",
        )
    })?;
    if paths.is_empty() {
        return Err(Failure::usage(
            "`evict` wants the files to let go of, after the URL",
        ));
    }
    let (root, manifest) = addressed(&url)?;

    let store_root = locate(base)?;
    let mut store = super::cache::open(&store_root)?;
    let repository = store_root
        .parent()
        .ok_or_else(|| Failure::error("this store has no repository around it"))?
        .to_path_buf();
    let named = files_of_bytes(&store, &paths)?;
    let payloads: BTreeSet<RevisionId> = named.iter().map(|(_, payload)| *payload).collect();
    let wanted: Vec<RevisionId> = payloads.iter().copied().collect();

    let source = Web::at(&root)?;
    let plan = store
        .eviction_plan(&source, &manifest, &wanted)
        .map_err(Failure::error)?;
    let working = super::cache::working(&repository, &store).map_err(Failure::error)?;
    let folder = update::plan_eviction(&store, &working, &payloads).map_err(Failure::error)?;

    if dry_run {
        return printing(|out| {
            for path in &folder.elsewhere {
                writeln!(out, "{:<7} {path}", "evict")?;
            }
            Ok(())
        });
    }

    let evicted: BTreeSet<RevisionId> = store
        .evict(&plan)
        .map_err(Failure::error)?
        .into_iter()
        .collect();
    let applied = update::apply(&store, &working, &repository, &folder).map_err(Failure::error)?;
    printing(|out| {
        for (path, payload) in &named {
            if evicted.contains(payload) {
                writeln!(out, "{:<7} {path}", "evicted")?;
            }
        }
        for path in &applied.removed {
            writeln!(out, "{:<7} {path}", "removed")?;
        }
        for (path, because) in &applied.left {
            writeln!(out, "left {path} alone: {because}")?;
        }
        Ok(())
    })
}

/// One path argument, spelled as `record` spells one: normalised, and with
/// the trailing slash a shell adds to a directory taken off.
fn path(argument: &str, command: &str) -> Result<String, Failure> {
    let path = format::nfc(argument.trim_end_matches('/')).into_owned();
    if path.is_empty() {
        return Err(Failure::usage(format!(
            "`{command}` takes the files to act on, and an empty path names nothing"
        )));
    }
    Ok(path)
}

/// The files of bytes the current heads hold at or beneath each path, with
/// the payload each names — one pair for each head that differs there.
///
/// A path naming a file of lines, or a directory holding no file of bytes,
/// is refused, since only a file of bytes is ever held elsewhere; a directory
/// takes the files of bytes beneath it and passes over the rest.
fn files_of_bytes(
    store: &Store,
    paths: &[String],
) -> Result<BTreeSet<(String, RevisionId)>, Failure> {
    // Every head's files by path, once, so that a thousand paths a shell
    // expanded are a thousand lookups rather than a thousand passes.
    let mut held: BTreeMap<String, Vec<(Kind, Option<RevisionId>)>> = BTreeMap::new();
    for head in target::current_heads(store) {
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

/// The directory a manifest sits in, and the manifest's own name in it.
///
/// Decision 0052 resolves every path in a manifest against the manifest's own
/// directory, so this is the whole of the convention: split the URL at its last
/// `/`, and everything after it is one more path in the same space.
fn addressed(url: &str) -> Result<(String, String), Failure> {
    let scheme = url.find("://").map(|at| at + 3).ok_or_else(|| {
        Failure::usage(format!(
            "`{url}` is not a URL; `fetch` wants one, and a directory on this \
             machine is `receive`'s to read"
        ))
    })?;
    // The transport is HTTP and nothing else (decision 0057). The platform's
    // client takes other schemes too, and answers `file:` with no status at
    // all, which a fetch waiting for one would wait on for good.
    if !["http://", "https://"]
        .iter()
        .any(|spoken| url[..scheme].eq_ignore_ascii_case(spoken))
    {
        return Err(Failure::usage(format!(
            "`{url}` is not an HTTP URL; `fetch` speaks HTTP, and a directory \
             on this machine is `receive`'s to read"
        )));
    }
    // A query or a fragment has nowhere to go: every other path a fetch asks
    // for is built by putting the manifest's own directory in front of what the
    // manifest says, and neither of those survives that.
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

/// A published root, over the platform's own HTTP.
struct Web {
    client: nyquest::BlockingClient,
    root: String,
}

impl Web {
    fn at(root: &str) -> Result<Self, Failure> {
        // Registering the backend is what makes `nyquest` resolve to WinRT,
        // NSURLSession or libcurl; done here rather than at `main` so that a
        // build with no `fetch` in it has no startup work and no `ctor`.
        nyquest_preset::register();
        let client = nyquest::ClientBuilder::default()
            .user_agent(concat!("historica/", env!("CARGO_PKG_VERSION")))
            // A fetch of a public directory says nothing about who is asking,
            // which is also the shape decision 0048 left authentication in:
            // deferred, and nothing sent in the meantime.
            .no_cookies()
            // Caching is refused for one reason, and it is the retry. Decision
            // 0048 answers a moved path by reading the manifest *again*, and a
            // cache that served the same manifest twice would turn the one
            // recoverable failure into the one unrecoverable one. Every other
            // file here is named by the digest of its bytes and fetched once,
            // so there was nothing for a cache to save.
            .no_caching()
            .request_timeout(Duration::from_secs(60))
            .build_blocking()
            .map_err(|error| Failure::error(format!("no HTTP client: {error}")))?;
        Ok(Self {
            client,
            root: root.to_owned(),
        })
    }
}

impl Source for Web {
    fn get(&self, path: &str) -> Result<Option<Vec<u8>>, Unreachable> {
        let url = format!("{}{}", self.root, escaped(path));
        let response = self
            .client
            .request(nyquest::blocking::Request::get(url))
            .map_err(said)?;
        let status = response.status();
        // The two ways a server says a file is not there, which decision 0048
        // makes an answer rather than a failure: the publisher moved on, and
        // the manifest is read again.
        if status.code() == 404 || status.code() == 410 {
            return Ok(None);
        }
        if !status.is_successful() {
            return Err(Unreachable::saying(format!(
                "the server answered {}",
                status.code()
            )));
        }
        response.bytes().map(Some).map_err(said)
    }
}

/// What went wrong, as far down as the error chain goes.
///
/// nyquest's own message is a category — "IO Error" — and what the platform
/// said is underneath it. A person reading a failed fetch wants the second.
fn said(error: nyquest::Error) -> Unreachable {
    let mut whole = error.to_string();
    let mut cause = std::error::Error::source(&error);
    while let Some(next) = cause {
        whole.push_str(&format!(": {next}"));
        cause = next.source();
    }
    Unreachable::saying(whole)
}

/// One manifest path, said as a URL.
///
/// A manifest's paths are filenames, and decision 0016 lets a person file their
/// history under any name they like — spaces included, which decision 0043
/// built the trailing-path convention around. So every byte that is not
/// unreserved is escaped, and `/` alone survives, because it is the one
/// character in a path that is structure rather than content.
fn escaped(path: &str) -> String {
    let mut escaped = String::with_capacity(path.len());
    for byte in path.bytes() {
        match byte {
            b'A'..=b'Z' | b'a'..=b'z' | b'0'..=b'9' | b'-' | b'.' | b'_' | b'~' | b'/' => {
                escaped.push(byte as char);
            }
            other => escaped.push_str(&format!("%{other:02X}")),
        }
    }
    escaped
}

#[cfg(test)]
mod tests {
    use super::{addressed, escaped};

    #[test]
    fn a_manifests_url_parts_into_its_directory_and_its_name() {
        assert_eq!(
            addressed("https://example.org/pub/offer.txt").expect("a manifest URL"),
            (
                "https://example.org/pub/".to_owned(),
                "offer.txt".to_owned()
            )
        );
        assert_eq!(
            addressed("https://example.org/offer.txt").expect("a manifest URL"),
            ("https://example.org/".to_owned(), "offer.txt".to_owned())
        );
        for refused in [
            "example.org/offer.txt",
            "https://example.org",
            "https://example.org/pub/",
            "https://example.org/offer.txt?v=2",
            "file:///srv/pub/offer.txt",
            "ftp://example.org/offer.txt",
        ] {
            assert!(addressed(refused).is_err(), "`{refused}` was accepted");
        }
    }

    #[test]
    fn a_path_a_person_filed_by_hand_survives_becoming_a_url() {
        assert_eq!(
            escaped("store/history/revisions/2026-08/a second copy.ops.txt"),
            "store/history/revisions/2026-08/a%20second%20copy.ops.txt"
        );
        // Every byte of a name that is not ASCII, escaped as its bytes: a store
        // is filed by whoever holds it, in whatever they write in.
        assert_eq!(escaped("history/notes/ré.txt"), "history/notes/r%C3%A9.txt");
    }
}
