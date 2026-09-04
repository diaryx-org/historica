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

use std::io::Write as _;
use std::path::Path;
use std::time::Duration;

use historica::store::{Source, Store, Unreachable};

use super::{Failure, locate, printing};

/// `fetch <url> [--join-unrelated]` — take what a published copy has and this
/// store lacks.
pub fn fetch(base: &Path, arguments: Vec<String>) -> Result<u8, Failure> {
    let mut join_unrelated = false;
    let mut url: Option<String> = None;
    for argument in arguments {
        match argument.as_str() {
            "--join-unrelated" => join_unrelated = true,
            other if other.starts_with('-') => {
                return Err(Failure::usage(format!(
                    "`{other}` is not an argument `fetch` takes"
                )));
            }
            other if url.is_none() => url = Some(other.to_owned()),
            other => {
                return Err(Failure::usage(format!(
                    "`fetch` wants one URL, not `{other}`"
                )));
            }
        }
    }
    let url = url.ok_or_else(|| {
        Failure::usage(
            "`fetch` wants the URL of a manifest: the `offer.txt` a publisher \
             wrote beside the copy `export` made",
        )
    })?;
    let (root, manifest) = addressed(&url)?;

    let mut store = Store::open(locate(base)?)?;
    let source = Web::at(&root)?;
    let fetched = store
        .fetch(&source, &manifest, join_unrelated)
        .map_err(Failure::error)?;

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
