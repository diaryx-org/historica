//! `offer`: the listing a directory has no way to give.
//!
//! Decision 0048, as decision 0052 amends it. Every other way a store travels
//! hands the reader a directory it can walk — `cp -r`, rsync, a mounted disk,
//! an archive somebody unpacked — and every one of decision 0029's rules is
//! written against a source that can be listed. A URL cannot be listed. There
//! is no `entries()` over HTTP, no listing a static file server is obliged to
//! serve, and no guessing at the answer: decision 0003 made filenames
//! presentation, 0019 made the readable names the default and 0041 put a month
//! directory in front of them, so where a document sits is a thing the
//! publisher chose and `arrange` exists to change.
//!
//! So what is missing at the far end of a URL is not a set difference — a
//! fetcher already knows its own half — but a directory listing, for a
//! directory that has no way to say what it holds. This module writes one, and
//! [`Offer::parse`] reads one back for [`fetch`](super::fetch).
//!
//! # What it is pointed at
//!
//! The published copy, which decision 0052 makes an `export` rather than the
//! live store: a manifest sits *beside* the exported directory, and every path
//! in it resolves against the manifest's own directory. So the paths begin
//! with that directory's name — `store/history/operations/…` for a manifest
//! beside a `store/` — and [`Store::offer`] takes that name as its prefix
//! because it is the one thing a listing of a directory cannot read out of the
//! directory. Nothing here asks anything of the origin: an offer is a
//! rendering of the published artifact, not a claim about a store somewhere
//! else.
//!
//! # The grammar
//!
//! ```text
//! historica-offer-1
//! head <digest>
//! <kind> <digest> <forgets|-> <path>
//! ```
//!
//! One `head` line per head, then one line per transferable file. The path is
//! last on decision 0043's reason — a path is the one field that may hold a
//! space, so it ends the line and nothing needs escaping — and nothing here is
//! escaped or quoted. It is text rather than JSON because every other document
//! this format has is line-oriented text, and a reader that can split on a
//! space is a reader that needs nothing installed.
//!
//! The header carries a number, unlike a document's preamble (decision 0047).
//! A document is permanent and a store's grammar is a promise; an offer is
//! neither. It is refetchable, and a reader that meets a spelling it does not
//! know discards it whole and falls back to fetching the archive, which never
//! stopped working — the standing `historica-working-1` already has.
//!
//! The heads answer *relatedness* and nothing else. Decision 0052 is explicit
//! that they are not a currency check: a forgetting document changes the set
//! without moving a head, so equal heads cannot mean equal content, and a
//! fetcher that stopped there would be the one path a redaction never travels.
//! They are the graph's heads, superseded ones included, because a listing
//! decides nothing about what is worth showing — `log` is where that policy
//! lives.
//!
//! # The kinds
//!
//! Decision 0048 named three, which is what `receive` already sorts the world
//! into: `revision`, `operation` and `payload`. Decision 0056 adds the two
//! that decisions 0051 and 0053 put into the transferable set after it, and
//! the parting line between them is what historica can read:
//!
//! - **`rule`** is a file of `skipped/`. Historica owns that grammar, answers
//!   for it in `check`, and can therefore say which rules travel — so the
//!   listing states the shared ones and never the `private` ones, which makes
//!   it safe wherever it is pointed rather than only at an export.
//! - **`reserved`** is a file historica carries and cannot read: a file of a
//!   reserved directory whose class is [`Travel::TravelsAndUnions`]. One kind
//!   for the class rather than one per directory, because decision 0053's
//!   whole point is that transport never learns which directory it is holding
//!   — a token per reservation would be the per-tool special case that
//!   decision refused, in the grammar this time. The path carries the
//!   directory, and a fetcher asks its *own* registry what that directory's
//!   class is before writing a byte of it.
//!
//! A forgetting document is an `operation`: it lives in `operations/`, it is
//! written in one of the two grammars decision 0032 gave that directory, and
//! what parts it from its neighbours is the fourth field rather than the
//! first. A resolution is an `operation` for the same reason.
//!
//! # The fourth field
//!
//! **What an entry forgets** is decision 0014 travelling. A fetcher that took
//! a plain set difference would keep an original that an arriving forgetting
//! document destroys, so the listing states the relationship exactly as a
//! catalogue entry does (decision 0036) and the fetcher honours it without
//! opening anything. Only an `operation` can carry it: a revision document
//! forgets nothing, a payload has no grammar to say it in, a rule file's
//! grammar has no such key, and a `reserved` file is one nothing here has
//! read — decision 0054's deferred revocation is the reserving tool's to
//! define and to act on. All four are `-`.
//!
//! # What is listed, and what is not
//!
//! `historica.txt` and `format.txt` are neither listed nor fetched: a fetcher
//! has a store already, with its own, and a store that did not would have
//! nothing to fetch into. `cache/` is not listed, on decision 0042's answer
//! unchanged: a cache is nobody's, and the directory is not walked, so a store
//! that has one costs a listing nothing. `names/` is listed, which is decision
//! 0062 superseding the other half of that sentence — otherwise a stranger who
//! copies a published export would get bookmarks and a stranger who fetches
//! from it would not, and the manifest is what a static host offers *of an
//! export*. Every bookmark that travels is named; a private one is not, for
//! the reason a private rule is not.
//!
//! # What it costs, and what it does not write
//!
//! `operations/` is measured through decision 0036's catalogue, which already
//! holds a digest and a forgetting relationship per file and reads only what
//! the cache cannot account for — the property that keeps a history with
//! photographs in it from being hashed end to end on every publish. What that
//! catalogue is keyed by is a digest, so it collapses two files holding one
//! set of bytes to one path; the pass that *builds* it does not, and this
//! takes the pass, because a listing names every file at the path it is at.
//!
//! `revisions/` has no catalogue, and decision 0048 left the choice between
//! giving it one and walking it as a measurement rather than a design. It is
//! walked. A revision document is a few hundred bytes and there is one per
//! revision rather than one per file per revision, so the directory is the
//! small half of the store by construction — the store reads all of it at
//! `open` already, and what `open` does not keep is *where* each one is, which
//! is one walk away. A second index in the cache would buy back the hashing of
//! the cheapest files in the store and cost a second thing that can be stale.
//!
//! One claim here is believed rather than read, and it is the catalogue's:
//! where a digest is. A file somebody edited in place would be listed under
//! the digest it used to have. That costs a fetcher one wasted request and
//! cannot produce a wrong store, because nothing enters a store unverified —
//! which is decision 0048's own price for a listing it cannot check, paid on
//! this side of the wire instead.
//!
//! **The listing is written nowhere.** Not into the store and not beside it:
//! an enumeration living in `history/` would be derived mutable state going
//! stale next to the thing it describes, which is what decision 0030 refused
//! and what 0042 leaned on. This is a rendering, with the standing `log` and
//! `status` have, and the publisher redirects it — conventionally to
//! `offer.txt` beside the exported directory, written last, after `export` has
//! left a consistent copy. What the store may still refresh while producing it
//! is the cache, exactly as every other reading command does, which decision
//! 0035 makes disposable and 0036 makes silent about failing.
//!
//! # Pages
//!
//! Decision 0080 adds a second shape, kept rather than printed. A whole
//! listing is linear in the store, and a fetcher that was current reads all of
//! it to learn about its last few lines. [`Store::publish_offer`] keeps a
//! [`Tip`] at a file beside the copy instead — the heads and the pages, named
//! by their digests — and writes one [`Page`] per publish that changed
//! anything, stating what it added and withdrew. A fetcher that remembers the
//! pages it has applied reads the tip and the pages after them, and one that
//! does not reads them all, which composes to exactly this listing. The first
//! page is a base listing everything, and a fresh one replaces the chain once
//! it is long enough, so the tip stays small at any length of history.
//!
//! That is the one place this module writes, and it writes beside the copy
//! rather than into it: the tip and the pages are the publisher's, as a
//! redirected listing always was, and the previous tip is what the next
//! publish reads to learn what it listed last.
//!
//! [`Travel::TravelsAndUnions`]: super::Travel::TravelsAndUnions

use std::collections::BTreeMap;
use std::fmt;
use std::io;
use std::path::{Path, PathBuf};

use crate::core::RevisionId;
use crate::fs::Filesystem;
use crate::working::SKIPPED_DIR;

use super::{
    NAME_SUFFIX, NAMES_DIR, REVISION_SUFFIXES, REVISIONS_DIR, STORE_DIR, Store, StoreError,
    catalogue, files_claiming, label_of, within,
};

/// The line a manifest starts with.
///
/// Numbered, for the reason the module documentation gives: a reader that does
/// not know this spelling discards the whole file rather than half-reading it,
/// and refetching costs one request.
pub const OFFER_HEADER: &str = "historica-offer-1";

/// What sort of file one line of a manifest names.
///
/// Decision 0048 named the first three and decision 0056 the last two. Not
/// exhaustive, because the set has grown once and a reader is expected to
/// discard a line it cannot classify rather than to refuse the manifest.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[non_exhaustive]
pub enum OfferKind {
    /// A revision document: who recorded what, when, and after what.
    Revision,
    /// A content document of `operations/`, in either of decision 0032's
    /// grammars, and including the forgetting documents decision 0014 writes.
    Operation,
    /// Decision 0017's content that arrives whole, carrying no format.
    Payload,
    /// One file of `skipped/`, stating one rule that travels (decision 0051).
    Rule,
    /// A file of a reserved directory that travels and unions (decision 0053).
    ///
    /// One word for the class rather than one per directory: transport never
    /// learns whose the directory is, and neither does this listing. The path
    /// names the directory, and a reader consults its own registry about it.
    Reserved,
    /// One bookmark file of `names/`, whose name travels (decision 0062).
    ///
    /// The one kind whose path is a **name** rather than an address. That is
    /// not an exception to decision 0048 so much as the one directory 0003's
    /// rule never covered: everywhere else identity is content and a filename
    /// is presentation, and a bookmark's filename is its identity. It is also
    /// the one kind whose bytes change under a path that does not, which a
    /// manifest survives because it is regenerated whole and a fetcher hashes
    /// what arrives against the line that named it.
    Name,
}

impl OfferKind {
    /// The word this kind is written as.
    pub fn as_str(self) -> &'static str {
        match self {
            OfferKind::Revision => "revision",
            OfferKind::Operation => "operation",
            OfferKind::Payload => "payload",
            OfferKind::Rule => "rule",
            OfferKind::Reserved => "reserved",
            OfferKind::Name => "name",
        }
    }

    /// The kind a word names, or nothing where a reader has met a spelling a
    /// later version writes and this one has never heard of.
    pub fn parse(word: &str) -> Option<Self> {
        Some(match word {
            "revision" => OfferKind::Revision,
            "operation" => OfferKind::Operation,
            "payload" => OfferKind::Payload,
            "rule" => OfferKind::Rule,
            "reserved" => OfferKind::Reserved,
            "name" => OfferKind::Name,
            _ => return None,
        })
    }
}

impl fmt::Display for OfferKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

/// One transferable file, as a manifest names it.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct Offered {
    /// What sort of file it is.
    pub kind: OfferKind,
    /// The digest of its bytes, which is what a fetcher hashes it against.
    pub digest: RevisionId,
    /// What it forgets, for a forgetting document. `None` for everything else.
    pub forgets: Option<RevisionId>,
    /// Where it is, relative to the manifest's own directory.
    ///
    /// An address rather than a name (decision 0048): bytes land in the
    /// receiving store under its own digest-derived names, and `arrange` gives
    /// them readable ones there. So no two stores ever have to agree about a
    /// filename — which is just as well, since a store and a partial copy of
    /// it genuinely cannot.
    pub path: String,
}

impl fmt::Display for Offered {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {} ", self.kind, self.digest)?;
        match self.forgets {
            Some(target) => write!(f, "{target} ")?,
            None => write!(f, "- ")?,
        }
        // Last, and written raw: decision 0043's convention is what stands in
        // for an escaping story.
        f.write_str(&self.path)
    }
}

/// The listing of one published copy's transferable files.
///
/// Rendered by [`fmt::Display`], which is the whole file: the header, the
/// heads, and one line per file.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Offer {
    heads: Vec<RevisionId>,
    entries: Vec<Offered>,
}

impl Offer {
    /// Every head the copy has, in digest order.
    pub fn heads(&self) -> &[RevisionId] {
        &self.heads
    }

    /// Every transferable file, in the order the manifest states them.
    ///
    /// **The order is specified**, rather than whatever a walk happened to
    /// produce. Two things want it. A manifest a publisher regenerates on a
    /// timer should be one set of bytes for one copy, so that a copy nothing
    /// has changed produces a file nothing has changed. And the groups are in
    /// decision 0048's fetch order — payloads, then documents, then revisions
    /// — so a fetcher working from the top understates what is reachable at
    /// every moment, rather than leaving a revision naming bytes that never
    /// arrived. Rules and the files of another tool come last: they are
    /// outside that invariant entirely, since no revision names them.
    ///
    /// Within a group the order is the path's, which is a walk's own order and
    /// stable for a given copy.
    pub fn entries(&self) -> &[Offered] {
        &self.entries
    }

    /// Every entry of one kind.
    pub fn of(&self, kind: OfferKind) -> impl Iterator<Item = &Offered> {
        self.entries.iter().filter(move |entry| entry.kind == kind)
    }
}

impl Offer {
    /// Read a manifest, as the fetcher at the far end of a URL reads it.
    ///
    /// Two kinds of strictness, and the parting between them is decision
    /// 0056's. **An unknown kind is a discarded line**, because the set of
    /// kinds has grown once and may grow again, and a file nobody here could
    /// classify is a file this fetcher does not take — which is the
    /// recoverable way to be wrong about it. **An unknown header spelling is a
    /// refused manifest**, because the number is what the grammar changes
    /// under, and a reader that met one and carried on would be guessing at a
    /// format somebody deliberately renumbered. What such a reader does
    /// instead is what has always worked: fetch the archive.
    ///
    /// Everything else is refused where a document is refused. A line with
    /// fewer than four fields, a digest that is not one, or a `head` line
    /// below an entry is a manifest that does not say what it appears to say,
    /// and this is the one place where being lenient would mean fetching a set
    /// nobody described. It costs a refetch, which is what an offer is for.
    pub fn parse(text: &str) -> Result<Self, OfferError> {
        let mut lines = text.lines().enumerate();
        match lines.next() {
            Some((_, line)) if line == OFFER_HEADER => {}
            Some((_, line)) => {
                return Err(OfferError::UnknownFormat {
                    found: line.to_owned(),
                });
            }
            None => {
                return Err(OfferError::UnknownFormat {
                    found: String::new(),
                });
            }
        }

        let mut heads: Vec<RevisionId> = Vec::new();
        let mut entries: Vec<Offered> = Vec::new();
        for (at, line) in lines {
            // Counted as a person counts, from one, since the number is only
            // ever printed at somebody.
            let at = at + 1;
            let stated = |because: &str| OfferError::Malformed {
                line: at,
                because: because.to_owned(),
            };
            if let Some(head) = line.strip_prefix("head ") {
                if !entries.is_empty() {
                    return Err(stated(
                        "a `head` line below an entry; the heads come first, \
                         above every file",
                    ));
                }
                heads.push(
                    head.parse()
                        .map_err(|_| stated("a head that is not a digest"))?,
                );
                continue;
            }
            if let Some(entry) = entry_in(line, at)? {
                entries.push(entry);
            }
        }

        Ok(Self { heads, entries })
    }

    /// The listing a chain of pages states, applied in order from nothing.
    ///
    /// Decision 0080. Each page withdraws what it says is gone and then adds
    /// what it lists, and the result is put in [`Offer::entries`]'s order, so
    /// a chain composes to exactly the listing [`Store::offer`] writes whole
    /// for the same copy — which is what a publisher checks before it trusts a
    /// chain it wrote, and what a fetcher relies on when it reads one.
    ///
    /// A withdrawal of something no earlier page listed is nothing to do: a
    /// fetcher that skipped the pages it had already applied composes the
    /// rest over nothing, and a page may withdraw what one of those listed.
    pub fn composed(heads: Vec<RevisionId>, pages: &[Page]) -> Self {
        let mut held: BTreeMap<String, Offered> = BTreeMap::new();
        for page in pages {
            for entry in &page.gone {
                held.remove(&entry.to_string());
            }
            for entry in &page.added {
                held.insert(entry.to_string(), entry.clone());
            }
        }
        let mut entries: Vec<Offered> = held.into_values().collect();
        canonical(&mut entries);
        Self { heads, entries }
    }
}

/// One entry line, read: `None` where its kind is one this reader has never
/// heard of.
///
/// Discarded rather than refused, and discarded *after* the shape is checked:
/// a line this reader cannot classify is still a line this grammar has to hold
/// together. Decision 0043, read from the other side: split three times and no
/// further, so the path keeps whatever spaces it has.
fn entry_in(line: &str, at: usize) -> Result<Option<Offered>, OfferError> {
    let stated = |because: &str| OfferError::Malformed {
        line: at,
        because: because.to_owned(),
    };
    let mut fields = line.splitn(4, ' ');
    let (Some(kind), Some(digest), Some(forgets), Some(path)) =
        (fields.next(), fields.next(), fields.next(), fields.next())
    else {
        return Err(stated(
            "a line with fewer than four fields; an entry is \
             `<kind> <digest> <forgets|-> <path>`",
        ));
    };
    let Some(kind) = OfferKind::parse(kind) else {
        return Ok(None);
    };
    Ok(Some(Offered {
        kind,
        digest: digest
            .parse()
            .map_err(|_| stated("a digest that is not a digest"))?,
        forgets: match forgets {
            "-" => None,
            target => Some(
                target
                    .parse()
                    .map_err(|_| stated("a forgotten digest that is not a digest"))?,
            ),
        },
        path: path.to_owned(),
    }))
}

/// Put entries in the order [`Offer::entries`] states: by group, and within a
/// group by path.
fn canonical(entries: &mut [Offered]) {
    fn group(kind: OfferKind) -> u8 {
        match kind {
            OfferKind::Payload => 0,
            OfferKind::Operation => 1,
            OfferKind::Revision => 2,
            OfferKind::Rule => 3,
            OfferKind::Reserved => 4,
            OfferKind::Name => 5,
        }
    }
    entries.sort_by(|left, right| {
        group(left.kind)
            .cmp(&group(right.kind))
            .then_with(|| left.path.cmp(&right.path))
    });
}

impl fmt::Display for Offer {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "{OFFER_HEADER}")?;
        for head in &self.heads {
            writeln!(f, "head {head}")?;
        }
        for entry in &self.entries {
            writeln!(f, "{entry}")?;
        }
        Ok(())
    }
}

/// Why a manifest could not be read.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum OfferError {
    /// The first line is not a spelling this reader knows.
    UnknownFormat {
        /// The line as found, which may be anything at all — a manifest is
        /// whatever a URL returned.
        found: String,
    },
    /// A line does not hold what the grammar says a line holds.
    Malformed {
        /// Which line, counted from one, the header being line one.
        line: usize,
        /// What was wrong with it, said for whoever has to fix the publisher.
        because: String,
    },
}

impl fmt::Display for OfferError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            OfferError::UnknownFormat { found } => write!(
                f,
                "this is not a manifest a reader of `{OFFER_HEADER}` can use: \
                 its first line is `{found}`. a manifest states its spelling so \
                 that a stranger can discard it whole rather than half-read it \
                 — fetch the published archive instead, which never stopped \
                 working"
            ),
            OfferError::Malformed { line, because } => {
                write!(f, "line {line} of the manifest is {because}")
            }
        }
    }
}

impl std::error::Error for OfferError {}

/// The line a paged manifest starts with (decision 0080).
///
/// A second number rather than a second meaning for the first: a reader of
/// `historica-offer-1` that met a manifest naming pages would find no files in
/// it and fetch nothing, where a reader that does not know this spelling
/// refuses it and says to fetch the archive.
pub const PAGED_HEADER: &str = "historica-offer-2";

/// The line one page of a paged manifest starts with.
pub const PAGE_HEADER: &str = "historica-offer-page-1";

/// How many pages a manifest names after its base before the next publish
/// that changes anything writes a fresh base instead.
///
/// What bounds the manifest itself, which names each page: sixteen lines, at
/// any length of history, is what a fetcher that was current reads beside the
/// one page it lacks.
const MOST_PAGES: usize = 16;

/// A manifest as a fetcher finds it at the URL it was given.
///
/// Decision 0080 adds the second shape. A whole listing is what `historica
/// offer` prints and what every publisher wrote before; a paged manifest is
/// what `historica offer --into` keeps, and names the pages a fetcher reads.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum Manifest {
    /// Every transferable file, listed whole (decision 0048).
    Whole(Offer),
    /// The heads and the pages that state the listing (decision 0080).
    Paged(Tip),
}

impl Manifest {
    /// Read a manifest in either spelling, and refuse any other.
    pub fn parse(text: &str) -> Result<Self, OfferError> {
        match text.lines().next() {
            Some(PAGED_HEADER) => Tip::parse(text).map(Manifest::Paged),
            _ => Offer::parse(text).map(Manifest::Whole),
        }
    }
}

/// What a paged manifest holds: the heads, and the pages in the order they
/// apply.
///
/// ```text
/// historica-offer-2
/// head <digest>
/// page <digest> <path>
/// ```
///
/// The first page is the **base**, which lists the whole copy as it stood when
/// it was written; each page after it states what one publish added and
/// withdrew. Each page is named by the digest of its bytes and never
/// rewritten, so a fetcher that has applied the base and some of the pages
/// after it reads this file and the pages it has not applied, and nothing
/// else. The heads are the copy's heads, and answer relatedness and nothing
/// else, as decision 0052 has them do in a whole listing.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Tip {
    heads: Vec<RevisionId>,
    pages: Vec<PageRef>,
}

/// One page, as a paged manifest names it.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct PageRef {
    /// The digest of the page's bytes, which a fetcher hashes it against.
    pub digest: RevisionId,
    /// Where it is, relative to the manifest's own directory.
    pub path: String,
}

impl Tip {
    /// Every head the copy has, in digest order.
    pub fn heads(&self) -> &[RevisionId] {
        &self.heads
    }

    /// The pages, the base first and each after it in the order it applies.
    pub fn pages(&self) -> &[PageRef] {
        &self.pages
    }

    /// Read a paged manifest.
    ///
    /// Held to [`Offer::parse`]'s standards: a line of a kind this reader has
    /// never heard of is discarded, and a `head` or `page` line that does not
    /// say what it appears to is refused, as is a `head` below a page.
    pub fn parse(text: &str) -> Result<Self, OfferError> {
        let mut lines = text.lines().enumerate();
        match lines.next() {
            Some((_, PAGED_HEADER)) => {}
            other => {
                return Err(OfferError::UnknownFormat {
                    found: other.map(|(_, line)| line.to_owned()).unwrap_or_default(),
                });
            }
        }
        let mut tip = Tip::default();
        for (at, line) in lines {
            let at = at + 1;
            let stated = |because: &str| OfferError::Malformed {
                line: at,
                because: because.to_owned(),
            };
            if let Some(head) = line.strip_prefix("head ") {
                if !tip.pages.is_empty() {
                    return Err(stated(
                        "a `head` line below a page; the heads come first, \
                         above every page",
                    ));
                }
                tip.heads.push(
                    head.parse()
                        .map_err(|_| stated("a head that is not a digest"))?,
                );
            } else if let Some(rest) = line.strip_prefix("page ") {
                let Some((digest, path)) = rest.split_once(' ') else {
                    return Err(stated(
                        "a page line with no path; a page is `page <digest> <path>`",
                    ));
                };
                tip.pages.push(PageRef {
                    digest: digest
                        .parse()
                        .map_err(|_| stated("a page whose digest is not a digest"))?,
                    path: path.to_owned(),
                });
            }
        }
        Ok(tip)
    }
}

impl fmt::Display for Tip {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "{PAGED_HEADER}")?;
        for head in &self.heads {
            writeln!(f, "head {head}")?;
        }
        for page in &self.pages {
            writeln!(f, "page {} {}", page.digest, page.path)?;
        }
        Ok(())
    }
}

/// What one publish changed in a copy's listing, or the whole of it for a
/// base.
///
/// ```text
/// historica-offer-page-1
/// <kind> <digest> <forgets|-> <path>
/// gone <kind> <digest> <forgets|-> <path>
/// ```
///
/// An entry line is a whole listing's, and means the file is there. A `gone`
/// line is a whole listing's line that the previous one stated and this one
/// does not: a file withdrawn, which is how a `forget`, a `prune`, a target
/// moving off a branch and a bookmark moving each reach a page. Both are in
/// [`Offer::entries`]'s order, the additions first.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Page {
    added: Vec<Offered>,
    gone: Vec<Offered>,
}

impl Page {
    /// What the page lists.
    pub fn added(&self) -> &[Offered] {
        &self.added
    }

    /// What the page withdraws from the pages before it.
    pub fn gone(&self) -> &[Offered] {
        &self.gone
    }

    /// Whether the page states nothing.
    pub fn is_empty(&self) -> bool {
        self.added.is_empty() && self.gone.is_empty()
    }

    /// The page that takes one listing to another.
    pub fn between(before: &[Offered], after: &[Offered]) -> Self {
        let lines = |entries: &[Offered]| -> BTreeMap<String, Offered> {
            entries
                .iter()
                .map(|entry| (entry.to_string(), entry.clone()))
                .collect()
        };
        let (was, is) = (lines(before), lines(after));
        let mut added: Vec<Offered> = is
            .iter()
            .filter(|(line, _)| !was.contains_key(*line))
            .map(|(_, entry)| entry.clone())
            .collect();
        let mut gone: Vec<Offered> = was
            .iter()
            .filter(|(line, _)| !is.contains_key(*line))
            .map(|(_, entry)| entry.clone())
            .collect();
        canonical(&mut added);
        canonical(&mut gone);
        Self { added, gone }
    }

    /// Read a page, held to [`Offer::parse`]'s standards.
    pub fn parse(text: &str) -> Result<Self, OfferError> {
        let mut lines = text.lines().enumerate();
        match lines.next() {
            Some((_, PAGE_HEADER)) => {}
            other => {
                return Err(OfferError::UnknownFormat {
                    found: other.map(|(_, line)| line.to_owned()).unwrap_or_default(),
                });
            }
        }
        let mut page = Page::default();
        for (at, line) in lines {
            let at = at + 1;
            match line.strip_prefix("gone ") {
                Some(rest) => page.gone.extend(entry_in(rest, at)?),
                None => page.added.extend(entry_in(line, at)?),
            }
        }
        Ok(page)
    }
}

impl fmt::Display for Page {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "{PAGE_HEADER}")?;
        for entry in &self.added {
            writeln!(f, "{entry}")?;
        }
        for entry in &self.gone {
            writeln!(f, "gone {entry}")?;
        }
        Ok(())
    }
}

/// What [`Store::publish_offer`] did to the manifest beside a copy.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
#[non_exhaustive]
pub struct Published {
    /// The page this run wrote, or `None` where the listing had not changed.
    pub page: Option<RevisionId>,
    /// Whether that page is a fresh base, listing the whole copy.
    pub base: bool,
    /// How many pages the manifest now names, its base included.
    pub pages: usize,
    /// How many pages the manifest no longer names were removed from beside
    /// it.
    pub removed: usize,
}

/// A page read back from beside a manifest: where the manifest names it, what
/// it says, and how many bytes it is.
type Kept = (PageRef, Page, usize);

impl<F: Filesystem> Store<F> {
    /// List every transferable file this store holds, for a reader that cannot
    /// walk the directory it is in.
    ///
    /// `prefix` is the name of the directory the manifest will sit beside —
    /// `store` for a manifest published next to a `store/` — and every path is
    /// written under it, because decision 0052 resolves a manifest's paths
    /// against the manifest's own directory. An empty prefix writes the paths
    /// from `history/` down, which is the same convention for a manifest
    /// published inside the copy's own root.
    ///
    /// Reads, and writes nothing anywhere. No `check` is run: a manifest
    /// describes what a directory holds rather than vouching for it, the
    /// command that leaves the copy consistent is `export`, and a fetcher
    /// hashes every arriving file regardless — so there is nothing here for a
    /// check to protect.
    pub fn offer(&self, prefix: &str) -> Result<Offer, StoreError> {
        // Decision 0036's pass, which reads only what the cache cannot account
        // for — and taken one entry per file rather than one per digest, since
        // an offer is a listing of a directory rather than a lookup.
        let mut payloads: Vec<Offered> = Vec::new();
        let mut documents: Vec<Offered> = Vec::new();
        for (id, filed) in catalogue::read(&self.files, &self.root, self.cache.as_deref())?.filings
        {
            let entry = Offered {
                kind: match filed.document {
                    true => OfferKind::Operation,
                    false => OfferKind::Payload,
                },
                digest: id,
                // Only a document can forget, and only a document is ever
                // catalogued as forgetting.
                forgets: filed.forgets,
                path: addressed(prefix, &spelled(&filed.path)),
            };
            match filed.document {
                true => documents.push(entry),
                false => payloads.push(entry),
            }
        }

        // Walked and hashed, which is the measurement decision 0048 deferred:
        // these are the small files, the store reads all of them at `open`
        // regardless, and the only thing `open` does not keep is where each one
        // sits. Decision 0043 takes the digest in pieces, so nothing here is
        // held whole to be hashed.
        let mut revisions: Vec<Offered> = Vec::new();
        for path in files_claiming(&self.files, &self.root, REVISIONS_DIR, &REVISION_SUFFIXES)? {
            let Some(label) = label_of(&self.root, &path) else {
                continue;
            };
            let Some(digest) = digest_at(&self.files, &path)? else {
                continue;
            };
            revisions.push(Offered {
                kind: OfferKind::Revision,
                digest,
                forgets: None,
                path: addressed(prefix, &label),
            });
        }

        // Decision 0052 lists `skipped/` and gives the reason: an export's
        // holds shared rules and nothing else, so listing it is safe by
        // construction. This is pointed at a directory rather than told what
        // made it, so it applies decision 0051's axis itself rather than
        // assuming somebody already did — a `private` rule's *filename* is
        // derived from its text (decision 0045), and naming one in a listing
        // published to the world would be the disclosure 0051 wrote the key to
        // prevent. Every rule that travels is named; nothing else under
        // `skipped/` is, the note `init` leaves included, because a file
        // stating no rule states nothing a recipient needs.
        let mut rules: Vec<Offered> = Vec::new();
        let skipped = self.root.join(SKIPPED_DIR);
        for (rule, file) in self.skipped.stating() {
            if !rule.travels() {
                continue;
            }
            let Some(file) = file else { continue };
            let Some(digest) = digest_at(&self.files, &within(&skipped, file))? else {
                continue;
            };
            rules.push(Offered {
                kind: OfferKind::Rule,
                digest,
                forgets: None,
                path: addressed(prefix, &format!("{SKIPPED_DIR}/{file}")),
            });
        }

        // Decision 0062, on the footing 0051 gives the rules above and with
        // the same reason for applying the axis here rather than trusting
        // somebody else to have applied it: a bookmark's *filename* is its
        // name, so naming a private one in a listing published to the world is
        // exactly the disclosure the axis was written to prevent. A bookmark
        // pointing past what this copy holds is not filtered here — this is a
        // listing of a directory rather than a plan, and what put the file
        // there was an `export` that already asked.
        let mut names: Vec<Offered> = Vec::new();
        for (name, bookmark) in &self.names {
            if !bookmark.travels() {
                continue;
            }
            let label = format!("{NAMES_DIR}/{name}{NAME_SUFFIX}");
            let Some(digest) = digest_at(&self.files, &within(&self.root, &label))? else {
                continue;
            };
            names.push(Offered {
                kind: OfferKind::Name,
                digest,
                forgets: None,
                path: addressed(prefix, &label),
            });
        }

        // Decision 0053: found by the walk everything else is found by, and
        // never opened. The class is the whole of what this knows about them,
        // and the path is the whole of what it says.
        let mut reserved: Vec<Offered> = Vec::new();
        for label in self.travelling_files()? {
            let Some(digest) = digest_at(&self.files, &within(&self.root, &label))? else {
                continue;
            };
            reserved.push(Offered {
                kind: OfferKind::Reserved,
                digest,
                forgets: None,
                path: addressed(prefix, &label),
            });
        }

        // The order [`Offer::entries`] states: content first and revisions
        // last, which is `receive`'s order and a fetcher's, then the two kinds
        // no revision names.
        let mut entries: Vec<Offered> = Vec::new();
        for group in [
            &mut payloads,
            &mut documents,
            &mut revisions,
            &mut rules,
            &mut reserved,
            &mut names,
        ] {
            group.sort_by(|left, right| left.path.cmp(&right.path));
            entries.append(group);
        }

        Ok(Offer {
            // The graph's heads, superseded ones included: a listing is not a
            // rendering, and every one of them answers relatedness.
            heads: self.history().heads().into_iter().collect(),
            entries,
        })
    }
}

impl<F: Filesystem> Store<F> {
    /// Keep a paged manifest at `manifest`, beside the copy this store is.
    ///
    /// Decision 0080. The listing is [`Store::offer`]'s, for `prefix`. What is
    /// kept beside the copy is the manifest, naming the heads and the pages,
    /// and the pages themselves in a directory named after it — `offer-pages/`
    /// beside `offer.txt`. A run compares the listing with what the pages it
    /// finds already state, and:
    ///
    /// - where nothing changed, writes nothing, so a copy nothing changed
    ///   keeps a manifest nothing changed;
    /// - where something did, writes one page stating what was added and what
    ///   withdrawn, and a manifest naming it after the others;
    /// - where there are already sixteen pages after the base, or the pages
    ///   after it would come to more bytes than the base, or there is no
    ///   manifest it can read back whole, writes a fresh base listing
    ///   everything, and a manifest naming it alone.
    ///
    /// The page is written before the manifest, and a page is never rewritten,
    /// so a fetcher holding the previous manifest reads the pages it names. A
    /// page no manifest names any more is removed last; a fetcher still
    /// working from it is told nothing is there, and reads the manifest again,
    /// which is decision 0048's answer to a publisher who moved on.
    pub fn publish_offer(&self, prefix: &str, manifest: &Path) -> Result<Published, StoreError> {
        let listing = self.offer(prefix)?;
        let beside = manifest.parent().map(Path::to_path_buf).unwrap_or_default();
        let directory = pages_directory(manifest);

        let mut chain: Vec<(PageRef, usize)> = Vec::new();
        let mut published = Published::default();
        if let Some(kept) = kept_pages(&self.files, manifest, &beside) {
            let pages: Vec<Page> = kept.iter().map(|(_, page, _)| page.clone()).collect();
            let before = Offer::composed(Vec::new(), &pages);
            let page = Page::between(before.entries(), listing.entries());
            chain = kept
                .iter()
                .map(|(at, _, size)| (at.clone(), *size))
                .collect();
            if !page.is_empty() {
                let size = page.to_string().len();
                let base = chain.first().map_or(0, |(_, size)| *size);
                let after: usize = chain.iter().skip(1).map(|(_, size)| size).sum();
                if chain.len() > MOST_PAGES || after + size > base {
                    chain.clear();
                } else {
                    let written = write_page(&self.files, &beside, &directory, &page)?;
                    published.page = Some(written.0.digest);
                    chain.push(written);
                }
            }
        }
        if chain.is_empty() {
            let base = Page {
                added: listing.entries().to_vec(),
                gone: Vec::new(),
            };
            let written = write_page(&self.files, &beside, &directory, &base)?;
            published.page = Some(written.0.digest);
            published.base = true;
            chain.push(written);
        }

        let tip = Tip {
            heads: listing.heads().to_vec(),
            pages: chain.iter().map(|(at, _)| at.clone()).collect(),
        };
        let text = tip.to_string();
        let unchanged = self
            .files
            .read(manifest)
            .is_ok_and(|held| held == text.as_bytes());
        if !unchanged {
            self.files
                .write(manifest, text.as_bytes())
                .map_err(|error| StoreError::io(manifest, error))?;
        }
        published.pages = tip.pages.len();

        // Last, so that a fetcher reading the manifest just replaced finds
        // every page it names. Only a file named as a page is: whatever else
        // somebody keeps in the directory is theirs.
        let named: Vec<RevisionId> = tip.pages.iter().map(|page| page.digest).collect();
        let pages = beside.join(&directory);
        let entries = match self.files.entries(&pages) {
            Ok(entries) => entries,
            Err(error) if error.kind() == io::ErrorKind::NotFound => Vec::new(),
            Err(error) => return Err(StoreError::io(&pages, error)),
        };
        for entry in entries {
            let Some(digest) = entry
                .path
                .file_name()
                .and_then(|name| name.to_str())
                .and_then(|name| name.strip_suffix(".txt"))
                .and_then(|stem| stem.parse::<RevisionId>().ok())
            else {
                continue;
            };
            if entry.kind.is_file() && !named.contains(&digest) {
                self.files
                    .remove_file(&entry.path)
                    .map_err(|error| StoreError::io(&entry.path, error))?;
                published.removed += 1;
            }
        }
        Ok(published)
    }
}

/// The directory a manifest's pages are kept in: its name without the
/// extension, and `-pages` after it.
fn pages_directory(manifest: &Path) -> String {
    let stem = manifest
        .file_stem()
        .map(|stem| stem.to_string_lossy().into_owned())
        .unwrap_or_default();
    format!("{stem}-pages")
}

/// The pages the manifest at `manifest` names, each read back and hashed, or
/// nothing where any of it cannot be.
///
/// Nothing is not an error: a manifest that is missing, whole rather than
/// paged, or naming a page that is gone or not what it says is one the next
/// run replaces with a fresh base, which is what a publisher starting over
/// would write anyway.
fn kept_pages<F: Filesystem + ?Sized>(
    files: &F,
    manifest: &Path,
    beside: &Path,
) -> Option<Vec<Kept>> {
    let text = String::from_utf8(files.read(manifest).ok()?).ok()?;
    let Manifest::Paged(tip) = Manifest::parse(&text).ok()? else {
        return None;
    };
    let mut kept = Vec::new();
    for at in tip.pages {
        let bytes = files.read(&within(beside, &at.path)).ok()?;
        if crate::format::digest(&bytes) != at.digest {
            return None;
        }
        let page = Page::parse(std::str::from_utf8(&bytes).ok()?).ok()?;
        kept.push((at, page, bytes.len()));
    }
    (!kept.is_empty()).then_some(kept)
}

/// Write one page under its digest, in the pages directory beside the
/// manifest, and say where the manifest will name it.
fn write_page<F: Filesystem + ?Sized>(
    files: &F,
    beside: &Path,
    directory: &str,
    page: &Page,
) -> Result<(PageRef, usize), StoreError> {
    let text = page.to_string();
    let digest = crate::format::digest(text.as_bytes());
    let path = format!("{directory}/{digest}.txt");
    let file = within(beside, &path);
    let parent: PathBuf = beside.join(directory);
    files
        .create_directory(&parent)
        .map_err(|error| StoreError::io(&parent, error))?;
    match files.create_new(&file, text.as_bytes()) {
        Ok(()) => {}
        // The name is the digest, so a file already there is this page —
        // unless somebody wrote something else under it, which is put right.
        Err(error) if error.kind() == io::ErrorKind::AlreadyExists => {
            if files.read(&file).ok().as_deref() != Some(text.as_bytes()) {
                files
                    .write(&file, text.as_bytes())
                    .map_err(|error| StoreError::io(&file, error))?;
            }
        }
        Err(error) => return Err(StoreError::io(&file, error)),
    }
    Ok((PageRef { digest, path }, text.len()))
}

/// One store-relative label, said as a fetcher will ask for it.
fn addressed(prefix: &str, label: &str) -> String {
    match prefix.is_empty() {
        true => format!("{STORE_DIR}/{label}"),
        false => format!("{prefix}/{STORE_DIR}/{label}"),
    }
}

/// One relative path, said with `/` for a separator.
///
/// A manifest is read on a machine that is not this one, so the separator is
/// the format's rather than the platform's — the rule decision 0033 already
/// applies to every path a document holds.
fn spelled(path: &Path) -> String {
    path.components()
        .map(|part| part.as_os_str().to_string_lossy())
        .collect::<Vec<_>>()
        .join("/")
}

/// What a file hashes to, or nothing where it is no longer there.
///
/// A listing is worked out from a walk rather than held under a lock, so a
/// file somebody removed in between is a file the next listing will not name.
/// Refusing to render the whole manifest over one of them would be a worse
/// answer than a manifest one line shorter.
fn digest_at<F: Filesystem + ?Sized>(
    files: &F,
    path: &Path,
) -> Result<Option<RevisionId>, StoreError> {
    match crate::fs::digest_of(files, path) {
        Ok(digest) => Ok(Some(digest)),
        Err(error) if error.kind() == io::ErrorKind::NotFound => Ok(None),
        Err(error) => Err(StoreError::io(path, error)),
    }
}
